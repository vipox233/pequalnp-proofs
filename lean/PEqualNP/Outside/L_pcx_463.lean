import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_463_aux

noncomputable section

open MvPolynomial PEqualNP.ProofComplexity

private abbrev K := ZMod 2

/-! ### Section 1: Basic `ZMod 2` and `MvPolynomial` Degree Helpers -/

private lemma z2_add_self (x : K) : x + x = 0 := by fin_cases x <;> rfl

private lemma z2_mul_self (x : K) : x * x = x := by fin_cases x <;> rfl

private lemma z2_cases (x : K) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_eq_one_of_ne_zero {x : K} (h : x ≠ 0) : x = 1 := by
  rcases z2_cases x with rfl | rfl
  · exact absurd rfl h
  · rfl

private lemma poly_add_self {σ : Type} (p : MvPolynomial σ K) : p + p = 0 := by
  ext m
  simp [z2_add_self]

private lemma poly_sub_eq_add {σ : Type} (p q : MvPolynomial σ K) : p - q = p + q := by
  have hq : q + q = 0 := poly_add_self q
  linear_combination -hq

private lemma poly_sq_add {σ : Type} (p q : MvPolynomial σ K) :
    (p + q) * (p + q) + (p + q) = (p * p + p) + (q * q + q) := by
  have hpq : p * q + p * q = 0 := poly_add_self (p * q)
  linear_combination hpq

private lemma poly_eq_sum_monomials {σ : Type} (p : MvPolynomial σ K) :
    p = ∑ m ∈ p.support, monomial m 1 := by
  conv_lhs => rw [p.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hne : p.coeff m ≠ 0 := mem_support_iff.mp hm
  rw [z2_eq_one_of_ne_zero hne]

private lemma totalDegree_sum_le_of_forall {σ : Type} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (B : ℕ) (h : ∀ i ∈ s, (f i).totalDegree ≤ B) :
    (∑ i ∈ s, f i).totalDegree ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (totalDegree_add _ _)
      (max_le (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

private lemma totalDegree_prod_le_sum {σ : Type} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact le_trans (totalDegree_mul _ _) (Nat.add_le_add_left ih _)

private lemma totalDegree_X_mul_of_ne_zero {σ : Type} (v : σ) {p : MvPolynomial σ K} (hp : p ≠ 0) :
    (X v * p).totalDegree = 1 + p.totalDegree := by
  classical
  have h1 : (X v * p).totalDegree ≤ 1 + p.totalDegree := by
    exact le_trans (totalDegree_mul (X v) p) (by simp)
  have h2 : 1 + p.totalDegree ≤ (X v * p).totalDegree := by
    have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr (fun h => hp (by ext m; simp [h]))
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image p.support (fun m => m.sum fun _ e => e) hne
    have hdeg_p : p.totalDegree = m.sum fun _ e => e := by
      unfold totalDegree
      apply le_antisymm
      · exact Finset.sup_le fun m' hm' => hmax m' hm'
      · exact Finset.le_sup (f := fun m => m.sum fun _ e => e) hm
    have hcoeff : (X v * p).coeff (Finsupp.single v 1 + m) = p.coeff m := by
      conv_lhs => rw [p.as_sum, Finset.mul_sum]
      rw [MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single m]
      · rw [X, monomial_mul_monomial, one_mul, coeff_monomial]; simp
      · intro b _ hbm
        rw [X, monomial_mul_monomial, one_mul, coeff_monomial]
        have hne' : Finsupp.single v 1 + b ≠ Finsupp.single v 1 + m := fun h => hbm (add_left_cancel h)
        simp [hne']
      · intro hnm
        exact absurd hm hnm
    have hmem : Finsupp.single v 1 + m ∈ (X v * p).support := by
      rw [mem_support_iff, hcoeff]
      exact mem_support_iff.mp hm
    have hle := Finset.le_sup (f := fun d : σ →₀ ℕ => d.sum fun _ e => e) hmem
    have hsum : (Finsupp.single v 1 + m).sum (fun _ e => e) = 1 + m.sum (fun _ e => e) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rw [hdeg_p, ← hsum]
    exact hle
  exact le_antisymm h1 h2

private lemma totalDegree_aeval_le {σ τ : Type} (g : σ → MvPolynomial τ K) (D : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ D) (p : MvPolynomial σ K) :
    (aeval g p).totalDegree ≤ p.totalDegree * D := by
  conv_lhs => rw [poly_eq_sum_monomials p, map_sum]
  apply totalDegree_sum_le_of_forall
  intro m hm
  have hm_le : (m.sum fun _ e => e) ≤ p.totalDegree :=
    Finset.le_sup (f := fun d : σ →₀ ℕ => d.sum fun _ e => e) hm
  have hmon : aeval g (monomial m (1 : K)) = ∏ v ∈ m.support, g v ^ m v := by
    rw [aeval_monomial, map_one, one_mul]; rfl
  rw [hmon]
  calc (∏ v ∈ m.support, g v ^ m v).totalDegree
      ≤ ∑ v ∈ m.support, (g v ^ m v).totalDegree := totalDegree_prod_le_sum _ _
    _ ≤ ∑ v ∈ m.support, m v * (g v).totalDegree :=
        Finset.sum_le_sum fun v _ => totalDegree_pow _ _
    _ ≤ ∑ v ∈ m.support, m v * D :=
        Finset.sum_le_sum fun v _ => Nat.mul_le_mul_left _ (hg v)
    _ = (m.sum fun _ e => e) * D := by rw [← Finset.sum_mul]; rfl
    _ ≤ p.totalDegree * D := Nat.mul_le_mul_right D hm_le

private lemma totalDegree_monomial_one {σ : Type} (m : σ →₀ ℕ) :
    (monomial m (1 : K)).totalDegree = m.sum (fun _ e => e) := by
  rw [totalDegree_monomial m (one_ne_zero : (1 : K) ≠ 0)]

/-! ### Section 2: `PCDerivable` Toolkit -/

private lemma pc_mono {σ : Type} {F G : Set (MvPolynomial σ K)} {B1 B2 : ℕ} {p : MvPolynomial σ K}
    (hFG : F ⊆ G) (hB : B1 ≤ B2) (h : PCDerivable F B1 p) : PCDerivable G B2 p := by
  induction h with
  | ax hp hdeg => exact PCDerivable.ax (hFG hp) (le_trans hdeg hB)
  | zero => exact PCDerivable.zero
  | add _ _ ih1 ih2 => exact PCDerivable.add ih1 ih2
  | mulX j _ hdeg ih => exact PCDerivable.mulX j ih (le_trans hdeg hB)

private lemma pc_sum {σ : Type} {ι : Type*} {F : Set (MvPolynomial σ K)} {B : ℕ}
    (s : Finset ι) (f : ι → MvPolynomial σ K) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PCDerivable.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma pc_smul_C {σ : Type} {F : Set (MvPolynomial σ K)} {B : ℕ} (c : K)
    {p : MvPolynomial σ K} (h : PCDerivable F B p) : PCDerivable F B (C c * p) := by
  rcases z2_cases c with rfl | rfl
  · rw [map_zero, zero_mul]; exact PCDerivable.zero
  · rw [map_one, one_mul]; exact h

private lemma pc_totalDegree_le {σ : Type} {F : Set (MvPolynomial σ K)} {B : ℕ}
    {p : MvPolynomial σ K} (h : PCDerivable F B p) : p.totalDegree ≤ B := by
  induction h with
  | ax _ hdeg => exact hdeg
  | zero => simp
  | add _ _ ih1 ih2 => exact le_trans (totalDegree_add _ _) (max_le ih1 ih2)
  | mulX _ _ hdeg _ => exact hdeg

private lemma pc_mul_monomial {σ : Type} {F : Set (MvPolynomial σ K)} {B : ℕ}
    (m : σ →₀ ℕ) {q : MvPolynomial σ K} (hq : PCDerivable F B q)
    (hdeg : (m.sum fun _ e => e) + q.totalDegree ≤ B) :
    PCDerivable F B (monomial m 1 * q) := by
  classical
  induction m using Finsupp.induction with
  | zero =>
    simpa [monomial_zero'] using hq
  | single_add v e m hvm he ih =>
    have hsum_step : (Finsupp.single v e + m).sum (fun _ k => k) = e + m.sum (fun _ k => k) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    have hq_m : PCDerivable F B (monomial m 1 * q) := ih (by omega)
    have hpow : ∀ k ≤ e, PCDerivable F B (X v ^ k * (monomial m 1 * q)) := by
      intro k hk
      induction k with
      | zero => simpa using hq_m
      | succ k ihk =>
        rw [pow_succ', mul_assoc]
        refine PCDerivable.mulX v (ihk (by omega)) ?_
        calc (X v * (X v ^ k * (monomial m 1 * q))).totalDegree
            ≤ (X v).totalDegree + (X v ^ k * (monomial m 1 * q)).totalDegree := totalDegree_mul _ _
          _ ≤ 1 + ((X v ^ k).totalDegree + (monomial m 1 * q).totalDegree) := by
              have h1 : (X v : MvPolynomial σ K).totalDegree ≤ 1 := by simp
              have h2 := totalDegree_mul (X v ^ k) (monomial m 1 * q)
              omega
          _ ≤ 1 + (k + ((m.sum fun _ c => c) + q.totalDegree)) := by
              have h1 : (X v ^ k : MvPolynomial σ K).totalDegree ≤ k :=
                le_trans (totalDegree_pow _ _) (by simp)
              have h2 : (monomial m 1 * q).totalDegree ≤ (m.sum fun _ c => c) + q.totalDegree := by
                exact le_trans (totalDegree_mul _ _) (by rw [totalDegree_monomial_one])
              omega
          _ ≤ B := by omega
    have hmon_eq : monomial (Finsupp.single v e + m) (1 : K) = X v ^ e * monomial m 1 := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
    rw [hmon_eq, mul_assoc]
    exact hpow e (le_refl e)

private lemma pc_mul_left {σ : Type} {F : Set (MvPolynomial σ K)} {B : ℕ}
    (p : MvPolynomial σ K) {q : MvPolynomial σ K} (hq : PCDerivable F B q)
    (hdeg : p.totalDegree + q.totalDegree ≤ B) :
    PCDerivable F B (p * q) := by
  rw [poly_eq_sum_monomials p, Finset.sum_mul]
  apply pc_sum
  intro m hm
  have hm_le : (m.sum fun _ e => e) ≤ p.totalDegree :=
    Finset.le_sup (f := fun d : σ →₀ ℕ => d.sum fun _ e => e) hm
  exact pc_mul_monomial m hq (by omega)

private lemma pc_mul_derivation {σ : Type} {F H : Set (MvPolynomial σ K)} {B E Dout : ℕ}
    (hBE : B + E ≤ Dout)
    (r : MvPolynomial σ K) (hr : r.totalDegree ≤ E) {p : MvPolynomial σ K}
    (hp : PCDerivable F B p)
    (hax : ∀ g ∈ F, g.totalDegree ≤ B → PCDerivable H Dout (r * g)) :
    PCDerivable H Dout (r * p) := by
  induction hp with
  | ax hg hdeg => exact hax _ hg hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [mul_add]
    exact PCDerivable.add ih1 ih2
  | @mulX j q _ hdeg ih =>
    have heq : r * (X j * q) = X j * (r * q) := by ring
    rw [heq]
    refine PCDerivable.mulX j ih ?_
    rw [← heq]
    exact le_trans (totalDegree_mul _ _) (by omega)

private lemma pc_bool_sq {σ : Type} {F : Set (MvPolynomial σ K)}
    (hbool : ∀ v : σ, X v * X v + X v ∈ F) (p : MvPolynomial σ K) :
    PCDerivable F (2 * p.totalDegree) (p * p + p) := by
  have hmon : ∀ m : σ →₀ ℕ,
      PCDerivable F (2 * (m.sum fun _ e => e)) (monomial m 1 * monomial m 1 + monomial m 1) := by
    intro m
    classical
    induction m using Finsupp.induction with
    | zero =>
      have hz : monomial (0 : σ →₀ ℕ) (1 : K) * monomial 0 1 + monomial 0 1 = 0 := by
        rw [monomial_zero', map_one, one_mul]; exact poly_add_self 1
      rw [hz]; exact PCDerivable.zero
    | single_add v e m hvm he ih =>
      have hpow : ∀ k : ℕ,
          PCDerivable F (2 * (k + m.sum fun _ c => c))
            ((X v ^ k * monomial m 1) * (X v ^ k * monomial m 1) + X v ^ k * monomial m 1) := by
        intro k
        induction k with
        | zero => simpa using ih
        | succ k ihk =>
          set q : MvPolynomial σ K := X v ^ k * monomial m 1
          have hqdeg : q.totalDegree ≤ k + m.sum (fun _ c => c) := by
            calc q.totalDegree ≤ (X v ^ k).totalDegree + (monomial m 1).totalDegree := totalDegree_mul _ _
              _ ≤ k + m.sum (fun _ c => c) := by
                  have h1 : (X v ^ k : MvPolynomial σ K).totalDegree ≤ k :=
                    le_trans (totalDegree_pow _ _) (by simp)
                  rw [totalDegree_monomial_one]; omega
          have hid : (X v ^ (k + 1) * monomial m 1) * (X v ^ (k + 1) * monomial m 1) +
              X v ^ (k + 1) * monomial m 1 =
              (q * q) * (X v * X v + X v) + X v * (q * q + q) := by
            have h2 : X v * (q * q) + X v * (q * q) = 0 := poly_add_self _
            have hstep : X v ^ (k + 1) * monomial m 1 = X v * q := by simp only [q, pow_succ']; ring
            rw [hstep]
            linear_combination -h2
          rw [hid]
          refine PCDerivable.add ?_ ?_
          · refine pc_mul_left (q * q) (PCDerivable.ax (hbool v) ?_) ?_
            · calc (X v * X v + X v : MvPolynomial σ K).totalDegree
                  ≤ max (X v * X v : MvPolynomial σ K).totalDegree (X v : MvPolynomial σ K).totalDegree :=
                    totalDegree_add _ _
                _ ≤ 2 := max_le (le_trans (totalDegree_mul _ _) (by simp)) (by simp)
                _ ≤ 2 * (k + 1 + m.sum fun _ c => c) := by omega
            · have h1 : (q * q).totalDegree ≤ 2 * (k + m.sum fun _ c => c) := by
                exact le_trans (totalDegree_mul _ _) (by omega)
              have h2 : (X v * X v + X v : MvPolynomial σ K).totalDegree ≤ 2 :=
                le_trans (totalDegree_add _ _) (max_le (le_trans (totalDegree_mul _ _) (by simp)) (by simp))
              omega
          · refine PCDerivable.mulX v (pc_mono (subset_refl F) (by omega) ihk) ?_
            have h1 : (q * q + q).totalDegree ≤ 2 * (k + m.sum fun _ c => c) :=
              pc_totalDegree_le ihk
            calc (X v * (q * q + q)).totalDegree
                ≤ (X v).totalDegree + (q * q + q).totalDegree := totalDegree_mul _ _
              _ ≤ 1 + 2 * (k + m.sum fun _ c => c) := by
                  have : (X v : MvPolynomial σ K).totalDegree ≤ 1 := by simp
                  omega
              _ ≤ 2 * (k + 1 + m.sum fun _ c => c) := by omega
      have hsum_step : (Finsupp.single v e + m).sum (fun _ c => c) = e + m.sum (fun _ c => c) := by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
        simp
      have hmon_eq : monomial (Finsupp.single v e + m) (1 : K) = X v ^ e * monomial m 1 := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
      rw [hsum_step, hmon_eq]
      exact hpow e
  have hsum_sq : ∀ (s : Finset (σ →₀ ℕ)),
      (∑ m ∈ s, monomial m (1 : K)) * (∑ m ∈ s, monomial m (1 : K)) + (∑ m ∈ s, monomial m (1 : K)) =
      ∑ m ∈ s, (monomial m (1 : K) * monomial m (1 : K) + monomial m (1 : K)) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, poly_sq_add, ih]
  have hp_sq : p * p + p = ∑ m ∈ p.support, (monomial m (1 : K) * monomial m (1 : K) + monomial m (1 : K)) := by
    conv_lhs => rw [poly_eq_sum_monomials p]
    exact hsum_sq p.support
  rw [hp_sq]
  apply pc_sum
  intro m hm
  have hm_le : (m.sum fun _ e => e) ≤ p.totalDegree :=
    Finset.le_sup (f := fun d : σ →₀ ℕ => d.sum fun _ e => e) hm
  exact pc_mono (subset_refl F) (by omega) (hmon m)

private lemma pc_rename {σ τ : Type} (f : σ → τ) {F : Set (MvPolynomial σ K)}
    {H : Set (MvPolynomial τ K)} {B : ℕ} {p : MvPolynomial σ K}
    (hp : PCDerivable F B p)
    (hax : ∀ g ∈ F, g.totalDegree ≤ B → PCDerivable H B (rename f g)) :
    PCDerivable H B (rename f p) := by
  induction hp with
  | ax hg hdeg => exact hax _ hg hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add]
    exact PCDerivable.add ih1 ih2
  | mulX j _ hdeg ih =>
    rw [map_mul, rename_X]
    refine PCDerivable.mulX (f j) ih ?_
    rw [← rename_X, ← map_mul]
    exact le_trans (totalDegree_rename_le f _) hdeg

private lemma pc_aeval {σ τ : Type} (g : σ → MvPolynomial τ K) (D_var : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ D_var)
    {F : Set (MvPolynomial σ K)} {H : Set (MvPolynomial τ K)} {B : ℕ} {p : MvPolynomial σ K}
    (hp : PCDerivable F B p)
    (hax : ∀ q ∈ F, q.totalDegree ≤ B → PCDerivable H (B * D_var) (aeval g q)) :
    PCDerivable H (B * D_var) (aeval g p) := by
  induction hp with
  | ax hq hdeg => exact hax _ hq hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add]
    exact PCDerivable.add ih1 ih2
  | @mulX j q _ hdeg ih =>
    rw [map_mul, aeval_X]
    by_cases hq0 : q = 0
    · subst hq0; simpa using PCDerivable.zero
    · have hqdeg : q.totalDegree + 1 ≤ B := by
        have := totalDegree_X_mul_of_ne_zero j hq0
        omega
      refine pc_mul_left (g j) ih ?_
      have h1 := hg j
      have h2 := totalDegree_aeval_le g D_var hg q
      have h3 : (q.totalDegree + 1) * D_var ≤ B * D_var := Nat.mul_le_mul_right D_var hqdeg
      linarith

/-! ### Section 3: Formal Boolean Completeness on `MvPolynomial W (ZMod 2)` -/

private def boolAx (W : Type) : Set (MvPolynomial W K) :=
  Set.range fun w : W => X w * X w + X w

private def sfFinsupp {W : Type} [DecidableEq W] (m : W →₀ ℕ) : W →₀ ℕ :=
  m.mapRange (fun e => if e = 0 then 0 else 1) (by simp)

private lemma sfFinsupp_apply {W : Type} [DecidableEq W] (m : W →₀ ℕ) (w : W) :
    sfFinsupp m w = if m w = 0 then 0 else 1 := by
  simp [sfFinsupp]

private lemma sfFinsupp_le {W : Type} [DecidableEq W] (m : W →₀ ℕ) (w : W) :
    sfFinsupp m w ≤ m w := by
  rw [sfFinsupp_apply]
  split_ifs with h
  · exact Nat.zero_le _
  · omega

private lemma sfFinsupp_le_one {W : Type} [DecidableEq W] (m : W →₀ ℕ) (w : W) :
    sfFinsupp m w ≤ 1 := by
  rw [sfFinsupp_apply]; split_ifs <;> omega

private lemma sfFinsupp_support {W : Type} [DecidableEq W] (m : W →₀ ℕ) :
    (sfFinsupp m).support = m.support := by
  ext w
  simp [Finsupp.mem_support_iff, sfFinsupp_apply]

private lemma eval_monomial_sf {W : Type} [DecidableEq W] (v : W → K) (m : W →₀ ℕ) :
    eval v (monomial (sfFinsupp m) (1 : K)) = eval v (monomial m (1 : K)) := by
  rw [eval_monomial, eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod, sfFinsupp_support]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hne : m w ≠ 0 := Finsupp.mem_support_iff.mp hw
  rw [sfFinsupp_apply, ite_eq_right_iff.mpr (fun h => absurd h hne), pow_one]
  have hpow : ∀ e ≥ 1, (v w) ^ e = v w := by
    intro e he
    induction e with
    | zero => omega
    | succ e ihe =>
      cases e with
      | zero => simp
      | succ e =>
        rw [pow_succ, ihe (by omega), z2_mul_self]
  exact (hpow (m w) (by omega)).symm

private lemma pc_monomial_sf {W : Type} [DecidableEq W] (m : W →₀ ℕ) :
    PCDerivable (boolAx W) (m.sum fun _ e => e) (monomial m 1 + monomial (sfFinsupp m) 1) := by
  have hgen : ∀ n : ℕ, ∀ m : W →₀ ℕ, (m.sum fun _ e => e) = n →
      PCDerivable (boolAx W) n (monomial m 1 + monomial (sfFinsupp m) 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro m hmn
      by_cases hsf : m = sfFinsupp m
      · rw [← hsf, poly_add_self]; exact PCDerivable.zero
      · have hex : ∃ w : W, 2 ≤ m w := by
          by_contra h
          push Not at h
          apply hsf
          ext w
          rw [sfFinsupp_apply]
          have := h w
          split_ifs <;> omega
        obtain ⟨w, hw⟩ := hex
        let m' : W →₀ ℕ := m - Finsupp.single w 2
        let m1 : W →₀ ℕ := Finsupp.single w 1 + m'
        have hm_eq : m = Finsupp.single w 2 + m' := by
          ext u
          by_cases hu : u = w
          · subst u; simp [m']; omega
          · simp [m', hu]
        have hsum_m : (m.sum fun _ e => e) = 2 + (m'.sum fun _ e => e) := by
          rw [hm_eq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
          simp
        have hsum_m1 : (m1.sum fun _ e => e) = 1 + (m'.sum fun _ e => e) := by
          simp only [m1]
          rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
          simp
        have hsf_eq : sfFinsupp m = sfFinsupp m1 := by
          ext u
          rw [sfFinsupp_apply, sfFinsupp_apply]
          by_cases hu : u = w
          · subst u
            have h1 : m w ≠ 0 := by omega
            have h2 : m1 w ≠ 0 := by simp [m1]
            simp [h1, h2]
          · have h1 : m1 u = m u := by simp [m1, m', hu]
            rw [h1]
        have hstep1 : PCDerivable (boolAx W) n (monomial m 1 + monomial m1 1) := by
          have heq : monomial m (1 : K) + monomial m1 1 =
              monomial m' 1 * (X w * X w + X w) := by
            rw [hm_eq, show m1 = Finsupp.single w 1 + m' from rfl, mul_add]
            have h1 : monomial (Finsupp.single w 2 + m') (1 : K) = monomial m' 1 * (X w * X w) := by
              rw [← pow_two, X_pow_eq_monomial, monomial_mul_monomial, mul_one, add_comm]
            have h2 : monomial (Finsupp.single w 1 + m') (1 : K) = monomial m' 1 * X w := by
              rw [X, monomial_mul_monomial, mul_one, add_comm]
            rw [h1, h2]
          rw [heq]
          refine pc_mul_monomial m' (PCDerivable.ax ⟨w, rfl⟩ ?_) ?_
          · calc (X w * X w + X w : MvPolynomial W K).totalDegree
                ≤ max (X w * X w : MvPolynomial W K).totalDegree (X w : MvPolynomial W K).totalDegree :=
                  totalDegree_add _ _
              _ ≤ 2 := max_le (le_trans (totalDegree_mul _ _) (by simp)) (by simp)
              _ ≤ n := by omega
          · have hdeg2 : (X w * X w + X w : MvPolynomial W K).totalDegree ≤ 2 :=
              le_trans (totalDegree_add _ _) (max_le (le_trans (totalDegree_mul _ _) (by simp)) (by simp))
            omega
        have hstep2 : PCDerivable (boolAx W) (1 + m'.sum fun _ e => e)
            (monomial m1 1 + monomial (sfFinsupp m1) 1) :=
          ih (1 + m'.sum fun _ e => e) (by omega) m1 hsum_m1
        have hcomb : monomial m (1 : K) + monomial (sfFinsupp m) 1 =
            (monomial m 1 + monomial m1 1) + (monomial m1 1 + monomial (sfFinsupp m1) 1) := by
          rw [hsf_eq]
          have := poly_add_self (monomial m1 (1 : K))
          linear_combination -this
        rw [hcomb]
        exact PCDerivable.add hstep1 (pc_mono (subset_refl _) (by omega) hstep2)
  exact hgen _ m rfl

private def multilin {W : Type} [DecidableEq W] (p : MvPolynomial W K) : MvPolynomial W K :=
  ∑ m ∈ p.support, monomial (sfFinsupp m) 1

private lemma pc_add_multilin {W : Type} [DecidableEq W] (p : MvPolynomial W K) :
    PCDerivable (boolAx W) p.totalDegree (p + multilin p) := by
  have hq : p + multilin p = ∑ m ∈ p.support, (monomial m (1 : K) + monomial (sfFinsupp m) 1) := by
    unfold multilin
    conv_lhs => arg 1; rw [poly_eq_sum_monomials p]
    rw [← Finset.sum_add_distrib]
  rw [hq]
  apply pc_sum
  intro m hm
  have hm_le : (m.sum fun _ e => e) ≤ p.totalDegree :=
    Finset.le_sup (f := fun d : W →₀ ℕ => d.sum fun _ e => e) hm
  exact pc_mono (subset_refl _) hm_le (pc_monomial_sf m)

private lemma eval_multilin {W : Type} [DecidableEq W] (v : W → K) (p : MvPolynomial W K) :
    eval v (multilin p) = eval v p := by
  conv_rhs => rw [poly_eq_sum_monomials p]
  unfold multilin
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun m _ => eval_monomial_sf v m

private lemma multilin_is_sf {W : Type} [DecidableEq W] (p : MvPolynomial W K) :
    ∀ m ∈ (multilin p).support, ∀ w : W, m w ≤ 1 := by
  intro m hm w
  have hmem : m ∈ (p.support.image sfFinsupp) := by
    by_contra hnot
    have hcoeff : (multilin p).coeff m = 0 := by
      unfold multilin
      rw [coeff_sum]
      apply Finset.sum_eq_zero
      intro m' hm'
      rw [coeff_monomial]
      simp [show sfFinsupp m' ≠ m from fun heq => hnot (Finset.mem_image.mpr ⟨m', hm', heq⟩)]
    exact mem_support_iff.mp hm hcoeff
  obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hmem
  exact sfFinsupp_le_one m' w

private def indPoly {W : Type} [Fintype W] (v : W → K) : MvPolynomial W K :=
  ∏ w : W, (X w + C (1 + v w))

private lemma totalDegree_indPoly {W : Type} [Fintype W] (v : W → K) :
    (indPoly v).totalDegree ≤ Fintype.card W := by
  unfold indPoly
  have hstep : ∀ w : W, (X w + C (1 + v w)).totalDegree ≤ 1 := fun w =>
    le_trans (totalDegree_add _ _) (max_le (by simp) (by rw [totalDegree_C]; exact Nat.zero_le 1))
  calc (∏ w : W, (X w + C (1 + v w))).totalDegree
      ≤ ∑ w : W, (X w + C (1 + v w)).totalDegree := totalDegree_prod_le_sum _ _
    _ ≤ ∑ _w : W, 1 := by exact Finset.sum_le_sum fun w _ => hstep w
    _ = Fintype.card W := by simp

private lemma multilin_eq_sum_ind {W : Type} [Fintype W] [DecidableEq W]
    (Q : MvPolynomial W K) (hQ : ∀ m ∈ Q.support, ∀ w : W, m w ≤ 1) :
    Q = ∑ v : W → K, C (eval v Q) * indPoly v := by
  have hgen : ∀ (s : Finset W) (Q : MvPolynomial W K),
      (∀ m ∈ Q.support, ∀ w : W, m w ≤ 1) →
      (∀ m ∈ Q.support, ∀ w : W, w ∉ s → m w = 0) →
      Q = ∑ v : ↥s → K,
        C (eval (fun w => if hw : w ∈ s then v ⟨w, hw⟩ else 0) Q) *
        ∏ w ∈ s.attach, (X w.1 + C (1 + v w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro Q _ hsupp
      have hconst : Q = C (Q.coeff 0) := by
        ext m
        by_cases hm : m = 0
        · subst hm; simp
        · rw [coeff_C, ite_eq_right_iff.mpr (fun h => absurd h.symm hm)]
          by_contra hne
          have hmem : m ∈ Q.support := mem_support_iff.mpr hne
          apply hm
          ext w
          exact hsupp m hmem w (Finset.notMem_empty w)
      have hev : eval (fun _ : W => (0 : K)) Q = Q.coeff 0 := by
        conv_lhs => rw [hconst]
        simp
      have huniv : (Finset.univ : Finset (↥(∅ : Finset W) → K)) =
          {fun x => False.elim (Finset.notMem_empty x.1 x.2)} := by
        ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        funext x; exact False.elim (Finset.notMem_empty x.1 x.2)
      rw [huniv, Finset.sum_singleton]
      simp only [Finset.attach_empty, Finset.prod_empty, mul_one, Finset.notMem_empty, ↓reduceDIte]
      rw [hev]
      exact hconst
    | insert w0 s hw0 ih =>
      intro Q hQ hsupp
      let Q0 : MvPolynomial W K := ∑ m ∈ Q.support.filter (fun m => m w0 = 0), monomial m 1
      let Q1 : MvPolynomial W K := ∑ m ∈ Q.support.filter (fun m => m w0 = 1), monomial (m - Finsupp.single w0 1) 1
      have hQsplit : Q = Q0 + X w0 * Q1 := by
        conv_lhs => rw [poly_eq_sum_monomials Q]
        have hpart := Finset.sum_filter_add_sum_filter_not Q.support (fun m => m w0 = 0) (fun m => monomial m (1 : K))
        rw [← hpart]
        congr 1
        have hfilt : Q.support.filter (fun m => ¬ m w0 = 0) = Q.support.filter (fun m => m w0 = 1) := by
          ext m
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hm, hne⟩; have := hQ m hm w0; exact ⟨hm, by omega⟩
          · rintro ⟨hm, h1⟩; exact ⟨hm, by omega⟩
        rw [hfilt, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm1 : m w0 = 1 := (Finset.mem_filter.mp hm).2
        have hmeq : m = Finsupp.single w0 1 + (m - Finsupp.single w0 1) := by
          ext u
          by_cases hu : u = w0
          · subst u; simp [hm1]
          · simp [hu]
        conv_lhs => rw [hmeq]
        rw [X, monomial_mul_monomial, mul_one]
      have hQ0_supp : ∀ m ∈ Q0.support, ∀ w, m w ≤ 1 ∧ (w ∉ s → m w = 0) := by
        intro m hm w
        have hmem : m ∈ Q.support.filter (fun m => m w0 = 0) := by
          by_contra hnot
          have hc : Q0.coeff m = 0 := by
            unfold Q0; rw [coeff_sum]
            apply Finset.sum_eq_zero; intro m' hm'
            rw [coeff_monomial]
            simp [show m' ≠ m from fun heq => hnot (heq ▸ hm')]
          exact mem_support_iff.mp hm hc
        obtain ⟨hmQ, hmw0⟩ := Finset.mem_filter.mp hmem
        refine ⟨hQ m hmQ w, fun hws => ?_⟩
        by_cases hw : w = w0
        · subst w; exact hmw0
        · exact hsupp m hmQ w (fun h => by rcases Finset.mem_insert.mp h with rfl | h'; exact hw rfl; exact hws h')
      have hQ1_supp : ∀ m ∈ Q1.support, ∀ w, m w ≤ 1 ∧ (w ∉ s → m w = 0) := by
        intro m hm w
        have hmem : m ∈ (Q.support.filter (fun m => m w0 = 1)).image (fun m => m - Finsupp.single w0 1) := by
          by_contra hnot
          have hc : Q1.coeff m = 0 := by
            unfold Q1; rw [coeff_sum]
            apply Finset.sum_eq_zero; intro m' hm'
            rw [coeff_monomial]
            simp [show m' - Finsupp.single w0 1 ≠ m from fun heq => hnot (Finset.mem_image.mpr ⟨m', hm', heq⟩)]
          exact mem_support_iff.mp hm hc
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hmem
        obtain ⟨hmQ, hmw0⟩ := Finset.mem_filter.mp hm'
        refine ⟨?_, fun hws => ?_⟩
        · by_cases hw : w = w0
          · subst w; simp [hmw0]
          · simp [hw]; exact hQ m' hmQ w
        · by_cases hw : w = w0
          · subst w; simp [hmw0]
          · simp [hw]
            exact hsupp m' hmQ w (fun h => by rcases Finset.mem_insert.mp h with rfl | h'; exact hw rfl; exact hws h')
      have hQ01_supp : ∀ m ∈ (Q0 + Q1).support, ∀ w, m w ≤ 1 ∧ (w ∉ s → m w = 0) := by
        intro m hm w
        rcases Finset.mem_union.mp (support_add hm) with h0 | h1
        · exact hQ0_supp m h0 w
        · exact hQ1_supp m h1 w
      have hQ0_eq := ih Q0 (fun m hm w => (hQ0_supp m hm w).1) (fun m hm w => (hQ0_supp m hm w).2)
      have hQ01_eq := ih (Q0 + Q1) (fun m hm w => (hQ01_supp m hm w).1) (fun m hm w => (hQ01_supp m hm w).2)
      have hQ_comb : Q = Q0 * (X w0 + C (1 + (0 : K))) + (Q0 + Q1) * (X w0 + C (1 + (1 : K))) := by
        rw [hQsplit]
        have h11 : (1 : K) + 1 = 0 := z2_add_self 1
        rw [add_zero, h11, map_zero, add_zero, map_one]
        have h2 : Q0 * X w0 + Q0 * X w0 = 0 := poly_add_self _
        linear_combination -h2
      -- Biject (↥(insert w0 s) → K) with K × (↥s → K)
      let eV : (↥(insert w0 s) → K) ≃ K × (↥s → K) :=
        { toFun := fun v => (v ⟨w0, Finset.mem_insert_self w0 s⟩, fun x => v ⟨x.1, Finset.mem_insert_of_mem x.2⟩)
          invFun := fun p x => if h : x.1 = w0 then p.1 else p.2 ⟨x.1, by
            rcases Finset.mem_insert.mp x.2 with hx | hs
            · exact absurd hx h
            · exact hs⟩
          left_inv := fun v => by
            funext ⟨x, hx⟩; dsimp only
            split_ifs with h
            · subst x; rfl
            · rfl
          right_inv := fun ⟨c, v⟩ => by
            apply Prod.ext
            · simp
            · funext ⟨x, hx⟩
              have hne : x ≠ w0 := fun h => hw0 (h ▸ hx)
              simp [hne] }
      have hlhs : Q =
          (∑ v : ↥s → K, C (eval (fun w => if hw : w ∈ s then v ⟨w, hw⟩ else 0) Q0) *
            ∏ w ∈ s.attach, (X w.1 + C (1 + v w))) * (X w0 + C (1 + (0 : K))) +
          (∑ v : ↥s → K, C (eval (fun w => if hw : w ∈ s then v ⟨w, hw⟩ else 0) (Q0 + Q1)) *
            ∏ w ∈ s.attach, (X w.1 + C (1 + v w))) * (X w0 + C (1 + (1 : K))) := by
        conv_lhs => rw [hQ_comb]
        congr 1
        · rw [← hQ0_eq]
        · rw [← hQ01_eq]
      conv_lhs => rw [hlhs, Finset.sum_mul, Finset.sum_mul]
      have hrhs : ∑ v : ↥(insert w0 s) → K,
          C (eval (fun w => if hw : w ∈ insert w0 s then v ⟨w, hw⟩ else 0) Q) *
          ∏ w ∈ (insert w0 s).attach, (X w.1 + C (1 + v w)) =
          ∑ p : K × (↥s → K),
          C (eval (fun w => if hw : w ∈ insert w0 s then (eV.symm p) ⟨w, hw⟩ else 0) Q) *
          ∏ w ∈ (insert w0 s).attach, (X w.1 + C (1 + (eV.symm p) w)) :=
        Fintype.sum_equiv eV _ _ (fun v => by simp)
      rw [hrhs, Fintype.sum_prod_type]
      have hfin2 : ∀ g : K → MvPolynomial W K, ∑ c : K, g c = g 0 + g 1 := fun g => by
        have huniv2 : (Finset.univ : Finset K) = {0, 1} := by decide
        rw [huniv2, Finset.sum_pair (by decide)]
      rw [hfin2]
      have hprod_split : ∀ (c : K) (v : ↥s → K),
          ∏ w ∈ (insert w0 s).attach, (X w.1 + C (1 + (eV.symm (c, v)) w)) =
          (∏ w ∈ s.attach, (X w.1 + C (1 + v w))) * (X w0 + C (1 + c)) := by
        intro c v
        let w0' : ↥(insert w0 s) := ⟨w0, Finset.mem_insert_self w0 s⟩
        have hmem0 : w0' ∈ (insert w0 s).attach := Finset.mem_attach _ _
        rw [← Finset.mul_prod_erase _ _ hmem0, mul_comm]
        congr 1
        · symm
          refine Finset.prod_bij (fun x _ => ⟨x.1, Finset.mem_insert_of_mem x.2⟩) ?_ ?_ ?_ ?_
          · intro x _
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_attach _ _⟩
            intro heq
            have hx : x.1 = w0 := congrArg Subtype.val heq
            exact hw0 (hx ▸ x.2)
          · intro x1 _ x2 _ h; exact Subtype.ext (by simpa using congrArg Subtype.val h)
          · intro y hy
            have hne : y.1 ≠ w0 := fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)
            have hys : y.1 ∈ s := (Finset.mem_insert.mp y.2).resolve_left hne
            exact ⟨⟨y.1, hys⟩, Finset.mem_attach _ _, rfl⟩
          · intro x _
            have hne : x.1 ≠ w0 := fun h => hw0 (h ▸ x.2)
            simp [eV, hne]
        · simp [eV, w0']
      have heval_eq : ∀ (c : K) (v : ↥s → K),
          eval (fun w => if hw : w ∈ insert w0 s then (eV.symm (c, v)) ⟨w, hw⟩ else 0) Q =
          eval (fun w => if hw : w ∈ s then v ⟨w, hw⟩ else 0) (if c = 0 then Q0 else Q0 + Q1) := by
        intro c v
        set f1 : W → K := fun w => if hw : w ∈ insert w0 s then (eV.symm (c, v)) ⟨w, hw⟩ else 0
        set f0 : W → K := fun w => if hw : w ∈ s then v ⟨w, hw⟩ else 0
        have hf1_w0 : f1 w0 = c := by simp [f1, eV]
        have hf1_on_s : ∀ w ∈ s, f1 w = f0 w := fun w hw => by
          have hne : w ≠ w0 := fun h => hw0 (h ▸ hw)
          simp [f1, f0, hw, eV, hne]
        have hev_agree : ∀ R : MvPolynomial W K, (∀ m ∈ R.support, ∀ w, w ∉ s → m w = 0) →
            eval f1 R = eval f0 R := by
          intro R hR
          conv_lhs => rw [R.as_sum]
          conv_rhs => rw [R.as_sum]
          rw [map_sum, map_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [eval_monomial, eval_monomial]
          congr 1
          refine Finset.prod_congr rfl fun w hw => ?_
          have hws : w ∈ s := by
            by_contra hnot
            exact Finsupp.mem_support_iff.mp hw (hR m hm w hnot)
          dsimp only
          rw [hf1_on_s w hws]
        rw [hQsplit, map_add, map_mul, eval_X, hf1_w0,
          hev_agree Q0 (fun m hm w => (hQ0_supp m hm w).2),
          hev_agree Q1 (fun m hm w => (hQ1_supp m hm w).2)]
        rcases z2_cases c with rfl | rfl <;> simp
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun v _ => ?_
        rw [hprod_split 0 v, heval_eq 0 v]
        simp only [↓reduceIte, mul_assoc]
      · refine Finset.sum_congr rfl fun v _ => ?_
        rw [hprod_split 1 v, heval_eq 1 v]
        simp only [one_ne_zero, ↓reduceIte, mul_assoc]
  have hall := hgen Finset.univ Q hQ (fun _ _ w hw => absurd (Finset.mem_univ w) hw)
  conv_lhs => rw [hall]
  let eU : (↥(Finset.univ : Finset W) → K) ≃ (W → K) :=
    { toFun := fun v w => v ⟨w, Finset.mem_univ w⟩
      invFun := fun v x => v x.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv eU _ _ fun v => ?_
  simp only [Finset.mem_univ, ↓reduceDIte, eU, Equiv.coe_fn_mk, indPoly]
  congr 1
  exact Finset.prod_attach Finset.univ (fun w => X w + C (1 + v ⟨w, Finset.mem_univ w⟩))

private lemma pc_ind_mul_var_diff {W : Type} [Fintype W] [DecidableEq W] (v : W → K) (w : W) :
    PCDerivable (boolAx W) (Fintype.card W + 1) (indPoly v * (X w + C (v w))) := by
  unfold indPoly
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have hprod : (X w + C (1 + v w)) * (X w + C (v w)) = X w * X w + X w := by
    have h1 : C (1 + v w) * X w + X w * C (v w) = X w := by
      rcases z2_cases (v w) with h | h <;> simp [h, z2_add_self]
    have h2 : C (1 + v w) * C (v w) = (0 : MvPolynomial W K) := by
      rw [← map_mul]; rcases z2_cases (v w) with h | h <;> simp [h, z2_add_self]
    calc (X w + C (1 + v w)) * (X w + C (v w))
        = X w * X w + (C (1 + v w) * X w + X w * C (v w)) + C (1 + v w) * C (v w) := by ring
      _ = X w * X w + X w := by rw [h1, h2, add_zero]
  have heq : (X w + C (1 + v w)) * (∏ u ∈ Finset.univ.erase w, (X u + C (1 + v u))) * (X w + C (v w)) =
      (∏ u ∈ Finset.univ.erase w, (X u + C (1 + v u))) * (X w * X w + X w) := by
    rw [← hprod]; ring
  rw [heq]
  have hstep_u : ∀ u : W, (X u + C (1 + v u)).totalDegree ≤ 1 := fun u =>
    le_trans (totalDegree_add _ _) (max_le (by simp) (by rw [totalDegree_C]; exact Nat.zero_le 1))
  have hdeg_rest : (∏ u ∈ Finset.univ.erase w, (X u + C (1 + v u))).totalDegree ≤ Fintype.card W - 1 := by
    calc (∏ u ∈ Finset.univ.erase w, (X u + C (1 + v u))).totalDegree
        ≤ ∑ u ∈ Finset.univ.erase w, (X u + C (1 + v u)).totalDegree := totalDegree_prod_le_sum _ _
      _ ≤ ∑ _u ∈ Finset.univ.erase w, 1 := by exact Finset.sum_le_sum fun u _ => hstep_u u
      _ = Fintype.card W - 1 := by simp [Finset.card_erase_of_mem]
  have hdeg_ax : (X w * X w + X w : MvPolynomial W K).totalDegree ≤ 2 :=
    le_trans (totalDegree_add _ _) (max_le (le_trans (totalDegree_mul _ _) (by simp)) (by simp))
  have hpos : 1 ≤ Fintype.card W := Fintype.card_pos_iff.mpr ⟨w⟩
  exact pc_mul_left _ (PCDerivable.ax ⟨w, rfl⟩ (by omega)) (by omega)

private lemma pc_ind_mul_eval_diff {W : Type} [Fintype W] [DecidableEq W]
    (v : W → K) (g : MvPolynomial W K) :
    PCDerivable (boolAx W) (Fintype.card W + g.totalDegree) (indPoly v * (g + C (eval v g))) := by
  have hmon : ∀ m : W →₀ ℕ,
      PCDerivable (boolAx W) (Fintype.card W + (m.sum fun _ e => e))
        (indPoly v * (monomial m 1 + C (eval v (monomial m 1)))) := by
    intro m
    induction m using Finsupp.induction with
    | zero =>
      have hz : monomial (0 : W →₀ ℕ) (1 : K) + C (eval v (monomial 0 1)) = 0 := by
        simp [monomial_zero', poly_add_self]
      rw [hz, mul_zero]; exact PCDerivable.zero
    | single_add w e m hwm he ih =>
      have hpow : ∀ k : ℕ,
          PCDerivable (boolAx W) (Fintype.card W + (k + m.sum fun _ c => c))
            (indPoly v * (X w ^ k * monomial m 1 + C (eval v (X w ^ k * monomial m 1)))) := by
        intro k
        induction k with
        | zero => simpa using ih
        | succ k ihk =>
          set q : MvPolynomial W K := X w ^ k * monomial m 1
          have hqdeg : q.totalDegree ≤ k + m.sum (fun _ c => c) := by
            calc q.totalDegree ≤ (X w ^ k).totalDegree + (monomial m 1).totalDegree := totalDegree_mul _ _
              _ ≤ k + m.sum (fun _ c => c) := by
                  have h1 : (X w ^ k : MvPolynomial W K).totalDegree ≤ k :=
                    le_trans (totalDegree_pow _ _) (by simp)
                  rw [totalDegree_monomial_one]; omega
          have hev : eval v (X w ^ (k + 1) * monomial m 1) = v w * eval v q := by
            simp [q, pow_succ', mul_assoc]
          have hid : indPoly v * (X w ^ (k + 1) * monomial m 1 + C (eval v (X w ^ (k + 1) * monomial m 1))) =
              q * (indPoly v * (X w + C (v w))) + C (v w) * (indPoly v * (q + C (eval v q))) := by
            rw [hev, map_mul]
            have hq2 : indPoly v * (C (v w) * q) + indPoly v * (C (v w) * q) = 0 := poly_add_self _
            have hstep : X w ^ (k + 1) * monomial m 1 = X w * q := by simp [q, pow_succ', mul_assoc]
            rw [hstep]
            linear_combination -hq2
          rw [hid]
          refine PCDerivable.add ?_ ?_
          · have hdeg1 : (indPoly v * (X w + C (v w))).totalDegree ≤ Fintype.card W + 1 :=
              pc_totalDegree_le (pc_ind_mul_var_diff v w)
            refine pc_mul_left q (pc_mono (subset_refl _) (by omega) (pc_ind_mul_var_diff v w)) ?_
            omega
          · exact pc_smul_C (v w) (pc_mono (subset_refl _) (by omega) ihk)
      have hsum_step : (Finsupp.single w e + m).sum (fun _ c => c) = e + m.sum (fun _ c => c) := by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
        simp
      have hmon_eq : monomial (Finsupp.single w e + m) (1 : K) = X w ^ e * monomial m 1 := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
      rw [hsum_step, hmon_eq]
      exact hpow e
  have hq : indPoly v * (g + C (eval v g)) =
      ∑ m ∈ g.support, indPoly v * (monomial m (1 : K) + C (eval v (monomial m (1 : K)))) := by
    conv_lhs => rw [poly_eq_sum_monomials g]
    rw [map_sum, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  rw [hq]
  apply pc_sum
  intro m hm
  have hm_le : (m.sum fun _ e => e) ≤ g.totalDegree :=
    Finset.le_sup (f := fun d : W →₀ ℕ => d.sum fun _ e => e) hm
  exact pc_mono (subset_refl _) (by omega) (hmon m)

/-! ### Section 4: Linear Algebra Witness Over `ZMod 2` -/

private lemma farkas_short_witness {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (α : I → K) (β : I → Fin k → K)
    (hunsat : ¬ ∃ σ : Fin k → K, ∀ i : I, α i + ∑ j : Fin k, σ j * β i j = 0) :
    ∃ S : Finset I, S.card ≤ k + 1 ∧ (∑ i ∈ S, α i = 1) ∧ ∀ j : Fin k, ∑ i ∈ S, β i j = 0 := by
  let M : (Fin k → K) →ₗ[K] (I → K) :=
    { toFun := fun σ i => ∑ j : Fin k, σ j * β i j
      map_add' := fun σ1 σ2 => by
        funext i; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c σ => by
        funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hnotmem : α ∉ LinearMap.range M := by
    rintro ⟨σ, hσ⟩
    apply hunsat
    refine ⟨σ, fun i => ?_⟩
    have hi : ∑ j : Fin k, σ j * β i j = α i := congrFun hσ i
    rw [hi, z2_add_self]
  -- Linear functional vanishing on range M and equal to 1 on α
  let qmap := (LinearMap.range M).mkQ
  have hqne : qmap α ≠ 0 := fun h => hnotmem ((Submodule.Quotient.mk_eq_zero _).mp h)
  let ι : K →ₗ[K] (I → K) ⧸ LinearMap.range M := LinearMap.toSpanSingleton K _ (qmap α)
  have hιker : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hsm : c • qmap α = 0 := hc
    exact (smul_eq_zero.mp hsm).resolve_right hqne
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective ι hιker
  let φ : (I → K) →ₗ[K] K := ψ.comp qmap
  have hφα : φ α = 1 := by
    have h1 := LinearMap.congr_fun hψ (1 : K)
    simpa [φ, ι, LinearMap.toSpanSingleton_apply] using h1
  have hφM : ∀ σ, φ (M σ) = 0 := fun σ => by
    change ψ (qmap (M σ)) = 0
    have hz : qmap (M σ) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨σ, rfl⟩
    rw [hz, map_zero]
  let S0 : Finset I := Finset.univ.filter (fun i => φ (Pi.single i 1) = 1)
  have hφ_sum : ∀ v : I → K, φ v = ∑ i ∈ S0, v i := by
    intro v
    have hv : v = ∑ i : I, v i • Pi.single i (1 : K) := by
      funext i; simp [Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    calc ∑ i : I, φ (v i • Pi.single i 1)
        = ∑ i : I, v i * φ (Pi.single i 1) := Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]
      _ = ∑ i : I, if φ (Pi.single i 1) = 1 then v i else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases z2_cases (φ (Pi.single i 1)) with h | h <;> simp [h]
      _ = ∑ i ∈ S0, v i := by rw [← Finset.sum_filter]
  let Good : Finset (Finset I) := Finset.univ.filter (fun S =>
    (∑ i ∈ S, α i = 1) ∧ ∀ j : Fin k, ∑ i ∈ S, β i j = 0)
  have hS0_mem : S0 ∈ Good := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun j => ?_⟩
    · rw [← hφ_sum α, hφα]
    · have hj := hφM (Pi.single j 1)
      rw [hφ_sum] at hj
      have hMcol : ∀ i : I, M (Pi.single j 1) i = β i j := fun i => by
        simp [M, Pi.single_apply]
      simp only [hMcol] at hj
      exact hj
  obtain ⟨S, hSgood, hSmin⟩ := Finset.exists_min_image Good Finset.card ⟨S0, hS0_mem⟩
  obtain ⟨hSα, hSβ⟩ := (Finset.mem_filter.mp hSgood).2
  refine ⟨S, ?_, hSα, hSβ⟩
  by_contra hgt
  have hge : k + 2 ≤ S.card := by omega
  let Ψ : (↥S → K) →ₗ[K] (K × (Fin k → K)) :=
    { toFun := fun c => (∑ i : ↥S, c i * α i.1, fun j => ∑ i : ↥S, c i * β i.1 j)
      map_add' := fun c1 c2 => by
        apply Prod.ext
        · simp only [Prod.fst_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        · funext j; simp only [Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        apply Prod.ext
        · simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
        · funext j; simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  have hdom : Module.finrank K (↥S → K) = S.card := by
    rw [Module.finrank_pi_fintype]; simp
  have hcod : Module.finrank K (LinearMap.range Ψ) ≤ k + 1 := by
    have h1 := Submodule.finrank_le (LinearMap.range Ψ)
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at h1
    omega
  have hker_pos : 0 < Module.finrank K (LinearMap.ker Ψ) := by omega
  obtain ⟨⟨c, hcKer⟩, hcne⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := LinearMap.ker Ψ)).mp hker_pos
  have hc0 : c ≠ 0 := fun h => hcne (Subtype.ext h)
  let T : Finset I := (Finset.univ.filter (fun i : ↥S => c i = 1)).image Subtype.val
  have hT_sub : T ⊆ S := by
    intro i hi
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    exact x.2
  have hT_ne : T.Nonempty := by
    have hex : ∃ x : ↥S, c x ≠ 0 := by
      by_contra h; push Not at h; exact hc0 (funext h)
    obtain ⟨x, hx⟩ := hex
    exact ⟨x.1, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z2_eq_one_of_ne_zero hx⟩, rfl⟩⟩
  have hsum_T : ∀ g : I → K, ∑ i ∈ T, g i = ∑ i : ↥S, c i * g i.1 := by
    intro g
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases z2_cases (c i) with h | h <;> simp [h]
  have hTα : ∑ i ∈ T, α i = 0 := by
    rw [hsum_T α]
    exact congrArg Prod.fst hcKer
  have hTβ : ∀ j : Fin k, ∑ i ∈ T, β i j = 0 := fun j => by
    rw [hsum_T (fun i => β i j)]
    exact congrFun (congrArg Prod.snd hcKer) j
  have hS'_good : S \ T ∈ Good := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun j => ?_⟩
    · have hadd := Finset.sum_sdiff hT_sub (f := α)
      rw [hSα, hTα, add_zero] at hadd
      exact hadd
    · have hadd := Finset.sum_sdiff hT_sub (f := fun i => β i j)
      rw [hSβ j, hTβ j, add_zero] at hadd
      exact hadd
  have hcard_lt : (S \ T).card < S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT_sub]
    have hpos := Finset.card_pos.mpr hT_ne
    have hle := Finset.card_le_card hT_sub
    omega
  have hle_min := hSmin (S \ T) hS'_good
  omega

/-! ### Section 5: Core Formal Product Derivation in `MvPolynomial W (ZMod 2)` -/

private lemma formal_product_derivable {m k : ℕ} (chosen : (Fin k → K) → Fin m) :
    let I : Finset (Fin m) := Finset.univ.image chosen
    let W := ↥I ⊕ (↥I × Fin k)
    let fA : ↥I → MvPolynomial W K := fun i => X (Sum.inl i)
    let fB : ↥I → Fin k → MvPolynomial W K := fun i j => X (Sum.inr (i, j))
    let fTest : Finset ↥I → MvPolynomial W K := fun S =>
      (∑ i ∈ S, fA i) * ∏ j : Fin k, (1 + ∑ i ∈ S, fB i j)
    let fVis : Set (MvPolynomial W K) :=
      boolAx W ∪ {g | ∃ S : Finset ↥I, S.card ≤ k + 1 ∧ g = fTest S}
    let fTarget : MvPolynomial W K :=
      ∏ σ : Fin k → K,
        (fA ⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩ +
          ∑ j : Fin k, C (σ j) * fB ⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩ j)
    PCDerivable fVis (max (2 ^ k) ((k + 1) * (I.card + 1))) fTarget := by
  intro I W fA fB fTest fVis fTarget
  set D := max (2 ^ k) ((k + 1) * (I.card + 1))
  have hWcard : Fintype.card W = I.card * (k + 1) := by
    simp only [W, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    ring
  have hdeg_target : fTarget.totalDegree ≤ 2 ^ k := by
    unfold fTarget
    calc (∏ σ : Fin k → K,
            (fA ⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩ +
              ∑ j : Fin k, C (σ j) * fB ⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩ j)).totalDegree
        ≤ ∑ σ : Fin k → K, (fA ⟨chosen σ, _⟩ + ∑ j : Fin k, C (σ j) * fB ⟨chosen σ, _⟩ j).totalDegree :=
          totalDegree_prod_le_sum _ _
      _ ≤ ∑ _σ : Fin k → K, 1 := by
          refine Finset.sum_le_sum fun σ _ => le_trans (totalDegree_add _ _) (max_le (by simp [fA]) ?_)
          apply totalDegree_sum_le_of_forall
          intro j _
          exact le_trans (totalDegree_mul _ _) (by simp [fB])
      _ = 2 ^ k := by simp
  set Q := multilin fTarget
  have hstep1 : PCDerivable fVis D (fTarget + Q) :=
    pc_mono Set.subset_union_left (le_trans hdeg_target (le_max_left _ _)) (pc_add_multilin fTarget)
  have hQ_eq : Q = ∑ v : W → K, C (eval v Q) * indPoly v :=
    multilin_eq_sum_ind Q (multilin_is_sf fTarget)
  have hstep2 : PCDerivable fVis D Q := by
    rw [hQ_eq]
    apply pc_sum
    intro v _
    by_cases hv : eval v Q = 0
    · rw [hv, map_zero, zero_mul]; exact PCDerivable.zero
    · have hv1 : eval v fTarget = 1 := by
        rw [← eval_multilin v fTarget]
        exact z2_eq_one_of_ne_zero hv
      rw [eval_multilin v fTarget, hv1, map_one, one_mul]
      let α : ↥I → K := fun i => v (Sum.inl i)
      let β : ↥I → Fin k → K := fun i j => v (Sum.inr (i, j))
      have hunsat : ¬ ∃ σ : Fin k → K, ∀ i : ↥I, α i + ∑ j : Fin k, σ j * β i j = 0 := by
        rintro ⟨σ, hσ⟩
        have hzero : eval v fTarget = 0 := by
          unfold fTarget
          rw [map_prod]
          apply Finset.prod_eq_zero (Finset.mem_univ σ)
          simp only [fA, fB, map_add, map_sum, map_mul, eval_X, eval_C]
          exact hσ ⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩
        rw [hv1] at hzero
        exact one_ne_zero hzero
      obtain ⟨S, hScard, hSα, hSβ⟩ := farkas_short_witness α β hunsat
      have hTest_mem : fTest S ∈ fVis := Or.inr ⟨S, hScard, rfl⟩
      have hTest_deg : (fTest S).totalDegree ≤ k + 1 := by
        unfold fTest
        refine le_trans (totalDegree_mul _ _) ?_
        have h1 : (∑ i ∈ S, fA i).totalDegree ≤ 1 :=
          totalDegree_sum_le_of_forall S _ 1 fun i _ => by simp [fA]
        have h2 : (∏ j : Fin k, (1 + ∑ i ∈ S, fB i j)).totalDegree ≤ k := by
          calc (∏ j : Fin k, (1 + ∑ i ∈ S, fB i j)).totalDegree
              ≤ ∑ j : Fin k, (1 + ∑ i ∈ S, fB i j).totalDegree := totalDegree_prod_le_sum _ _
            _ ≤ ∑ _j : Fin k, 1 := by
                refine Finset.sum_le_sum fun j _ => le_trans (totalDegree_add _ _) (max_le (by simp) ?_)
                exact totalDegree_sum_le_of_forall S _ 1 fun i _ => by simp [fB]
            _ = k := by simp
        omega
      have hTest_ev : eval v (fTest S) = 1 := by
        unfold fTest
        rw [map_mul, map_sum, map_prod]
        have h1 : ∑ i ∈ S, eval v (fA i) = 1 := by simpa [fA, α] using hSα
        have h2 : ∏ j : Fin k, eval v (1 + ∑ i ∈ S, fB i j) = 1 := by
          apply Finset.prod_eq_one
          intro j _
          rw [map_add, map_one, map_sum]
          have hj : ∑ i ∈ S, eval v (fB i j) = 0 := by simpa [fB, β] using hSβ j
          rw [hj, add_zero]
        rw [h1, h2, mul_one]
      have hboundD : Fintype.card W + (k + 1) ≤ D := by
        have : Fintype.card W + (k + 1) = (k + 1) * (I.card + 1) := by rw [hWcard]; ring
        rw [this]
        exact le_max_right _ _
      have hder1 : PCDerivable fVis D (indPoly v * fTest S) :=
        pc_mul_left (indPoly v) (PCDerivable.ax hTest_mem (by omega))
          (le_trans (Nat.add_le_add (totalDegree_indPoly v) hTest_deg) hboundD)
      have hder2 : PCDerivable fVis D (indPoly v * (fTest S + 1)) := by
        have h := pc_ind_mul_eval_diff v (fTest S)
        rw [hTest_ev, map_one] at h
        exact pc_mono Set.subset_union_left (by omega) h
      have hid : indPoly v = indPoly v * fTest S + indPoly v * (fTest S + 1) := by
        have := poly_add_self (indPoly v * fTest S)
        linear_combination -this
      rw [hid]
      exact PCDerivable.add hder1 hder2
  have hfinal : fTarget = (fTarget + Q) + Q := by
    have := poly_add_self Q
    linear_combination -this
  rw [hfinal]
  exact PCDerivable.add hstep1 hstep2

private lemma pc_visible_to_hidden {n m k d : ℕ}
    (F : Set (MvPolynomial (Fin n) K)) (a : Fin m → MvPolynomial (Fin n) K)
    (b : Fin m → Fin k → MvPolynomial (Fin n) K)
    (hbool : ∀ i : Fin n, X i * X i + X i ∈ F)
    (hdeg : ∀ i, (a i).totalDegree ≤ d + 1 ∧ ∀ j, (b i j).totalDegree ≤ d) :
    let lift : MvPolynomial (Fin n) K → MvPolynomial (Fin n ⊕ Fin k) K := rename Sum.inl
    let h : Fin k → MvPolynomial (Fin n ⊕ Fin k) K := fun j => X (Sum.inr j)
    let hidden := Set.image lift F ∪ Set.range (fun j => h j * h j + h j) ∪
      Set.range (fun i => lift (a i) + ∑ j, h j * lift (b i j))
    let test := fun (S : Finset (Fin m)) => (∑ i ∈ S, a i) * ∏ j, (1 + ∑ i ∈ S, b i j)
    let visible := F ∪ {g : MvPolynomial (Fin n) K | ∃ S : Finset (Fin m), S.card ≤ k + 1 ∧ g = test S}
    ∀ B, PCRefutable visible B → PCRefutable hidden (max B (d + 1 + k * d)) := by
  intro lift h hidden test visible B href
  set D1 := max B (d + 1 + k * d)
  have hlift_ref : PCDerivable hidden D1 (lift 1) := by
    refine pc_rename (Sum.inl : Fin n → Fin n ⊕ Fin k) (pc_mono (subset_refl visible) (le_max_left B _) href) ?_
    intro g hg hdeg_g
    rcases hg with hgF | ⟨S, _, rfl⟩
    · exact PCDerivable.ax (Or.inl (Or.inl ⟨g, hgF, rfl⟩))
        (le_trans (totalDegree_rename_le _ _) hdeg_g)
    · let AS : MvPolynomial (Fin n ⊕ Fin k) K := ∑ i ∈ S, lift (a i)
      let Bj : Fin k → MvPolynomial (Fin n ⊕ Fin k) K := fun j => ∑ i ∈ S, lift (b i j)
      let G : MvPolynomial (Fin n ⊕ Fin k) K := ∏ j : Fin k, (1 + Bj j)
      have hlift_test : lift (test S) = AS * G := by
        simp only [test, lift, AS, Bj, G, map_mul, map_sum, map_prod, map_add, map_one]
      change PCDerivable hidden D1 (lift (test S))
      rw [hlift_test]
      have hdeg_AS : AS.totalDegree ≤ d + 1 :=
        totalDegree_sum_le_of_forall S _ (d + 1) fun i _ =>
          le_trans (totalDegree_rename_le _ _) (hdeg i).1
      have hdeg_Bj : ∀ j, (Bj j).totalDegree ≤ d := fun j =>
        totalDegree_sum_le_of_forall S _ d fun i _ =>
          le_trans (totalDegree_rename_le _ _) ((hdeg i).2 j)
      have hdeg_G : G.totalDegree ≤ k * d := by
        calc G.totalDegree ≤ ∑ j : Fin k, (1 + Bj j).totalDegree := totalDegree_prod_le_sum _ _
          _ ≤ ∑ _j : Fin k, d := Finset.sum_le_sum fun j _ =>
              le_trans (totalDegree_add _ _) (max_le (by simp) (hdeg_Bj j))
          _ = k * d := by simp
      have hrow_sum : PCDerivable hidden D1 (AS + ∑ j : Fin k, h j * Bj j) := by
        have heq : AS + ∑ j : Fin k, h j * Bj j =
            ∑ i ∈ S, (lift (a i) + ∑ j : Fin k, h j * lift (b i j)) := by
          simp only [AS, Bj, Finset.sum_add_distrib, Finset.mul_sum]
          rw [Finset.sum_comm]
        rw [heq]
        apply pc_sum
        intro i _
        refine PCDerivable.ax (Or.inr ⟨i, rfl⟩) ?_
        have h1 : (lift (a i)).totalDegree ≤ d + 1 := le_trans (totalDegree_rename_le _ _) (hdeg i).1
        have h2 : (∑ j : Fin k, h j * lift (b i j)).totalDegree ≤ d + 1 := by
          apply totalDegree_sum_le_of_forall
          intro j _
          have hb : (lift (b i j)).totalDegree ≤ d := le_trans (totalDegree_rename_le _ _) ((hdeg i).2 j)
          have hh : (h j).totalDegree ≤ 1 := by simp [h]
          exact le_trans (totalDegree_mul _ _) (by omega)
        have htot := le_trans (totalDegree_add _ _) (max_le h1 h2)
        exact le_trans htot (le_trans (by omega : d + 1 ≤ d + 1 + k * d) (le_max_right B _))
      have hmul_G : PCDerivable hidden D1 (AS * G + ∑ j : Fin k, h j * Bj j * G) := by
        have heq : AS * G + ∑ j : Fin k, h j * Bj j * G = G * (AS + ∑ j : Fin k, h j * Bj j) := by
          rw [mul_add, mul_comm G AS, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun j _ => by ring
        rw [heq]
        have hdeg_lin : (AS + ∑ j : Fin k, h j * Bj j).totalDegree ≤ d + 1 := by
          refine le_trans (totalDegree_add _ _) (max_le hdeg_AS ?_)
          apply totalDegree_sum_le_of_forall
          intro j _
          have hh : (h j).totalDegree ≤ 1 := by simp [h]
          exact le_trans (totalDegree_mul _ _) (by have := hdeg_Bj j; omega)
        exact pc_mul_left G hrow_sum (le_trans (by omega : G.totalDegree + (AS + ∑ j, h j * Bj j).totalDegree ≤ d + 1 + k * d) (le_max_right B _))
      have hcancel : PCDerivable hidden D1 (∑ j : Fin k, h j * Bj j * G) := by
        apply pc_sum
        intro j _
        have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun hk0 => by subst hk0; exact j.elim0)
        let Gj : MvPolynomial (Fin n ⊕ Fin k) K := ∏ l ∈ Finset.univ.erase j, (1 + Bj l)
        have hG_eq : G = (1 + Bj j) * Gj := by
          unfold G Gj
          rw [← Finset.mul_prod_erase Finset.univ (fun l => 1 + Bj l) (Finset.mem_univ j)]
        have hterm : h j * Bj j * G = (h j * Gj) * (Bj j * Bj j + Bj j) := by
          rw [hG_eq]; ring
        rw [hterm]
        let bjP : MvPolynomial (Fin n) K := ∑ i ∈ S, b i j
        have hbjP_deg : bjP.totalDegree ≤ d :=
          totalDegree_sum_le_of_forall S _ d fun i _ => (hdeg i).2 j
        have hsqP : PCDerivable F (2 * d) (bjP * bjP + bjP) :=
          pc_mono (subset_refl F) (by omega) (pc_bool_sq hbool bjP)
        have hsqA : PCDerivable hidden (2 * d) (Bj j * Bj j + Bj j) := by
          have hlift_sq : lift (bjP * bjP + bjP) = Bj j * Bj j + Bj j := by
            simp only [bjP, Bj, lift, map_add, map_mul, map_sum]
          rw [← hlift_sq]
          exact pc_rename Sum.inl hsqP fun f hf hdf =>
            PCDerivable.ax (Or.inl (Or.inl ⟨f, hf, rfl⟩)) (le_trans (totalDegree_rename_le _ _) hdf)
        have hdeg_Gj : Gj.totalDegree ≤ (k - 1) * d := by
          calc Gj.totalDegree ≤ ∑ l ∈ Finset.univ.erase j, (1 + Bj l).totalDegree := totalDegree_prod_le_sum _ _
            _ ≤ ∑ _l ∈ Finset.univ.erase j, d := Finset.sum_le_sum fun l _ =>
                le_trans (totalDegree_add _ _) (max_le (by simp) (hdeg_Bj l))
            _ = (k - 1) * d := by simp [Finset.card_erase_of_mem]
        have hdeg_hGj : (h j * Gj).totalDegree ≤ 1 + (k - 1) * d := by
          have hh : (h j).totalDegree ≤ 1 := by simp [h]
          exact le_trans (totalDegree_mul _ _) (by omega)
        have hdeg_sq : (Bj j * Bj j + Bj j).totalDegree ≤ 2 * d := pc_totalDegree_le hsqA
        have hsum_deg : 1 + (k - 1) * d + 2 * d ≤ d + 1 + k * d := by
          have : (k - 1) * d + d = k * d := by
            rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
          omega
        exact pc_mul_left (h j * Gj)
          (pc_mono (subset_refl hidden) (le_trans (by omega : 2 * d ≤ d + 1 + k * d) (le_max_right B _)) hsqA)
          (le_trans (by omega : (h j * Gj).totalDegree + (Bj j * Bj j + Bj j).totalDegree ≤ d + 1 + k * d) (le_max_right B _))
      have hid : AS * G = (AS * G + ∑ j : Fin k, h j * Bj j * G) + ∑ j : Fin k, h j * Bj j * G := by
        have := poly_add_self (∑ j : Fin k, h j * Bj j * G)
        linear_combination -this
      rw [hid]
      exact PCDerivable.add hmul_G hcancel
  change PCDerivable hidden D1 1
  simpa [lift] using hlift_ref

private lemma pc_hidden_to_visible {n m k d : ℕ}
    (F : Set (MvPolynomial (Fin n) K)) (a : Fin m → MvPolynomial (Fin n) K)
    (b : Fin m → Fin k → MvPolynomial (Fin n) K)
    (hbool : ∀ i : Fin n, X i * X i + X i ∈ F)
    (hdeg : ∀ i, (a i).totalDegree ≤ d + 1 ∧ ∀ j, (b i j).totalDegree ≤ d) :
    let lift : MvPolynomial (Fin n) K → MvPolynomial (Fin n ⊕ Fin k) K := rename Sum.inl
    let h : Fin k → MvPolynomial (Fin n ⊕ Fin k) K := fun j => X (Sum.inr j)
    let hidden := Set.image lift F ∪ Set.range (fun j => h j * h j + h j) ∪
      Set.range (fun i => lift (a i) + ∑ j, h j * lift (b i j))
    let test := fun (S : Finset (Fin m)) => (∑ i ∈ S, a i) * ∏ j, (1 + ∑ i ∈ S, b i j)
    let visible := F ∪ {g : MvPolynomial (Fin n) K | ∃ S : Finset (Fin m), S.card ≤ k + 1 ∧ g = test S}
    let branches := 2 ^ k
    let localCost := (d + 1) * max branches ((k + 1) * (min m branches + 1))
    ∀ B, PCRefutable hidden B →
      PCRefutable visible (max (B + (branches - 1) * (d + 1)) localCost) := by
  intro lift h hidden test visible branches localCost B href
  set D2 := max (B + (branches - 1) * (d + 1)) localCost
  let L : (Fin k → K) → Fin m → MvPolynomial (Fin n) K := fun σ i => a i + ∑ j : Fin k, C (σ j) * b i j
  have hLdeg : ∀ σ i, (L σ i).totalDegree ≤ d + 1 := fun σ i => by
    refine le_trans (totalDegree_add _ _) (max_le (hdeg i).1 ?_)
    apply totalDegree_sum_le_of_forall
    intro j _
    exact le_trans (totalDegree_mul _ _) (by have := (hdeg i).2 j; simp; omega)
  have hspec : ∀ σ : Fin k → K, PCRefutable (F ∪ Set.range (L σ)) B := by
    intro σ
    let ev : Fin n ⊕ Fin k → MvPolynomial (Fin n) K := Sum.elim X (fun j => C (σ j))
    have hev_deg : ∀ u : Fin n ⊕ Fin k, (ev u).totalDegree ≤ 1 := fun u => by
      cases u <;> simp [ev]
    have hlift_ev : ∀ p : MvPolynomial (Fin n) K, aeval ev (lift p) = p := fun p => by
      simp only [lift, aeval_rename]
      have hcomp : ev ∘ Sum.inl = X := rfl
      rw [hcomp, aeval_X_left]; rfl
    have h1 := pc_aeval (H := F ∪ Set.range (L σ)) ev 1 hev_deg href ?_
    · change PCDerivable (F ∪ Set.range (L σ)) B 1
      simpa using h1
    · intro g hg hdg
      rw [mul_one]
      rcases hg with (⟨f, hf, rfl⟩ | ⟨j, rfl⟩) | ⟨i, rfl⟩
      · have hdg' : (aeval ev (lift f)).totalDegree ≤ B := by
          have := totalDegree_aeval_le ev 1 hev_deg (lift f)
          omega
        rw [hlift_ev f] at hdg' ⊢
        exact PCDerivable.ax (Or.inl hf) hdg'
      · have hz : aeval ev (h j * h j + h j) = 0 := by
          simp only [h, map_add, map_mul, aeval_X, ev, Sum.elim_inr]
          rw [← map_mul, ← map_add, z2_mul_self, z2_add_self, map_zero]
        rw [hz]; exact PCDerivable.zero
      · have heq : aeval ev (lift (a i) + ∑ j : Fin k, h j * lift (b i j)) = L σ i := by
          simp only [L, map_add, map_sum, map_mul, hlift_ev, h, aeval_X, ev, Sum.elim_inr]
        have hdg' : (aeval ev (lift (a i) + ∑ j : Fin k, h j * lift (b i j))).totalDegree ≤ B := by
          have := totalDegree_aeval_le ev 1 hev_deg (lift (a i) + ∑ j : Fin k, h j * lift (b i j))
          dsimp only at hdg
          omega
        rw [heq] at hdg' ⊢
        exact PCDerivable.ax (Or.inr ⟨i, rfl⟩) hdg'
  by_cases hm0 : m = 0
  · have h0 := hspec 0
    have hsub : F ∪ Set.range (L 0) ⊆ visible := by
      rintro g (hgF | ⟨i, rfl⟩)
      · exact Or.inl hgF
      · exact absurd i.isLt (by omega)
    exact pc_mono hsub (le_trans (by omega : B ≤ B + (branches - 1) * (d + 1)) (le_max_left _ _)) h0
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hbase : ∀ chosen : (Fin k → K) → Fin m,
      PCDerivable visible localCost (∏ σ : Fin k → K, L σ (chosen σ)) := by
    intro chosen
    let I : Finset (Fin m) := Finset.univ.image chosen
    have hI_pos : 1 ≤ I.card := Finset.card_pos.mpr ⟨chosen 0, Finset.mem_image_of_mem chosen (Finset.mem_univ 0)⟩
    have hI_le_m : I.card ≤ m := by
      have := Finset.card_le_univ I; simpa using this
    have hI_le_br : I.card ≤ branches := by
      calc I.card ≤ (Finset.univ : Finset (Fin k → K)).card := Finset.card_image_le
        _ = branches := by simp [branches, K, ZMod.card]
    have hI_le_min : I.card ≤ min m branches := le_min hI_le_m hI_le_br
    let W := ↥I ⊕ (↥I × Fin k)
    set Df := max (2 ^ k) ((k + 1) * (I.card + 1))
    have hDf_ge2 : 2 ≤ Df := by
      have : 2 ≤ (k + 1) * (I.card + 1) := by nlinarith
      exact le_trans this (le_max_right _ _)
    have hDf_le : Df * (d + 1) ≤ localCost := by
      unfold localCost branches
      rw [mul_comm (d + 1)]
      refine Nat.mul_le_mul_right (d + 1) (max_le_max_left (2 ^ k) ?_)
      exact Nat.mul_le_mul_left (k + 1) (Nat.add_le_add_right hI_le_min 1)
    let subG : W → MvPolynomial (Fin n) K := Sum.elim (fun i => a i.1) (fun ij => b ij.1.1 ij.2)
    have hsubG_deg : ∀ w : W, (subG w).totalDegree ≤ d + 1 := fun w => by
      cases w with
      | inl i => exact (hdeg i.1).1
      | inr ij => exact le_trans ((hdeg ij.1.1).2 ij.2) (by omega)
    have hformal := formal_product_derivable chosen
    have hsubst := pc_aeval (H := visible) subG (d + 1) hsubG_deg hformal ?_
    · have htarget_eq : aeval subG (∏ σ : Fin k → K,
          (X (Sum.inl ⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩) +
            ∑ j : Fin k, C (σ j) * X (Sum.inr (⟨chosen σ, Finset.mem_image_of_mem chosen (Finset.mem_univ σ)⟩, j)))) =
          ∏ σ : Fin k → K, L σ (chosen σ) := by
        simp only [L, map_prod, map_add, map_sum, map_mul, aeval_X, aeval_C, subG, Sum.elim_inl, Sum.elim_inr]
        rfl
      rw [htarget_eq] at hsubst
      exact pc_mono (subset_refl visible) hDf_le hsubst
    · intro q hq _
      rcases hq with ⟨w, rfl⟩ | ⟨S, hScard, rfl⟩
      · simp only [map_add, map_mul, aeval_X]
        have hsq := pc_bool_sq hbool (subG w)
        have h2 : 2 * (subG w).totalDegree ≤ Df * (d + 1) := by
          have := hsubG_deg w
          nlinarith
        exact pc_mono Set.subset_union_left h2 hsq
      · have heq : aeval subG ((∑ i ∈ S, (X (Sum.inl i) : MvPolynomial W K)) *
            ∏ j : Fin k, (1 + ∑ i ∈ S, (X (Sum.inr (i, j)) : MvPolynomial W K))) =
            test (S.image Subtype.val) := by
          simp only [test, map_mul, map_sum, map_prod, map_add, map_one, aeval_X, subG,
            Sum.elim_inl, Sum.elim_inr]
          rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
        rw [heq]
        have hScard' : (S.image Subtype.val).card ≤ k + 1 :=
          le_trans Finset.card_image_le hScard
        have htest_deg : (test (S.image Subtype.val)).totalDegree ≤ Df * (d + 1) := by
          unfold test
          refine le_trans (totalDegree_mul _ _) ?_
          have h1 : (∑ i ∈ S.image Subtype.val, a i).totalDegree ≤ d + 1 :=
            totalDegree_sum_le_of_forall _ _ (d + 1) fun i _ => (hdeg i).1
          have h2 : (∏ j : Fin k, (1 + ∑ i ∈ S.image Subtype.val, b i j)).totalDegree ≤ k * d := by
            calc (∏ j : Fin k, (1 + ∑ i ∈ S.image Subtype.val, b i j)).totalDegree
                ≤ ∑ j : Fin k, (1 + ∑ i ∈ S.image Subtype.val, b i j).totalDegree := totalDegree_prod_le_sum _ _
              _ ≤ ∑ _j : Fin k, d := Finset.sum_le_sum fun j _ =>
                  le_trans (totalDegree_add _ _) (max_le (by simp)
                    (totalDegree_sum_le_of_forall _ _ d fun i _ => (hdeg i).2 j))
              _ = k * d := by simp
          have h3 : (d + 1) + k * d ≤ (k + 1) * (d + 1) := by nlinarith
          have h4 : (k + 1) ≤ Df := le_trans (by nlinarith : k + 1 ≤ (k + 1) * (I.card + 1)) (le_max_right _ _)
          nlinarith
        exact PCDerivable.ax (Or.inr ⟨S.image Subtype.val, hScard', rfl⟩) htest_deg
  have hbr_pos : 1 ≤ branches := Nat.one_le_two_pow
  have helim : ∀ (R : Finset (Fin k → K)) (Prest : MvPolynomial (Fin n) K),
      Prest.totalDegree ≤ (branches - R.card) * (d + 1) →
      (∀ chosen : (Fin k → K) → Fin m, PCDerivable visible D2 (Prest * ∏ σ ∈ R, L σ (chosen σ))) →
      PCDerivable visible D2 Prest := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro Prest _ hch
      simpa using hch (fun _ => ⟨0, hm_pos⟩)
    | insert σ0 R' hσ0 ih =>
      intro Prest hPdeg hch
      have hRcard : (insert σ0 R').card = R'.card + 1 := Finset.card_insert_of_notMem hσ0
      have hRle : R'.card + 1 ≤ branches := by
        rw [← hRcard]
        have := Finset.card_le_univ (insert σ0 R')
        simpa [branches, K, ZMod.card] using this
      have hPdeg' : Prest.totalDegree ≤ (branches - 1) * (d + 1) := by
        have : branches - (insert σ0 R').card ≤ branches - 1 := by omega
        exact le_trans hPdeg (Nat.mul_le_mul_right (d + 1) this)
      have hmul := pc_mul_derivation (H := visible) (Dout := D2) (le_max_left _ _) Prest hPdeg' (hspec σ0) ?_
      · rw [mul_one] at hmul
        exact hmul
      · intro g hg hgd
        rcases hg with hgF | ⟨i0, rfl⟩
        · refine pc_mul_left Prest (PCDerivable.ax (Or.inl hgF)
            (le_trans hgd (le_trans (by omega : B ≤ B + (branches - 1) * (d + 1)) (le_max_left _ _)))) ?_
          have : Prest.totalDegree + g.totalDegree ≤ B + (branches - 1) * (d + 1) := by omega
          exact le_trans this (le_max_left _ _)
        · have hdeg_next : (Prest * L σ0 i0).totalDegree ≤ (branches - R'.card) * (d + 1) := by
            have h1 := hLdeg σ0 i0
            have h2 : (branches - (insert σ0 R').card) * (d + 1) + (d + 1) = (branches - R'.card) * (d + 1) := by
              rw [hRcard, ← Nat.succ_mul]
              congr 1; omega
            exact le_trans (totalDegree_mul _ _) (by omega)
          exact ih (Prest * L σ0 i0) hdeg_next fun chosen' => by
            let chosen : (Fin k → K) → Fin m := fun σ => if σ = σ0 then i0 else chosen' σ
            have hprod : (Prest * L σ0 i0) * ∏ σ ∈ R', L σ (chosen' σ) =
                Prest * ∏ σ ∈ insert σ0 R', L σ (chosen σ) := by
              rw [Finset.prod_insert hσ0, mul_assoc]
              congr 1
              simp only [chosen, ↓reduceIte]
              congr 1
              refine Finset.prod_congr rfl fun σ hσ => ?_
              have hne : σ ≠ σ0 := fun h => hσ0 (h ▸ hσ)
              simp [hne]
            rw [hprod]
            exact hch chosen
  exact helim Finset.univ 1 (by simp [branches, K, ZMod.card]) fun chosen => by
    rw [one_mul]
    exact pc_mono (subset_refl visible) (le_max_right _ _) (hbase chosen)

end

end PEqualNP.Outside.L_pcx_463_aux

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_463_aux in
theorem PEqualNP.Outside.L_pcx_463 :
    ∀ (n m k d : ℕ),
      let K := ZMod 2
      let V := Fin n
      let U := V ⊕ Fin k
      let P := MvPolynomial V K
      let A := MvPolynomial U K
      let lift := fun p : P => MvPolynomial.rename (Sum.inl : V → U) p
      let h : Fin k → A := fun j => MvPolynomial.X (Sum.inr j)
      ∀ (F : Set P) (a : Fin m → P) (b : Fin m → Fin k → P),
        (∀ i : V, MvPolynomial.X i * MvPolynomial.X i + MvPolynomial.X i ∈ F) →
        (∀ i, (a i).totalDegree ≤ d+1 ∧ ∀ j, (b i j).totalDegree ≤ d) →
        let hidden := Set.image lift F ∪ Set.range (fun j => h j * h j + h j) ∪
          Set.range (fun i => lift (a i) + ∑ j, h j * lift (b i j))
        let test := fun (S : Finset (Fin m)) => (∑ i ∈ S, a i) * ∏ j, (1 + ∑ i ∈ S, b i j)
        let visible := F ∪ {g : P | ∃ S : Finset (Fin m), S.card ≤ k+1 ∧ g = test S}
        let branches := 2^k
        let localCost := (d+1) * max branches ((k+1)*(min m branches+1))
        (∀ B, PEqualNP.ProofComplexity.PCRefutable visible B →
          PEqualNP.ProofComplexity.PCRefutable hidden (max B (d+1+k*d))) ∧
        ∀ B, PEqualNP.ProofComplexity.PCRefutable hidden B →
          PEqualNP.ProofComplexity.PCRefutable visible (max (B+(branches-1)*(d+1)) localCost) := by
  intro n m k d K V U P A lift h F a b hbool hdeg hidden test visible branches localCost
  exact ⟨pc_visible_to_hidden F a b hbool hdeg, pc_hidden_to_visible F a b hbool hdeg⟩

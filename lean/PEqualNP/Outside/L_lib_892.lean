import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_892

abbrev F := ZMod 2
abbrev W (k : ℕ) := Fin k → F
abbrev S := F × F

def edge {k : ℕ} (x : W k) : W k := fun i => x i * x (finRotate k i)

def energy {k : ℕ} (f : W k → W k) : ℕ :=
  ((Finset.univ : Finset (W k × W k)).filter (fun p => f p.1 = f p.2)).card

def bound (k : ℕ) := 2 * (∑ j ∈ Finset.range (k/2+1), k.choose (2*j) * 3^j) +
  (if 2 ∣ k then 2 else 0)

def mat : Matrix S S ℕ := fun a b => if a.1*b.1 = a.2*b.2 then 1 else 0
def star : Matrix S S ℕ := fun a b => if (a = 0) ≠ (b = 0) then 1 else 0
def perm : Matrix S S ℕ := fun a b =>
  if (a = 0 ↔ b = 0) ∧ a.1*b.1 = a.2*b.2 then 1 else 0

def path {n : ℕ} (a b : S) (f : Fin n → S) : ℕ :=
  ∏ i, mat (Fin.cons (α := fun _ => S) a f i) (Fin.snoc (α := fun _ => S) f b i)

theorem sum_cons {n : ℕ} (f : (Fin (n+1) → S) → ℕ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → S, f (Fin.cons a x) := by
  rw [← Fintype.sum_prod_type (fun p : S × (Fin n → S) => f (Fin.cons p.1 p.2))]
  exact Fintype.sum_equiv (Fin.consEquiv (fun _ => S)).symm _ _ (fun x => by simp)

theorem path_count (n : ℕ) (a b : S) : ∑ f : Fin n → S, path a b f = (mat^(n+1)) a b := by
  induction n generalizing a with
  | zero =>
    simp [path, Fin.snoc, Fin.cons]
  | succ n ih =>
    rw [sum_cons, pow_succ' mat (n+1), Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [← ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [path, ← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]

theorem energy_trace (n : ℕ) : energy (@edge (n+1)) = (mat^(n+1)).trace := by
  unfold energy
  rw [Finset.card_filter]
  let e := (Equiv.arrowProdEquivProdArrow (Fin (n+1)) (fun _ => F) (fun _ => F)).symm
  trans ∑ f : Fin (n+1) → S, ∏ i, mat (f i) (f (finRotate _ i))
  · apply Fintype.sum_equiv e
    intro p
    simp only [mat, Finset.prod_boole, Finset.mem_univ, forall_const]
    congr 1
    exact propext funext_iff
  · rw [sum_cons, Matrix.trace]
    apply Finset.sum_congr rfl
    intro a _
    simpa only [path, Fin.snoc_eq_cons_rotate, Matrix.diag_apply] using path_count n a a

theorem star_perm : star * perm = star := by decide
theorem perm_star : perm * star = star := by decide
theorem perm_sq : perm^2 = 1 := by decide
theorem star_cube : star^3 = 3 • star := by decide

theorem star_step (m : ℕ) : star^(m+3) = 3 • star^(m+1) := by
  rw [pow_add, star_cube, Matrix.mul_smul, pow_succ]

theorem star_odd (j : ℕ) : (star^(2*j+1)).trace = 0 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show 2*(j+1)+1 = 2*j+3 by omega, star_step, Matrix.trace_smul, ih, smul_zero]

theorem star_even (j : ℕ) : (star^(2*j+2)).trace = 2 * 3^(j+1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show 2*(j+1)+2 = (2*j+1)+3 by omega, star_step, Matrix.trace_smul]
    change 3 * (star^(2*j+2)).trace = _
    rw [ih, pow_succ _ (j+1)]
    omega

theorem abs_perm (m n : ℕ) : star^(m+1) * perm^n = star^(m+1) := by
  have h : star^(m+1) * perm = star^(m+1) := by rw [pow_succ, mul_assoc, star_perm]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ perm, ← mul_assoc, ih, h]

theorem perm_trace (n : ℕ) : (perm^n).trace = 2 + (if 2 ∣ n then 2 else 0) := by
  by_cases h : 2 ∣ n
  · obtain ⟨j, rfl⟩ := h
    rw [pow_mul, perm_sq, one_pow, ite_eq_left (dvd_mul_right ..)]
    decide
  · obtain ⟨j, hj⟩ : ∃ j, n = 2*j+1 := ⟨n/2, by omega⟩
    rw [ite_eq_right h, hj, pow_succ, pow_mul, perm_sq, one_pow, one_mul]
    decide

theorem trace_term (k m : ℕ) :
    (star^m * perm^(k-m) * (k.choose m : ℕ)).trace =
    (if 2 ∣ m then 2 * (k.choose m * 3^(m/2)) else 0) +
      (if m = 0 ∧ 2 ∣ k then 2 else 0) := by
  rw [← Nat.cast_comm, ← nsmul_eq_mul, Matrix.trace_smul, smul_eq_mul]
  cases m with
  | zero => simp [perm_trace]
  | succ m =>
    rw [abs_perm]
    simp only [Nat.succ_ne_zero, false_and, ↓reduceIte, add_zero]
    by_cases h : 2 ∣ m+1
    · rw [ite_eq_left h]
      have he : m+1 = 2*(m/2)+2 := by omega
      rw [he, star_even, show (2*(m/2)+2)/2 = m/2+1 by omega]
      ring
    · rw [ite_eq_right h, show m+1 = 2*(m/2)+1 by omega, star_odd, mul_zero]

theorem exact_count (k : ℕ) (hk : 0 < k) : energy (@edge k) = bound k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [energy_trace]
  change (mat^(n+1)).trace = bound (n+1)
  generalize n+1 = k
  have hp : mat = star+perm := by decide
  have hc : Commute star perm := star_perm.trans perm_star.symm
  rw [hp, hc.add_pow, Matrix.trace_sum]
  simp_rw [trace_term, Finset.sum_add_distrib]
  unfold bound
  congr 1
  · rw [← Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_bij' (fun a _ => a/2) (fun a _ => 2*a)
    all_goals simp only [Finset.mem_filter, Finset.mem_range]
    all_goals intro a ha
    all_goals first | omega | rw [show 2*(a/2) = a by omega]
  · by_cases h : 2 ∣ k <;> simp [h]

def polar {k : ℕ} (d x : W k) : W k :=
  fun i => d i * x (finRotate _ i) + x i * d (finRotate _ i)

def res {k : ℕ} (A : W k →ₗ[F] W k) (b x : W k) := edge x + A x + b

def mass {k : ℕ} (d r : W k) : ℕ :=
  (Finset.univ.filter (fun x => polar d x = r)).card

def translated {k : ℕ} (A : W k →ₗ[F] W k) (b : W k) :=
  ∃ t c : W k, ∀ z, res A b z = edge (z+t) + c

theorem edge_add {k : ℕ} (x d : W k) : edge (x+d) = edge x + polar d x + edge d := by
  ext i
  simp only [edge, polar, Pi.add_apply]
  ring

theorem neg_self {k : ℕ} (x : W k) : -x = x := by
  ext i
  exact ZMod.neg_eq_self_mod_two _

theorem polar_add {k : ℕ} (d x t : W k) : polar d (x+t) = polar d x + polar d t := by
  ext i
  simp only [polar, Pi.add_apply]
  ring

theorem split_energy {k : ℕ} (A : W k →ₗ[F] W k) (b : W k) :
    energy (res A b) = ∑ d, mass d (edge d + A d) := by
  let e : W k × W k ≃ W k × W k :=
    { toFun := fun p => (p.2-p.1,p.1)
      invFun := fun q => (q.2,q.2+q.1)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp }
  simp only [energy, mass, Finset.card_filter]
  rw [← Fintype.sum_prod_type (fun p : W k × W k =>
    if polar p.1 p.2 = edge p.1 + A p.1 then 1 else 0)]
  symm
  apply Fintype.sum_equiv e.symm
  rintro ⟨d,x⟩
  change (if polar d x = edge d + A d then 1 else 0) =
    (if res A b x = res A b (x+d) then 1 else 0)
  congr 1
  rw [show res A b (x+d) = res A b x + (polar d x + (edge d + A d)) by
    simp only [res, edge_add, map_add]; abel]
  simp [add_eq_zero_iff_eq_neg, neg_self, add_comm]

theorem mass_eq {k : ℕ} (d t : W k) : mass d 0 = mass d (polar d t) := by
  apply Finset.card_equiv (Equiv.addRight t)
  intro x
  simp [polar_add]

theorem mass_empty {k : ℕ} {d r : W k} (h : ¬ ∃ x, polar d x = r) : mass d r = 0 := by
  simp [mass, not_exists.mp h]

theorem mass_le {k : ℕ} (d r : W k) : mass d r ≤ mass d 0 := by
  by_cases h : ∃ x, polar d x = r
  · obtain ⟨x, rfl⟩ := h
    exact (mass_eq d x).ge
  · simp [mass_empty h]

theorem translated_count {k : ℕ} {A : W k →ₗ[F] W k} {b : W k} (h : translated A b) :
    energy (res A b) = energy (@edge k) := by
  obtain ⟨t,c,ht⟩ := h
  apply Finset.card_equiv ((Equiv.addRight t).prodCongr (Equiv.addRight t))
  intro p
  simp [ht]

theorem bits (a : F) : a = 0 ∨ a = 1 := by revert a; decide

theorem base_feasible {k : ℕ} [NeZero k] (d : W k) (h : d ≠ 1 ∨ 2 ∣ k) :
    ∃ x, polar d x = edge d := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  obtain ⟨u,hu⟩ : ∃ u : Fin (n+1), d u = 0 ∨ 2 ∣ n+1 := by
    rcases h with h | h
    · by_contra! H
      exact h (funext fun i => (bits _).resolve_left (H i).1)
    · exact ⟨0, Or.inr h⟩
  refine ⟨fun i => d i * ((i-u).val : F), ?_⟩
  funext i
  let v := i-u
  have hv : finRotate _ i - u = v+1 := by rw [finRotate_apply]; dsimp [v]; abel
  change d i * (d _ * ((finRotate _ i-u).val : F)) +
    d i * (v.val : F) * d _ = d i * d (finRotate _ i)
  rw [hv, Fin.val_add_one]
  by_cases hl : v = Fin.last n
  · have he : finRotate _ i = u := sub_eq_zero.mp (by rw [hv, hl, Fin.last_add_one])
    rw [ite_eq_left hl, hl, Fin.val_last, he]
    rcases hu with hu | hu
    · simp [hu]
    · have hn := (CharP.cast_eq_zero_iff F 2 (n+1)).2 hu
      rw [Nat.cast_add_one, add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two] at hn
      simp [hn]
  · rw [ite_eq_right hl, Nat.cast_add_one]
    have he (a b c : F) : a*(b*(c+1))+a*c*b = a*b := by revert a b c; decide
    exact he _ _ _

theorem full_kernel {k : ℕ} [NeZero k] : mass (1 : W k) 0 ≤ 2 := by
  have hc (x : W k) (hx : polar 1 x = 0) (i : Fin k) : x i = x 0 := by
    have hs (j : Fin k) : x (j+1) = x j := by
      have := congrFun hx j
      simpa [polar, finRotate_apply, add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two] using this
    have hh (m : ℕ) : x (Fin.ofNat k m) = x 0 := by
      induction m with
      | zero => simp
      | succ m ih =>
        have he : Fin.ofNat k (m+1) = Fin.ofNat k m + 1 :=
          (Fin.instAddMonoidWithOne k).natCast_succ m
        rw [he, hs, ih]
    simpa using hh i.val
  trans (Finset.univ : Finset F).card
  swap
  · simp [ZMod.card]
  apply Finset.card_le_card_of_injOn (fun x : W k => x 0) (fun _ _ => Finset.mem_univ _)
  intro x hx y hy he
  exact funext fun i => (hc x (Finset.mem_filter.mp hx).2 i).trans
    (he.trans (hc y (Finset.mem_filter.mp hy).2 i).symm)

theorem total_kernel {k : ℕ} [NeZero k] :
    ∑ d : W k, mass d 0 ≤ energy (@edge k) + (if 2 ∣ k then 0 else 2) := by
  have h (d : W k) : mass d 0 ≤ mass d (edge d) +
      (if d = 1 then (if 2 ∣ k then 0 else 2) else 0) := by
    by_cases hd : d ≠ 1 ∨ 2 ∣ k
    · obtain ⟨x,hx⟩ := base_feasible d hd
      rw [← hx, ← mass_eq]
      omega
    · push Not at hd
      rw [hd.1]
      simp only [↓reduceIte, ite_eq_right hd.2]
      exact (full_kernel (k := k)).trans (Nat.le_add_left ..)
  have hz : res (0 : W k →ₗ[F] W k) 0 = edge := by ext x i; simp [res]
  simpa [Finset.sum_add_distrib, ← hz, split_energy] using Finset.sum_le_sum
    (s := Finset.univ) (fun d _ => h d)

def unit {k : ℕ} (j : Fin k) : W k := Pi.single j 1

def coeff {k : ℕ} (A : W k →ₗ[F] W k) (i j : Fin k) := A (unit j) i

theorem distinct_sites {k : ℕ} (hk : 3 ≤ k) (i : Fin k) :
    finRotate k i ≠ i ∧ finRotate k (finRotate k i) ≠ i := by
  let := i.neZero
  have h (m : ℕ) (hm : 0 < m) (hm' : m < k) : i + Fin.ofNat k m ≠ i := by
    intro he
    have hz : Fin.ofNat k m = 0 := add_left_cancel (he.trans (add_zero i).symm)
    have := Nat.le_of_dvd hm (Fin.natCast_eq_zero.mp hz)
    omega
  simp only [finRotate_apply, add_assoc]
  refine ⟨h 1 (by decide) (by omega), ?_⟩
  have he : Fin.ofNat k 2 = (1 : Fin k) + 1 := (Fin.instAddMonoidWithOne k).natCast_succ 1
  rw [← he]
  exact h 2 (by decide) (by omega)

theorem local_row {k : ℕ} (hk : 3 ≤ k) (A : W k →ₗ[F] W k) (i : Fin k)
    (h : ∀ j, j ≠ i → j ≠ finRotate k i → coeff A i j = 0) (z : W k) :
    A z i = z i * coeff A i i + z (finRotate k i) * coeff A i (finRotate k i) := by
  have hz : z = ∑ j, z j • unit j := by
    ext u
    simp [Finset.sum_apply, Pi.smul_apply, unit, Pi.single_apply, mul_ite, smul_eq_mul]
  calc
    A z i = ∑ j, z j * coeff A i j := by
      conv_lhs => rw [hz, map_sum, Finset.sum_apply]
      simp [coeff, Pi.smul_apply, smul_eq_mul]
    _ = ∑ j ∈ ({i,finRotate k i} : Finset _), z j * coeff A i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [h j hj.1 hj.2]
    _ = _ := by
      rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using (distinct_sites hk i).1.symm),
        Finset.sum_singleton]

theorem bad_direction {k : ℕ} (hk : 3 ≤ k) (A : W k →ₗ[F] W k) (b : W k)
    (ht : ¬ translated A b) :
    ∃ (p : Fin k) (d : W k), d ≠ 0 ∧
      (∀ j, d j ≠ 0 → j = p ∨ j = finRotate _ (finRotate _ p)) ∧
      mass d (edge d + A d) = 0 := by
  let r := finRotate k
  by_cases hl : ∀ i j, j ≠ i → j ≠ r i → coeff A i j = 0
  · have row := fun i z => local_row hk A i (hl i) z
    by_cases hc : ∀ i, coeff A i i = coeff A (r i) (r (r i))
    · exfalso
      apply ht
      let t : W k := fun i => coeff A i (r i)
      refine ⟨t,b-edge t,fun z => ?_⟩
      have ha : A z = polar t z := by
        funext i
        rw [row]
        change _ = t i * z (r i) + z i * t (r i)
        rw [hc i]
        dsimp [t,r]
        ring
      rw [res, ha, edge_add]
      abel
    · push Not at hc
      obtain ⟨i,hi⟩ := hc
      let d := unit i + unit (r (r i))
      have h₁ := (distinct_sites hk i).1
      have h₂ := (distinct_sites hk i).2
      have h₃ := (distinct_sites hk (r i)).1
      change r i ≠ i at h₁
      change r (r i) ≠ i at h₂
      change r (r i) ≠ r i at h₃
      have a : d i = 1 := by simp [d, unit, h₂.symm]
      have c : d (r i) = 0 := by simp [d, unit, h₁, h₃.symm]
      have e : d (r (r i)) = 1 := by simp [d, unit, h₂]
      refine ⟨i,d,fun hd => one_ne_zero (α := F) (a.symm.trans (congrFun hd i)), ?_, ?_⟩
      · intro j hj
        by_contra! hn
        change j ≠ i ∧ j ≠ r (r i) at hn
        exact hj (by simp [d, unit, hn.1, hn.2])
      · apply mass_empty
        rintro ⟨x,hx⟩
        have hL := congrFun hx i
        have hR := congrFun hx (r i)
        change d i*x (r i)+x i*d (r i) = d i*d (r i)+A d i at hL
        change d (r i)*x (r (r i))+x (r i)*d (r (r i)) =
          d (r i)*d (r (r i))+A d (r i) at hR
        rw [row] at hL hR
        change _ = _ + (d i * coeff A i i + d (r i) * coeff A i (r i)) at hL
        change _ = _ + (d (r i)*coeff A (r i) (r i) +
          d (r (r i))*coeff A (r i) (r (r i))) at hR
        simp only [a,c,e,one_mul,mul_zero,zero_add,add_zero,zero_mul,mul_one] at hL hR
        exact hi (hL.symm.trans hR)
  · push Not at hl
    obtain ⟨i,j,hj,hr,hc⟩ := hl
    refine ⟨j,unit j,?_,?_,?_⟩
    · intro he
      have := congrFun he j
      simp [unit] at this
    · intro u hu
      exact Or.inl (by by_contra h; exact hu (by simp [unit, h]))
    · apply mass_empty
      rintro ⟨x,hx⟩
      apply hc
      have he := congrFun hx i
      change unit j i * x (r i) + x i * unit j (r i) =
        unit j i * unit j (r i) + coeff A i j at he
      simpa [unit, Pi.single_apply, hj.symm, hr.symm] using he.symm

theorem kernel_two {k : ℕ} {d : W k} (hd : d ≠ 0) : 2 ≤ mass d 0 := by
  have h : ({0,d} : Finset (W k)) ⊆ Finset.univ.filter (fun x => polar d x = 0) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hx with rfl | rfl
    · ext i; simp [polar]
    · ext i; exact CharTwo.add_self_eq_zero _
  simpa [mass, hd.symm] using Finset.card_le_card h

theorem sparse_kernel {k : ℕ} (p : Fin k) (d : W k)
    (hs : ∀ j, d j ≠ 0 → j = p ∨ j = finRotate k (finRotate k p)) :
    2^(k-3) ≤ mass d 0 := by
  let r := finRotate k
  let s : Finset (Fin k) := {r.symm p, r p, r (r (r p))}
  have hc : s.card ≤ 3 := by
    dsimp only [s]
    have h₁ := Finset.card_insert_le (r.symm p) ({r p,r (r (r p))} : Finset _)
    have h₂ := Finset.card_insert_le (r p) ({r (r (r p))} : Finset _)
    simp only [Finset.card_singleton] at h₂
    omega
  let V := {j : Fin k // j ∉ s} → F
  let lift (f : V) : W k := fun j => if hj : j ∈ s then 0 else f ⟨j,hj⟩
  have hzero (f : V) (j : Fin k) (hj : j ∈ s) : lift f j = 0 := by simp [lift, hj]
  have image (f : V) : polar d (lift f) = 0 := by
    funext i
    change d i * lift f (r i) + lift f i * d (r i) = 0
    have h₁ : d i * lift f (r i) = 0 := by
      by_cases hi : d i = 0
      · simp [hi]
      · apply mul_eq_zero.mpr ∘ Or.inr
        apply hzero
        rcases hs i hi with h | h <;> rw [h] <;> simp only [s, r, Finset.mem_insert,
          Finset.mem_singleton] <;> tauto
    rw [h₁, zero_add]
    by_cases hi : d (r i) = 0
    · simp [hi]
    · apply mul_eq_zero.mpr ∘ Or.inl
      apply hzero
      rcases hs (r i) hi with h | h
      · have he := r.eq_symm_apply.mpr h
        rw [he]
        exact Finset.mem_insert_self ..
      · have he : i = r p := r.injective h
        simp [s, he]
  have hcard : (Finset.univ : Finset V).card = 2^(k-s.card) := by
    simp [V, ZMod.card]
  calc
    2^(k-3) ≤ 2^(k-s.card) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = (Finset.univ : Finset V).card := hcard.symm
    _ ≤ mass d 0 := by
      apply Finset.card_le_card_of_injOn lift
      · exact fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,image f⟩
      · intro f _ g _ he
        funext j
        simpa only [lift, dite_eq_right j.property] using congrFun he j.val

theorem loss {k : ℕ} [NeZero k] (hk : 3 ≤ k) (A : W k →ₗ[F] W k) (b : W k)
    (ht : ¬ translated A b) : energy (res A b) + max 2 (2^(k-3)) ≤
      bound k + (if 2 ∣ k then 0 else 2) := by
  obtain ⟨p,d,hd,hs,he⟩ := bad_direction hk A b ht
  have h (j : W k) : mass j (edge j + A j) +
      (if j = d then max 2 (2^(k-3)) else 0) ≤ mass j 0 := by
    by_cases hj : j = d
    · subst j
      simpa [he] using max_le (kernel_two hd) (sparse_kernel p d hs)
    · simpa [hj] using mass_le j (edge j + A j)
  have H := Finset.sum_le_sum (s := Finset.univ) fun j _ => h j
  rw [split_energy, ← exact_count k (Nat.pos_of_ne_zero (NeZero.ne k))]
  apply le_trans _ total_kernel
  simpa [Finset.sum_add_distrib] using H

theorem finish {k : ℕ} (hk : 3 ≤ k) :
    energy (res (0 : W k →ₗ[F] W k) 0) = bound k ∧ ∀ (A : W k →ₗ[F] W k) (b : W k),
      energy (res A b) ≤ bound k ∧
      (5 ≤ k → (energy (res A b) = bound k ↔ translated A b) ∧
        (¬ translated A b → energy (res A b) + 2^(k-3) ≤ bound k + (if 2 ∣ k then 0 else 2))) := by
  let : NeZero k := ⟨by omega⟩
  have hb := exact_count k (by omega)
  have hz : res (0 : W k →ₗ[F] W k) 0 = edge := by ext x i; simp [res]
  refine ⟨hz ▸ hb,?_⟩
  intro A b
  by_cases ht : translated A b
  · have he := (translated_count ht).trans hb
    exact ⟨he.le,fun _ => ⟨iff_of_true he ht,fun h => (h ht).elim⟩⟩
  · have he := loss hk A b ht
    have h₂ := le_max_left 2 (2^(k-3))
    have h₃ := le_max_right 2 (2^(k-3))
    have hb' : (if 2 ∣ k then 0 else 2) ≤ 2 := by split <;> decide
    refine ⟨by omega,fun h₅ => ⟨?_,fun _ => by omega⟩⟩
    have hp : 2^2 ≤ 2^(k-3) := Nat.pow_le_pow_right (by decide) (by omega)
    exact iff_of_false (by omega) ht

end PEqualNP.Outside.L_lib_892

theorem PEqualNP.Outside.L_lib_892 : ∀ (k : Nat) (hk : 0 < k), 3 ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let nxt := fun j : Fin k => (⟨(j.val+1)%k, Nat.mod_lt _ hk⟩ : Fin k)
  let edge := fun (x : W) (i : Fin k) => x i * x (nxt i)
  let residual := fun (A : W →ₗ[F] W) (b z : W) => edge z + A z + b
  let energy := fun (A : W →ₗ[F] W) (b : W) =>
    ((Finset.univ : Finset (W × W)).filter
      (fun p => residual A b p.1 = residual A b p.2)).card
  let translated := fun (A : W →ₗ[F] W) (b : W) =>
    ∃ t c : W, ∀ z : W, residual A b z = edge (z+t) + c
  let top := 2 * (∑ j ∈ Finset.range (k/2+1), k.choose (2*j) * 3^j) +
    (if 2 ∣ k then 2 else 0)
  energy 0 0 = top ∧ ∀ (A : W →ₗ[F] W) (b : W),
    energy A b ≤ top ∧
    (5 ≤ k → (energy A b = top ↔ translated A b) ∧
      (¬ translated A b → energy A b + 2^(k-3) ≤ top + (if 2 ∣ k then 0 else 2))) := by
  intro k hk h₃
  let : NeZero k := ⟨hk.ne'⟩
  have hn (i : Fin k) : (⟨(i.val+1)%k, Nat.mod_lt _ hk⟩ : Fin k) = finRotate k i := by
    apply Fin.ext
    simp only [finRotate_apply, Fin.add_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < k by omega)]
  dsimp only
  simp only [hn]
  exact PEqualNP.Outside.L_lib_892.finish h₃

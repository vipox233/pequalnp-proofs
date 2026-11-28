import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.SimpRw
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_914_aux

open Finset

lemma kernel_term (I : ℕ → ℕ) (t f h : ℕ) :
    f.choose h * t.descFactorial h * I (t-h) =
      (t.choose h * I (t-h)) * f.descFactorial h := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  ring

lemma falling_det (d : ℕ) (f : Fin (d+1) → ℕ) :
    (Matrix.of fun h j : Fin (d+1) => ((f j).descFactorial h.val : ℤ)).det =
      (Matrix.vandermonde (fun j => (f j : ℤ))).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun j => (f j : ℤ)) (fun h : Fin (d+1) => descPochhammer ℤ h.val)
    (fun h => descPochhammer_natDegree ℤ h.val)
    (fun h => monic_descPochhammer ℤ h.val)
  rw [← Matrix.det_transpose]
  rw [h]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, descPochhammer_eval_eq_descFactorial]

lemma lower_det (I : ℕ → ℕ) (hI : I 0 = 1) (d : ℕ) :
    (Matrix.of fun t h : Fin (d+1) => ((t.val.choose h.val * I (t.val-h.val) : ℕ) : ℤ)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hI]
  · intro i j hij
    have hij' : i.val < j.val := hij
    simp [Nat.choose_eq_zero_of_lt hij']

lemma kernel_matrix_factor (I : ℕ → ℕ) (d : ℕ) (f : Fin (d+1) → ℕ) :
    (Matrix.of fun t j : Fin (d+1) =>
      (((range (t.val+1)).sum (fun h =>
        (f j).choose h * t.val.descFactorial h * I (t.val-h))) : ℤ)) =
    (Matrix.of fun t h : Fin (d+1) => ((t.val.choose h.val * I (t.val-h.val) : ℕ) : ℤ)) *
    (Matrix.of fun h j : Fin (d+1) => ((f j).descFactorial h.val : ℤ)) := by
  ext t j
  have hn : (∑ h ∈ range (t.val+1),
      (f j).choose h * t.val.descFactorial h * I (t.val-h)) =
      ∑ h : Fin (d+1), (t.val.choose h.val * I (t.val-h.val)) *
        (f j).descFactorial h.val := by
    rw [show (∑ h : Fin (d+1), (t.val.choose h.val * I (t.val-h.val)) *
        (f j).descFactorial h.val) =
        ∑ h ∈ range (d+1), (t.val.choose h * I (t.val-h)) *
          (f j).descFactorial h from
      Fin.sum_univ_eq_sum_range (fun h => (t.val.choose h * I (t.val-h)) *
          (f j).descFactorial h) (d+1)]
    simp_rw [kernel_term]
    apply sum_subset (range_mono (by omega : t.val+1 ≤ d+1))
    intro h hh hnot
    have hlt : t.val < h := by simp only [mem_range, not_lt] at hnot; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact_mod_cast hn

lemma kernel_det (I : ℕ → ℕ) (hI : I 0 = 1) (d : ℕ)
    (f : Fin (d+1) → ℕ) :
    (Matrix.of fun t j : Fin (d+1) =>
      (((range (t.val+1)).sum (fun h =>
        (f j).choose h * t.val.descFactorial h * I (t.val-h))) : ℤ)).det =
      (Matrix.vandermonde (fun j => (f j : ℤ))).det := by
  rw [kernel_matrix_factor, Matrix.det_mul, lower_det I hI, one_mul, falling_det]

lemma affine_vandermonde (d e : ℕ) :
    (Matrix.vandermonde (fun j : Fin (d+1) => ((e+2*j.val : ℕ) : ℤ))).det =
      (2:ℤ)^(d*(d+1)/2) * ∏ j : Fin (d+1), (j.val.factorial : ℤ) := by
  have he : (fun j : Fin (d+1) => ((e+2*j.val : ℕ) : ℤ)) =
      (fun j => 2*(j.val:ℤ) + (e:ℤ)) := by ext j; push_cast; ring
  rw [he, Matrix.det_vandermonde_add]
  have hs : (Matrix.vandermonde (fun j : Fin (d+1) => 2*(j.val:ℤ))) =
      (Matrix.of (fun i j : Fin (d+1) => (2:ℤ)^j.val *
        Matrix.vandermonde (fun k : Fin (d+1) => (k.val:ℤ)) i j)) := by
    ext i j
    simp [Matrix.vandermonde_apply, mul_pow]
  rw [hs, Matrix.det_mul_row, Matrix.det_vandermonde_id_eq_superFactorial]
  congr 1
  · rw [prod_pow_eq_pow_sum]
    congr 1
    rw [show (∑ i : Fin (d+1), i.val) = ∑ i ∈ range (d+1), i from
      Fin.sum_univ_eq_sum_range (fun i => i) (d+1), sum_range_id]
    simp [Nat.mul_comm]
  · rw [show (∏ j : Fin (d+1), (j.val.factorial : ℤ)) =
      ∏ j ∈ range (d+1), (j.factorial : ℤ) from
      Fin.prod_univ_eq_prod_range (fun j => (j.factorial : ℤ)) (d+1),
      ← Nat.cast_prod, Nat.prod_range_succ_factorial]

lemma involution_zero :
    Nat.card {P : Equiv.Perm (Fin 0) // Function.Involutive P} = 1 := by
  have h : Unique {P : Equiv.Perm (Fin 0) // Function.Involutive P} :=
    { default := ⟨Equiv.refl _, fun x => Fin.elim0 x⟩
      uniq := fun p => Subtype.ext (Subsingleton.elim _ _) }
  let := h
  exact Nat.card_unique

lemma exact_kernel_det (n : ℕ) :
    let I := fun k : ℕ => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}
    let d := n/2
    let free := fun j : Fin (d+1) => n % 2+2*j.val
    let kernel := fun t f : ℕ => (range (t+1)).sum (fun h =>
      f.choose h * t.descFactorial h * I (t-h))
    let K : Matrix (Fin (d+1)) (Fin (d+1)) ℤ := fun t j => (kernel t.val (free j) : ℤ)
    K.det = (2:ℤ)^(d*(d+1)/2) * ∏ j : Fin (d+1), (j.val.factorial : ℤ) := by
  dsimp only
  have h := (kernel_det (fun k : ℕ => Nat.card {P : Equiv.Perm (Fin k) //
      Function.Involutive P}) involution_zero (n/2)
      (fun j => n%2+2*j.val)).trans (affine_vandermonde (n/2) (n%2))
  rw [← h]
  congr 1
  ext t j
  simp only [Matrix.of_apply, Nat.cast_sum, Nat.cast_mul]

def restrictOld {α β : Type*} (P : Equiv.Perm (α ⊕ β)) (a : α) : α :=
  (P (Sum.inl a)).elim id (fun _ => a)

lemma restrictOld_involutive {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (hP : Function.Involutive P) : Function.Involutive (restrictOld P) := by
  intro a
  cases h : P (Sum.inl a) with
  | inl b =>
    have hb : P (Sum.inl b) = Sum.inl a := by
      rw [← h]
      exact hP _
    simp [restrictOld, h, hb]
  | inr b => simp [restrictOld, h]

lemma restrictOld_eq_iff {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (a b : α) (hne : b ≠ a) :
    restrictOld P a = b ↔ P (Sum.inl a) = Sum.inl b := by
  cases h : P (Sum.inl a) with
  | inl c => simp [restrictOld, h]
  | inr c => simp [restrictOld, h, Ne.symm hne]

lemma restrictOld_preserves_winning {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (R : Set α) :
    (∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (Sum.inl u) = Sum.inl v) ↔
    ∃ u ∈ R, restrictOld P u ∈ R ∧ restrictOld P u ≠ u := by
  constructor
  · rintro ⟨u, hu, v, hv, hne, hP⟩
    have hq := (restrictOld_eq_iff P u v (Ne.symm hne)).mpr hP
    exact ⟨u, hu, hq ▸ hv, hq ▸ Ne.symm hne⟩
  · rintro ⟨u, hu, hv, hne⟩
    exact ⟨u, hu, restrictOld P u, hv, Ne.symm hne,
      (restrictOld_eq_iff P u (restrictOld P u) hne).mp rfl⟩

lemma involution_fixed_histogram_index (n : ℕ) (P : Equiv.Perm (Fin n))
    (hP : Function.Involutive P) :
    ∃ j : Fin (n/2+1),
      (univ.filter (fun u => P u = u)).card = n%2+2*j.val := by
  let A := univ.filter (fun u : Fin n => u < P u)
  let B := univ.filter (fun u : Fin n => P u < u)
  let F := univ.filter (fun u : Fin n => P u = u)
  have hab : A.card = B.card := by
    apply card_bij (fun u _ => P u)
    · intro u hu
      simpa only [A, B, mem_filter, mem_univ, true_and, hP u] using hu
    · intro a ha b hb heq
      exact P.injective heq
    · intro b hb
      refine ⟨P b, ?_, hP b⟩
      simpa only [A, B, mem_filter, mem_univ, true_and, hP b] using hb
  have hsplit : n = F.card + A.card + B.card := by
    have h₁ := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun u => P u = u)
    have h₂ := card_filter_add_card_filter_not
      (s := univ.filter (fun u : Fin n => P u ≠ u)) (fun u => u < P u)
    have hA : ((univ.filter (fun u : Fin n => P u ≠ u)).filter
        (fun u => u < P u)) = A := by
      ext u
      simp only [A, mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨Ne.symm (ne_of_lt h), h⟩
    have hB : ((univ.filter (fun u : Fin n => P u ≠ u)).filter
        (fun u => ¬u < P u)) = B := by
      ext u
      simp only [B, mem_filter, mem_univ, true_and]
      omega
    rw [hA, hB] at h₂
    simp only [Fintype.card_fin, card_univ] at h₁
    change F.card + _ = n at h₁
    calc
      n = F.card + (A.card + B.card) := by rw [h₂]; exact h₁.symm
      _ = F.card + A.card + B.card := (Nat.add_assoc _ _ _).symm
  refine ⟨⟨F.card/2, by omega⟩, ?_⟩
  change F.card = n%2+2*(F.card/2)
  omega

def finSplitPerm (n t : ℕ) (P : Equiv.Perm (Fin (n+t))) :
    Equiv.Perm (Fin n ⊕ Fin t) :=
  (finSumFinEquiv (m := n) (n := t)).symm.permCongr P

lemma finSplitPerm_involutive (n t : ℕ) (P : Equiv.Perm (Fin (n+t)))
    (hP : Function.Involutive P) : Function.Involutive (finSplitPerm n t P) := by
  intro x
  change finSumFinEquiv.symm
    (P (finSumFinEquiv (finSumFinEquiv.symm (P (finSumFinEquiv x))))) = x
  rw [Equiv.apply_symm_apply, hP (finSumFinEquiv x), Equiv.symm_apply_apply]

def paddedOldRestriction (n t : ℕ) (P : Equiv.Perm (Fin (n+t)))
    (hP : Function.Involutive P) : Equiv.Perm (Fin n) :=
  (restrictOld_involutive _ (finSplitPerm_involutive n t P hP)).toPerm _

lemma paddedOldRestriction_involutive (n t : ℕ) (P : Equiv.Perm (Fin (n+t)))
    (hP : Function.Involutive P) :
    Function.Involutive (paddedOldRestriction n t P hP) :=
  restrictOld_involutive _ (finSplitPerm_involutive n t P hP)

lemma paddedOldRestriction_winning (n t : ℕ) (P : Equiv.Perm (Fin (n+t)))
    (hP : Function.Involutive P) (R : Finset (Fin n)) :
    (∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (u.castAdd t) = v.castAdd t) ↔
    (∃ u ∈ R, paddedOldRestriction n t P hP u ∈ R ∧
      paddedOldRestriction n t P hP u ≠ u) := by
  have he (u v : Fin n) :
      finSplitPerm n t P (Sum.inl u) = Sum.inl v ↔
        P (u.castAdd t) = v.castAdd t := by
    simp only [finSplitPerm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
  simpa only [he, paddedOldRestriction, Function.Involutive.coe_toPerm,
    Set.mem_ofPred_eq] using
      (restrictOld_preserves_winning (finSplitPerm n t P) {u | u ∈ R})

lemma histogram_partition {α : Type*} [Finite α] (Q : α → Prop)
    (f : α → ℕ) (d e : ℕ)
    (hf : ∀ a, Q a → ∃ j : Fin (d+1), f a = e+2*j.val) :
    Nat.card {a // Q a} =
      ∑ j : Fin (d+1), Nat.card {a // Q a ∧ f a = e+2*j.val} := by
  let forget : (Σ j : Fin (d+1), {a // Q a ∧ f a = e+2*j.val}) → {a // Q a} :=
    fun p => ⟨p.2.val, p.2.property.1⟩
  have hi : Function.Injective forget := by
    rintro ⟨i, a, ha, hfa⟩ ⟨j, b, hb, hfb⟩ heq
    have hab : a = b := congrArg Subtype.val heq
    subst b
    have hij : i = j := Fin.ext (by omega)
    subst j
    rfl
  have hs : Function.Surjective forget := by
    intro a
    obtain ⟨j, hj⟩ := hf a.val a.property
    exact ⟨⟨j, a.val, a.property, hj⟩, rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective forget ⟨hi, hs⟩)
  rw [Nat.card_sigma] at hc
  exact hc.symm

lemma winning_histogram_partition (n : ℕ) (H : Finset (Finset (Fin n))) :
    Nat.card {P : Equiv.Perm (Fin n) // Function.Involutive P ∧
      ∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u} =
    ∑ j : Fin (n/2+1), Nat.card {P : Equiv.Perm (Fin n) //
      Function.Involutive P ∧
      (∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u) ∧
      (univ.filter (fun u => P u = u)).card = n%2+2*j.val} := by
  classical
  simpa only [and_assoc] using histogram_partition
    (fun P : Equiv.Perm (Fin n) => Function.Involutive P ∧
      ∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u)
    (fun P => (univ.filter (fun u => P u = u)).card) (n/2) (n%2)
    (fun P hP => involution_fixed_histogram_index n P hP.1)

lemma exact_padding_zero (n : ℕ) (H : Finset (Finset (Fin n))) :
    let I := fun k : ℕ => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}
    let kernel := fun t f : ℕ => (range (t+1)).sum (fun h =>
      f.choose h * t.descFactorial h * I (t-h))
    Nat.card {P : Equiv.Perm (Fin (n+0)) // Function.Involutive P ∧
      ∀ R ∈ H, ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (u.castAdd 0) = v.castAdd 0} =
    ∑ j : Fin (n/2+1), kernel 0 (n%2+2*j.val) *
      Nat.card {P : Equiv.Perm (Fin n) //
        Function.Involutive P ∧
        (∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u) ∧
        (univ.filter (fun u => P u = u)).card = n%2+2*j.val} := by
  dsimp only
  simp only [Nat.zero_add, range_one, sum_singleton, Nat.choose_zero_right,
    Nat.descFactorial_zero, mul_one, Nat.sub_zero, involution_zero, one_mul]
  rw [← winning_histogram_partition n H]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro P
  constructor
  · rintro ⟨hP, hw⟩
    refine ⟨hP, ?_⟩
    intro R hR
    obtain ⟨u, hu, v, hv, hne, heq⟩ := hw R hR
    have heq' : P u = v := by simpa using heq
    exact ⟨u, hu, heq' ▸ hv, heq' ▸ Ne.symm hne⟩
  · rintro ⟨hP, hw⟩
    refine ⟨hP, ?_⟩
    intro R hR
    obtain ⟨u, hu, hv, hne⟩ := hw R hR
    exact ⟨u, hu, P u, hv, Ne.symm hne, by simp⟩

lemma all_fixed_unique (n : ℕ) (P : Equiv.Perm (Fin n))
    (h : (univ.filter (fun u => P u = u)).card = n) : P = Equiv.refl _ := by
  classical
  have hs : univ.filter (fun u => P u = u) = univ := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    simp [h]
  ext u
  have hu : u ∈ univ.filter (fun u => P u = u) := by rw [hs]; simp
  exact congrArg Fin.val (mem_filter.mp hu).2

lemma all_fixed_involution_count (n : ℕ) :
    Nat.card {P : Equiv.Perm (Fin n) // Function.Involutive P ∧
      (univ.filter (fun u => P u = u)).card = n} = 1 := by
  classical
  have h : Unique {P : Equiv.Perm (Fin n) // Function.Involutive P ∧
      (univ.filter (fun u => P u = u)).card = n} :=
    { default := ⟨Equiv.refl _, by simp [Function.Involutive]⟩
      uniq := fun P => Subtype.ext (all_fixed_unique n P.val P.property.2) }
  let := h
  exact Nat.card_unique

lemma card_restricted_fibers {α β : Type*} [Finite α] [Fintype β]
    (f : α → β) (Q : β → Prop) [DecidablePred Q] :
    Nat.card {a // Q (f a)} = ∑ b : {b // Q b}, Nat.card {a // f a = b.val} := by
  classical
  let forget : (Σ b : {b // Q b}, {a // f a = b.val}) → {a // Q (f a)} :=
    fun p => ⟨p.2.val, p.2.property.symm ▸ p.1.property⟩
  have hi : Function.Injective forget := by
    rintro ⟨⟨b, hb⟩, a, hfa⟩ ⟨⟨c, hc⟩, d, hfd⟩ heq
    have had : a = d := congrArg Subtype.val heq
    subst d
    have hbc : b = c := hfa.symm.trans hfd
    subst c
    rfl
  have hs : Function.Surjective forget := by
    intro a
    exact ⟨⟨⟨f a.val, a.property⟩, a.val, rfl⟩, rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective forget ⟨hi, hs⟩)
  rw [Nat.card_sigma] at hc
  exact hc.symm

def oldProjection (n t : ℕ) :
    {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P} →
    {P : Equiv.Perm (Fin n) // Function.Involutive P} :=
  fun P => ⟨paddedOldRestriction n t P.val P.property,
    paddedOldRestriction_involutive n t P.val P.property⟩

def winsOld (n : ℕ) (H : Finset (Finset (Fin n))) (P : Equiv.Perm (Fin n)) : Prop :=
  ∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u

lemma padded_fits_as_old_wins (n t : ℕ) (H : Finset (Finset (Fin n)))
    (P : Equiv.Perm (Fin (n+t))) (hP : Function.Involutive P) :
    (∀ R ∈ H, ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (u.castAdd t) = v.castAdd t) ↔
    winsOld n H (paddedOldRestriction n t P hP) := by
  unfold winsOld
  exact forall_congr' fun R => forall_congr' fun _ =>
    paddedOldRestriction_winning n t P hP R

open scoped Classical in
lemma exact_count_as_restriction_fibers (n t : ℕ) (H : Finset (Finset (Fin n))) :
    Nat.card {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P ∧
      ∀ R ∈ H, ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (u.castAdd t) = v.castAdd t} =
    ∑ Q : {Q : {P : Equiv.Perm (Fin n) // Function.Involutive P} //
      winsOld n H Q.val},
      Nat.card {P : {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P} //
        oldProjection n t P = Q.val} := by
  classical
  let := Fintype.ofFinite {Q : {P : Equiv.Perm (Fin n) // Function.Involutive P} //
    winsOld n H Q.val}
  rw [← card_restricted_fibers (oldProjection n t) (fun Q => winsOld n H Q.val)]
  apply Nat.card_congr
  exact
    { toFun := fun P => ⟨⟨P.val, P.property.1⟩,
        (padded_fits_as_old_wins n t H P.val P.property.1).mp P.property.2⟩
      invFun := fun P => ⟨P.val.val, P.val.property,
        (padded_fits_as_old_wins n t H P.val.val P.val.property).mpr P.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def crossingPartner {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (a : {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b}) : β :=
  Classical.choose a.property

lemma crossingPartner_spec {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (a : {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b}) :
    P (Sum.inl a.val) = Sum.inr (crossingPartner P a) :=
  Classical.choose_spec a.property

lemma crossingPartner_injective {α β : Type*} (P : Equiv.Perm (α ⊕ β)) :
    Function.Injective (crossingPartner P) := by
  intro a b h
  apply Subtype.ext
  apply Sum.inl_injective
  apply P.injective
  rw [crossingPartner_spec, crossingPartner_spec, h]

lemma crossingPartner_reverse {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (hP : Function.Involutive P)
    (a : {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b}) :
    P (Sum.inr (crossingPartner P a)) = Sum.inl a.val := by
  rw [← crossingPartner_spec]
  exact hP _

lemma crossing_old_fixed {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (a : {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b}) :
    restrictOld P a.val = a.val := by
  simp [restrictOld, crossingPartner_spec P a]

lemma crossing_card_bounds {α β : Type*} [Finite α] [Finite β]
    (P : Equiv.Perm (α ⊕ β)) :
    Nat.card {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b} ≤ Nat.card β ∧
    Nat.card {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b} ≤
      Nat.card {a : α // restrictOld P a = a} := by
  constructor
  · exact Nat.card_le_card_of_injective _ (crossingPartner_injective P)
  · let f : {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b} →
        {a : α // restrictOld P a = a} := fun a => ⟨a.val, crossing_old_fixed P a⟩
    apply Nat.card_le_card_of_injective f
    intro a b h
    exact Subtype.ext (congrArg (fun x : {a : α // restrictOld P a = a} => x.val) h)

def unusedPad {α β : Type*} (P : Equiv.Perm (α ⊕ β)) (b : β) : Prop :=
  ∀ a : α, P (Sum.inl a) ≠ Sum.inr b

lemma unusedPad_image {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (hP : Function.Involutive P) (b : β) (hb : unusedPad P b) :
    ∃ c : β, P (Sum.inr b) = Sum.inr c ∧ unusedPad P c := by
  cases h : P (Sum.inr b) with
  | inl a =>
    exfalso
    apply hb a
    rw [← h]
    exact hP _
  | inr c =>
    refine ⟨c, rfl, ?_⟩
    intro a ha
    have heq := P.injective (ha.trans h.symm)
    cases heq

noncomputable def residualPad {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (hP : Function.Involutive P) (b : {b : β // unusedPad P b}) :
    {b : β // unusedPad P b} :=
  ⟨Classical.choose (unusedPad_image P hP b.val b.property),
    (Classical.choose_spec (unusedPad_image P hP b.val b.property)).2⟩

lemma residualPad_spec {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (hP : Function.Involutive P) (b : {b : β // unusedPad P b}) :
    P (Sum.inr b.val) = Sum.inr (residualPad P hP b).val :=
  (Classical.choose_spec (unusedPad_image P hP b.val b.property)).1

lemma residualPad_involutive {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (hP : Function.Involutive P) : Function.Involutive (residualPad P hP) := by
  intro b
  apply Subtype.ext
  apply Sum.inr_injective
  rw [← residualPad_spec, ← residualPad_spec]
  exact hP _

lemma unusedPad_iff_not_range_crossing {α β : Type*} (P : Equiv.Perm (α ⊕ β))
    (b : β) : unusedPad P b ↔ b ∉ Set.range (crossingPartner P) := by
  constructor
  · intro hb ⟨a, ha⟩
    exact hb a.val (by rw [crossingPartner_spec, ha])
  · intro hb a ha
    apply hb
    refine ⟨⟨a, b, ha⟩, ?_⟩
    apply Sum.inr_injective
    exact (crossingPartner_spec P ⟨a, b, ha⟩).symm.trans ha

lemma unusedPad_card {α β : Type*} [Finite α] [Finite β]
    (P : Equiv.Perm (α ⊕ β)) :
    Nat.card {b : β // unusedPad P b} = Nat.card β -
      Nat.card {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b} := by
  classical
  let := Fintype.ofFinite β
  have hc := Nat.card_congr (Equiv.subtypeEquivRight
    (unusedPad_iff_not_range_crossing P))
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_range_of_injective (crossingPartner_injective P)]

noncomputable def gluePairing {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (U : Finset α) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) : α ⊕ β → α ⊕ β := by
  classical
  exact fun x => match x with
    | Sum.inl a => if h : a ∈ U then Sum.inr (e ⟨a, h⟩) else Sum.inl (Q a)
    | Sum.inr b => if h : b ∈ Set.range e then
        Sum.inl (Classical.choose h).val else Sum.inr (R ⟨b, h⟩).val

lemma gluePairing_old_matched {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (U : Finset α) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) (a : U) :
    gluePairing Q U e R (Sum.inl a.val) = Sum.inr (e a) := by
  simp [gluePairing, a.property]

lemma gluePairing_pad_matched {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (U : Finset α) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) (a : U) :
    gluePairing Q U e R (Sum.inr (e a)) = Sum.inl a.val := by
  classical
  have h : e a ∈ Set.range e := ⟨a, rfl⟩
  simp only [gluePairing, dite_eq_left h]
  exact congrArg (fun x : U => Sum.inl x.val) (e.injective (Classical.choose_spec h))

lemma gluePairing_pad_unused {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (U : Finset α) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e})
    (b : {b : β // b ∉ Set.range e}) :
    gluePairing Q U e R (Sum.inr b.val) = Sum.inr (R b).val := by
  simp [gluePairing, b.property]

lemma gluePairing_involutive {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q)
    (U : Finset α) (hU : ∀ a ∈ U, Q a = a) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) (hR : Function.Involutive R) :
    Function.Involutive (gluePairing Q U e R) := by
  classical
  intro x
  cases x with
  | inl a =>
    by_cases ha : a ∈ U
    · rw [gluePairing_old_matched Q U e R ⟨a, ha⟩,
        gluePairing_pad_matched Q U e R ⟨a, ha⟩]
    · have hQa : Q a ∉ U := by
        intro h
        have hfix := hU (Q a) h
        have heq : Q a = a := hfix.symm.trans (hQ a)
        exact ha (heq ▸ h)
      simp [gluePairing, ha, hQa, hQ a]
  | inr b =>
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      rw [gluePairing_pad_matched, gluePairing_old_matched]
    · rw [gluePairing_pad_unused Q U e R ⟨b, hb⟩,
        gluePairing_pad_unused Q U e R (R ⟨b, hb⟩)]
      exact congrArg (fun z : {b : β // b ∉ Set.range e} => Sum.inr z.val) (hR _)

noncomputable def gluedPerm {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q)
    (U : Finset α) (hU : ∀ a ∈ U, Q a = a) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) (hR : Function.Involutive R) :
    Equiv.Perm (α ⊕ β) :=
  (gluePairing_involutive Q hQ U hU e R hR).toPerm _

lemma restrictOld_gluedPerm {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q)
    (U : Finset α) (hU : ∀ a ∈ U, Q a = a) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) (hR : Function.Involutive R) :
    restrictOld (gluedPerm Q hQ U hU e R hR) = Q := by
  classical
  funext a
  by_cases ha : a ∈ U
  · simp [restrictOld, gluedPerm, gluePairing, ha, hU a ha]
  · simp [restrictOld, gluedPerm, gluePairing, ha]

lemma glue_crossing_iff {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (U : Finset α) (e : U ↪ β)
    (R : Equiv.Perm {b : β // b ∉ Set.range e}) (a : α) :
    (∃ b : β, gluePairing Q U e R (Sum.inl a) = Sum.inr b) ↔ a ∈ U := by
  classical
  by_cases ha : a ∈ U <;> simp [gluePairing, ha]

noncomputable def crossingSet {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) : Finset α := by
  classical
  exact univ.filter (fun a => ∃ b : β, P (Sum.inl a) = Sum.inr b)

lemma mem_crossingSet {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) (a : α) :
    a ∈ crossingSet P ↔ ∃ b : β, P (Sum.inl a) = Sum.inr b := by
  classical
  simp [crossingSet]

noncomputable def crossingEmbedding {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) : crossingSet P ↪ β :=
  { toFun := fun a => crossingPartner P ⟨a.val, (mem_crossingSet P a.val).mp a.property⟩
    inj' := by
      intro a b h
      have := crossingPartner_injective P h
      exact Subtype.ext (congrArg
        (fun z : {a : α // ∃ b : β, P (Sum.inl a) = Sum.inr b} => z.val) this) }

lemma crossingEmbedding_spec {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) (a : crossingSet P) :
    P (Sum.inl a.val) = Sum.inr (crossingEmbedding P a) :=
  crossingPartner_spec P ⟨a.val, (mem_crossingSet P a.val).mp a.property⟩

lemma unused_crossingEmbedding {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) (b : β) :
    unusedPad P b ↔ b ∉ Set.range (crossingEmbedding P) := by
  constructor
  · intro hb ⟨a, ha⟩
    exact hb a.val (by rw [crossingEmbedding_spec, ha])
  · intro hb a ha
    apply hb
    have ham : a ∈ crossingSet P := (mem_crossingSet P a).mpr ⟨b, ha⟩
    refine ⟨⟨a, ham⟩, ?_⟩
    apply Sum.inr_injective
    exact (crossingEmbedding_spec P ⟨a, ham⟩).symm.trans ha

lemma permCongr_involutive {α β : Type*} (e : α ≃ β) (P : Equiv.Perm α)
    (hP : Function.Involutive P) : Function.Involutive (e.permCongr P) := by
  intro x
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hP (e.symm x), Equiv.apply_symm_apply]

noncomputable def residualPermutation {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) (hP : Function.Involutive P) :
    Equiv.Perm {b : β // b ∉ Set.range (crossingEmbedding P)} :=
  (Equiv.subtypeEquivRight (unused_crossingEmbedding P)).permCongr
    ((residualPad_involutive P hP).toPerm _)

lemma residualPermutation_involutive {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) (hP : Function.Involutive P) :
    Function.Involutive (residualPermutation P hP) :=
  permCongr_involutive _ _ (residualPad_involutive P hP)

lemma residualPermutation_spec {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) (hP : Function.Involutive P)
    (b : {b : β // b ∉ Set.range (crossingEmbedding P)}) :
    P (Sum.inr b.val) = Sum.inr (residualPermutation P hP b).val := by
  exact residualPad_spec P hP
    ⟨b.val, (unused_crossingEmbedding P b.val).mpr b.property⟩

lemma crossingSet_old_fixed {α β : Type*} [Fintype α]
    (P : Equiv.Perm (α ⊕ β)) :
    ∀ a ∈ crossingSet P, restrictOld P a = a := by
  intro a ha
  exact crossing_old_fixed P ⟨a, (mem_crossingSet P a).mp ha⟩

lemma glue_recovers_original {α β : Type*} [Fintype α] [DecidableEq α]
    (P : Equiv.Perm (α ⊕ β)) (hP : Function.Involutive P) :
    gluePairing ((restrictOld_involutive P hP).toPerm _)
      (crossingSet P) (crossingEmbedding P) (residualPermutation P hP) = P := by
  classical
  funext x
  cases x with
  | inl a =>
    by_cases ha : a ∈ crossingSet P
    · rw [gluePairing_old_matched _ _ _ _ ⟨a, ha⟩]
      exact (crossingEmbedding_spec P ⟨a, ha⟩).symm
    · have hn : ¬ ∃ b : β, P (Sum.inl a) = Sum.inr b := by
        simpa only [mem_crossingSet] using ha
      cases h : P (Sum.inl a) with
      | inl c => simp [gluePairing, ha, restrictOld, h]
      | inr c => exact (hn ⟨c, h⟩).elim
  | inr b =>
    by_cases hb : b ∈ Set.range (crossingEmbedding P)
    · obtain ⟨a, rfl⟩ := hb
      rw [gluePairing_pad_matched]
      rw [← crossingEmbedding_spec, hP]
    · rw [gluePairing_pad_unused _ _ _ _ ⟨b, hb⟩]
      exact (residualPermutation_spec P hP ⟨b, hb⟩).symm

def ExtensionData {α : Type*} (Q : Equiv.Perm α) (β : Type*) :=
  Σ U : {U : Finset α // ∀ a ∈ U, Q a = a},
    Σ e : U.val ↪ β, {R : Equiv.Perm {b : β // b ∉ Set.range e} // Function.Involutive R}

noncomputable def glueData {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q) (D : ExtensionData Q β) :
    {P : Equiv.Perm (α ⊕ β) // Function.Involutive P ∧ restrictOld P = Q} :=
  ⟨gluedPerm Q hQ D.1.val D.1.property D.2.1 D.2.2.val D.2.2.property,
    gluePairing_involutive Q hQ D.1.val D.1.property D.2.1 D.2.2.val D.2.2.property,
    restrictOld_gluedPerm Q hQ D.1.val D.1.property D.2.1 D.2.2.val D.2.2.property⟩

lemma glueData_injective {α β : Type*} [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q) :
    Function.Injective (glueData (β := β) Q hQ) := by
  classical
  rintro ⟨⟨U, hU⟩, e, R, hR⟩ ⟨⟨V, hV⟩, f, S, hS⟩ heq
  have hg : gluePairing Q U e R = gluePairing Q V f S :=
    congrArg (fun p => (p.val : α ⊕ β → α ⊕ β)) heq
  have huv : U = V := by
    ext a
    rw [← glue_crossing_iff Q U e R, ← glue_crossing_iff Q V f S, hg]
  subst V
  have hef : e = f := by
    ext a
    apply Sum.inr_injective
    rw [← gluePairing_old_matched Q U e R a, hg,
      gluePairing_old_matched Q U f S a]
  subst f
  have hrs : R = S := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    apply Sum.inr_injective
    rw [← gluePairing_pad_unused Q U e R b, hg,
      gluePairing_pad_unused Q U e S b]
  subst S
  rfl

lemma glueData_surjective {α β : Type*} [Fintype α] [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q) :
    Function.Surjective (glueData (β := β) Q hQ) := by
  classical
  rintro ⟨P, hP, hres⟩
  have hU : ∀ a ∈ crossingSet P, Q a = a := by
    intro a ha
    rw [← congrFun hres a]
    exact crossingSet_old_fixed P a ha
  let D : ExtensionData Q β := ⟨⟨crossingSet P, hU⟩, crossingEmbedding P,
    residualPermutation P hP, residualPermutation_involutive P hP⟩
  refine ⟨D, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change gluePairing Q (crossingSet P) (crossingEmbedding P)
    (residualPermutation P hP) x = P x
  have hperm : (restrictOld_involutive P hP).toPerm _ = Q := by
    apply Equiv.ext
    exact fun a => congrFun hres a
  rw [← hperm, glue_recovers_original]

lemma permCongr_involutive_iff {α β : Type*} (e : α ≃ β) (P : Equiv.Perm α) :
    Function.Involutive P ↔ Function.Involutive (e.permCongr P) := by
  constructor
  · exact permCongr_involutive e P
  · intro h a
    apply e.injective
    have hx := h (e a)
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using hx

lemma involution_card_congr {α β : Type*} (e : α ≃ β) :
    Nat.card {P : Equiv.Perm α // Function.Involutive P} =
    Nat.card {P : Equiv.Perm β // Function.Involutive P} :=
  Nat.card_congr (Equiv.subtypeEquiv e.permCongr (permCongr_involutive_iff e))

lemma involution_card_fin {α : Type*} [Finite α] :
    Nat.card {P : Equiv.Perm α // Function.Involutive P} =
    Nat.card {P : Equiv.Perm (Fin (Nat.card α)) // Function.Involutive P} := by
  let := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card (α := α)]
  exact involution_card_congr (Fintype.equivFin α)

lemma unused_embedding_card {α β : Type*} [Finite α] [Finite β] (e : α ↪ β) :
    Nat.card {b : β // b ∉ Set.range e} = Nat.card β - Nat.card α := by
  classical
  let := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_range_of_injective e.injective]

open scoped Classical in
lemma extensionData_card {α β : Type*} [Fintype α] [Fintype β]
    (Q : Equiv.Perm α) :
    Nat.card (ExtensionData Q β) =
      ∑ U : {U : Finset α // ∀ a ∈ U, Q a = a},
        (Nat.card β).descFactorial U.val.card *
        Nat.card {P : Equiv.Perm (Fin (Nat.card β-U.val.card)) // Function.Involutive P} := by
  classical
  unfold ExtensionData
  rw [Nat.card_sigma]
  apply sum_congr rfl
  intro U hU
  rw [Nat.card_sigma]
  have hc : ∀ e : U.val ↪ β,
      Nat.card {R : Equiv.Perm {b : β // b ∉ Set.range e} // Function.Involutive R} =
      Nat.card {P : Equiv.Perm (Fin (Nat.card β-U.val.card)) // Function.Involutive P} := by
    intro e
    have hsize : Nat.card {b : β // b ∉ Set.range e} = Nat.card β-U.val.card := by
      rw [unused_embedding_card, Nat.card_eq_finsetCard]
    rw [involution_card_fin, hsize]
  simp_rw [hc]
  rw [sum_const, nsmul_eq_mul]
  congr 1
  simp only [card_univ, Nat.cast_id]
  rw [Fintype.card_embedding_eq]
  simp [Nat.card_eq_fintype_card]

lemma kernel_trim (I : ℕ → ℕ) (f t : ℕ) :
    ∑ h ∈ range (f+1), f.choose h * t.descFactorial h * I (t-h) =
    ∑ h ∈ range (t+1), f.choose h * t.descFactorial h * I (t-h) := by
  rcases le_total f t with hft | htf
  · apply sum_subset (range_mono (by omega : f+1 ≤ t+1))
    intro h hh hnot
    have hfh : f < h := by simp only [mem_range] at hnot; omega
    simp [Nat.choose_eq_zero_of_lt hfh]
  · symm
    apply sum_subset (range_mono (by omega : t+1 ≤ f+1))
    intro h hh hnot
    have hth : t < h := by simp only [mem_range] at hnot; omega
    simp [Nat.descFactorial_of_lt hth]

open scoped Classical in
lemma sum_fixed_subsets {α : Type*} [Fintype α] (Q : Equiv.Perm α)
    (g : ℕ → ℕ) :
    (∑ U : {U : Finset α // ∀ a ∈ U, Q a = a}, g U.val.card) =
    ∑ h ∈ range ((univ.filter (fun a => Q a = a)).card+1),
      (univ.filter (fun a => Q a = a)).card.choose h * g h := by
  classical
  let F := univ.filter (fun a => Q a = a)
  have hm : ∀ U : Finset α, U ∈ F.powerset ↔ ∀ a ∈ U, Q a = a := by
    intro U
    simp only [mem_powerset, F, subset_iff, mem_filter, mem_univ, true_and]
  rw [← sum_subtype F.powerset hm (fun U => g U.card), sum_powerset_apply_card]
  simp [F]

lemma extension_fiber_card_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (Q : Equiv.Perm α) (hQ : Function.Involutive Q) :
    Nat.card {P : Equiv.Perm (α ⊕ β) // Function.Involutive P ∧ restrictOld P = Q} =
    ∑ h ∈ range (Nat.card β+1),
      (univ.filter (fun a => Q a = a)).card.choose h * (Nat.card β).descFactorial h *
      Nat.card {P : Equiv.Perm (Fin (Nat.card β-h)) // Function.Involutive P} := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective (glueData (β := β) Q hQ)
    ⟨glueData_injective Q hQ, glueData_surjective Q hQ⟩), extensionData_card,
    sum_fixed_subsets Q (fun h => (Nat.card β).descFactorial h *
      Nat.card {P : Equiv.Perm (Fin (Nat.card β-h)) // Function.Involutive P})]
  simp_rw [← Nat.mul_assoc]
  convert! kernel_trim (fun k => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P})
      (univ.filter (fun a => Q a = a)).card (Nat.card β) using 1
  congr! 10

lemma fin_extension_fiber_card (n t : ℕ)
    (Q : {P : Equiv.Perm (Fin n) // Function.Involutive P}) :
    Nat.card {P : {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P} //
      oldProjection n t P = Q} =
    ∑ h ∈ range (t+1),
      (univ.filter (fun a => Q.val a = a)).card.choose h * t.descFactorial h *
      Nat.card {P : Equiv.Perm (Fin (t-h)) // Function.Involutive P} := by
  classical
  let e : Fin (n+t) ≃ Fin n ⊕ Fin t := finSumFinEquiv.symm
  let E : {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P} ≃
      {P : Equiv.Perm (Fin n ⊕ Fin t) // Function.Involutive P} :=
    Equiv.subtypeEquiv e.permCongr (permCongr_involutive_iff e)
  have hp : ∀ P : {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P},
      oldProjection n t P = Q ↔ restrictOld (E P).val = Q.val := by
    intro P
    constructor
    · intro h
      exact congrArg (fun z => (z.val : Fin n → Fin n)) h
    · intro h
      apply Subtype.ext
      apply Equiv.ext
      exact fun a => congrFun h a
  have hcard := Nat.card_congr ((Equiv.subtypeEquiv E hp).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun P : Equiv.Perm (Fin n ⊕ Fin t) => Function.Involutive P)
      (fun P => restrictOld P = Q.val)))
  rw [hcard, extension_fiber_card_sum Q.val Q.property]
  simp only [Nat.card_eq_fintype_card (α := Fin t), Fintype.card_fin]
  apply sum_congr rfl
  intro h hh
  congr 1
  rw [Nat.card_fin]

open scoped Classical in
lemma weighted_histogram_partition {α : Type*} [Fintype α] (Q : α → Prop)
    (f : α → ℕ) (d e : ℕ) (w : ℕ → ℕ)
    (hf : ∀ a, Q a → ∃ j : Fin (d+1), f a = e+2*j.val) :
    (∑ a : {a // Q a}, w (f a.val)) =
      ∑ j : Fin (d+1), w (e+2*j.val) * Nat.card {a // Q a ∧ f a = e+2*j.val} := by
  classical
  let forget : (Σ j : Fin (d+1), {a // Q a ∧ f a = e+2*j.val}) → {a // Q a} :=
    fun p => ⟨p.2.val, p.2.property.1⟩
  have hi : Function.Injective forget := by
    rintro ⟨i, a, ha, hfa⟩ ⟨j, b, hb, hfb⟩ heq
    have hab : a = b := congrArg Subtype.val heq
    subst b
    have hij : i = j := Fin.ext (by omega)
    subst j
    rfl
  have hs : Function.Surjective forget := by
    intro a
    obtain ⟨j, hj⟩ := hf a.val a.property
    exact ⟨⟨j, a.val, a.property, hj⟩, rfl⟩
  rw [← (Equiv.ofBijective forget ⟨hi, hs⟩).sum_comp
    (fun a => w (f a.val)), Fintype.sum_sigma]
  apply sum_congr rfl
  intro j hj
  have hw : ∀ a : {a // Q a ∧ f a = e+2*j.val}, w (f a.val) = w (e+2*j.val) :=
    fun a => congrArg w a.property.2
  change (∑ a : {a // Q a ∧ f a = e+2*j.val}, w (f a.val)) = _
  simp only [hw, sum_const, nsmul_eq_mul, card_univ, Nat.cast_id,
    ← Nat.card_eq_fintype_card]
  exact Nat.mul_comm _ _

lemma nat_sum_fintype_irrel {α : Type*} (A B : Fintype α) (f : α → ℕ) :
    @Finset.sum α ℕ _ (@univ α A) f = @Finset.sum α ℕ _ (@univ α B) f := by
  cases Subsingleton.elim A B
  rfl

lemma exact_padding_count (n t : ℕ) (H : Finset (Finset (Fin n))) :
    let I := fun k : ℕ => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}
    let kernel := fun t f : ℕ => (range (t+1)).sum (fun h =>
      f.choose h * t.descFactorial h * I (t-h))
    Nat.card {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P ∧
      ∀ R ∈ H, ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (u.castAdd t) = v.castAdd t} =
    ∑ j : Fin (n/2+1), kernel t (n%2+2*j.val) *
      Nat.card {P : Equiv.Perm (Fin n) //
        Function.Involutive P ∧
        (∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u) ∧
        (univ.filter (fun u => P u = u)).card = n%2+2*j.val} := by
  classical
  dsimp only
  rw [exact_count_as_restriction_fibers]
  let w : ℕ → ℕ := fun f => ∑ h ∈ range (t+1), f.choose h * t.descFactorial h *
    Nat.card {P : Equiv.Perm (Fin (t-h)) // Function.Involutive P}
  have hs : (∑ Q : {Q : {P : Equiv.Perm (Fin n) // Function.Involutive P} //
      winsOld n H Q.val},
      Nat.card {P : {P : Equiv.Perm (Fin (n+t)) // Function.Involutive P} //
        oldProjection n t P = Q.val}) =
    ∑ Q : {P : Equiv.Perm (Fin n) // Function.Involutive P ∧ winsOld n H P},
      w (univ.filter (fun u => Q.val u = u)).card := by
    trans ∑ Q : {Q : {P : Equiv.Perm (Fin n) // Function.Involutive P} //
        winsOld n H Q.val}, w (univ.filter (fun u => Q.val.val u = u)).card
    · apply sum_congr rfl
      intro Q hQ
      exact fin_extension_fiber_card n t Q.val
    · exact Fintype.sum_equiv
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun P : Equiv.Perm (Fin n) => Function.Involutive P) (winsOld n H)) _ _
          (fun _ => rfl)
  rw [hs]
  have hp := weighted_histogram_partition
    (fun P : Equiv.Perm (Fin n) => Function.Involutive P ∧ winsOld n H P)
    (fun P => (univ.filter (fun u => P u = u)).card) (n/2) (n%2) w
    (fun P hP => involution_fixed_histogram_index n P hP.1)
  simp only [w, winsOld, and_assoc] at hp
  refine Eq.trans ?_ hp
  exact nat_sum_fintype_irrel _ _ _

noncomputable def invCount (k : ℕ) := Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}

noncomputable def extKernel (t f : ℕ) := ∑ h ∈ range (t+1), f.choose h * t.descFactorial h * invCount (t-h)

noncomputable def fixedCount (m f : ℕ) := Nat.card {P : Equiv.Perm (Fin m) //
  Function.Involutive P ∧ (univ.filter (fun u => P u = u)).card = f}

lemma invCount_interpolation (m t : ℕ) :
    invCount (m+t) = ∑ j : Fin (m/2+1),
      extKernel t (m%2+2*j.val) * fixedCount m (m%2+2*j.val) := by
  have h := exact_padding_count m t ∅
  simpa only [invCount, extKernel, fixedCount, Finset.forall_mem_empty_iff,
    and_true, true_and] using h

lemma fixedCount_diagonal (m : ℕ) : fixedCount m m = 1 :=
  all_fixed_involution_count m

lemma fixedCount_zero (m f : ℕ) (h : m < f) : fixedCount m f = 0 := by
  have he : IsEmpty {P : Equiv.Perm (Fin m) // Function.Involutive P ∧
      (univ.filter (fun u => P u = u)).card = f} := by
    refine ⟨fun P => ?_⟩
    have hc := card_le_card (filter_subset (fun u => P.val u = u) univ)
    simp only [card_univ, Fintype.card_fin] at hc
    have hp := P.property.2
    omega
  exact Nat.card_eq_zero.mpr (Or.inl he)

lemma invCount_interpolation_affine (e j t : ℕ) (he : e < 2) :
    invCount (t+(e+2*j)) = ∑ k : Fin (j+1),
      extKernel t (e+2*k.val) * fixedCount (e+2*j) (e+2*k.val) := by
  have h := invCount_interpolation (e+2*j) t
  have hm : (e+2*j)%2 = e := by omega
  have hd : (e+2*j)/2 = j := by omega
  rw [hm, hd, Nat.add_comm (e+2*j) t] at h
  exact h

lemma invCount_interpolation_padded (d e t : ℕ) (he : e < 2) (j : Fin (d+1)) :
    invCount (t+(e+2*j.val)) = ∑ k : Fin (d+1),
      extKernel t (e+2*k.val) * fixedCount (e+2*j.val) (e+2*k.val) := by
  rw [invCount_interpolation_affine e j.val t he]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => extKernel t (e+2*k) * fixedCount (e+2*j.val) (e+2*k)) (j.val+1),
    Fin.sum_univ_eq_sum_range
      (fun k => extKernel t (e+2*k) * fixedCount (e+2*j.val) (e+2*k)) (d+1)]
  apply sum_subset (range_mono (by omega : j.val+1 ≤ d+1))
  intro k hk hnot
  have hjk : j.val < k := by simp only [mem_range] at hnot; omega
  rw [fixedCount_zero (e+2*j.val) (e+2*k) (by omega), mul_zero]

lemma exact_involution_matrix_det (d e : ℕ) (he : e < 2) :
    (Matrix.of fun t j : Fin (d+1) => (invCount (t.val+(e+2*j.val)) : ℤ)).det =
      (2:ℤ)^(d*(d+1)/2) * ∏ j : Fin (d+1), (j.val.factorial : ℤ) := by
  classical
  let K : Matrix (Fin (d+1)) (Fin (d+1)) ℤ :=
    Matrix.of fun t j => (extKernel t.val (e+2*j.val) : ℤ)
  let B : Matrix (Fin (d+1)) (Fin (d+1)) ℤ :=
    Matrix.of fun k j => (fixedCount (e+2*j.val) (e+2*k.val) : ℤ)
  have hfactor : (Matrix.of fun t j : Fin (d+1) =>
      (invCount (t.val+(e+2*j.val)) : ℤ)) = K * B := by
    ext t j
    simp only [K, B, Matrix.of_apply, Matrix.mul_apply]
    exact_mod_cast invCount_interpolation_padded d e t.val he j
  have hB : B.IsUpperTriangular := by
    intro i j hij
    have hj : j.val < i.val := hij
    change (fixedCount (e+2*j.val) (e+2*i.val) : ℤ) = 0
    rw [fixedCount_zero _ _ (by omega), Nat.cast_zero]
  have hdetB : B.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hB]
    simp only [B, Matrix.of_apply, fixedCount_diagonal, Nat.cast_one, prod_const_one]
  have hdetK : K.det = (2:ℤ)^(d*(d+1)/2) *
      ∏ j : Fin (d+1), (j.val.factorial : ℤ) := by
    have h := (kernel_det invCount involution_zero d (fun j => e+2*j.val)).trans
      (affine_vandermonde d e)
    rw [← h]
    congr 1
    ext t j
    simp only [K, extKernel, Matrix.of_apply, Nat.cast_sum, Nat.cast_mul]
  rw [hfactor, Matrix.det_mul, hdetB, mul_one, hdetK]

end PEqualNP.Outside.L_lib_914_aux

theorem PEqualNP.Outside.L_lib_914 : (∀ (n : Nat) (H : Finset (Finset (Fin n))),
  let I := fun k : Nat => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}
  let d := n/2
  let free := fun j : Fin (d+1) => n % 2+2*j.val
  let kernel := fun (t f : Nat) => (Finset.range (t+1)).sum (fun h =>
    f.choose h * t.descFactorial h * I (t-h))
  let fits := fun (t : Nat) (P : Equiv.Perm (Fin (n+t))) =>
    Function.Involutive P ∧ ∀ R ∈ H, ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ P (u.castAdd t) = v.castAdd t
  let hist := fun j : Fin (d+1) => Nat.card {P : Equiv.Perm (Fin n) //
    Function.Involutive P ∧ (∀ R ∈ H, ∃ u ∈ R, P u ∈ R ∧ P u ≠ u) ∧
    (Finset.univ.filter (fun u => P u = u)).card = free j}
  let K : Matrix (Fin (d+1)) (Fin (d+1)) Int := fun t j => (kernel t.val (free j) : Int)
  let J : Matrix (Fin (d+1)) (Fin (d+1)) Int := fun t j => (I (t.val+free j) : Int)
  let delta := (2 : Int)^(d*(d+1)/2) * ∏ j : Fin (d+1), (j.val.factorial : Int)
  (∀ t : Nat, Nat.card {P : Equiv.Perm (Fin (n+t)) // fits t P} =
    ∑ j : Fin (d+1), kernel t (free j) * hist j) ∧ K.det = delta ∧ J.det = delta) := by
  intro n H
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact PEqualNP.Outside.L_lib_914_aux.exact_padding_count n t H
  · exact PEqualNP.Outside.L_lib_914_aux.exact_kernel_det n
  · have h := PEqualNP.Outside.L_lib_914_aux.exact_involution_matrix_det
      (n/2) (n%2) (Nat.mod_lt n (by omega))
    rw [← h]
    congr 1

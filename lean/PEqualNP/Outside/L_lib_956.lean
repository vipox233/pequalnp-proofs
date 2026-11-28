import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_956

open scoped BigOperators Matrix

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases z2_cases x with rfl | rfl <;> decide

lemma z2_vec_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  ext j
  exact z2_add_self (v j)

lemma z2_eq_zero_iff_even (k : ℕ) : ((k : ZMod 2) = 0) ↔ 2 ∣ k := by
  rw [ZMod.natCast_eq_zero_iff]

lemma two_dvd_of_fpf_invol {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α)
    (hmem : ∀ x ∈ S, f x ∈ S) (hne : ∀ x ∈ S, f x ≠ x) (hinv : ∀ x ∈ S, f (f x) = x) :
    2 ∣ S.card := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | ind m ih =>
    by_cases hneS : S.Nonempty
    · obtain ⟨x, hx⟩ := hneS
      have hfx : f x ∈ S := hmem x hx
      have hne_x : f x ≠ x := hne x hx
      let S' := (S.erase x).erase (f x)
      have hcard : S'.card + 2 = S.card := by
        have h1 : f x ∈ S.erase x := Finset.mem_erase.mpr ⟨hne_x, hfx⟩
        have h2 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
        have h3 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one h1
        omega
      have hsub : S' ⊆ S := fun y hy =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hmem' : ∀ y ∈ S', f y ∈ S' := by
        intro y hy
        have hy1 : y ≠ f x := (Finset.mem_erase.mp hy).1
        have hy2 : y ∈ S.erase x := (Finset.mem_erase.mp hy).2
        have hy3 : y ≠ x := (Finset.mem_erase.mp hy2).1
        have hyS : y ∈ S := (Finset.mem_erase.mp hy2).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hyS⟩⟩
        · intro heq
          have := congrArg f heq
          rw [hinv y hyS, hinv x hx] at this
          exact hy3 this
        · intro heq
          have := congrArg f heq
          rw [hinv y hyS] at this
          exact hy1 this
      have hdiv' : 2 ∣ S'.card := ih S'.card (by omega) S' hmem'
        (fun y hy => hne y (hsub hy)) (fun y hy => hinv y (hsub hy)) rfl
      rcases hdiv' with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩
    · rw [← hn, Finset.not_nonempty_iff_eq_empty.mp hneS]
      simp

def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

def chi {n : ℕ} (v x : Fin n → ZMod 2) : ℤ := sgn (dotProduct v x)

lemma sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> decide

lemma chi_zero {n : ℕ} (x : Fin n → ZMod 2) : chi 0 x = 1 := by
  simp [chi, sgn]

lemma chi_mul {n : ℕ} (u v x : Fin n → ZMod 2) : chi u x * chi v x = chi (u + v) x := by
  simp only [chi, add_dotProduct, sgn_add]

lemma card_vec_z2 (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  simp [Fintype.card_pi, ZMod.card]

lemma sum_chi {n : ℕ} (v : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, chi v x) = if v = 0 then (2 : ℤ) ^ n else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [chi_zero, card_vec_z2]
  · rw [if_neg hv]
    have hex : ∃ j : Fin n, v j ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hv (funext hall)
    obtain ⟨j, hj⟩ := hex
    have hj1 : v j = 1 := by
      rcases z2_cases (v j) with h | h
      · exact (hj h).elim
      · exact h
    let τ : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun x => x + Pi.single j (1 : ZMod 2)
    have hτinv : ∀ x, τ (τ x) = x := by
      intro x
      ext k
      simp only [τ, Pi.add_apply, add_assoc]
      rw [z2_add_self, add_zero]
    have hτdot : ∀ x, dotProduct v (τ x) = dotProduct v x + 1 := by
      intro x
      simp only [τ, dotProduct_add, dotProduct_single, mul_one, hj1]
    have hτchi : ∀ x, chi v (τ x) = - chi v x := by
      intro x
      simp only [chi, hτdot x]
      rcases z2_cases (dotProduct v x) with h | h <;> rw [h] <;> decide
    have hsum : (∑ x : Fin n → ZMod 2, chi v (τ x)) = ∑ x : Fin n → ZMod 2, chi v x := by
      refine Fintype.sum_equiv (Equiv.ofBijective τ ⟨?_, ?_⟩) _ _ (fun _ => rfl)
      · intro x y h
        have := congrArg τ h
        simpa [hτinv] using this
      · intro y
        exact ⟨τ y, hτinv y⟩
    have hneg : (∑ x : Fin n → ZMod 2, chi v x) = -(∑ x : Fin n → ZMod 2, chi v x) := by
      calc ∑ x : Fin n → ZMod 2, chi v x
          = ∑ x : Fin n → ZMod 2, chi v (τ x) := hsum.symm
        _ = ∑ x : Fin n → ZMod 2, (- chi v x) := by simp_rw [hτchi]
        _ = -(∑ x : Fin n → ZMod 2, chi v x) := by rw [Finset.sum_neg_distrib]
    omega

lemma four_distinct {n : ℕ} {a b : Fin n → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a + b ≠ 0 ∧ a + b ≠ a ∧ a + b ≠ b := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hab
    have h1 := congrArg (fun x => x + b) h
    simp only [add_assoc, z2_vec_add_self, add_zero, zero_add] at h1
    exact h1
  · intro h
    apply hb
    have h1 := congrArg (fun x => a + x) h
    simp only [← add_assoc, z2_vec_add_self, zero_add] at h1
    exact h1
  · intro h
    apply ha
    have h1 := congrArg (fun x => x + b) h
    simp only [add_assoc, z2_vec_add_self, add_zero] at h1
    exact h1

lemma vec_add_eq_zero_iff {n : ℕ} (x y : Fin n → ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 := congrArg (fun z => z + y) h
    rw [add_assoc, z2_vec_add_self, add_zero, zero_add] at h1
    exact h1
  · intro h
    rw [h, z2_vec_add_self]

def rowErr {n : ℕ} (a b c : Fin n → ZMod 2) (d : ZMod 2) (x : Fin n → ZMod 2) : ℤ :=
  if dotProduct c x + d ≠ dotProduct a x * dotProduct b x then 1 else 0

lemma four_mul_rowErr {n : ℕ} (a b c : Fin n → ZMod 2) (d : ZMod 2) (x : Fin n → ZMod 2) :
    4 * rowErr a b c d x = 2 - sgn d * chi c x * (1 + chi a x + chi b x - chi (a + b) x) := by
  simp only [rowErr, chi, add_dotProduct]
  rcases z2_cases (dotProduct c x) with hc | hc <;>
  rcases z2_cases d with hd | hd <;>
  rcases z2_cases (dotProduct a x) with ha | ha <;>
  rcases z2_cases (dotProduct b x) with hb | hb <;>
  rw [hc, hd, ha, hb] <;> decide

lemma sum_four_mul_rowErr {n : ℕ} (a b c : Fin n → ZMod 2) (d : ZMod 2) :
    4 * (∑ x : Fin n → ZMod 2, rowErr a b c d x) =
      2 * (2 : ℤ) ^ n - sgn d *
        ((if c = 0 then (2 : ℤ) ^ n else 0) +
         (if c = a then (2 : ℤ) ^ n else 0) +
         (if c = b then (2 : ℤ) ^ n else 0) -
         (if c = a + b then (2 : ℤ) ^ n else 0)) := by
  rw [Finset.mul_sum]
  have h1 : ∀ x : Fin n → ZMod 2, 4 * rowErr a b c d x =
      2 - sgn d * (chi c x + chi (c + a) x + chi (c + b) x - chi (c + (a + b)) x) := by
    intro x
    rw [four_mul_rowErr, ← chi_mul c a x, ← chi_mul c b x, ← chi_mul c (a + b) x]
    ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_vec_z2, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, mul_comm ((2 : ℤ) ^ n) 2]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [sum_chi, vec_add_eq_zero_iff]

def cellAff {n : ℕ} (a b : Fin n → ZMod 2) (t : Bool × Bool) : (Fin n → ZMod 2) × ZMod 2 :=
  match t with
  | (false, false) => (a + b, 1)
  | (true, false) => (a, 0)
  | (false, true) => (b, 0)
  | (true, true) => (0, 0)

def signOf {n : ℕ} (a b : Fin n → ZMod 2) (t : Bool × Bool) (v : Fin n → ZMod 2) : Bool :=
  if v = a then t.1 else if v = b then t.2 else if v = a + b then xor t.1 t.2 else false

lemma cellAff_inj {n : ℕ} {a b : Fin n → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (cellAff a b) := by
  have ⟨h1, h2, h3⟩ := four_distinct ha hb hab
  rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  have hfst : (cellAff a b (x1, y1)).1 = (cellAff a b (x2, y2)).1 := congrArg Prod.fst h
  cases x1 <;> cases y1 <;> cases x2 <;> cases y2 <;>
    simp only [cellAff] at hfst ⊢
  · exact (h3 hfst).elim
  · exact (h2 hfst).elim
  · exact (h1 hfst).elim
  · exact (h3 hfst.symm).elim
  · exact (hab hfst.symm).elim
  · exact (hb hfst).elim
  · exact (h2 hfst.symm).elim
  · exact (hab hfst).elim
  · exact (ha hfst).elim
  · exact (h1 hfst.symm).elim
  · exact (hb hfst.symm).elim
  · exact (ha hfst.symm).elim

lemma sum_four_mul_rowErr_ge {n : ℕ} {a b : Fin n → ZMod 2}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (c : Fin n → ZMod 2) (d : ZMod 2) :
    (2 : ℤ) ^ n ≤ 4 * (∑ x : Fin n → ZMod 2, rowErr a b c d x) := by
  have ⟨h1, h2, h3⟩ := four_distinct ha hb hab
  rw [sum_four_mul_rowErr]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
  by_cases hc0 : c = 0
  · subst hc0
    simp only [↓reduceIte, ha.symm, hb.symm, h1.symm]
    rcases z2_cases d with rfl | rfl <;> simp [sgn] <;> linarith
  · by_cases hca : c = a
    · subst hca
      simp only [hc0, ↓reduceIte, hab, h2.symm]
      rcases z2_cases d with rfl | rfl <;> simp [sgn] <;> linarith
    · by_cases hcb : c = b
      · subst hcb
        simp only [hc0, hca, ↓reduceIte, h3.symm]
        rcases z2_cases d with rfl | rfl <;> simp [sgn] <;> linarith
      · by_cases hcab : c = a + b
        · subst hcab
          simp only [hc0, hca, hcb, ↓reduceIte]
          rcases z2_cases d with rfl | rfl <;> simp [sgn] <;> linarith
        · simp only [hc0, hca, hcb, hcab, ↓reduceIte]
          linarith

lemma sum_four_mul_rowErr_eq_iff {n : ℕ} {a b : Fin n → ZMod 2}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (c : Fin n → ZMod 2) (d : ZMod 2) :
    4 * (∑ x : Fin n → ZMod 2, rowErr a b c d x) = (2 : ℤ) ^ n ↔
      ∃ t : Bool × Bool, cellAff a b t = (c, d) := by
  have ⟨h1, h2, h3⟩ := four_distinct ha hb hab
  rw [sum_four_mul_rowErr]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
  constructor
  · intro heq
    by_cases hc0 : c = 0
    · subst hc0
      simp only [↓reduceIte, ha.symm, hb.symm, h1.symm] at heq
      rcases z2_cases d with rfl | rfl
      · exact ⟨(true, true), rfl⟩
      · simp only [sgn, one_ne_zero, ↓reduceIte] at heq; linarith
    · by_cases hca : c = a
      · subst hca
        simp only [hc0, ↓reduceIte, hab, h2.symm] at heq
        rcases z2_cases d with rfl | rfl
        · exact ⟨(true, false), rfl⟩
        · simp only [sgn, one_ne_zero, ↓reduceIte] at heq; linarith
      · by_cases hcb : c = b
        · subst hcb
          simp only [hc0, hca, ↓reduceIte, h3.symm] at heq
          rcases z2_cases d with rfl | rfl
          · exact ⟨(false, true), rfl⟩
          · simp only [sgn, one_ne_zero, ↓reduceIte] at heq; linarith
        · by_cases hcab : c = a + b
          · subst hcab
            simp only [hc0, hca, hcb, ↓reduceIte] at heq
            rcases z2_cases d with rfl | rfl
            · simp only [sgn, ↓reduceIte] at heq; linarith
            · exact ⟨(false, false), rfl⟩
          · simp only [hc0, hca, hcb, hcab, ↓reduceIte] at heq
            linarith
  · rintro ⟨⟨x, y⟩, h⟩
    cases x <;> cases y <;> simp only [cellAff, Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl, rfl⟩
    · simp only [h1, h2, h3, ↓reduceIte, sgn, one_ne_zero]; ring
    · simp only [hb, hab.symm, h3.symm, ↓reduceIte, sgn]; ring
    · simp only [ha, hab, h2.symm, ↓reduceIte, sgn]; ring
    · simp only [ha.symm, hb.symm, h1.symm, ↓reduceIte, sgn]; ring

lemma four_mul_rowErr_cellAff {n : ℕ} {a b : Fin n → ZMod 2}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (t : Bool × Bool) (x : Fin n → ZMod 2) :
    4 * rowErr a b (cellAff a b t).1 (cellAff a b t).2 x =
      1 + ∑ v ∈ ({a, b, a + b} : Finset (Fin n → ZMod 2)),
        (if signOf a b t v then (-1 : ℤ) else 1) * chi v x := by
  have ⟨_, h2, h3⟩ := four_distinct ha hb hab
  have hsum : ∑ v ∈ ({a, b, a + b} : Finset (Fin n → ZMod 2)),
      (if signOf a b t v then (-1 : ℤ) else 1) * chi v x =
      (if t.1 then (-1 : ℤ) else 1) * chi a x +
      (if t.2 then (-1 : ℤ) else 1) * chi b x +
      (if xor t.1 t.2 then (-1 : ℤ) else 1) * chi (a + b) x := by
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp [signOf, hab.symm, h2, h3, add_assoc]
    · simp [h3.symm]
    · simp [hab, h2.symm]
  rw [hsum, four_mul_rowErr]
  rcases t with ⟨t1, t2⟩
  cases t1 <;> cases t2
  · have hA : chi (a + b) x * chi a x = chi b x := by
      rw [chi_mul, add_comm a b, add_assoc, z2_vec_add_self, add_zero]
    have hB : chi (a + b) x * chi b x = chi a x := by
      rw [chi_mul, add_assoc, z2_vec_add_self, add_zero]
    have hC : chi (a + b) x * chi (a + b) x = 1 := by
      rw [chi_mul, z2_vec_add_self, chi_zero]
    have hs : sgn (1 : ZMod 2) = -1 := by decide
    simp only [cellAff, xor, bne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hs]
    linear_combination hA + hB - hC
  · have hA : chi b x * chi a x = chi (a + b) x := by
      rw [chi_mul, add_comm b a]
    have hB : chi b x * chi b x = 1 := by
      rw [chi_mul, z2_vec_add_self, chi_zero]
    have hC : chi b x * chi (a + b) x = chi a x := by
      rw [chi_mul, add_comm a b, ← add_assoc, z2_vec_add_self, zero_add]
    have hs : sgn (0 : ZMod 2) = 1 := by decide
    have hxor : xor false true = true := rfl
    simp only [cellAff, hxor, Bool.false_eq_true, ↓reduceIte, hs]
    linear_combination -hA - hB + hC
  · have hA : chi a x * chi a x = 1 := by
      rw [chi_mul, z2_vec_add_self, chi_zero]
    have hB : chi a x * chi b x = chi (a + b) x := chi_mul a b x
    have hC : chi a x * chi (a + b) x = chi b x := by
      rw [chi_mul, ← add_assoc, z2_vec_add_self, zero_add]
    have hs : sgn (0 : ZMod 2) = 1 := by decide
    have hxor : xor true false = true := rfl
    simp only [cellAff, hxor, Bool.false_eq_true, ↓reduceIte, hs]
    linear_combination -hA - hB + hC
  · have hs : sgn (0 : ZMod 2) = 1 := by decide
    simp only [cellAff, xor, bne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hs, chi_zero]
    ring

noncomputable def compOf {I : Type*} [Fintype I] (adj : I → I → Prop) (i : I) : Finset I :=
  (Finset.univ : Finset I).filter (fun j => @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true)

noncomputable def compsOf {I : Type*} [Fintype I] [DecidableEq I] (adj : I → I → Prop) : Finset (Finset I) :=
  (Finset.univ : Finset I).image (compOf adj)

lemma mem_compOf {I : Type*} [Fintype I] (adj : I → I → Prop) (i j : I) :
    j ∈ compOf adj i ↔ Relation.EqvGen adj i j := by
  simp [compOf]

lemma self_mem_compOf {I : Type*} [Fintype I] (adj : I → I → Prop) (i : I) :
    i ∈ compOf adj i :=
  (mem_compOf adj i i).mpr (Relation.EqvGen.refl i)

lemma compOf_eq_of_eqv {I : Type*} [Fintype I] (adj : I → I → Prop) {i j : I}
    (h : Relation.EqvGen adj i j) : compOf adj i = compOf adj j := by
  ext k
  simp only [mem_compOf]
  exact ⟨fun hik => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hik,
         fun hjk => Relation.EqvGen.trans _ _ _ h hjk⟩

lemma compOf_eq_iff {I : Type*} [Fintype I] (adj : I → I → Prop) (i j : I) :
    compOf adj i = compOf adj j ↔ Relation.EqvGen adj i j := by
  constructor
  · intro h
    have : j ∈ compOf adj i := by rw [h]; exact self_mem_compOf adj j
    exact (mem_compOf adj i j).mp this
  · exact compOf_eq_of_eqv adj

lemma compOf_disjoint {I : Type*} [Fintype I] [DecidableEq I] (adj : I → I → Prop) {C₁ C₂ : Finset I}
    (h1 : C₁ ∈ compsOf adj) (h2 : C₂ ∈ compsOf adj) (hne : C₁ ≠ C₂) : Disjoint C₁ C₂ := by
  rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
  rw [Finset.disjoint_left]
  intro k hki hkj
  apply hne
  exact compOf_eq_of_eqv adj (Relation.EqvGen.trans _ _ _ ((mem_compOf adj i k).mp hki)
    (Relation.EqvGen.symm _ _ ((mem_compOf adj j k).mp hkj)))

lemma mem_compsOf_nonempty {I : Type*} [Fintype I] [DecidableEq I] (adj : I → I → Prop)
    {C : Finset I} (hC : C ∈ compsOf adj) : C.Nonempty := by
  rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
  exact ⟨i, self_mem_compOf adj i⟩

lemma card_invol_bip {α : Type*} [Fintype α] [DecidableEq α]
    (S P N : Finset α) (hdisj : Disjoint P N) (hunion : P ∪ N = S) (heq : P.card = N.card) :
    ((Finset.univ : Finset (α → α)).filter (fun f =>
      ∀ i, if i ∈ S then f i ≠ i ∧ f i ∈ S ∧ f (f i) = i ∧ ((i ∈ P) ↔ (f i ∈ N))
           else f i = i)).card = Nat.factorial P.card := by
  classical
  let A := (Finset.univ : Finset (α → α)).filter (fun f =>
    ∀ i, if i ∈ S then f i ≠ i ∧ f i ∈ S ∧ f (f i) = i ∧ ((i ∈ P) ↔ (f i ∈ N))
         else f i = i)
  have hPsub : P ⊆ S := by rw [← hunion]; exact Finset.subset_union_left
  have hNsub : N ⊆ S := by rw [← hunion]; exact Finset.subset_union_right
  have hbi : A.card = Fintype.card (↥P ≃ ↥N) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun ⟨f, hf⟩ =>
          have hfa := (Finset.mem_filter.mp hf).2
          { toFun := fun ⟨i, hi⟩ =>
              have h := hfa i
              ⟨f i, by rw [if_pos (hPsub hi)] at h; exact h.2.2.2.mp hi⟩
            invFun := fun ⟨j, hj⟩ =>
              have h := hfa j
              ⟨f j, by
                rw [if_pos (hNsub hj)] at h
                have hfj : f j ∈ S := h.2.1
                have h2 := hfa (f j)
                rw [if_pos hfj, h.2.2.1] at h2
                exact h2.2.2.2.mpr hj⟩
            left_inv := fun ⟨i, hi⟩ => by
              ext
              have h := hfa i
              rw [if_pos (hPsub hi)] at h
              exact h.2.2.1
            right_inv := fun ⟨j, hj⟩ => by
              ext
              have h := hfa j
              rw [if_pos (hNsub hj)] at h
              exact h.2.2.1 }
        invFun := fun e =>
          ⟨fun i => if hi : i ∈ P then (e ⟨i, hi⟩).val
                    else if hj : i ∈ N then (e.symm ⟨i, hj⟩).val
                    else i, by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun i => ?_⟩
            by_cases hiS : i ∈ S
            · rw [if_pos hiS]
              rw [← hunion, Finset.mem_union] at hiS
              rcases hiS with hiP | hiN
              · have hiNotN : i ∉ N := Finset.disjoint_left.mp hdisj hiP
                have heN : (e ⟨i, hiP⟩).val ∈ N := (e ⟨i, hiP⟩).property
                have heNotP : (e ⟨i, hiP⟩).val ∉ P := Finset.disjoint_right.mp hdisj heN
                simp only [dif_pos hiP, dif_neg heNotP, dif_pos heN]
                refine ⟨fun h => hiNotN (h ▸ heN), hNsub heN, ?_, by simp [hiP, heN]⟩
                exact congrArg Subtype.val (e.symm_apply_apply ⟨i, hiP⟩)
              · have hiNotP : i ∉ P := Finset.disjoint_right.mp hdisj hiN
                have heP : (e.symm ⟨i, hiN⟩).val ∈ P := (e.symm ⟨i, hiN⟩).property
                have heNotN : (e.symm ⟨i, hiN⟩).val ∉ N := Finset.disjoint_left.mp hdisj heP
                simp only [dif_neg hiNotP, dif_pos hiN, dif_pos heP]
                refine ⟨fun h => hiNotP (h ▸ heP), hPsub heP, ?_, by simp [hiNotP, heNotN]⟩
                exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hiN⟩)
            · rw [if_neg hiS]
              have hiNotP : i ∉ P := fun h => hiS (hPsub h)
              have hiNotN : i ∉ N := fun h => hiS (hNsub h)
              simp [dif_neg hiNotP, dif_neg hiNotN]⟩
        left_inv := fun ⟨f, hf⟩ => by
          ext i
          have hfa := (Finset.mem_filter.mp hf).2 i
          by_cases hiP : i ∈ P
          · simp [dif_pos hiP]
          · by_cases hiN : i ∈ N
            · simp [dif_neg hiP, dif_pos hiN]
            · have hiNotS : i ∉ S := by
                rw [← hunion, Finset.mem_union]; push_neg; exact ⟨hiP, hiN⟩
              rw [if_neg hiNotS] at hfa
              simp [dif_neg hiP, dif_neg hiN, hfa]
        right_inv := fun e => by
          ext ⟨i, hi⟩
          simp [dif_pos hi] }
  rw [hbi]
  have heq_t : Fintype.card ↥P = Fintype.card ↥N := by simp [heq]
  have eqv := Fintype.equivOfCardEq heq_t
  have hperm : Fintype.card (↥P ≃ ↥N) = Fintype.card (Equiv.Perm ↥P) :=
    Fintype.card_congr
      { toFun := fun g => g.trans eqv.symm
        invFun := fun p => p.trans eqv
        left_inv := fun g => by ext x; simp
        right_inv := fun p => by ext x; simp }
  rw [hperm, Fintype.card_perm, Fintype.card_coe]

lemma exists_fpf_invol_of_even {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (heven : 2 ∣ S.card) :
    ∃ f : α → α, ∀ i, if i ∈ S then f i ≠ i ∧ f i ∈ S ∧ f (f i) = i else f i = i := by
  rcases heven with ⟨k, hk⟩
  have hcard : Fintype.card ↥S = Fintype.card (Fin k × Bool) := by
    simp [Fintype.card_coe, hk, mul_comm]
  let e : ↥S ≃ Fin k × Bool := Fintype.equivOfCardEq hcard
  let f : α → α := fun i => if hi : i ∈ S then (e.symm ((e ⟨i, hi⟩).1, !(e ⟨i, hi⟩).2)).val else i
  refine ⟨f, fun i => ?_⟩
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hfi : f i = (e.symm ((e ⟨i, hi⟩).1, !(e ⟨i, hi⟩).2)).val := dif_pos hi
    have hmem : f i ∈ S := hfi ▸ (e.symm ((e ⟨i, hi⟩).1, !(e ⟨i, hi⟩).2)).property
    refine ⟨?_, hmem, ?_⟩
    · intro h
      have h1 : e.symm ((e ⟨i, hi⟩).1, !(e ⟨i, hi⟩).2) = ⟨i, hi⟩ := Subtype.ext (hfi.symm.trans h)
      have h2 := congrArg e h1
      simp only [Equiv.apply_symm_apply] at h2
      have h3 := congrArg Prod.snd h2
      dsimp only at h3
      cases hp : (e ⟨i, hi⟩).2 <;> simp [hp] at h3
    · have hff : f (f i) = (e.symm ((e ⟨f i, hmem⟩).1, !(e ⟨f i, hmem⟩).2)).val := dif_pos hmem
      rw [hff]
      have h1 : (⟨f i, hmem⟩ : ↥S) = e.symm ((e ⟨i, hi⟩).1, !(e ⟨i, hi⟩).2) := Subtype.ext hfi
      rw [h1, Equiv.apply_symm_apply]
      simp only [Bool.not_not, Prod.mk.eta]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨i, hi⟩)
  · rw [if_neg hi]
    exact dif_neg hi

section MainProof

variable (n e : ℕ) (a b : Fin (4 * e) → Fin n → ZMod 2)

def freqF (i : Fin (4 * e)) : Finset (Fin n → ZMod 2) := {a i, b i, a i + b i}

def freqsF : Finset (Fin n → ZMod 2) := (Finset.univ : Finset (Fin (4 * e))).biUnion (freqF n e a b)

def rowsF (v : Fin n → ZMod 2) : Finset (Fin (4 * e)) :=
  (Finset.univ : Finset (Fin (4 * e))).filter (fun i => v ∈ freqF n e a b i)

def goodF : Finset ((Fin (4 * e) → Fin n → ZMod 2) × (Fin (4 * e) → ZMod 2)) :=
  (Finset.univ : Finset _).filter (fun p =>
    ∀ x : Fin n → ZMod 2, ((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
      dotProduct (p.1 i) x + p.2 i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ e)

def goodSignF : Finset (Fin (4 * e) → Bool × Bool) :=
  (Finset.univ : Finset _).filter (fun t =>
    ∀ v ∈ freqsF n e a b,
      ((rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = true)).card =
      ((rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = false)).card)

def pairsF : Finset (↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e)) :=
  (Finset.univ : Finset _).filter (fun π =>
    ∀ v i, if v.val ∈ freqF n e a b i then
      π v i ≠ i ∧ v.val ∈ freqF n e a b (π v i) ∧ π v (π v i) = i
    else π v i = i)

abbrev compatF (t : Fin (4 * e) → Bool × Bool) (π : ↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e)) : Prop :=
  ∀ (v : ↥(freqsF n e a b)) (i : Fin (4 * e)), v.val ∈ freqF n e a b i →
    signOf (a i) (b i) (t i) v.val ≠ signOf (a (π v i)) (b (π v i)) (t (π v i)) v.val

noncomputable def weightF (π : ↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e)) : ℕ :=
  let cs := compsOf (fun i j => ∃ v : ↥(freqsF n e a b), v.val ∈ freqF n e a b i ∧ π v i = j)
  if ∀ C ∈ cs, 4 ∣ C.card then 2 ^ cs.card else 0

lemma freqF_card (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (i : Fin (4 * e)) :
    (freqF n e a b i).card = 3 := by
  have ⟨ha, hb, hne⟩ := hab i
  have ⟨_, h2, h3⟩ := four_distinct ha hb hne
  simp [freqF, hne, h2.symm, h3.symm]

lemma freqF_nz (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (i : Fin (4 * e))
    (v : Fin n → ZMod 2) (hv : v ∈ freqF n e a b i) : v ≠ 0 := by
  have ⟨ha, hb, hne⟩ := hab i
  have ⟨h1, _, _⟩ := four_distinct ha hb hne
  simp only [freqF, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

lemma freqsF_nz (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (v : Fin n → ZMod 2) (hv : v ∈ freqsF n e a b) : v ≠ 0 := by
  rcases Finset.mem_biUnion.mp hv with ⟨i, _, hvi⟩
  exact freqF_nz n e a b hab i v hvi

lemma swap_freq_sum {α : Type*} [AddCommMonoid α] (g : Fin (4 * e) → (Fin n → ZMod 2) → α) :
    (∑ i : Fin (4 * e), ∑ v ∈ freqF n e a b i, g i v) =
    ∑ v ∈ freqsF n e a b, ∑ i ∈ rowsF n e a b v, g i v := by
  classical
  calc ∑ i : Fin (4 * e), ∑ v ∈ freqF n e a b i, g i v
      = ∑ i : Fin (4 * e), ∑ v ∈ freqsF n e a b, if v ∈ freqF n e a b i then g i v else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v
        rw [Finset.mem_filter]
        exact ⟨fun h => ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩, h⟩, fun h => h.2⟩
    _ = ∑ v ∈ freqsF n e a b, ∑ i : Fin (4 * e), if v ∈ freqF n e a b i then g i v else 0 :=
        Finset.sum_comm
    _ = ∑ v ∈ freqsF n e a b, ∑ i ∈ rowsF n e a b v, g i v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.sum_filter]
        rfl

lemma good_card_eq_sign (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) :
    (goodF n e a b).card = (goodSignF n e a b).card := by
  classical
  refine (Finset.card_bij
    (fun (t : Fin (4 * e) → Bool × Bool) _ =>
      ((fun i => (cellAff (a i) (b i) (t i)).1), (fun i => (cellAff (a i) (b i) (t i)).2)))
    ?_ ?_ ?_).symm
  · intro t ht
    have hbal := (Finset.mem_filter.mp ht).2
    rw [goodF, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun x => ?_⟩
    have hsum4 : 4 * (∑ i : Fin (4 * e), rowErr (a i) (b i) (cellAff (a i) (b i) (t i)).1
        (cellAff (a i) (b i) (t i)).2 x) = 4 * (e : ℤ) := by
      rw [Finset.mul_sum]
      have hpt : ∀ i : Fin (4 * e), 4 * rowErr (a i) (b i) (cellAff (a i) (b i) (t i)).1
          (cellAff (a i) (b i) (t i)).2 x =
          1 + ∑ v ∈ freqF n e a b i, (if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x := by
        intro i
        have ⟨ha, hb, hne⟩ := hab i
        exact four_mul_rowErr_cellAff ha hb hne (t i) x
      simp_rw [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [swap_freq_sum n e a b (fun i v => (if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x)]
      have hzero : ∀ v ∈ freqsF n e a b,
          (∑ i ∈ rowsF n e a b v, (if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x) = 0 := by
        intro v hv
        rw [← Finset.sum_mul]
        have hb' := hbal v hv
        have hsplit := (Finset.sum_filter_add_sum_filter_not (rowsF n e a b v)
          (fun i => signOf (a i) (b i) (t i) v = true)
          (fun i => if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1)).symm
        have h1 : (∑ i ∈ (rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = true),
            if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) =
            - (((rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = true)).card : ℤ) := by
          trans (∑ _i ∈ (rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = true), (-1 : ℤ))
          · refine Finset.sum_congr rfl fun i hi => ?_
            simp [(Finset.mem_filter.mp hi).2]
          · simp
        have h2 : (∑ i ∈ (rowsF n e a b v).filter (fun i => ¬ signOf (a i) (b i) (t i) v = true),
            if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) =
            (((rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = false)).card : ℤ) := by
          have hfeq : (rowsF n e a b v).filter (fun i => ¬ signOf (a i) (b i) (t i) v = true) =
              (rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = false) := by
            ext i; simp [Bool.not_eq_true]
          rw [hfeq]
          trans (∑ _i ∈ (rowsF n e a b v).filter (fun i => signOf (a i) (b i) (t i) v = false), (1 : ℤ))
          · refine Finset.sum_congr rfl fun i hi => ?_
            simp [(Finset.mem_filter.mp hi).2]
          · simp
        rw [hsplit, h1, h2, hb']
        ring
      rw [Finset.sum_eq_zero hzero, add_zero]
      simp [nsmul_eq_mul]
    have hcard_eq : (∑ i : Fin (4 * e), rowErr (a i) (b i) (cellAff (a i) (b i) (t i)).1
        (cellAff (a i) (b i) (t i)).2 x) =
        (((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
          dotProduct (cellAff (a i) (b i) (t i)).1 x + (cellAff (a i) (b i) (t i)).2 ≠
            dotProduct (a i) x * dotProduct (b i) x)).card : ℤ) := by
      simp only [rowErr, Finset.sum_boole]
    rw [hcard_eq] at hsum4
    have hle : ((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
        dotProduct (cellAff (a i) (b i) (t i)).1 x + (cellAff (a i) (b i) (t i)).2 ≠
          dotProduct (a i) x * dotProduct (b i) x)).card ≤ e := by omega
    convert hle
  · intro t1 _ t2 _ heq
    ext i
    · have h1 := congrArg (fun p : (Fin (4 * e) → Fin n → ZMod 2) × (Fin (4 * e) → ZMod 2) => (p.1 i, p.2 i)) heq
      have ⟨ha, hb, hne⟩ := hab i
      exact congrArg Prod.fst (cellAff_inj ha hb hne h1)
    · have h1 := congrArg (fun p : (Fin (4 * e) → Fin n → ZMod 2) × (Fin (4 * e) → ZMod 2) => (p.1 i, p.2 i)) heq
      have ⟨ha, hb, hne⟩ := hab i
      exact congrArg Prod.snd (cellAff_inj ha hb hne h1)
  · intro p hp
    have hpg := (Finset.mem_filter.mp hp).2
    have hrow_ge : ∀ i : Fin (4 * e), (2 : ℤ) ^ n ≤ 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x) := by
      intro i
      have ⟨ha, hb, hne⟩ := hab i
      exact sum_four_mul_rowErr_ge ha hb hne (p.1 i) (p.2 i)
    have hrow_le_x : ∀ x : Fin n → ZMod 2, (∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) ≤ (e : ℤ) := by
      intro x
      have hcard_eq : (∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) =
          (((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
            dotProduct (p.1 i) x + p.2 i ≠ dotProduct (a i) x * dotProduct (b i) x)).card : ℤ) := by
        simp only [rowErr, Finset.sum_boole]
      rw [hcard_eq]
      exact_mod_cast hpg x
    have htot_le : 4 * (∑ x : Fin n → ZMod 2, ∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) ≤
        (4 * (e : ℤ)) * (2 : ℤ) ^ n := by
      have h1 : (∑ x : Fin n → ZMod 2, ∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) ≤
          ∑ _x : Fin n → ZMod 2, (e : ℤ) := Finset.sum_le_sum (fun x _ => hrow_le_x x)
      rw [Finset.sum_const, Finset.card_univ, card_vec_z2, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h1
      linarith
    have htot_ge : (4 * (e : ℤ)) * (2 : ℤ) ^ n ≤
        ∑ i : Fin (4 * e), 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x) := by
      have h1 : (∑ _i : Fin (4 * e), (2 : ℤ) ^ n) ≤
          ∑ i : Fin (4 * e), 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x) :=
        Finset.sum_le_sum (fun i _ => hrow_ge i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h1
      exact h1
    have hswap_tot : (∑ i : Fin (4 * e), 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x)) =
        4 * (∑ x : Fin n → ZMod 2, ∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have htot_eq : ∑ i : Fin (4 * e), 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x) =
        (4 * (e : ℤ)) * (2 : ℤ) ^ n := by
      linarith
    have hrow_eq : ∀ i : Fin (4 * e), 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x) = (2 : ℤ) ^ n := by
      intro i
      by_contra hne
      have hlt : (2 : ℤ) ^ n < 4 * (∑ x : Fin n → ZMod 2, rowErr (a i) (b i) (p.1 i) (p.2 i) x) :=
        lt_of_le_of_ne (hrow_ge i) (Ne.symm hne)
      have hstrict : (∑ _j : Fin (4 * e), (2 : ℤ) ^ n) <
          ∑ j : Fin (4 * e), 4 * (∑ x : Fin n → ZMod 2, rowErr (a j) (b j) (p.1 j) (p.2 j) x) :=
        Finset.sum_lt_sum (fun j _ => hrow_ge j) ⟨i, Finset.mem_univ i, hlt⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at hstrict
      linarith
    have hx_eq : ∀ x : Fin n → ZMod 2, (∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) = (e : ℤ) := by
      intro x
      by_contra hne
      have hlt : (∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) < (e : ℤ) :=
        lt_of_le_of_ne (hrow_le_x x) hne
      have hstrict : (∑ y : Fin n → ZMod 2, ∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) y) <
          ∑ _y : Fin n → ZMod 2, (e : ℤ) :=
        Finset.sum_lt_sum (fun y _ => hrow_le_x y) ⟨x, Finset.mem_univ x, hlt⟩
      rw [Finset.sum_const, Finset.card_univ, card_vec_z2, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hstrict
      linarith
    have hex_t : ∀ i : Fin (4 * e), ∃ t : Bool × Bool, cellAff (a i) (b i) t = (p.1 i, p.2 i) := by
      intro i
      have ⟨ha, hb, hne⟩ := hab i
      exact (sum_four_mul_rowErr_eq_iff ha hb hne (p.1 i) (p.2 i)).mp (hrow_eq i)
    choose t ht using hex_t
    refine ⟨t, ?_, ?_⟩
    · rw [goodSignF, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun u hu => ?_⟩
      have hzero_x : ∀ x : Fin n → ZMod 2,
          (∑ v ∈ freqsF n e a b, (∑ i ∈ rowsF n e a b v,
            if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x) = 0 := by
        intro x
        have h1 : 4 * (∑ i : Fin (4 * e), rowErr (a i) (b i) (p.1 i) (p.2 i) x) = 4 * (e : ℤ) := by
          rw [hx_eq x]
        rw [Finset.mul_sum] at h1
        have hpt : ∀ i : Fin (4 * e), 4 * rowErr (a i) (b i) (p.1 i) (p.2 i) x =
            1 + ∑ v ∈ freqF n e a b i, (if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x := by
          intro i
          have ⟨ha, hb, hne⟩ := hab i
          have hp1 : p.1 i = (cellAff (a i) (b i) (t i)).1 := (congrArg Prod.fst (ht i)).symm
          have hp2 : p.2 i = (cellAff (a i) (b i) (t i)).2 := (congrArg Prod.snd (ht i)).symm
          rw [hp1, hp2]
          exact four_mul_rowErr_cellAff ha hb hne (t i) x
        simp_rw [hpt] at h1
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
        rw [swap_freq_sum n e a b (fun i v => (if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x)] at h1
        simp_rw [← Finset.sum_mul] at h1
        simp only [nsmul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_ofNat] at h1
        linarith
      have horth : (∑ x : Fin n → ZMod 2, chi u x * (∑ v ∈ freqsF n e a b, (∑ i ∈ rowsF n e a b v,
          if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x)) = 0 := by
        simp_rw [hzero_x, mul_zero, Finset.sum_const_zero]
      have hcalc : (∑ x : Fin n → ZMod 2, chi u x * (∑ v ∈ freqsF n e a b, (∑ i ∈ rowsF n e a b v,
          if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x)) =
          (2 : ℤ) ^ n * (∑ i ∈ rowsF n e a b u, if signOf (a i) (b i) (t i) u then (-1 : ℤ) else 1) := by
        have h1 : ∀ x : Fin n → ZMod 2, chi u x * (∑ v ∈ freqsF n e a b, (∑ i ∈ rowsF n e a b v,
            if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi v x) =
            ∑ v ∈ freqsF n e a b, (∑ i ∈ rowsF n e a b v,
              if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi (u + v) x := by
          intro x
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← chi_mul u v x]
          ring
        simp_rw [h1]
        rw [Finset.sum_comm]
        have h2 : ∀ v ∈ freqsF n e a b, (∑ x : Fin n → ZMod 2, (∑ i ∈ rowsF n e a b v,
            if signOf (a i) (b i) (t i) v then (-1 : ℤ) else 1) * chi (u + v) x) =
            if v = u then (2 : ℤ) ^ n * (∑ i ∈ rowsF n e a b u,
              if signOf (a i) (b i) (t i) u then (-1 : ℤ) else 1) else 0 := by
          intro v _
          rw [← Finset.mul_sum, sum_chi]
          simp only [vec_add_eq_zero_iff]
          by_cases hvu : v = u
          · subst hvu
            simp [mul_comm]
          · simp [hvu, Ne.symm hvu]
        rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' (freqsF n e a b) u, if_pos hu]
      rw [hcalc] at horth
      have hpos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
      have hsum0 : (∑ i ∈ rowsF n e a b u, if signOf (a i) (b i) (t i) u then (-1 : ℤ) else 1) = 0 := by
        rcases mul_eq_zero.mp horth with h | h
        · linarith
        · exact h
      have hsplit := (Finset.sum_filter_add_sum_filter_not (rowsF n e a b u)
        (fun i => signOf (a i) (b i) (t i) u = true)
        (fun i => if signOf (a i) (b i) (t i) u then (-1 : ℤ) else 1)).symm
      rw [hsplit] at hsum0
      have h1 : (∑ i ∈ (rowsF n e a b u).filter (fun i => signOf (a i) (b i) (t i) u = true),
          if signOf (a i) (b i) (t i) u then (-1 : ℤ) else 1) =
          - (((rowsF n e a b u).filter (fun i => signOf (a i) (b i) (t i) u = true)).card : ℤ) := by
        trans (∑ _i ∈ (rowsF n e a b u).filter (fun i => signOf (a i) (b i) (t i) u = true), (-1 : ℤ))
        · refine Finset.sum_congr rfl fun i hi => ?_
          simp [(Finset.mem_filter.mp hi).2]
        · simp
      have h2 : (∑ i ∈ (rowsF n e a b u).filter (fun i => ¬ signOf (a i) (b i) (t i) u = true),
          if signOf (a i) (b i) (t i) u then (-1 : ℤ) else 1) =
          (((rowsF n e a b u).filter (fun i => signOf (a i) (b i) (t i) u = false)).card : ℤ) := by
        have hfeq : (rowsF n e a b u).filter (fun i => ¬ signOf (a i) (b i) (t i) u = true) =
            (rowsF n e a b u).filter (fun i => signOf (a i) (b i) (t i) u = false) := by
          ext i; simp [Bool.not_eq_true]
        rw [hfeq]
        trans (∑ _i ∈ (rowsF n e a b u).filter (fun i => signOf (a i) (b i) (t i) u = false), (1 : ℤ))
        · refine Finset.sum_congr rfl fun i hi => ?_
          simp [(Finset.mem_filter.mp hi).2]
        · simp
      rw [h1, h2] at hsum0
      omega
    · refine Prod.ext ?_ ?_
      · funext i; exact congrArg Prod.fst (ht i)
      · funext i; exact congrArg Prod.snd (ht i)

lemma card_compat_for_sign (t : Fin (4 * e) → Bool × Bool) (ht : t ∈ goodSignF n e a b) :
    ((pairsF n e a b).filter (fun π => compatF n e a b t π)).card =
      ∏ v ∈ freqsF n e a b, Nat.factorial ((rowsF n e a b v).card / 2) := by
  classical
  have hbal := (Finset.mem_filter.mp ht).2
  let fib : ↥(freqsF n e a b) → Finset (Fin (4 * e) → Fin (4 * e)) := fun v =>
    (Finset.univ : Finset (Fin (4 * e) → Fin (4 * e))).filter (fun f =>
      ∀ i, if i ∈ rowsF n e a b v.val then
        f i ≠ i ∧ f i ∈ rowsF n e a b v.val ∧ f (f i) = i ∧
        ((i ∈ (rowsF n e a b v.val).filter (fun j => signOf (a j) (b j) (t j) v.val = true)) ↔
         (f i ∈ (rowsF n e a b v.val).filter (fun j => signOf (a j) (b j) (t j) v.val = false)))
      else f i = i)
  have hset : (pairsF n e a b).filter (fun π => compatF n e a b t π) = Fintype.piFinset fib := by
    ext π
    simp only [Finset.mem_filter, Fintype.mem_piFinset, pairsF, compatF, Finset.mem_univ, true_and, fib]
    constructor
    · rintro ⟨hp, hc⟩ v i
      have hpi := hp v i
      by_cases hv : v.val ∈ freqF n e a b i
      · have hi_rows : i ∈ rowsF n e a b v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        rw [if_pos hi_rows]
        rw [if_pos hv] at hpi
        have hcmp := hc v i hv
        have hmem_pi : π v i ∈ rowsF n e a b v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi.2.1⟩
        refine ⟨hpi.1, hmem_pi, hpi.2.2, ?_⟩
        simp only [Finset.mem_filter, hi_rows, hmem_pi, true_and]
        cases hs1 : signOf (a i) (b i) (t i) v.val <;>
        cases hs2 : signOf (a (π v i)) (b (π v i)) (t (π v i)) v.val <;>
        simp [hs1, hs2] at hcmp ⊢
      · have hi_rows : i ∉ rowsF n e a b v.val := by simp [rowsF, hv]
        rw [if_neg hi_rows]
        rw [if_neg hv] at hpi
        exact hpi
    · intro h
      refine ⟨fun v i => ?_, fun v i hv => ?_⟩
      · have hvi := h v i
        by_cases hmem : v.val ∈ freqF n e a b i
        · have hi_rows : i ∈ rowsF n e a b v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
          rw [if_pos hi_rows] at hvi
          rw [if_pos hmem]
          exact ⟨hvi.1, (Finset.mem_filter.mp hvi.2.1).2, hvi.2.2.1⟩
        · have hi_rows : i ∉ rowsF n e a b v.val := by simp [rowsF, hmem]
          rw [if_neg hi_rows] at hvi
          rw [if_neg hmem]
          exact hvi
      · have hi_rows : i ∈ rowsF n e a b v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        have hvi := h v i
        rw [if_pos hi_rows] at hvi
        have hiff := hvi.2.2.2
        simp only [Finset.mem_filter, hi_rows, hvi.2.1, true_and] at hiff
        cases hs1 : signOf (a i) (b i) (t i) v.val <;>
        cases hs2 : signOf (a (π v i)) (b (π v i)) (t (π v i)) v.val <;>
        simp [hs1, hs2] at hiff ⊢
  rw [hset, Fintype.card_piFinset]
  have hfib_card : ∀ v : ↥(freqsF n e a b), (fib v).card = Nat.factorial ((rowsF n e a b v.val).card / 2) := by
    intro v
    let P := (rowsF n e a b v.val).filter (fun j => signOf (a j) (b j) (t j) v.val = true)
    let N := (rowsF n e a b v.val).filter (fun j => signOf (a j) (b j) (t j) v.val = false)
    have hdisj : Disjoint P N := by
      rw [Finset.disjoint_left]
      intro j hP hN
      have h1 := (Finset.mem_filter.mp hP).2
      have h2 := (Finset.mem_filter.mp hN).2
      rw [h1] at h2
      exact Bool.noConfusion h2
    have hunion : P ∪ N = rowsF n e a b v.val := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, P, N]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        cases hs : signOf (a j) (b j) (t j) v.val
        · right; exact ⟨h, rfl⟩
        · left; exact ⟨h, rfl⟩
    have heqPN : P.card = N.card := hbal v.val v.property
    have hhalf : P.card = (rowsF n e a b v.val).card / 2 := by
      have hc : (P ∪ N).card = P.card + N.card := Finset.card_union_of_disjoint hdisj
      rw [hunion, heqPN] at hc
      omega
    rw [← hhalf]
    convert card_invol_bip (rowsF n e a b v.val) P N hdisj hunion heqPN
  simp_rw [hfib_card]
  exact Finset.prod_coe_sort (freqsF n e a b) (fun v => Nat.factorial ((rowsF n e a b v).card / 2))

set_option maxHeartbeats 400000 in
lemma card_compat_for_pair (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (π : ↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e))
    (hπ : π ∈ pairsF n e a b) :
    ((goodSignF n e a b).filter (fun t => compatF n e a b t π)).card =
      2 ^ (2 * e) * weightF n e a b π := by
  classical
  have hπ_prop := (Finset.mem_filter.mp hπ).2
  have hcompat_good : ∀ t : Fin (4 * e) → Bool × Bool, compatF n e a b t π → t ∈ goodSignF n e a b := by
    intro t hct
    rw [goodSignF, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun v hv => ?_⟩
    let vf : ↥(freqsF n e a b) := ⟨v, hv⟩
    refine Finset.card_bij (fun i _ => π vf i) ?_ ?_ ?_
    · intro i hi
      have ⟨hi_r, hi_s⟩ := Finset.mem_filter.mp hi
      have hvi : v ∈ freqF n e a b i := (Finset.mem_filter.mp hi_r).2
      have hp := hπ_prop vf i
      rw [if_pos hvi] at hp
      have hc := hct vf i hvi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2.1⟩, ?_⟩
      rw [hi_s] at hc
      cases hs : signOf (a (π vf i)) (b (π vf i)) (t (π vf i)) v
      · rfl
      · exact (hc hs.symm).elim
    · intro i1 hi1 i2 hi2 heq
      have hv1 : v ∈ freqF n e a b i1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi1).1).2
      have hv2 : v ∈ freqF n e a b i2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi2).1).2
      have hp1 := hπ_prop vf i1; rw [if_pos hv1] at hp1
      have hp2 := hπ_prop vf i2; rw [if_pos hv2] at hp2
      have := congrArg (π vf) heq
      rw [hp1.2.2, hp2.2.2] at this
      exact this
    · intro j hj
      have ⟨hj_r, hj_s⟩ := Finset.mem_filter.mp hj
      have hvj : v ∈ freqF n e a b j := (Finset.mem_filter.mp hj_r).2
      have hp := hπ_prop vf j; rw [if_pos hvj] at hp
      have hc := hct vf j hvj
      refine ⟨π vf j, ?_, hp.2.2⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2.1⟩, ?_⟩
      rw [hj_s] at hc
      cases hs : signOf (a (π vf j)) (b (π vf j)) (t (π vf j)) v
      · exact (hc hs.symm).elim
      · rfl
  have hfilt_eq : (goodSignF n e a b).filter (fun t => compatF n e a b t π) =
      (Finset.univ : Finset (Fin (4 * e) → Bool × Bool)).filter (fun t => compatF n e a b t π) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hcompat_good t h, h⟩⟩
  rw [hfilt_eq]
  let E := {q : ↥(freqsF n e a b) × Fin (4 * e) // q.1.val ∈ freqF n e a b q.2 ∧ q.2 < π q.1 q.2}
  have hE_card : Fintype.card E = 6 * e := by
    let Inc := {q : ↥(freqsF n e a b) × Fin (4 * e) // q.1.val ∈ freqF n e a b q.2}
    have hInc_card : Fintype.card Inc = 12 * e := by
      have h1 : Fintype.card Inc = ∑ i : Fin (4 * e), (freqF n e a b i).card := by
        rw [← Finset.card_univ]
        have hbij : (Finset.univ : Finset Inc).card =
            ((Finset.univ : Finset (Fin (4 * e))).sigma (fun i => freqF n e a b i)).card := by
          refine Finset.card_bij
            (fun (x : Inc) _ => ⟨x.val.2, x.val.1.val⟩) ?_ ?_ ?_
          · intro x _; simp [x.property]
          · intro x1 _ x2 _ h
            rcases x1 with ⟨⟨⟨v1, hv1⟩, i1⟩, h1⟩
            rcases x2 with ⟨⟨⟨v2, hv2⟩, i2⟩, h2⟩
            simp only [Sigma.mk.inj_iff] at h
            rcases h with ⟨rfl, h⟩
            have hv : v1 = v2 := eq_of_heq h
            subst hv; rfl
          · intro y hy
            rcases y with ⟨i, v⟩
            have hv : v ∈ freqF n e a b i := (Finset.mem_sigma.mp hy).2
            have hvf : v ∈ freqsF n e a b := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
            exact ⟨⟨(⟨v, hvf⟩, i), hv⟩, Finset.mem_univ _, rfl⟩
        rw [hbij, Finset.card_sigma]
      rw [h1]
      simp_rw [freqF_card n e a b hab]
      simp; omega
    let E_gt := {q : ↥(freqsF n e a b) × Fin (4 * e) // q.1.val ∈ freqF n e a b q.2 ∧ π q.1 q.2 < q.2}
    have hdisj_sum : Fintype.card Inc = Fintype.card E + Fintype.card E_gt := by
      rw [← Fintype.card_sum]
      refine Fintype.card_congr
        { toFun := fun ⟨⟨v, i⟩, hvi⟩ =>
            if hlt : i < π v i then Sum.inl ⟨(v, i), ⟨hvi, hlt⟩⟩
            else Sum.inr ⟨(v, i), ⟨hvi, by
              have hp := hπ_prop v i; rw [if_pos hvi] at hp
              exact lt_of_le_of_ne (not_lt.mp hlt) hp.1⟩⟩
          invFun := fun s => match s with
            | Sum.inl ⟨q, hq⟩ => ⟨q, hq.1⟩
            | Sum.inr ⟨q, hq⟩ => ⟨q, hq.1⟩
          left_inv := fun ⟨⟨v, i⟩, hvi⟩ => by
            by_cases hlt : i < π v i <;> simp [hlt]
          right_inv := fun s => by
            rcases s with ⟨⟨v, i⟩, ⟨hvi, hlt⟩⟩ | ⟨⟨v, i⟩, ⟨hvi, hgt⟩⟩
            · simp [hlt]
            · have hnot : ¬ (i < π v i) := not_lt.mpr (le_of_lt hgt)
              simp [hnot] }
    have hE_eq_gt : Fintype.card E = Fintype.card E_gt := by
      refine Fintype.card_congr
        { toFun := fun ⟨⟨v, i⟩, ⟨hvi, hlt⟩⟩ =>
            have hp := hπ_prop v i
            ⟨(v, π v i), ⟨by rw [if_pos hvi] at hp; exact hp.2.1,
              by rw [if_pos hvi] at hp; rw [hp.2.2]; exact hlt⟩⟩
          invFun := fun ⟨⟨v, i⟩, ⟨hvi, hgt⟩⟩ =>
            have hp := hπ_prop v i
            ⟨(v, π v i), ⟨by rw [if_pos hvi] at hp; exact hp.2.1,
              by rw [if_pos hvi] at hp; rw [hp.2.2]; exact hgt⟩⟩
          left_inv := fun ⟨⟨v, i⟩, ⟨hvi, _⟩⟩ => by
            have hp := hπ_prop v i; rw [if_pos hvi] at hp
            exact Subtype.ext (Prod.ext rfl hp.2.2)
          right_inv := fun ⟨⟨v, i⟩, ⟨hvi, _⟩⟩ => by
            have hp := hπ_prop v i; rw [if_pos hvi] at hp
            exact Subtype.ext (Prod.ext rfl hp.2.2) }
    omega
  let B : Matrix (Fin (4 * e)) E (ZMod 2) :=
    Matrix.of (fun i q => if q.val.2 = i ∨ π q.val.1 q.val.2 = i then 1 else 0)
  let y0 : Fin (4 * e) → ZMod 2 := fun i =>
    ∑ v ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i ∧ π v i < i), (1 : ZMod 2)
  have hsol_card : ((Finset.univ : Finset (Fin (4 * e) → Bool × Bool)).filter (fun t => compatF n e a b t π)).card =
      ((Finset.univ : Finset (E → ZMod 2)).filter (fun x => B.mulVec x = y0)).card := by
    let b2z : Bool → ZMod 2 := fun b => if b then 1 else 0
    let z2b : ZMod 2 → Bool := fun z => decide (z = 1)
    have hbz : ∀ b, z2b (b2z b) = b := by intro b; cases b <;> decide
    have hzb : ∀ z, b2z (z2b z) = z := by intro z; rcases z2_cases z with rfl | rfl <;> decide
    have hbz_not : ∀ b, b2z (!b) = b2z b + 1 := by intro b; cases b <;> decide
    have hbz_xor : ∀ b1 b2, b2z (xor b1 b2) = b2z b1 + b2z b2 := by
      intro b1 b2; cases b1 <;> cases b2 <;> decide
    let sOf : (E → ZMod 2) → ↥(freqsF n e a b) → Fin (4 * e) → ZMod 2 := fun x v i =>
      if hvi : v.val ∈ freqF n e a b i then
        if hlt : i < π v i then x ⟨(v, i), ⟨hvi, hlt⟩⟩
        else
          have hp := hπ_prop v i
          x ⟨(v, π v i), ⟨by rw [if_pos hvi] at hp; exact hp.2.1,
            by rw [if_pos hvi] at hp; rw [hp.2.2]; exact lt_of_le_of_ne (not_lt.mp hlt) hp.1⟩⟩ + 1
      else 0
    have hsOf_sum : ∀ (x : E → ZMod 2) (i : Fin (4 * e)),
        (∑ v ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i), sOf x v i) =
        B.mulVec x i + y0 i := by
      intro x i
      have hB : B.mulVec x i =
          ∑ v ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i),
            if hlt : i < π v i then
              if hvi : v.val ∈ freqF n e a b i then x ⟨(v, i), ⟨hvi, hlt⟩⟩ else 0
            else
              if hvi : v.val ∈ freqF n e a b i then
                have hp := hπ_prop v i
                x ⟨(v, π v i), ⟨by rw [if_pos hvi] at hp; exact hp.2.1,
                  by rw [if_pos hvi] at hp; rw [hp.2.2]; exact lt_of_le_of_ne (not_lt.mp hlt) hp.1⟩⟩
              else 0 := by
        simp only [Matrix.mulVec, dotProduct, B, Matrix.of_apply, ite_mul, one_mul, zero_mul]
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun (q : E) _ => q.val.1) ?_ ?_ ?_ ?_
        · intro q hq
          have hcond := (Finset.mem_filter.mp hq).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases hcond with rfl | hpi
          · exact q.property.1
          · have hp := hπ_prop q.val.1 q.val.2
            rw [if_pos q.property.1] at hp
            rw [← hpi]; exact hp.2.1
        · intro q1 hq1 q2 hq2 heq
          have hc1 := (Finset.mem_filter.mp hq1).2
          have hc2 := (Finset.mem_filter.mp hq2).2
          rcases q1 with ⟨⟨v1, j1⟩, ⟨hv1, hlt1⟩⟩
          rcases q2 with ⟨⟨v2, j2⟩, ⟨hv2, hlt2⟩⟩
          simp only at heq hc1 hc2 hv1 hv2 hlt1 hlt2
          subst heq
          rcases hc1 with rfl | h1 <;> rcases hc2 with rfl | h2
          · rfl
          · have hp2 := hπ_prop v1 j2; rw [if_pos hv2] at hp2
            have hlt' : π v1 j2 < j2 := by rw [← h2, hp2.2.2] at hlt1; exact hlt1
            exact (lt_asymm hlt2 hlt').elim
          · have hp1 := hπ_prop v1 j1; rw [if_pos hv1] at hp1
            have hlt' : π v1 j1 < j1 := by rw [← h1, hp1.2.2] at hlt2; exact hlt2
            exact (lt_asymm hlt1 hlt').elim
          · have hp1 := hπ_prop v1 j1; rw [if_pos hv1] at hp1
            have hp2 := hπ_prop v1 j2; rw [if_pos hv2] at hp2
            have : j1 = j2 := by
              have := congrArg (π v1) (h1.trans h2.symm)
              rw [hp1.2.2, hp2.2.2] at this
              exact this
            subst this; rfl
        · intro v hv
          have hvi : v.val ∈ freqF n e a b i := (Finset.mem_filter.mp hv).2
          have hp := hπ_prop v i; rw [if_pos hvi] at hp
          by_cases hlt : i < π v i
          · exact ⟨⟨(v, i), ⟨hvi, hlt⟩⟩, by simp, rfl⟩
          · have hgt : π v i < i := lt_of_le_of_ne (not_lt.mp hlt) hp.1
            refine ⟨⟨(v, π v i), ⟨hp.2.1, by rw [hp.2.2]; exact hgt⟩⟩, ?_, rfl⟩
            simp [hp.2.2]
        · intro q hq
          have hcond := (Finset.mem_filter.mp hq).2
          rcases q with ⟨⟨v, j⟩, ⟨hvj, hltj⟩⟩
          simp only at hcond hvj hltj ⊢
          rcases hcond with rfl | hpi
          · simp [dif_pos hltj, dif_pos hvj]
          · have hp := hπ_prop v j; rw [if_pos hvj] at hp
            have hvi : v.val ∈ freqF n e a b i := by rw [← hpi]; exact hp.2.1
            have hnotlt : ¬ (i < π v i) := by
              rw [← hpi, hp.2.2]; exact not_lt.mpr (le_of_lt hltj)
            simp only [dif_neg hnotlt, dif_pos hvi]
            congr 1
            apply Subtype.ext
            simp only [Prod.mk.injEq, true_and]
            rw [← hpi, hp.2.2]
      rw [hB]
      have hy0_eq : y0 i =
          ∑ v ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i),
            if i < π v i then (0 : ZMod 2) else 1 := by
        simp only [y0]
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hvi, hlt⟩
          exact ⟨hvi, not_lt.mpr (le_of_lt hlt)⟩
        · rintro ⟨hvi, hnot⟩
          have hp := hπ_prop v i; rw [if_pos hvi] at hp
          exact ⟨hvi, lt_of_le_of_ne (not_lt.mp hnot) hp.1⟩
      rw [hy0_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvi : v.val ∈ freqF n e a b i := (Finset.mem_filter.mp hv).2
      by_cases hlt : i < π v i
      · simp only [sOf, dif_pos hvi, dif_pos hlt, if_pos hlt, add_zero]
      · simp only [sOf, dif_pos hvi, dif_neg hlt, if_neg hlt]
    have hfreq_three : ∀ (i : Fin (4 * e)) (g : ↥(freqsF n e a b) → ZMod 2),
        (∑ v ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i), g v) =
        g ⟨a i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ +
        g ⟨b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ +
        g ⟨a i + b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ := by
      intro i g
      have ⟨ha, hb, hne⟩ := hab i
      have ⟨_, h2, h3⟩ := four_distinct ha hb hne
      let va : ↥(freqsF n e a b) := ⟨a i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩
      let vb : ↥(freqsF n e a b) := ⟨b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩
      let vab : ↥(freqsF n e a b) := ⟨a i + b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩
      have hset : (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i) = {va, vb, vab} := by
        ext ⟨v, hv⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, freqF, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl)
          · left; exact Subtype.ext rfl
          · right; left; exact Subtype.ext rfl
          · right; right; exact Subtype.ext rfl
        · rintro (h | h | h)
          · left; exact congrArg Subtype.val h
          · right; left; exact congrArg Subtype.val h
          · right; right; exact congrArg Subtype.val h
      rw [hset, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton, add_assoc]
      · intro h
        have hv : b i = a i + b i := congrArg Subtype.val (Finset.mem_singleton.mp h)
        exact h3.symm hv
      · intro h
        rcases Finset.mem_insert.mp h with h1 | h1
        · exact hne (congrArg Subtype.val h1)
        · exact h2.symm (congrArg Subtype.val (Finset.mem_singleton.mp h1))
    refine Finset.card_bij
      (fun (t : Fin (4 * e) → Bool × Bool) _ (q : E) => b2z (signOf (a q.val.2) (b q.val.2) (t q.val.2) q.val.1.val))
      ?_ ?_ ?_
    · intro t ht
      have hct := (Finset.mem_filter.mp ht).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, funext fun i => ?_⟩
      let x : E → ZMod 2 := fun q => b2z (signOf (a q.val.2) (b q.val.2) (t q.val.2) q.val.1.val)
      have hmatch : ∀ v : ↥(freqsF n e a b), v.val ∈ freqF n e a b i →
          sOf x v i = b2z (signOf (a i) (b i) (t i) v.val) := by
        intro v hvi
        simp only [sOf, dif_pos hvi]
        by_cases hlt : i < π v i
        · simp [dif_pos hlt, x]
        · simp only [dif_neg hlt, x]
          have hc := hct v i hvi
          have hnot : signOf (a (π v i)) (b (π v i)) (t (π v i)) v.val =
              !(signOf (a i) (b i) (t i) v.val) := by
            cases h1 : signOf (a i) (b i) (t i) v.val <;>
            cases h2 : signOf (a (π v i)) (b (π v i)) (t (π v i)) v.val <;>
            simp [h1, h2] at hc ⊢
          rw [hnot, hbz_not, add_assoc, z2_add_self, add_zero]
      have hsum0 : (∑ v ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i), sOf x v i) = 0 := by
        rw [Finset.sum_congr rfl (fun v hv => hmatch v (Finset.mem_filter.mp hv).2), hfreq_three i]
        have ⟨ha, hb, hne⟩ := hab i
        have ⟨_, h2, h3⟩ := four_distinct ha hb hne
        simp only [signOf, ↓reduceIte, hne.symm, h2, h3, hbz_xor]
        cases (t i).1 <;> cases (t i).2 <;> decide
      have hEq := hsOf_sum x i
      rw [hsum0] at hEq
      have h' := congrArg (fun z => z + y0 i) hEq.symm
      simpa [add_assoc, z2_add_self] using h'
    · intro t1 ht1 t2 ht2 heq
      have hct1 := (Finset.mem_filter.mp ht1).2
      have hct2 := (Finset.mem_filter.mp ht2).2
      have hall : ∀ (v : ↥(freqsF n e a b)) (i : Fin (4 * e)), v.val ∈ freqF n e a b i →
          signOf (a i) (b i) (t1 i) v.val = signOf (a i) (b i) (t2 i) v.val := by
        intro v i hvi
        by_cases hlt : i < π v i
        · have h1 := congrFun heq ⟨(v, i), ⟨hvi, hlt⟩⟩
          have h2 := congrArg z2b h1
          simpa [hbz] using h2
        · have hp := hπ_prop v i; rw [if_pos hvi] at hp
          have hgt : π v i < i := lt_of_le_of_ne (not_lt.mp hlt) hp.1
          have h1 := congrFun heq ⟨(v, π v i), ⟨hp.2.1, by rw [hp.2.2]; exact hgt⟩⟩
          have h2 := congrArg z2b h1
          simp only [hbz] at h2
          have hc1 := hct1 v i hvi
          have hc2 := hct2 v i hvi
          cases hs1 : signOf (a i) (b i) (t1 i) v.val <;>
          cases hs2 : signOf (a i) (b i) (t2 i) v.val <;>
          cases hp1 : signOf (a (π v i)) (b (π v i)) (t1 (π v i)) v.val <;>
          cases hp2 : signOf (a (π v i)) (b (π v i)) (t2 (π v i)) v.val <;>
          simp [hs1, hs2, hp1, hp2] at h2 hc1 hc2 ⊢
      ext i
      · have hv : a i ∈ freqF n e a b i := by simp [freqF]
        have hvf : a i ∈ freqsF n e a b := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
        have h := hall ⟨a i, hvf⟩ i hv
        simpa [signOf] using h
      · have ⟨_, _, hne⟩ := hab i
        have hv : b i ∈ freqF n e a b i := by simp [freqF]
        have hvf : b i ∈ freqsF n e a b := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
        have h := hall ⟨b i, hvf⟩ i hv
        simpa [signOf, hne.symm] using h
    · intro x hx
      have hBx : B.mulVec x = y0 := (Finset.mem_filter.mp hx).2
      let t : Fin (4 * e) → Bool × Bool := fun i =>
        (z2b (sOf x ⟨a i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ i),
         z2b (sOf x ⟨b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ i))
      have hsign_eq : ∀ (v : ↥(freqsF n e a b)) (i : Fin (4 * e)), v.val ∈ freqF n e a b i →
          b2z (signOf (a i) (b i) (t i) v.val) = sOf x v i := by
        intro v i hvi
        have ⟨ha, hb, hne⟩ := hab i
        have ⟨_, h2, h3⟩ := four_distinct ha hb hne
        have hsum0 : (∑ u ∈ (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun u => u.val ∈ freqF n e a b i), sOf x u i) = 0 := by
          rw [hsOf_sum x i, hBx, z2_add_self]
        rw [hfreq_three i] at hsum0
        have hv_mem : v.val = a i ∨ v.val = b i ∨ v.val = a i + b i := by
          simpa [freqF] using hvi
        rcases hv_mem with h | h | h
        · have hveq : v = ⟨a i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ := Subtype.ext h
          subst hveq
          simp [signOf, t, hzb]
        · have hveq : v = ⟨b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ := Subtype.ext h
          subst hveq
          simp [signOf, hne.symm, t, hzb]
        · have hveq : v = ⟨a i + b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ := Subtype.ext h
          subst hveq
          simp only [signOf, h2, h3, ↓reduceIte, t, hbz_xor, hzb]
          have h' := congrArg (fun z => z + sOf x ⟨a i + b i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [freqF]⟩⟩ i) hsum0
          simpa [add_assoc, z2_add_self] using h'
      refine ⟨t, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun v i hvi => ?_⟩
        have hp := hπ_prop v i; rw [if_pos hvi] at hp
        have h1 := hsign_eq v i hvi
        have h2 := hsign_eq v (π v i) hp.2.1
        have hflip : sOf x v (π v i) = sOf x v i + 1 := by
          by_cases hlt : i < π v i
          · have hnot : ¬ (π v i < π v (π v i)) := by rw [hp.2.2]; exact not_lt.mpr (le_of_lt hlt)
            simp only [sOf, dif_pos hvi, dif_pos hp.2.1, dif_pos hlt, dif_neg hnot]
            congr 1; congr 1; exact Subtype.ext (Prod.ext rfl hp.2.2)
          · have hgt : π v i < i := lt_of_le_of_ne (not_lt.mp hlt) hp.1
            have hlt' : π v i < π v (π v i) := by rw [hp.2.2]; exact hgt
            simp only [sOf, dif_pos hvi, dif_pos hp.2.1, dif_neg hlt, dif_pos hlt', add_assoc,
              z2_add_self, add_zero]
        intro heq
        rw [heq] at h1
        rw [h1, hflip] at h2
        have h3 := congrArg (fun z => sOf x v i + z) h2
        rw [z2_add_self, ← add_assoc, z2_add_self, zero_add] at h3
        exact zero_ne_one h3
      · ext q
        rw [hsign_eq q.val.1 q.val.2 q.property.1]
        simp [sOf, dif_pos q.property.1, dif_pos q.property.2]
  rw [hsol_card]
  let adj_π : Fin (4 * e) → Fin (4 * e) → Prop := fun i j => ∃ v : ↥(freqsF n e a b), v.val ∈ freqF n e a b i ∧ π v i = j
  let cs := compsOf adj_π
  let evalC : (Fin (4 * e) → ZMod 2) →ₗ[ZMod 2] (↥cs → ZMod 2) :=
    { toFun := fun y C => ∑ i ∈ C.val, y i
      map_add' := fun y1 y2 => by ext C; simp [Finset.sum_add_distrib]
      map_smul' := fun r y => by ext C; simp [Finset.mul_sum] }
  have hrange_le : LinearMap.range B.mulVecLin ≤ LinearMap.ker evalC := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    ext ⟨C, hC⟩
    simp only [evalC, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, B, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun q _ => ?_
    have hsame : (q.val.2 ∈ C) ↔ (π q.val.1 q.val.2 ∈ C) := by
      rcases Finset.mem_image.mp hC with ⟨i0, _, rfl⟩
      simp only [mem_compOf]
      have hadj : adj_π q.val.2 (π q.val.1 q.val.2) := ⟨q.val.1, q.property.1, rfl⟩
      exact ⟨fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ hadj),
             fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hadj))⟩
    have hne_end : q.val.2 ≠ π q.val.1 q.val.2 := ne_of_lt q.property.2
    simp only [ite_mul, one_mul, zero_mul]
    by_cases hmem : q.val.2 ∈ C
    · have hmem2 : π q.val.1 q.val.2 ∈ C := hsame.mp hmem
      rw [← Finset.sum_filter]
      have hfilt : C.filter (fun i => q.val.2 = i ∨ π q.val.1 q.val.2 = i) = {q.val.2, π q.val.1 q.val.2} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl | rfl⟩
          · left; rfl
          · right; rfl
        · rintro (rfl | rfl)
          · exact ⟨hmem, Or.inl rfl⟩
          · exact ⟨hmem2, Or.inr rfl⟩
      rw [hfilt, Finset.sum_pair hne_end, z2_add_self]
    · have hmem2 : π q.val.1 q.val.2 ∉ C := mt hsame.mpr hmem
      refine Finset.sum_eq_zero fun i hi => ?_
      have hnot : ¬ (q.val.2 = i ∨ π q.val.1 q.val.2 = i) := by
        rintro (rfl | rfl)
        · exact hmem hi
        · exact hmem2 hi
      simp [hnot]
  have hevalC_surj : Function.Surjective evalC := by
    intro g
    let rep : ↥cs → Fin (4 * e) := fun C => (mem_compsOf_nonempty adj_π C.property).choose
    have hrep_mem : ∀ C : ↥cs, rep C ∈ C.val := fun C => (mem_compsOf_nonempty adj_π C.property).choose_spec
    let y : Fin (4 * e) → ZMod 2 := fun i =>
      ∑ C : ↥cs, if rep C = i then g C else 0
    refine ⟨y, ?_⟩
    ext C
    simp only [evalC, LinearMap.coe_mk, AddHom.coe_mk, y]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single C]
    · rw [Finset.sum_ite_eq C.val (rep C), if_pos (hrep_mem C)]
    · intro D _ hDC
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : rep D ≠ i := by
        rintro rfl
        have hdisj := compOf_disjoint adj_π D.property C.property (mt Subtype.ext hDC)
        exact Finset.disjoint_left.mp hdisj (hrep_mem D) hi
      simp [hne]
    · intro h; exact (h (Finset.mem_univ C)).elim
  have hker_evalC_rank : Module.finrank (ZMod 2) (LinearMap.ker evalC) + cs.card = 4 * e := by
    have h1 := LinearMap.finrank_range_add_finrank_ker evalC
    rw [LinearMap.range_eq_top.mpr hevalC_surj, finrank_top] at h1
    simp only [Module.finrank_pi, Fintype.card_coe, Fintype.card_fin] at h1
    omega
  have hker_BT_rank : Module.finrank (ZMod 2) (LinearMap.ker Bᵀ.mulVecLin) = cs.card := by
    let φ : (↥cs → ZMod 2) ≃ₗ[ZMod 2] LinearMap.ker Bᵀ.mulVecLin :=
      { toFun := fun g =>
          ⟨fun i => g ⟨compOf adj_π i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩, by
            rw [LinearMap.mem_ker]
            ext q
            simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
              B, Matrix.of_apply, Pi.zero_apply, ite_mul, one_mul, zero_mul]
            have hne_end : q.val.2 ≠ π q.val.1 q.val.2 := ne_of_lt q.property.2
            rw [← Finset.sum_filter]
            have hfeq : (Finset.univ : Finset (Fin (4 * e))).filter (fun i => q.val.2 = i ∨ π q.val.1 q.val.2 = i) =
                {q.val.2, π q.val.1 q.val.2} := by
              ext i; simp [eq_comm]
            rw [hfeq, Finset.sum_pair hne_end]
            have heqc : compOf adj_π q.val.2 = compOf adj_π (π q.val.1 q.val.2) :=
              compOf_eq_of_eqv adj_π (Relation.EqvGen.rel _ _ ⟨q.val.1, q.property.1, rfl⟩)
            have hsub : (⟨compOf adj_π q.val.2, Finset.mem_image.mpr ⟨q.val.2, Finset.mem_univ _, rfl⟩⟩ : ↥cs) =
                ⟨compOf adj_π (π q.val.1 q.val.2), Finset.mem_image.mpr ⟨π q.val.1 q.val.2, Finset.mem_univ _, rfl⟩⟩ :=
              Subtype.ext heqc
            rw [hsub, z2_add_self]⟩
        map_add' := fun g1 g2 => by ext i; rfl
        map_smul' := fun r g => by ext i; rfl
        invFun := fun f C => f.val (mem_compsOf_nonempty adj_π C.property).choose
        left_inv := fun g => by
          ext ⟨C, hC⟩
          let j := (mem_compsOf_nonempty adj_π hC).choose
          have hj : j ∈ C := (mem_compsOf_nonempty adj_π hC).choose_spec
          have heqc : compOf adj_π j = C := by
            rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
            exact compOf_eq_of_eqv adj_π (Relation.EqvGen.symm _ _ ((mem_compOf adj_π i j).mp hj))
          exact congrArg g (Subtype.ext heqc)
        right_inv := fun ⟨f, hf⟩ => by
          ext i
          have hker := LinearMap.mem_ker.mp hf
          have hq_eq : ∀ q : E, f q.val.2 + f (π q.val.1 q.val.2) = 0 := by
            intro q
            have h0 := congrFun hker q
            simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
              B, Matrix.of_apply, Pi.zero_apply, ite_mul, one_mul, zero_mul] at h0
            have hne_end : q.val.2 ≠ π q.val.1 q.val.2 := ne_of_lt q.property.2
            rw [← Finset.sum_filter] at h0
            have hfeq : (Finset.univ : Finset (Fin (4 * e))).filter (fun k => q.val.2 = k ∨ π q.val.1 q.val.2 = k) =
                {q.val.2, π q.val.1 q.val.2} := by ext k; simp [eq_comm]
            rw [hfeq, Finset.sum_pair hne_end] at h0
            exact h0
          have hstep : ∀ x y, adj_π x y → f x = f y := by
            rintro x y ⟨v, hvx, rfl⟩
            have hp := hπ_prop v x; rw [if_pos hvx] at hp
            by_cases hlt : x < π v x
            · have h0 := hq_eq ⟨(v, x), ⟨hvx, hlt⟩⟩
              have h' := congrArg (fun z => z + f (π v x)) h0
              simpa [add_assoc, z2_add_self] using h'
            · have hgt : π v x < x := lt_of_le_of_ne (not_lt.mp hlt) hp.1
              have h0 := hq_eq ⟨(v, π v x), ⟨hp.2.1, by rw [hp.2.2]; exact hgt⟩⟩
              simp only [hp.2.2] at h0
              have h' := congrArg (fun z => z + f x) h0
              simpa [add_assoc, z2_add_self] using h'.symm
          have heqv_eq : ∀ x y, Relation.EqvGen adj_π x y → f x = f y := by
            intro x y h
            induction h with
            | rel x y hxy => exact hstep x y hxy
            | refl _ => rfl
            | symm _ _ _ ih => exact ih.symm
            | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
          let C : ↥cs := ⟨compOf adj_π i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
          have hj : (mem_compsOf_nonempty adj_π C.property).choose ∈ compOf adj_π i :=
            (mem_compsOf_nonempty adj_π C.property).choose_spec
          exact (heqv_eq i _ ((mem_compOf adj_π i _).mp hj)).symm }
    rw [← φ.finrank_eq]
    simp [Fintype.card_coe]
  have hrange_eq : LinearMap.range B.mulVecLin = LinearMap.ker evalC := by
    refine Submodule.eq_of_le_of_finrank_eq hrange_le ?_
    have hrankT : Bᵀ.rank = B.rank := Matrix.rank_transpose B
    have hBT_rn := LinearMap.finrank_range_add_finrank_ker Bᵀ.mulVecLin
    rw [hker_BT_rank] at hBT_rn
    simp only [Module.finrank_pi, Fintype.card_fin] at hBT_rn
    change B.rank = Module.finrank (ZMod 2) (LinearMap.ker evalC)
    change Bᵀ.rank + cs.card = 4 * e at hBT_rn
    omega
  have hker_B_rank : Module.finrank (ZMod 2) (LinearMap.ker B.mulVecLin) = 2 * e + cs.card := by
    have hB_rn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [hrange_eq] at hB_rn
    simp only [Module.finrank_pi, hE_card] at hB_rn
    omega
  have hy0_cond : (y0 ∈ LinearMap.range B.mulVecLin) ↔ (∀ C ∈ cs, 4 ∣ C.card) := by
    rw [hrange_eq, LinearMap.mem_ker]
    have hsum_C : ∀ C ∈ cs, (∑ i ∈ C, y0 i) =
        (((Finset.univ : Finset E).filter (fun q => q.val.2 ∈ C)).card : ZMod 2) := by
      intro C hC
      have hbij : ((Finset.univ : Finset E).filter (fun q => q.val.2 ∈ C)).card =
          ∑ i ∈ C, ((Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i ∧ π v i < i)).card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij
          (fun (q : E) _ => ⟨π q.val.1 q.val.2, q.val.1⟩) ?_ ?_ ?_
        · intro q hq
          have hqC : q.val.2 ∈ C := (Finset.mem_filter.mp hq).2
          have hp := hπ_prop q.val.1 q.val.2; rw [if_pos q.property.1] at hp
          have hpiC : π q.val.1 q.val.2 ∈ C := by
            rcases Finset.mem_image.mp hC with ⟨i0, _, rfl⟩
            exact (mem_compOf adj_π i0 _).mpr
              (Relation.EqvGen.trans _ _ _ ((mem_compOf adj_π i0 _).mp hqC)
                (Relation.EqvGen.rel _ _ ⟨q.val.1, q.property.1, rfl⟩))
          rw [Finset.mem_sigma]
          refine ⟨hpiC, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2.1, ?_⟩⟩
          rw [hp.2.2]; exact q.property.2
        · intro q1 _ q2 _ heq
          rcases q1 with ⟨⟨v1, i1⟩, ⟨hv1, hlt1⟩⟩
          rcases q2 with ⟨⟨v2, i2⟩, ⟨hv2, hlt2⟩⟩
          simp only [Sigma.mk.inj_iff] at heq
          rcases heq with ⟨hpi, hv⟩
          have hv' : v1 = v2 := eq_of_heq hv
          subst hv'
          have hp1 := hπ_prop v1 i1; rw [if_pos hv1] at hp1
          have hp2 := hπ_prop v1 i2; rw [if_pos hv2] at hp2
          have hi : i1 = i2 := by
            have := congrArg (π v1) hpi
            rw [hp1.2.2, hp2.2.2] at this; exact this
          subst hi; rfl
        · intro y hy
          rcases y with ⟨i, v⟩
          rcases Finset.mem_sigma.mp hy with ⟨hiC, hv⟩
          rcases (Finset.mem_filter.mp hv).2 with ⟨hvi, hlt⟩
          have hp := hπ_prop v i; rw [if_pos hvi] at hp
          have hpiC : π v i ∈ C := by
            rcases Finset.mem_image.mp hC with ⟨i0, _, rfl⟩
            exact (mem_compOf adj_π i0 _).mpr
              (Relation.EqvGen.trans _ _ _ ((mem_compOf adj_π i0 _).mp hiC)
                (Relation.EqvGen.rel _ _ ⟨v, hvi, rfl⟩))
          refine ⟨⟨(v, π v i), ⟨hp.2.1, by rw [hp.2.2]; exact hlt⟩⟩, by simp [hpiC], ?_⟩
          simp [hp.2.2]
      rw [hbij, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [y0]
    have hdeg_C : ∀ C ∈ cs,
        2 * ((Finset.univ : Finset E).filter (fun q => q.val.2 ∈ C)).card = 3 * C.card := by
      intro C hC
      let EC := (Finset.univ : Finset E).filter (fun q => q.val.2 ∈ C)
      let IC := C.sigma (fun i => (Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i))
      have hIC_card : IC.card = 3 * C.card := by
        rw [Finset.card_sigma]
        have h3 : ∀ i ∈ C, ((Finset.univ : Finset ↥(freqsF n e a b)).filter (fun v => v.val ∈ freqF n e a b i)).card = 3 := by
          intro i _
          rw [← freqF_card n e a b hab i]
          refine Finset.card_bij (fun (v : ↥(freqsF n e a b)) _ => v.val) ?_ ?_ ?_
          · intro v hv; exact (Finset.mem_filter.mp hv).2
          · intro v1 _ v2 _ h; exact Subtype.ext h
          · intro v hv
            exact ⟨⟨v, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩⟩, by simp [hv], rfl⟩
        rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [← hIC_card]
      have h2EC : 2 * EC.card = (EC ×ˢ (Finset.univ : Finset Bool)).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
      rw [h2EC]
      refine Finset.card_bij
        (fun (p : E × Bool) _ =>
          if p.2 then ⟨p.1.val.2, p.1.val.1⟩ else ⟨π p.1.val.1 p.1.val.2, p.1.val.1⟩)
        ?_ ?_ ?_
      · intro ⟨q, b'⟩ hp
        have hqC : q.val.2 ∈ C := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
        have hqp := hπ_prop q.val.1 q.val.2; rw [if_pos q.property.1] at hqp
        cases b'
        · simp only [Bool.false_eq_true, ↓reduceIte, IC, Finset.mem_sigma, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨?_, hqp.2.1⟩
          rcases Finset.mem_image.mp hC with ⟨i0, _, rfl⟩
          exact (mem_compOf adj_π i0 _).mpr
            (Relation.EqvGen.trans _ _ _ ((mem_compOf adj_π i0 _).mp hqC)
              (Relation.EqvGen.rel _ _ ⟨q.val.1, q.property.1, rfl⟩))
        · simp [IC, hqC, q.property.1]
      · intro ⟨q1, b1⟩ _ ⟨q2, b2⟩ _ heq
        rcases q1 with ⟨⟨v1, i1⟩, ⟨hv1, hlt1⟩⟩
        rcases q2 with ⟨⟨v2, i2⟩, ⟨hv2, hlt2⟩⟩
        have hp1 := hπ_prop v1 i1; rw [if_pos hv1] at hp1
        have hp2 := hπ_prop v2 i2; rw [if_pos hv2] at hp2
        cases b1 <;> cases b2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Sigma.mk.inj_iff] at heq
        · rcases heq with ⟨hpi, hv⟩
          have hv' : v1 = v2 := eq_of_heq hv
          subst hv'
          have hi : i1 = i2 := by
            have := congrArg (π v1) hpi
            rw [hp1.2.2, hp2.2.2] at this; exact this
          subst hi; rfl
        · rcases heq with ⟨hpi, hv⟩
          have hv' : v1 = v2 := eq_of_heq hv
          subst hv'
          rw [← hpi, hp1.2.2] at hlt2
          exact (lt_asymm hlt1 hlt2).elim
        · rcases heq with ⟨hpi, hv⟩
          have hv' : v1 = v2 := eq_of_heq hv
          subst hv'
          rw [hpi, hp2.2.2] at hlt1
          exact (lt_asymm hlt1 hlt2).elim
        · rcases heq with ⟨rfl, hv⟩
          have hv' : v1 = v2 := eq_of_heq hv
          subst hv'; rfl
      · intro ⟨i, v⟩ hy
        rcases Finset.mem_sigma.mp hy with ⟨hiC, hv⟩
        have hvi : v.val ∈ freqF n e a b i := (Finset.mem_filter.mp hv).2
        have hp := hπ_prop v i; rw [if_pos hvi] at hp
        by_cases hlt : i < π v i
        · exact ⟨(⟨(v, i), ⟨hvi, hlt⟩⟩, true), by simp [EC, hiC], rfl⟩
        · have hgt : π v i < i := lt_of_le_of_ne (not_lt.mp hlt) hp.1
          have hpiC : π v i ∈ C := by
            rcases Finset.mem_image.mp hC with ⟨i0, _, rfl⟩
            exact (mem_compOf adj_π i0 _).mpr
              (Relation.EqvGen.trans _ _ _ ((mem_compOf adj_π i0 _).mp hiC)
                (Relation.EqvGen.rel _ _ ⟨v, hvi, rfl⟩))
          refine ⟨(⟨(v, π v i), ⟨hp.2.1, by rw [hp.2.2]; exact hgt⟩⟩, false), by simp [EC, hpiC], ?_⟩
          simp [hp.2.2]
    constructor
    · intro h C hC
      have h0 := congrFun h ⟨C, hC⟩
      simp only [evalC, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      rw [hsum_C C hC, z2_eq_zero_iff_even] at h0
      have hd := hdeg_C C hC
      rcases h0 with ⟨k, hk⟩
      rw [hk] at hd
      omega
    · intro h4
      ext ⟨C, hC⟩
      simp only [evalC, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      rw [hsum_C C hC, z2_eq_zero_iff_even]
      have hd := hdeg_C C hC
      rcases h4 C hC with ⟨k, hk⟩
      rw [hk] at hd
      omega
  change ((Finset.univ : Finset (E → ZMod 2)).filter (fun x => B.mulVec x = y0)).card =
    2 ^ (2 * e) * (if ∀ C ∈ cs, 4 ∣ C.card then 2 ^ cs.card else 0)
  by_cases h4 : ∀ C ∈ cs, 4 ∣ C.card
  · rw [if_pos h4]
    obtain ⟨x0, hx0⟩ := hy0_cond.mpr h4
    rw [Matrix.mulVecLin_apply] at hx0
    have hcard_ker : ((Finset.univ : Finset (E → ZMod 2)).filter (fun x => B.mulVec x = y0)).card =
        Fintype.card (LinearMap.ker B.mulVecLin) := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun ⟨x, hx⟩ =>
            ⟨x + x0, by
              rw [LinearMap.mem_ker, map_add]
              have h1 : B.mulVec x = y0 := (Finset.mem_filter.mp hx).2
              change B.mulVec x + B.mulVec x0 = 0
              rw [h1, hx0, z2_vec_add_self]⟩
          invFun := fun ⟨z, hz⟩ =>
            ⟨z + x0, by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h1 : B.mulVec z = 0 := LinearMap.mem_ker.mp hz
              rw [Matrix.mulVec_add, h1, zero_add]
              exact hx0⟩
          left_inv := fun ⟨x, _⟩ => by ext j; simp [add_assoc, z2_add_self]
          right_inv := fun ⟨z, _⟩ => by ext j; simp [add_assoc, z2_add_self] }
    rw [hcard_ker, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hker_B_rank, pow_add]
  · rw [if_neg h4, mul_zero]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hBx
    exact h4 (hy0_cond.mp ⟨x, hBx⟩)

lemma counting_identity (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) :
    (goodF n e a b).card * (∏ v ∈ freqsF n e a b, Nat.factorial ((rowsF n e a b v).card / 2)) =
      2 ^ (2 * e) * ∑ π ∈ pairsF n e a b, weightF n e a b π := by
  classical
  let CP := ((goodSignF n e a b) ×ˢ (pairsF n e a b)).filter (fun p => compatF n e a b p.1 p.2)
  have hleft : CP.card = (goodSignF n e a b).card *
      (∏ v ∈ freqsF n e a b, Nat.factorial ((rowsF n e a b v).card / 2)) := by
    have h1 : CP.card = ∑ t ∈ goodSignF n e a b, ((pairsF n e a b).filter (fun π => compatF n e a b t π)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.card_filter]
    rw [h1, Finset.sum_congr rfl (fun t ht => card_compat_for_sign n e a b t ht), Finset.sum_const, smul_eq_mul]
  have hright : CP.card = 2 ^ (2 * e) * ∑ π ∈ pairsF n e a b, weightF n e a b π := by
    have h1 : CP.card = ∑ π ∈ pairsF n e a b, ((goodSignF n e a b).filter (fun t => compatF n e a b t π)).card := by
      rw [Finset.card_filter, Finset.sum_product_right]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [Finset.card_filter]
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun π hπ => card_compat_for_pair n e a b hab π hπ)
  rw [good_card_eq_sign n e a b hab, ← hleft, hright]

lemma no_bridge (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (π : ↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e))
    (hπ : π ∈ pairsF n e a b) (v : ↥(freqsF n e a b)) (i : Fin (4 * e)) (hvi : v.val ∈ freqF n e a b i) :
    Relation.EqvGen (fun x y => ∃ u : ↥(freqsF n e a b), u.val ∈ freqF n e a b x ∧ π u x = y ∧
      ¬ (u = v ∧ (x = i ∨ x = π v i))) i (π v i) := by
  classical
  have hπ_prop := (Finset.mem_filter.mp hπ).2
  let adjDel : Fin (4 * e) → Fin (4 * e) → Prop := fun x y =>
    ∃ u : ↥(freqsF n e a b), u.val ∈ freqF n e a b x ∧ π u x = y ∧ ¬ (u = v ∧ (x = i ∨ x = π v i))
  by_contra hnot
  let S := (Finset.univ : Finset (Fin (4 * e))).filter (fun k => Relation.EqvGen adjDel i k)
  have hiS : i ∈ S := by simp [S, Relation.EqvGen.refl]
  have hpiNotS : π v i ∉ S := by
    change ¬ Relation.EqvGen adjDel i (π v i) at hnot
    simp [S, hnot]
  have hsum0 : (∑ k ∈ S, ∑ u ∈ freqF n e a b k, u) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have ⟨ha, hb, hne⟩ := hab k
    have ⟨_, h2, h3⟩ := four_distinct ha hb hne
    simp only [freqF]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · rw [← add_assoc, z2_vec_add_self]
    · simp [h3.symm]
    · simp [hne, h2.symm]
  have hswap : (∑ k ∈ S, ∑ u ∈ freqF n e a b k, u) =
      ∑ u : ↥(freqsF n e a b), (S.filter (fun k => u.val ∈ freqF n e a b k)).card • u.val := by
    calc ∑ k ∈ S, ∑ u ∈ freqF n e a b k, u
        = ∑ k ∈ S, ∑ u : ↥(freqsF n e a b), if u.val ∈ freqF n e a b k then u.val else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_filter]
          refine (Finset.sum_bij (fun (u : ↥(freqsF n e a b)) _ => u.val) ?_ ?_ ?_ (fun _ _ => rfl)).symm
          · intro u hu; exact (Finset.mem_filter.mp hu).2
          · intro u1 _ u2 _ h; exact Subtype.ext h
          · intro w hw
            exact ⟨⟨w, Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hw⟩⟩, by simp [hw], rfl⟩
      _ = ∑ u : ↥(freqsF n e a b), ∑ k ∈ S, if u.val ∈ freqF n e a b k then u.val else 0 := Finset.sum_comm
      _ = ∑ u : ↥(freqsF n e a b), (S.filter (fun k => u.val ∈ freqF n e a b k)).card • u.val := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const]
  have hnsmul_even : ∀ (m : ℕ) (w : Fin n → ZMod 2), 2 ∣ m → m • w = 0 := by
    rintro m w ⟨t, rfl⟩
    ext c
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Pi.zero_apply]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_mul, zero_mul]
  have hother : ∀ u : ↥(freqsF n e a b), u ≠ v →
      (S.filter (fun k => u.val ∈ freqF n e a b k)).card • u.val = 0 := by
    intro u huv
    apply hnsmul_even
    refine two_dvd_of_fpf_invol (S.filter (fun k => u.val ∈ freqF n e a b k)) (π u) ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkS, huk⟩
      have hp := hπ_prop u k; rw [if_pos huk] at hp
      rw [Finset.mem_filter]
      refine ⟨?_, hp.2.1⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Relation.EqvGen.trans _ _ _ (Finset.mem_filter.mp hkS).2
        (Relation.EqvGen.rel _ _ ⟨u, huk, rfl, fun h => huv h.1⟩)⟩
    · intro k hk
      have huk := (Finset.mem_filter.mp hk).2
      have hp := hπ_prop u k; rw [if_pos huk] at hp
      exact hp.1
    · intro k hk
      have huk := (Finset.mem_filter.mp hk).2
      have hp := hπ_prop u k; rw [if_pos huk] at hp
      exact hp.2.2
  have hself : (S.filter (fun k => v.val ∈ freqF n e a b k)).card • v.val = v.val := by
    have hiT : i ∈ S.filter (fun k => v.val ∈ freqF n e a b k) := Finset.mem_filter.mpr ⟨hiS, hvi⟩
    let T' := (S.filter (fun k => v.val ∈ freqF n e a b k)).erase i
    have hdiv : 2 ∣ T'.card := by
      refine two_dvd_of_fpf_invol T' (π v) ?_ ?_ ?_
      · intro k hk
        rcases Finset.mem_erase.mp hk with ⟨hki, hkT⟩
        rcases Finset.mem_filter.mp hkT with ⟨hkS, hvk⟩
        have hp := hπ_prop v k; rw [if_pos hvk] at hp
        have hk_ne_pi : k ≠ π v i := fun heq => hpiNotS (heq ▸ hkS)
        have hpi_ne_i : π v k ≠ i := by
          intro heq
          have := congrArg (π v) heq
          rw [hp.2.2] at this
          exact hk_ne_pi this
        refine Finset.mem_erase.mpr ⟨hpi_ne_i, Finset.mem_filter.mpr ⟨?_, hp.2.1⟩⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Relation.EqvGen.trans _ _ _ (Finset.mem_filter.mp hkS).2
            (Relation.EqvGen.rel _ _ ⟨v, hvk, rfl, fun h => by
              rcases h.2 with rfl | rfl
              · exact hki rfl
              · exact hk_ne_pi rfl⟩)⟩
      · intro k hk
        have hvk := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
        have hp := hπ_prop v k; rw [if_pos hvk] at hp
        exact hp.1
      · intro k hk
        have hvk := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
        have hp := hπ_prop v k; rw [if_pos hvk] at hp
        exact hp.2.2
    have hcard : (S.filter (fun k => v.val ∈ freqF n e a b k)).card = T'.card + 1 :=
      (Finset.card_erase_add_one hiT).symm
    rw [hcard, add_nsmul, one_nsmul, hnsmul_even T'.card v.val hdiv, zero_add]
  rw [hswap, Finset.sum_eq_single v (fun u _ huv => hother u huv) (fun h => (h (Finset.mem_univ v)).elim),
    hself] at hsum0
  exact freqsF_nz n e a b hab v.val v.property hsum0

lemma exists_good_iff (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) :
    (0 < (goodF n e a b).card ↔
      (∀ v ∈ freqsF n e a b, 2 ∣ (rowsF n e a b v).card) ∧
      (∀ C ∈ compsOf (fun i j => ∃ v ∈ freqF n e a b i, v ∈ freqF n e a b j), 4 ∣ C.card)) := by
  classical
  have hcount := counting_identity n e a b hab
  let parts := compsOf (fun i j => ∃ v ∈ freqF n e a b i, v ∈ freqF n e a b j)
  constructor
  · intro hpos
    have hprod_pos : 0 < ∏ v ∈ freqsF n e a b, Nat.factorial ((rowsF n e a b v).card / 2) :=
      Finset.prod_pos fun v _ => Nat.factorial_pos _
    have hsum_pos : 0 < ∑ π ∈ pairsF n e a b, weightF n e a b π := by
      have h1 : 0 < 2 ^ (2 * e) * ∑ π ∈ pairsF n e a b, weightF n e a b π := by
        rw [← hcount]; exact Nat.mul_pos hpos hprod_pos
      exact Nat.pos_of_mul_pos_left h1
    obtain ⟨π, hπ, hw_pos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hsum_pos)
    have hπ_prop := (Finset.mem_filter.mp hπ).2
    refine ⟨fun v hv => ?_, fun C hC => ?_⟩
    · refine two_dvd_of_fpf_invol (rowsF n e a b v) (π ⟨v, hv⟩) ?_ ?_ ?_
      · intro i hi
        have hvi : v ∈ freqF n e a b i := (Finset.mem_filter.mp hi).2
        have hp := hπ_prop ⟨v, hv⟩ i; rw [if_pos hvi] at hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2.1⟩
      · intro i hi
        have hvi : v ∈ freqF n e a b i := (Finset.mem_filter.mp hi).2
        have hp := hπ_prop ⟨v, hv⟩ i; rw [if_pos hvi] at hp
        exact hp.1
      · intro i hi
        have hvi : v ∈ freqF n e a b i := (Finset.mem_filter.mp hi).2
        have hp := hπ_prop ⟨v, hv⟩ i; rw [if_pos hvi] at hp
        exact hp.2.2
    · let adj_π : Fin (4 * e) → Fin (4 * e) → Prop :=
        fun i j => ∃ v : ↥(freqsF n e a b), v.val ∈ freqF n e a b i ∧ π v i = j
      let adj_p : Fin (4 * e) → Fin (4 * e) → Prop :=
        fun i j => ∃ v ∈ freqF n e a b i, v ∈ freqF n e a b j
      have h4_π : ∀ D ∈ compsOf adj_π, 4 ∣ D.card := by
        by_contra hnot
        simp only [weightF, adj_π, if_neg hnot] at hw_pos
        exact hw_pos rfl
      have hrefine : ∀ x y, Relation.EqvGen adj_π x y → Relation.EqvGen adj_p x y := by
        intro x y h
        induction h with
        | rel x y hxy =>
          rcases hxy with ⟨v, hvx, rfl⟩
          have hp := hπ_prop v x; rw [if_pos hvx] at hp
          exact Relation.EqvGen.rel _ _ ⟨v.val, hvx, hp.2.1⟩
        | refl _ => exact Relation.EqvGen.refl _
        | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      let subCs := (compsOf adj_π).filter (fun D => D ⊆ C)
      have hbiUnion : subCs.biUnion id = C := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq, subCs]
        constructor
        · rintro ⟨D, ⟨_, hDC⟩, hxD⟩; exact hDC hxD
        · intro hxC
          refine ⟨compOf adj_π x, ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, ?_⟩,
            self_mem_compOf adj_π x⟩
          intro y hy
          rcases Finset.mem_image.mp hC with ⟨i0, _, rfl⟩
          exact (mem_compOf adj_p i0 y).mpr
            (Relation.EqvGen.trans _ _ _ ((mem_compOf adj_p i0 x).mp hxC)
              (hrefine x y ((mem_compOf adj_π x y).mp hy)))
      have hpw : Set.PairwiseDisjoint (subCs : Set (Finset (Fin (4 * e)))) id := by
        intro D1 hD1 D2 hD2 hne
        exact compOf_disjoint adj_π (Finset.mem_filter.mp hD1).1 (Finset.mem_filter.mp hD2).1 hne
      rw [← hbiUnion, Finset.card_biUnion hpw]
      exact Finset.dvd_sum fun D hD => h4_π D (Finset.mem_filter.mp hD).1
  · rintro ⟨heven, h4parts⟩
    have hpi_exists : ∀ v : ↥(freqsF n e a b),
        ∃ f : Fin (4 * e) → Fin (4 * e),
          ∀ i, if v.val ∈ freqF n e a b i then f i ≠ i ∧ v.val ∈ freqF n e a b (f i) ∧ f (f i) = i else f i = i := by
      intro v
      obtain ⟨f, hf⟩ := exists_fpf_invol_of_even (rowsF n e a b v.val) (heven v.val v.property)
      refine ⟨f, fun i => ?_⟩
      have h := hf i
      by_cases hv : v.val ∈ freqF n e a b i
      · have hr : i ∈ rowsF n e a b v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        rw [if_pos hr] at h
        rw [if_pos hv]
        exact ⟨h.1, (Finset.mem_filter.mp h.2.1).2, h.2.2⟩
      · have hr : i ∉ rowsF n e a b v.val := by simp [rowsF, hv]
        rw [if_neg hr] at h
        rw [if_neg hv]
        exact h
    choose π0 hπ0 using hpi_exists
    have hpairs_ne : (pairsF n e a b).Nonempty := ⟨π0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ0⟩⟩
    let adjOf : (↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e)) → Fin (4 * e) → Fin (4 * e) → Prop :=
      fun π i j => ∃ v : ↥(freqsF n e a b), v.val ∈ freqF n e a b i ∧ π v i = j
    obtain ⟨π, hπ, hmin⟩ := Finset.exists_min_image (pairsF n e a b) (fun π => (compsOf (adjOf π)).card) hpairs_ne
    have hπ_prop := (Finset.mem_filter.mp hπ).2
    have hcs_eq_parts : compsOf (adjOf π) = parts := by
      by_contra hne_parts
      have hex_edge : ∃ (v : ↥(freqsF n e a b)) (i j : Fin (4 * e)),
          v.val ∈ freqF n e a b i ∧ v.val ∈ freqF n e a b j ∧ ¬ Relation.EqvGen (adjOf π) i j := by
        by_contra hall
        push_neg at hall
        apply hne_parts
        have heqv_eq : ∀ x y, Relation.EqvGen (adjOf π) x y ↔
            Relation.EqvGen (fun a' b' => ∃ v ∈ freqF n e a b a', v ∈ freqF n e a b b') x y := by
          intro x y
          constructor
          · intro h
            induction h with
            | rel a' b' hab' =>
              rcases hab' with ⟨v, hva, rfl⟩
              have hp := hπ_prop v a'; rw [if_pos hva] at hp
              exact Relation.EqvGen.rel _ _ ⟨v.val, hva, hp.2.1⟩
            | refl _ => exact Relation.EqvGen.refl _
            | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
            | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
          · intro h
            induction h with
            | rel a' b' hab' =>
              rcases hab' with ⟨v, hva, hvb⟩
              exact hall ⟨v, Finset.mem_biUnion.mpr ⟨a', Finset.mem_univ a', hva⟩⟩ a' b' hva hvb
            | refl _ => exact Relation.EqvGen.refl _
            | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
            | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
        simp only [parts, compsOf]
        congr 1; funext i; ext j
        simp only [mem_compOf, heqv_eq]
      obtain ⟨v, i, j, hvi, hvj, hnot_eqv⟩ := hex_edge
      have hpi := hπ_prop v i; rw [if_pos hvi] at hpi
      have hpj := hπ_prop v j; rw [if_pos hvj] at hpj
      let i' := π v i
      let j' := π v j
      have h_i_ne_j : i ≠ j := fun h => hnot_eqv (by rw [h]; exact Relation.EqvGen.refl j)
      have h_i_ne_j' : i ≠ j' := fun h => hnot_eqv (by
        rw [h]; exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨v, hvj, rfl⟩))
      have h_i'_ne_j : i' ≠ j := fun h => hnot_eqv (by
        rw [← h]; exact Relation.EqvGen.rel _ _ ⟨v, hvi, rfl⟩)
      have h_i'_ne_j' : i' ≠ j' := fun h => hnot_eqv (by
        have h1 : Relation.EqvGen (adjOf π) i i' := Relation.EqvGen.rel _ _ ⟨v, hvi, rfl⟩
        have h2 : Relation.EqvGen (adjOf π) j' j := Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨v, hvj, rfl⟩)
        rw [h] at h1
        exact Relation.EqvGen.trans _ _ _ h1 h2)
      have h_i_ne_i' : i ≠ i' := hpi.1.symm
      have h_j_ne_j' : j ≠ j' := hpj.1.symm
      let π' : ↥(freqsF n e a b) → Fin (4 * e) → Fin (4 * e) := fun u k =>
        if u = v then
          if k = i then j
          else if k = j then i
          else if k = i' then j'
          else if k = j' then i'
          else π v k
        else π u k
      have hπ'_mem : π' ∈ pairsF n e a b := by
        rw [pairsF, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun u k => ?_⟩
        by_cases huv : u = v
        · subst huv
          have hvi' : u.val ∈ freqF n e a b i' := hpi.2.1
          have hvj' : u.val ∈ freqF n e a b j' := hpj.2.1
          by_cases hki : k = i
          · subst hki; simp [π', hvi, hvj, h_i_ne_j.symm, h_i_ne_j]
          · by_cases hkj : k = j
            · subst hkj; simp [π', hvi, hvj, h_i_ne_j, h_i_ne_j.symm]
            · by_cases hki' : k = i'
              · subst hki'
                simp [π', hvi', hvj', h_i_ne_i'.symm, h_i'_ne_j, h_i'_ne_j', h_i'_ne_j'.symm,
                  h_i_ne_j'.symm, h_j_ne_j'.symm]
              · by_cases hkj' : k = j'
                · subst hkj'
                  simp [π', hvi', hvj', h_i_ne_j'.symm, h_j_ne_j'.symm, h_i'_ne_j'.symm,
                    h_i_ne_i'.symm, h_i'_ne_j, h_i'_ne_j']
                · have hpk := hπ_prop u k
                  have hne_pk : π u k ≠ i ∧ π u k ≠ j ∧ π u k ≠ i' ∧ π u k ≠ j' := by
                    by_cases hku : u.val ∈ freqF n e a b k
                    · rw [if_pos hku] at hpk
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · intro h; have := congrArg (π u) h; rw [hpk.2.2] at this; exact hki' this
                      · intro h; have := congrArg (π u) h; rw [hpk.2.2] at this; exact hkj' this
                      · intro h; have := congrArg (π u) h; rw [hpk.2.2, hpi.2.2] at this; exact hki this
                      · intro h; have := congrArg (π u) h; rw [hpk.2.2, hpj.2.2] at this; exact hkj this
                    · rw [if_neg hku] at hpk; rw [hpk]; exact ⟨hki, hkj, hki', hkj'⟩
                  by_cases hku : u.val ∈ freqF n e a b k
                  · rw [if_pos hku] at hpk ⊢
                    simp [π', hki, hkj, hki', hkj', hne_pk.1, hne_pk.2.1, hne_pk.2.2.1, hne_pk.2.2.2, hpk]
                  · rw [if_neg hku] at hpk ⊢
                    simp [π', hki, hkj, hki', hkj', hpk]
        · simp [π', huv, hπ_prop u k]
      have hlift_i : Relation.EqvGen (adjOf π') i i' := by
        have hnb := no_bridge n e a b hab π hπ v i hvi
        have hsub : ∀ x y, Relation.EqvGen (fun a' b' => ∃ u : ↥(freqsF n e a b),
            u.val ∈ freqF n e a b a' ∧ π u a' = b' ∧ ¬ (u = v ∧ (a' = i ∨ a' = i'))) x y →
            Relation.EqvGen (adjOf π) i x →
            Relation.EqvGen (adjOf π') x y ∧ Relation.EqvGen (adjOf π) i y := by
          intro x y h
          induction h with
          | rel a' b' hab' =>
            intro hia
            rcases hab' with ⟨u, hua, rfl, hnotv⟩
            have hne_j : a' ≠ j := fun h => hnot_eqv (by rw [← h]; exact hia)
            have hne_j' : a' ≠ j' := fun h => hnot_eqv (by
              have h1 : Relation.EqvGen (adjOf π) i j' := h ▸ hia
              exact Relation.EqvGen.trans _ _ _ h1
                (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨v, hvj, rfl⟩)))
            have hpieq : π' u a' = π u a' := by
              by_cases huv : u = v
              · subst huv
                have hne_i : a' ≠ i := fun h => hnotv ⟨rfl, Or.inl h⟩
                have hne_i' : a' ≠ i' := fun h => hnotv ⟨rfl, Or.inr h⟩
                simp [π', hne_i, hne_j, hne_i', hne_j']
              · simp [π', huv]
            exact ⟨Relation.EqvGen.rel _ _ ⟨u, hua, hpieq⟩,
              Relation.EqvGen.trans _ _ _ hia (Relation.EqvGen.rel _ _ ⟨u, hua, rfl⟩)⟩
          | refl a' => intro hia; exact ⟨Relation.EqvGen.refl a', hia⟩
          | symm a' b' h ih =>
            intro hib
            have hia : Relation.EqvGen (adjOf π) i a' := by
              have hrev : ∀ p q, Relation.EqvGen (fun x y => ∃ u : ↥(freqsF n e a b),
                  u.val ∈ freqF n e a b x ∧ π u x = y ∧ ¬ (u = v ∧ (x = i ∨ x = i'))) p q →
                  Relation.EqvGen (adjOf π) p q := by
                intro p q hpq
                induction hpq with
                | rel x y hxy => rcases hxy with ⟨u, hux, rfl, _⟩; exact Relation.EqvGen.rel _ _ ⟨u, hux, rfl⟩
                | refl _ => exact Relation.EqvGen.refl _
                | symm _ _ _ ih' => exact Relation.EqvGen.symm _ _ ih'
                | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
              exact Relation.EqvGen.trans _ _ _ hib (Relation.EqvGen.symm _ _ (hrev a' b' h))
            exact ⟨Relation.EqvGen.symm _ _ (ih hia).1, hia⟩
          | trans a' b' c' _ _ ih1 ih2 =>
            intro hia
            have r1 := ih1 hia
            have r2 := ih2 r1.2
            exact ⟨Relation.EqvGen.trans _ _ _ r1.1 r2.1, r2.2⟩
        exact (hsub i i' hnb (Relation.EqvGen.refl i)).1
      have hlift_j : Relation.EqvGen (adjOf π') j j' := by
        have hnb := no_bridge n e a b hab π hπ v j hvj
        have hsub : ∀ x y, Relation.EqvGen (fun a' b' => ∃ u : ↥(freqsF n e a b),
            u.val ∈ freqF n e a b a' ∧ π u a' = b' ∧ ¬ (u = v ∧ (a' = j ∨ a' = j'))) x y →
            Relation.EqvGen (adjOf π) j x →
            Relation.EqvGen (adjOf π') x y ∧ Relation.EqvGen (adjOf π) j y := by
          intro x y h
          induction h with
          | rel a' b' hab' =>
            intro hja
            rcases hab' with ⟨u, hua, rfl, hnotv⟩
            have hne_i : a' ≠ i := fun h => hnot_eqv (Relation.EqvGen.symm _ _ (by rw [← h]; exact hja))
            have hne_i' : a' ≠ i' := fun h => hnot_eqv (by
              have h1 : Relation.EqvGen (adjOf π) j i' := h ▸ hja
              exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨v, hvi, rfl⟩)
                (Relation.EqvGen.symm _ _ h1))
            have hpieq : π' u a' = π u a' := by
              by_cases huv : u = v
              · subst huv
                have hne_j : a' ≠ j := fun h => hnotv ⟨rfl, Or.inl h⟩
                have hne_j' : a' ≠ j' := fun h => hnotv ⟨rfl, Or.inr h⟩
                simp [π', hne_i, hne_j, hne_i', hne_j']
              · simp [π', huv]
            exact ⟨Relation.EqvGen.rel _ _ ⟨u, hua, hpieq⟩,
              Relation.EqvGen.trans _ _ _ hja (Relation.EqvGen.rel _ _ ⟨u, hua, rfl⟩)⟩
          | refl a' => intro hja; exact ⟨Relation.EqvGen.refl a', hja⟩
          | symm a' b' h ih =>
            intro hjb
            have hja : Relation.EqvGen (adjOf π) j a' := by
              have hrev : ∀ p q, Relation.EqvGen (fun x y => ∃ u : ↥(freqsF n e a b),
                  u.val ∈ freqF n e a b x ∧ π u x = y ∧ ¬ (u = v ∧ (x = j ∨ x = j'))) p q →
                  Relation.EqvGen (adjOf π) p q := by
                intro p q hpq
                induction hpq with
                | rel x y hxy => rcases hxy with ⟨u, hux, rfl, _⟩; exact Relation.EqvGen.rel _ _ ⟨u, hux, rfl⟩
                | refl _ => exact Relation.EqvGen.refl _
                | symm _ _ _ ih' => exact Relation.EqvGen.symm _ _ ih'
                | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
              exact Relation.EqvGen.trans _ _ _ hjb (Relation.EqvGen.symm _ _ (hrev a' b' h))
            exact ⟨Relation.EqvGen.symm _ _ (ih hja).1, hja⟩
          | trans a' b' c' _ _ ih1 ih2 =>
            intro hja
            have r1 := ih1 hja
            have r2 := ih2 r1.2
            exact ⟨Relation.EqvGen.trans _ _ _ r1.1 r2.1, r2.2⟩
        exact (hsub j j' hnb (Relation.EqvGen.refl j)).1
      have hlift_all : ∀ x y, Relation.EqvGen (adjOf π) x y → Relation.EqvGen (adjOf π') x y := by
        intro x y h
        induction h with
        | rel x y hxy =>
          rcases hxy with ⟨u, hux, rfl⟩
          by_cases huv : u = v
          · subst huv
            by_cases hxi : x = i
            · subst hxi; exact hlift_i
            · by_cases hxj : x = j
              · subst hxj; exact hlift_j
              · by_cases hxi' : x = i'
                · subst hxi'; rw [hpi.2.2]; exact Relation.EqvGen.symm _ _ hlift_i
                · by_cases hxj' : x = j'
                  · subst hxj'; rw [hpj.2.2]; exact Relation.EqvGen.symm _ _ hlift_j
                  · refine Relation.EqvGen.rel _ _ ⟨u, hux, ?_⟩
                    simp [π', hxi, hxj, hxi', hxj']
          · refine Relation.EqvGen.rel _ _ ⟨u, hux, ?_⟩
            simp [π', huv]
        | refl _ => exact Relation.EqvGen.refl _
        | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      have hij' : Relation.EqvGen (adjOf π') i j :=
        Relation.EqvGen.rel _ _ ⟨v, hvi, by simp [π']⟩
      let mapC : Finset (Fin (4 * e)) → Finset (Fin (4 * e)) := fun C =>
        if hC : C.Nonempty then compOf (adjOf π') hC.choose else ∅
      have hmap_comp : ∀ k : Fin (4 * e), mapC (compOf (adjOf π) k) = compOf (adjOf π') k := by
        intro k
        have hne : (compOf (adjOf π) k).Nonempty := ⟨k, self_mem_compOf _ k⟩
        simp only [mapC, dif_pos hne]
        exact compOf_eq_of_eqv (adjOf π')
          (Relation.EqvGen.symm _ _ (hlift_all k hne.choose ((mem_compOf _ k _).mp hne.choose_spec)))
      have hsurj_img : (compsOf (adjOf π)).image mapC = compsOf (adjOf π') := by
        ext D
        simp only [Finset.mem_image, compsOf]
        constructor
        · rintro ⟨C, ⟨k, _, rfl⟩, rfl⟩
          exact ⟨k, Finset.mem_univ k, (hmap_comp k).symm⟩
        · rintro ⟨k, _, rfl⟩
          exact ⟨compOf (adjOf π) k, ⟨k, Finset.mem_univ k, rfl⟩, hmap_comp k⟩
      have hCi_mem : compOf (adjOf π) i ∈ compsOf (adjOf π) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hCj_mem : compOf (adjOf π) j ∈ compsOf (adjOf π) :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      have hCi_ne_Cj : compOf (adjOf π) i ≠ compOf (adjOf π) j := by
        intro heq
        exact hnot_eqv ((compOf_eq_iff (adjOf π) i j).mp heq)
      have hlt_card : (compsOf (adjOf π')).card < (compsOf (adjOf π)).card := by
        rw [← hsurj_img]
        have hsub : ((compsOf (adjOf π)).erase (compOf (adjOf π) j)).image mapC =
            (compsOf (adjOf π)).image mapC := by
          ext D
          simp only [Finset.mem_image, Finset.mem_erase]
          constructor
          · rintro ⟨C, ⟨_, hC⟩, rfl⟩; exact ⟨C, hC, rfl⟩
          · rintro ⟨C, hC, rfl⟩
            by_cases hCj : C = compOf (adjOf π) j
            · subst hCj
              refine ⟨compOf (adjOf π) i, ⟨hCi_ne_Cj, hCi_mem⟩, ?_⟩
              rw [hmap_comp i, hmap_comp j]
              exact compOf_eq_of_eqv (adjOf π') hij'
            · exact ⟨C, ⟨hCj, hC⟩, rfl⟩
        rw [← hsub]
        have hle1 := Finset.card_image_le (s := (compsOf (adjOf π)).erase (compOf (adjOf π) j)) (f := mapC)
        have hlt2 : ((compsOf (adjOf π)).erase (compOf (adjOf π) j)).card < (compsOf (adjOf π)).card :=
          Finset.card_erase_lt_of_mem hCj_mem
        omega
      have hmin' := hmin π' hπ'_mem
      omega
    have hw_pos : 0 < weightF n e a b π := by
      simp only [weightF]
      change 0 < if ∀ C ∈ compsOf (adjOf π), 4 ∣ C.card then 2 ^ (compsOf (adjOf π)).card else 0
      rw [hcs_eq_parts, if_pos h4parts]
      positivity
    have hsum_pos : 0 < ∑ ρ ∈ pairsF n e a b, weightF n e a b ρ :=
      lt_of_lt_of_le hw_pos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hπ)
    have hrhs_pos : 0 < 2 ^ (2 * e) * ∑ ρ ∈ pairsF n e a b, weightF n e a b ρ :=
      Nat.mul_pos (by positivity) hsum_pos
    rw [← hcount] at hrhs_pos
    exact Nat.pos_of_mul_pos_right hrhs_pos

end MainProof

theorem main : ∀ (n e : Nat),
  let F := ZMod 2
  let W := Fin n → F
  let I := Fin (4*e)
  ∀ a b : I → W,
    (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let freq := fun (i : I) => ({a i, b i, a i+b i} : Finset W)
    let freqs := (Finset.univ : Finset I).biUnion freq
    let rows := fun v : W => (Finset.univ : Finset I).filter (fun i => v ∈ freq i)
    let comps := fun (adj : I → I → Prop) => (Finset.univ : Finset I).image (fun i =>
      (Finset.univ : Finset I).filter (fun j => @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
    let parts := comps (fun i j => ∃ v ∈ freq i, v ∈ freq j)
    let good := (Finset.univ : Finset ((I → W) × (I → F))).filter (fun p =>
      ∀ x : W, ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (p.1 i) x+p.2 i ≠ dotProduct (a i) x*dotProduct (b i) x)).card ≤ e)
    let pairs := (Finset.univ : Finset (↥freqs → I → I)).filter (fun π =>
      ∀ v i, if v.val ∈ freq i then π v i ≠ i ∧ v.val ∈ freq (π v i) ∧ π v (π v i) = i else π v i = i)
    let weight := fun (π : ↥freqs → I → I) =>
      let cs := comps (fun i j => ∃ v : ↥freqs, v.val ∈ freq i ∧ π v i = j)
      if ∀ C ∈ cs, 4 ∣ C.card then 2^cs.card else 0
    (0 < good.card ↔ (∀ v ∈ freqs, 2 ∣ (rows v).card) ∧ (∀ C ∈ parts, 4 ∣ C.card)) ∧
      good.card * (∏ v ∈ freqs, Nat.factorial ((rows v).card / 2)) =
        2^(2*e) * ∑ π ∈ pairs, weight π :=
  fun n e a b hab => ⟨exists_good_iff n e a b hab, counting_identity n e a b hab⟩

end PEqualNP.Outside.L_lib_956

theorem PEqualNP.Outside.L_lib_956 : (∀ (n e : Nat),
  let F := ZMod 2
  let W := Fin n → F
  let I := Fin (4*e)
  ∀ a b : I → W,
    (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let freq := fun (i : I) => ({a i, b i, a i+b i} : Finset W)
    let freqs := (Finset.univ : Finset I).biUnion freq
    let rows := fun v : W => (Finset.univ : Finset I).filter (fun i => v ∈ freq i)
    let comps := fun (adj : I → I → Prop) => (Finset.univ : Finset I).image (fun i =>
      (Finset.univ : Finset I).filter (fun j => @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
    let parts := comps (fun i j => ∃ v ∈ freq i, v ∈ freq j)
    let good := (Finset.univ : Finset ((I → W) × (I → F))).filter (fun p =>
      ∀ x : W, ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (p.1 i) x+p.2 i ≠ dotProduct (a i) x*dotProduct (b i) x)).card ≤ e)
    let pairs := (Finset.univ : Finset (↥freqs → I → I)).filter (fun π =>
      ∀ v i, if v.val ∈ freq i then π v i ≠ i ∧ v.val ∈ freq (π v i) ∧ π v (π v i) = i else π v i = i)
    let weight := fun (π : ↥freqs → I → I) =>
      let cs := comps (fun i j => ∃ v : ↥freqs, v.val ∈ freq i ∧ π v i = j)
      if ∀ C ∈ cs, 4 ∣ C.card then 2^cs.card else 0
    (0 < good.card ↔ (∀ v ∈ freqs, 2 ∣ (rows v).card) ∧ (∀ C ∈ parts, 4 ∣ C.card)) ∧
      good.card * (∏ v ∈ freqs, Nat.factorial ((rows v).card / 2)) =
        2^(2*e) * ∑ π ∈ pairs, weight π) :=
  PEqualNP.Outside.L_lib_956.main

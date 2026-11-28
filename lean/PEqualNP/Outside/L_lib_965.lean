import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_965_aux

abbrev F2 := ZMod 2

def chi {n : Nat} (v x : Fin n → F2) : Int :=
  if dotProduct v x = 0 then 1 else -1

lemma zmod2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma zmod2_one_add_one : (1 : F2) + 1 = 0 := by decide

lemma chi_zero {n : Nat} (x : Fin n → F2) : chi (0 : Fin n → F2) x = 1 := by
  simp [chi]

lemma chi_add {n : Nat} (u v x : Fin n → F2) : chi (u + v) x = chi u x * chi v x := by
  unfold chi
  rw [add_dotProduct]
  rcases zmod2_cases (dotProduct u x) with hu | hu <;>
  rcases zmod2_cases (dotProduct v x) with hv | hv <;>
  simp [hu, hv, zmod2_one_add_one]

lemma sum_chi_eq_zero {n : Nat} {v : Fin n → F2} (hv : v ≠ 0) :
    (∑ x : Fin n → F2, chi v x) = 0 := by
  have hk : ∃ k : Fin n, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  rcases hk with ⟨k, hk⟩
  have hk1 : v k = 1 := by
    rcases zmod2_cases (v k) with h0 | h1
    · exact absurd h0 hk
    · exact h1
  let e : (Fin n → F2) ≃ (Fin n → F2) := Equiv.addRight (Pi.single k (1 : F2))
  have hshift : ∀ x : Fin n → F2, chi v (e x) = - chi v x := by
    intro x
    change chi v (x + Pi.single k 1) = - chi v x
    unfold chi
    rw [dotProduct_add, dotProduct_single, hk1, mul_one]
    rcases zmod2_cases (dotProduct v x) with h | h <;>
    simp [h, zmod2_one_add_one]
  have hsum : (∑ x : Fin n → F2, chi v (e x)) = ∑ x : Fin n → F2, chi v x :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  simp_rw [hshift, Finset.sum_neg_distrib] at hsum
  omega

def errVal {n : Nat} (a b P : Fin n → F2) (d : F2) (x : Fin n → F2) : Int :=
  if dotProduct P x + d ≠ dotProduct a x * dotProduct b x then 1 else 0

lemma four_mul_errVal {n : Nat} (a b P : Fin n → F2) (d : F2) (x : Fin n → F2) :
    4 * errVal a b P d x =
      2 - (if d = 0 then (1 : Int) else -1) *
        (chi P x + chi (P + a) x + chi (P + b) x - chi (P + a + b) x) := by
  unfold errVal chi
  simp only [add_dotProduct]
  rcases zmod2_cases (dotProduct P x) with hP | hP <;>
  rcases zmod2_cases (dotProduct a x) with ha | ha <;>
  rcases zmod2_cases (dotProduct b x) with hb | hb <;>
  rcases zmod2_cases d with hd | hd <;>
  simp [hP, ha, hb, hd, zmod2_one_add_one]

lemma zmod2_add_self {n : Nat} (v : Fin n → F2) : v + v = 0 := by
  funext i
  rcases zmod2_cases (v i) with h | h <;> simp [h, zmod2_one_add_one]

lemma zmod2_add_eq_zero {n : Nat} {u v : Fin n → F2} : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    have := congrArg (· + v) h
    simpa [add_assoc, zmod2_add_self] using this
  · intro h
    subst h
    exact zmod2_add_self u

lemma card_vec_int (n : Nat) : (Fintype.card (Fin n → F2) : Int) = (2 : Int) ^ n := by
  simp

lemma sum_four_errVal_ge {n : Nat} {a b P : Fin n → F2} {d : F2}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ((2 : Int) ^ n) ≤ ∑ x : Fin n → F2, 4 * errVal a b P d x := by
  have hN : (0 : Int) ≤ (2 : Int) ^ n := by positivity
  have h1 : (∑ x : Fin n → F2, 4 * errVal a b P d x) =
      2 * (2 : Int) ^ n - (if d = 0 then (1 : Int) else -1) *
        ((∑ x, chi P x) + (∑ x, chi (P + a) x) + (∑ x, chi (P + b) x) -
          (∑ x, chi (P + a + b) x)) := by
    simp_rw [four_mul_errVal]
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  rw [h1]
  have hsum_chi : ∀ u : Fin n → F2,
      (∑ x : Fin n → F2, chi u x) = if u = 0 then (2 : Int) ^ n else 0 := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [chi_zero]
    · simp [hu, sum_chi_eq_zero hu]
  simp_rw [hsum_chi]
  by_cases hP : P = 0
  · subst hP
    have hPa : (0 : Fin n → F2) + a ≠ 0 := by simpa using ha
    have hPb : (0 : Fin n → F2) + b ≠ 0 := by simpa using hb
    have hPab : (0 : Fin n → F2) + a + b ≠ 0 := by simpa [zmod2_add_eq_zero] using hab
    simp [hPa, hPb, hPab]
    split_ifs <;> omega
  · by_cases hPa : P + a = 0
    · have hPb : P + b ≠ 0 := by
        intro h; exact hab ((zmod2_add_eq_zero.mp hPa).symm.trans (zmod2_add_eq_zero.mp h))
      have hPab : P + a + b ≠ 0 := by rw [hPa, zero_add]; exact hb
      simp [hP, hPa, hPb, hPab]
      split_ifs <;> omega
    · by_cases hPb : P + b = 0
      · have hPab : P + a + b ≠ 0 := by rw [add_right_comm, hPb, zero_add]; exact ha
        simp [hP, hPa, hPb, hPab]
        split_ifs <;> omega
      · by_cases hPab : P + a + b = 0
        · simp [hP, hPa, hPb, hPab]
          split_ifs <;> omega
        · simp [hP, hPa, hPb, hPab]

lemma sum_four_errVal_eq_iff {n : Nat} {a b P : Fin n → F2} {d : F2}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (heq : ∑ x : Fin n → F2, 4 * errVal a b P d x = (2 : Int) ^ n) :
    ∃ s1 s2 : Int, (s1 = 1 ∨ s1 = -1) ∧ (s2 = 1 ∨ s2 = -1) ∧
      ∀ x : Fin n → F2, 4 * errVal a b P d x =
        1 + s1 * chi a x + s2 * chi b x + (s1 * s2) * chi (a + b) x := by
  have hNpos : (0 : Int) < (2 : Int) ^ n := by positivity
  have h1 : (∑ x : Fin n → F2, 4 * errVal a b P d x) =
      2 * (2 : Int) ^ n - (if d = 0 then (1 : Int) else -1) *
        ((∑ x, chi P x) + (∑ x, chi (P + a) x) + (∑ x, chi (P + b) x) -
          (∑ x, chi (P + a + b) x)) := by
    simp_rw [four_mul_errVal]
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  have hsum_chi : ∀ u : Fin n → F2,
      (∑ x : Fin n → F2, chi u x) = if u = 0 then (2 : Int) ^ n else 0 := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [chi_zero]
    · simp [hu, sum_chi_eq_zero hu]
  rw [h1] at heq
  simp_rw [hsum_chi] at heq
  by_cases hP : P = 0
  · subst hP
    have hPa : (0 : Fin n → F2) + a ≠ 0 := by simpa using ha
    have hPb : (0 : Fin n → F2) + b ≠ 0 := by simpa using hb
    have hPab : (0 : Fin n → F2) + a + b ≠ 0 := by simpa [zmod2_add_eq_zero] using hab
    simp [hPa, hPb, hPab] at heq
    have hd : d = 0 := by
      by_contra hne; simp [hne] at heq; omega
    subst hd
    refine ⟨-1, -1, Or.inr rfl, Or.inr rfl, ?_⟩
    intro x
    rw [four_mul_errVal]
    simp [chi_zero]
    ring
  · by_cases hPa : P + a = 0
    · have hPb : P + b ≠ 0 := by
        intro h; exact hab ((zmod2_add_eq_zero.mp hPa).symm.trans (zmod2_add_eq_zero.mp h))
      have hPab : P + a + b ≠ 0 := by rw [hPa, zero_add]; exact hb
      simp [hP, hPa, hPb, hPab] at heq
      have hd : d = 0 := by
        by_contra hne; simp [hne] at heq; omega
      subst hd
      have hPeq : P = a := zmod2_add_eq_zero.mp hPa
      subst hPeq
      refine ⟨-1, 1, Or.inr rfl, Or.inl rfl, ?_⟩
      intro x
      rw [four_mul_errVal]
      simp [zmod2_add_self, chi_zero]
      ring
    · by_cases hPb : P + b = 0
      · have hPab : P + a + b ≠ 0 := by rw [add_right_comm, hPb, zero_add]; exact ha
        simp [hP, hPa, hPb, hPab] at heq
        have hd : d = 0 := by
          by_contra hne; simp [hne] at heq
        subst hd
        have hPeq : P = b := zmod2_add_eq_zero.mp hPb
        refine ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
        intro x
        rw [four_mul_errVal, hPeq]
        have hba : b + a = a + b := add_comm b a
        have habb : a + b + b = a := by rw [add_assoc, zmod2_add_self, add_zero]
        rw [zmod2_add_self, hba, habb, chi_zero]
        simp
        ring
      · by_cases hPab : P + a + b = 0
        · simp [hP, hPa, hPb, hPab] at heq
          have hd : d ≠ 0 := by
            intro h0; simp [h0] at heq
          have hPeq : P = a + b := by
            have h' : P + (a + b) = 0 := by simpa [add_assoc] using hPab
            exact zmod2_add_eq_zero.mp h'
          refine ⟨1, 1, Or.inl rfl, Or.inl rfl, ?_⟩
          intro x
          rw [four_mul_errVal, hPeq]
          have h1' : a + b + a = b := by rw [add_right_comm, zmod2_add_self, zero_add]
          have h2' : a + b + b = a := by rw [add_assoc, zmod2_add_self, add_zero]
          rw [h1', h2', zmod2_add_self, chi_zero]
          simp [hd]
          ring
        · simp [hP, hPa, hPb, hPab] at heq

def freqOf {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (i : Fin (4 * e)) :
    Finset (Fin n → F2) :=
  {a i, b i, a i + b i}

def adjOf {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (i j : Fin (4 * e)) : Prop :=
  ∃ v ∈ freqOf a b i, v ∈ freqOf a b j

noncomputable def partsOf {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) : Finset (Finset (Fin (4 * e))) :=
  (Finset.univ : Finset (Fin (4 * e))).image (fun i =>
    (Finset.univ : Finset (Fin (4 * e))).filter (fun j =>
      @decide (Relation.EqvGen (adjOf a b) i j) (Classical.propDecidable _) = true))

def spanOf {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (S : Finset (Fin (4 * e))) :
    Submodule F2 (Fin n → F2) :=
  Submodule.span F2 (↑(S.image a ∪ S.image b) : Set (Fin n → F2))

noncomputable def rkOf {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (S : Finset (Fin (4 * e))) : Nat :=
  Module.finrank F2 (spanOf a b S)

lemma mem_partsOf_iff {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)} {C : Finset (Fin (4 * e))} :
    C ∈ partsOf a b ↔ ∃ i : Fin (4 * e),
      C = Finset.univ.filter (fun j =>
        @decide (Relation.EqvGen (adjOf a b) i j) (Classical.propDecidable _) = true) := by
  simp [partsOf, eq_comm]

lemma partsOf_nonempty {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) : C.Nonempty := by
  rcases mem_partsOf_iff.mp hC with ⟨i, rfl⟩
  exact ⟨i, by simp [Relation.EqvGen.refl]⟩

lemma partsOf_closed {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) {i j : Fin (4 * e)}
    (hi : i ∈ C) (hadj : adjOf a b i j) : j ∈ C := by
  rcases mem_partsOf_iff.mp hC with ⟨r, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi ⊢
  exact Relation.EqvGen.trans r i j hi (Relation.EqvGen.rel i j hadj)

lemma partsOf_eqv {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) {i j : Fin (4 * e)}
    (hi : i ∈ C) (hj : j ∈ C) : Relation.EqvGen (adjOf a b) i j := by
  rcases mem_partsOf_iff.mp hC with ⟨r, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi hj
  exact Relation.EqvGen.trans i r j (Relation.EqvGen.symm r i hi) hj

lemma partsOf_pairwiseDisjoint {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) :
    (partsOf a b : Set (Finset (Fin (4 * e)))).PairwiseDisjoint id := by
  intro C1 hC1 C2 hC2 hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx1 hx2
  apply hne
  rcases mem_partsOf_iff.mp hC1 with ⟨r1, rfl⟩
  rcases mem_partsOf_iff.mp hC2 with ⟨r2, rfl⟩
  ext j
  simp only [id_eq, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx1 hx2 ⊢
  have h12 : Relation.EqvGen (adjOf a b) r1 r2 :=
    Relation.EqvGen.trans r1 x r2 hx1 (Relation.EqvGen.symm r2 x hx2)
  exact ⟨fun h => Relation.EqvGen.trans r2 r1 j (Relation.EqvGen.symm r1 r2 h12) h,
         fun h => Relation.EqvGen.trans r1 r2 j h12 h⟩

lemma partsOf_biUnion {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) :
    (partsOf a b).biUnion id = Finset.univ := by
  ext j
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  refine ⟨Finset.univ.filter (fun k =>
    @decide (Relation.EqvGen (adjOf a b) j k) (Classical.propDecidable _) = true), ?_, ?_⟩
  · exact mem_partsOf_iff.mpr ⟨j, rfl⟩
  · simp [Relation.EqvGen.refl]

lemma partsOf_sum_card {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) :
    (∑ C ∈ partsOf a b, C.card) = 4 * e := by
  have h := Finset.card_biUnion (s := partsOf a b) (t := id) (by
    intro x hx y hy hne
    exact partsOf_pairwiseDisjoint a b hx hy hne)
  rw [partsOf_biUnion] at h
  simpa using h.symm

lemma eligible_signs {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (happrox : ∃ (P : Fin (4 * e) → (Fin n → F2)) (d : Fin (4 * e) → F2), ∀ x : Fin n → F2,
      ((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
        dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ e) :
    ∃ s1 s2 : Fin (4 * e) → Int,
      (∀ i, s1 i = 1 ∨ s1 i = -1) ∧
      (∀ i, s2 i = 1 ∨ s2 i = -1) ∧
      (∀ v : Fin n → F2, v ≠ 0 →
        (∑ i : Fin (4 * e),
          ((if a i = v then s1 i else 0) +
          (if b i = v then s2 i else 0) +
          (if a i + b i = v then s1 i * s2 i else 0))) = 0) := by
  rcases happrox with ⟨P, d, hbound⟩
  have hNpos : (0 : Int) < (2 : Int) ^ n := by positivity
  have hx_le : ∀ x : Fin n → F2, (∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) ≤ 4 * (e : Int) := by
    intro x
    have hcard : (∑ i : Fin (4 * e), errVal (a i) (b i) (P i) (d i) x) =
        (((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
          dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card : Int) := by
      unfold errVal
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [← Finset.mul_sum, hcard]
    have hb := hbound x
    omega
  have hi_ge : ∀ i : Fin (4 * e), (2 : Int) ^ n ≤ ∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x := by
    intro i
    rcases hnondeg i with ⟨ha, hb, hab⟩
    exact sum_four_errVal_ge ha hb hab
  have hswap : (∑ x : Fin n → F2, ∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) =
      ∑ i : Fin (4 * e), ∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x :=
    Finset.sum_comm
  have hlow : (4 * e : Int) * (2 : Int) ^ n ≤
      ∑ i : Fin (4 * e), ∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x := by
    calc (4 * e : Int) * (2 : Int) ^ n
        = ∑ _i : Fin (4 * e), (2 : Int) ^ n := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i : Fin (4 * e), ∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x :=
          Finset.sum_le_sum (fun i _ => hi_ge i)
  have hhigh : (∑ x : Fin n → F2, ∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) ≤
      (4 * e : Int) * (2 : Int) ^ n := by
    calc (∑ x : Fin n → F2, ∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x)
        ≤ ∑ _x : Fin n → F2, (4 * e : Int) := Finset.sum_le_sum (fun x _ => hx_le x)
      _ = (4 * e : Int) * (2 : Int) ^ n := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have htot_i : (∑ i : Fin (4 * e), ∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x) =
      (4 * e : Int) * (2 : Int) ^ n := by omega
  have htot_x : (∑ x : Fin n → F2, ∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) =
      (4 * e : Int) * (2 : Int) ^ n := by omega
  have hi_eq : ∀ i : Fin (4 * e), (∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x) = (2 : Int) ^ n := by
    intro i
    by_contra hne
    have hlt : (2 : Int) ^ n < ∑ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x :=
      lt_of_le_of_ne (hi_ge i) (Ne.symm hne)
    have hstrict : (∑ _j : Fin (4 * e), (2 : Int) ^ n) <
        ∑ j : Fin (4 * e), ∑ x : Fin n → F2, 4 * errVal (a j) (b j) (P j) (d j) x :=
      Finset.sum_lt_sum (fun j _ => hi_ge j) ⟨i, Finset.mem_univ i, hlt⟩
    simp [Finset.sum_const, nsmul_eq_mul] at hstrict
    omega
  have hx_eq : ∀ x : Fin n → F2, (∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) = 4 * (e : Int) := by
    intro x
    by_contra hne
    have hlt : (∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) < 4 * (e : Int) :=
      lt_of_le_of_ne (hx_le x) hne
    have hstrict : (∑ y : Fin n → F2, ∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) y) <
        ∑ _y : Fin n → F2, (4 * e : Int) :=
      Finset.sum_lt_sum (fun y _ => hx_le y) ⟨x, Finset.mem_univ x, hlt⟩
    simp [Finset.sum_const, nsmul_eq_mul] at hstrict
    linarith
  have hex : ∀ i : Fin (4 * e), ∃ s1 s2 : Int, (s1 = 1 ∨ s1 = -1) ∧ (s2 = 1 ∨ s2 = -1) ∧
      ∀ x : Fin n → F2, 4 * errVal (a i) (b i) (P i) (d i) x =
        1 + s1 * chi (a i) x + s2 * chi (b i) x + (s1 * s2) * chi (a i + b i) x := by
    intro i
    rcases hnondeg i with ⟨ha, hb, hab⟩
    exact sum_four_errVal_eq_iff ha hb hab (hi_eq i)
  choose s1 s2 hs1 hs2 hform using hex
  refine ⟨s1, s2, hs1, hs2, ?_⟩
  intro v hv
  have h0 : (∑ x : Fin n → F2, (∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) * chi v x) = 0 := by
    simp_rw [hx_eq, ← Finset.mul_sum, sum_chi_eq_zero hv, mul_zero]
  have hsum_chi_eq : ∀ u : Fin n → F2,
      (∑ x : Fin n → F2, chi u x * chi v x) = if u = v then (2 : Int) ^ n else 0 := by
    intro u
    simp_rw [← chi_add]
    by_cases huv : u = v
    · subst huv; simp [zmod2_add_self, chi_zero]
    · have hne0 : u + v ≠ 0 := fun h => huv (zmod2_add_eq_zero.mp h)
      simp [huv, sum_chi_eq_zero hne0]
  have h1 : (∑ x : Fin n → F2, (∑ i : Fin (4 * e), 4 * errVal (a i) (b i) (P i) (d i) x) * chi v x) =
      (∑ i : Fin (4 * e),
        ((if a i = v then s1 i else 0) +
        (if b i = v then s2 i else 0) +
        (if a i + b i = v then s1 i * s2 i else 0))) * (2 : Int) ^ n := by
    simp_rw [hform, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hexp : ∀ x : Fin n → F2,
        (1 + s1 i * chi (a i) x + s2 i * chi (b i) x + s1 i * s2 i * chi (a i + b i) x) * chi v x =
        chi v x + s1 i * (chi (a i) x * chi v x) + s2 i * (chi (b i) x * chi v x) +
          (s1 i * s2 i) * (chi (a i + b i) x * chi v x) := fun x => by ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, sum_chi_eq_zero hv, hsum_chi_eq]
    split_ifs <;> ring
  rw [h1] at h0
  exact (mul_eq_zero.mp h0).resolve_right (ne_of_gt hNpos)

lemma comp_parity_and_div4 {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (s1 s2 : Fin (4 * e) → Int)
    (hs1 : ∀ i, s1 i = 1 ∨ s1 i = -1)
    (hs2 : ∀ i, s2 i = 1 ∨ s2 i = -1)
    (hbal : ∀ v : Fin n → F2, v ≠ 0 →
      (∑ i : Fin (4 * e),
        ((if a i = v then s1 i else 0) +
        (if b i = v then s2 i else 0) +
        (if a i + b i = v then s1 i * s2 i else 0))) = 0)
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) :
    (∀ v : Fin n → F2, Even (C.filter (fun i => v ∈ freqOf a b i)).card) ∧ 4 ∣ C.card := by
  let sgn : Fin (4 * e) → (Fin n → F2) → Int := fun i v =>
    (if a i = v then s1 i else 0) +
    (if b i = v then s2 i else 0) +
    (if a i + b i = v then s1 i * s2 i else 0)
  have hsgn_val : ∀ i v,
      (v ∈ freqOf a b i → (sgn i v = 1 ∨ sgn i v = -1)) ∧
      (v ∉ freqOf a b i → sgn i v = 0) := by
    intro i v
    rcases hnondeg i with ⟨ha, hb, hab⟩
    have h1 : a i ≠ a i + b i := fun h => hb (by have := congrArg (a i + ·) h.symm; simpa [← add_assoc, zmod2_add_self] using this)
    have h2 : b i ≠ a i + b i := fun h => ha (by have := congrArg (· + b i) h.symm; simpa [add_assoc, zmod2_add_self] using this)
    constructor
    · intro hv
      simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · simp [sgn, hab.symm, h1.symm]; exact hs1 i
      · simp [sgn, hab, h2.symm]; exact hs2 i
      · simp [sgn, h1, h2]
        rcases hs1 i with h | h <;> rcases hs2 i with h' | h' <;> simp [h, h']
    · intro hv
      simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      rcases hv with ⟨hva, hvb, hvab⟩
      simp [sgn, Ne.symm hva, Ne.symm hvb, Ne.symm hvab]
  have hcomp_bal : ∀ v : Fin n → F2, (∑ i ∈ C, sgn i v) = 0 := by
    intro v
    by_cases hv0 : v = 0
    · apply Finset.sum_eq_zero
      intro i _
      apply (hsgn_val i v).2
      rcases hnondeg i with ⟨ha, hb, hab⟩
      subst hv0
      simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha.symm, hb.symm, by intro h; exact hab (zmod2_add_eq_zero.mp h.symm)⟩
    · by_cases hex : ∃ i ∈ C, v ∈ freqOf a b i
      · rcases hex with ⟨i0, hi0, hvi0⟩
        have hsub : ∑ i ∈ C, sgn i v = ∑ i : Fin (4 * e), sgn i v := by
          apply Finset.sum_subset (Finset.subset_univ C)
          intro j _ hjC
          apply (hsgn_val j v).2
          intro hvj
          exact hjC (partsOf_closed hC hi0 ⟨v, hvi0, hvj⟩)
        rw [hsub]
        exact hbal v hv0
      · push Not at hex
        apply Finset.sum_eq_zero
        intro i hi
        exact (hsgn_val i v).2 (hex i hi)
  have hneg_double : ∀ v : Fin n → F2,
      2 * (C.filter (fun i => sgn i v = -1)).card = (C.filter (fun i => v ∈ freqOf a b i)).card := by
    intro v
    have hsum := hcomp_bal v
    have hpart : ∀ i ∈ C, sgn i v = (if v ∈ freqOf a b i then (1 : Int) else 0) -
        2 * (if sgn i v = -1 then (1 : Int) else 0) := by
      intro i _
      by_cases hv : v ∈ freqOf a b i
      · rcases (hsgn_val i v).1 hv with h1 | hm1
        · simp [hv, h1]
        · simp [hv, hm1]
      · have h0 := (hsgn_val i v).2 hv
        simp [hv, h0]
    have hsum2 : (∑ i ∈ C, sgn i v) =
        ((C.filter (fun i => v ∈ freqOf a b i)).card : Int) -
        2 * ((C.filter (fun i => sgn i v = -1)).card : Int) := by
      calc (∑ i ∈ C, sgn i v)
          = ∑ i ∈ C, ((if v ∈ freqOf a b i then (1 : Int) else 0) -
              2 * (if sgn i v = -1 then (1 : Int) else 0)) := Finset.sum_congr rfl hpart
        _ = (∑ i ∈ C, if v ∈ freqOf a b i then (1 : Int) else 0) -
              2 * (∑ i ∈ C, if sgn i v = -1 then (1 : Int) else 0) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = ((C.filter (fun i => v ∈ freqOf a b i)).card : Int) -
              2 * ((C.filter (fun i => sgn i v = -1)).card : Int) := by
              simp [Finset.sum_boole]
    omega
  constructor
  · intro v
    exact ⟨(C.filter (fun i => sgn i v = -1)).card, by have := hneg_double v; omega⟩
  · let V := C.biUnion (freqOf a b)
    have hsum_neg : 2 * (∑ v ∈ V, (C.filter (fun i => sgn i v = -1)).card) =
        ∑ v ∈ V, (C.filter (fun i => v ∈ freqOf a b i)).card := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => hneg_double v)
    have hrhs : (∑ v ∈ V, (C.filter (fun i => v ∈ freqOf a b i)).card) = 3 * C.card := by
      have h1 : (∑ v ∈ V, (C.filter (fun i => v ∈ freqOf a b i)).card) =
          ∑ i ∈ C, (V.filter (fun v => v ∈ freqOf a b i)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      rw [h1]
      have h3 : ∀ i ∈ C, (V.filter (fun v => v ∈ freqOf a b i)).card = 3 := by
        intro i hi
        have heq : V.filter (fun v => v ∈ freqOf a b i) = freqOf a b i := by
          ext v
          simp only [Finset.mem_filter, and_iff_right_iff_imp]
          intro hv
          exact Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
        rw [heq]
        rcases hnondeg i with ⟨ha, hb, hab⟩
        have h1' : a i ≠ a i + b i := fun h => hb (by have := congrArg (a i + ·) h.symm; simpa [← add_assoc, zmod2_add_self] using this)
        have h2' : b i ≠ a i + b i := fun h => ha (by have := congrArg (· + b i) h.symm; simpa [add_assoc, zmod2_add_self] using this)
        simp [freqOf, hab, h1', h2']
      rw [Finset.sum_congr rfl h3]
      simp [Finset.sum_const, mul_comm]
    have hlhs_even : Even (∑ v ∈ V, (C.filter (fun i => sgn i v = -1)).card) := by
      have h1 : (∑ v ∈ V, (C.filter (fun i => sgn i v = -1)).card) =
          ∑ i ∈ C, (V.filter (fun v => sgn i v = -1)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      rw [h1]
      apply Finset.even_sum
      intro i hi
      have hsub : V.filter (fun v => sgn i v = -1) = (freqOf a b i).filter (fun v => sgn i v = -1) := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_, hm1⟩
          refine ⟨?_, hm1⟩
          by_contra hnot
          have := (hsgn_val i v).2 hnot
          omega
        · rintro ⟨hv, hm1⟩
          exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, hv⟩, hm1⟩
      rw [hsub]
      rcases hnondeg i with ⟨ha, hb, hab⟩
      have h1' : a i ≠ a i + b i := fun h => hb (by have := congrArg (a i + ·) h.symm; simpa [← add_assoc, zmod2_add_self] using this)
      have h2' : b i ≠ a i + b i := fun h => ha (by have := congrArg (· + b i) h.symm; simpa [add_assoc, zmod2_add_self] using this)
      rcases hs1 i with h1s | h1s <;> rcases hs2 i with h2s | h2s
      · have : (freqOf a b i).filter (fun v => sgn i v = -1) = ∅ := by
          ext v; simp [freqOf, sgn, h1s, h2s, hab, hab.symm, h1', h1'.symm, h2', h2'.symm]
          intro h; rcases h with rfl | rfl | rfl <;> simp [hab, hab.symm, h1', h1'.symm, h2', h2'.symm]
        rw [this]; exact ⟨0, rfl⟩
      · have : (freqOf a b i).filter (fun v => sgn i v = -1) = {b i, a i + b i} := by
          ext v
          simp only [Finset.mem_filter, freqOf, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, hm⟩
            · simp [sgn, h1s, h2s, hab.symm, h1'.symm] at hm
            · left; rfl
            · right; rfl
          · rintro (rfl | rfl)
            · exact ⟨Or.inr (Or.inl rfl), by simp [sgn, h1s, h2s, hab, h2'.symm]⟩
            · exact ⟨Or.inr (Or.inr rfl), by simp [sgn, h1s, h2s, h1', h2']⟩
        rw [this, Finset.card_pair h2']; exact ⟨1, rfl⟩
      · have : (freqOf a b i).filter (fun v => sgn i v = -1) = {a i, a i + b i} := by
          ext v
          simp only [Finset.mem_filter, freqOf, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, hm⟩
            · left; rfl
            · simp [sgn, h1s, h2s, hab, h2'.symm] at hm
            · right; rfl
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, by simp [sgn, h1s, h2s, hab.symm, h1'.symm]⟩
            · exact ⟨Or.inr (Or.inr rfl), by simp [sgn, h1s, h2s, h1', h2']⟩
        rw [this, Finset.card_pair h1']; exact ⟨1, rfl⟩
      · have : (freqOf a b i).filter (fun v => sgn i v = -1) = {a i, b i} := by
          ext v
          simp only [Finset.mem_filter, freqOf, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, hm⟩
            · left; rfl
            · right; rfl
            · simp [sgn, h1s, h2s, h1', h2'] at hm
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, by simp [sgn, h1s, h2s, hab.symm, h1'.symm]⟩
            · exact ⟨Or.inr (Or.inl rfl), by simp [sgn, h1s, h2s, hab, h2'.symm]⟩
        rw [this, Finset.card_pair hab]; exact ⟨1, rfl⟩
    rcases hlhs_even with ⟨k, hk⟩
    omega

def dartLbl {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (p : Fin (4 * e) × Fin 3) : Fin n → F2 :=
  match p.2 with
  | ⟨0, _⟩ => a p.1
  | ⟨1, _⟩ => b p.1
  | ⟨2, _⟩ => a p.1 + b p.1

lemma dartLbl_sum_zero {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (i : Fin (4 * e)) :
    (∑ k : Fin 3, dartLbl a b (i, k)) = 0 := by
  rw [Fin.sum_univ_three]
  simp only [dartLbl]
  exact zmod2_add_self (a i + b i)

lemma dartLbl_ne_zero {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (p : Fin (4 * e) × Fin 3) :
    dartLbl a b p ≠ 0 := by
  rcases hnondeg p.1 with ⟨ha, hb, hab⟩
  match hp : p.2 with
  | ⟨0, _⟩ => simp [dartLbl, hp, ha]
  | ⟨1, _⟩ => simp [dartLbl, hp, hb]
  | ⟨2, _⟩ =>
    simp only [dartLbl, hp]
    intro h
    exact hab (zmod2_add_eq_zero.mp h)

lemma dartLbl_mem_freq {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (p : Fin (4 * e) × Fin 3) :
    dartLbl a b p ∈ freqOf a b p.1 := by
  match hp : p.2 with
  | ⟨0, _⟩ => simp [dartLbl, freqOf, hp]
  | ⟨1, _⟩ => simp [dartLbl, freqOf, hp]
  | ⟨2, _⟩ => simp [dartLbl, freqOf, hp]

lemma exists_fpf_involution {α : Type*} [DecidableEq α] :
    ∀ (s : Finset α), Even s.card →
      ∃ f : α → α, (∀ x ∈ s, f x ∈ s ∧ f (f x) = x ∧ f x ≠ x) ∧ (∀ x ∉ s, f x = x) := by
  intro s
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | ind m ih =>
    intro heven
    by_cases h0 : m = 0
    · subst h0
      have hs : s = ∅ := Finset.card_eq_zero.mp hn
      subst hs
      exact ⟨id, by simp, fun _ _ => rfl⟩
    · have hge2 : 2 ≤ s.card := by rcases heven with ⟨k, hk⟩; omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      have hcard_er : 0 < (s.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard_er
      have hxy : y ≠ x := Finset.ne_of_mem_erase hy
      have hys : y ∈ s := Finset.mem_of_mem_erase hy
      let s' := (s.erase x).erase y
      have hcard' : s'.card = m - 2 := by
        rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega
      have heven' : Even s'.card := by rcases heven with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      obtain ⟨f', hf'in, hf'out⟩ := ih s'.card (by omega) s' rfl heven'
      refine ⟨fun z => if z = x then y else if z = y then x else f' z, ?_, ?_⟩
      · intro z hz
        by_cases hzx : z = x
        · subst hzx; simp [hxy, hxy.symm, hys]
        · by_cases hzy : z = y
          · subst hzy; simp [hxy, hxy.symm, hx]
          · have hzs' : z ∈ s' := Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hz⟩⟩
            rcases hf'in z hzs' with ⟨hmem, hinv, hne⟩
            have hfx : f' z ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)
            have hfy : f' z ≠ y := Finset.ne_of_mem_erase hmem
            simp only [hzx, hzy, ↓reduceIte]
            refine ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem), ?_, hne⟩
            simp [hfx, hfy, hinv]
      · intro z hz
        have hzx : z ≠ x := fun h => hz (h ▸ hx)
        have hzy : z ≠ y := fun h => hz (h ▸ hys)
        have hzs' : z ∉ s' := fun h => hz (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
        simp [hzx, hzy, hf'out z hzs']

structure Pairing {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2)) (C : Finset (Fin (4 * e))) where
  mate : Fin (4 * e) × Fin 3 → Fin (4 * e) × Fin 3
  mem : ∀ p, p.1 ∈ C → (mate p).1 ∈ C
  invol : ∀ p, p.1 ∈ C → mate (mate p) = p
  ne_self : ∀ p, p.1 ∈ C → mate p ≠ p
  pres_lbl : ∀ p, p.1 ∈ C → dartLbl a b (mate p) = dartLbl a b p
  out_id : ∀ p, p.1 ∉ C → mate p = p

lemma exists_pairing {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    {C : Finset (Fin (4 * e))}
    (heven : ∀ v : Fin n → F2, Even (C.filter (fun i => v ∈ freqOf a b i)).card) :
    Nonempty (Pairing a b C) := by
  let D : Finset (Fin (4 * e) × Fin 3) := C ×ˢ Finset.univ
  have hDv_even : ∀ v : Fin n → F2, Even (D.filter (fun p => dartLbl a b p = v)).card := by
    intro v
    have hbij : (D.filter (fun p => dartLbl a b p = v)).card =
        (C.filter (fun i => v ∈ freqOf a b i)).card := by
      apply Finset.card_bij (fun p _ => p.1)
      · intro p hp
        simp only [Finset.mem_filter, D, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
        exact ⟨hp.1, hp.2 ▸ dartLbl_mem_freq a b p⟩
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_filter] at hp1 hp2
        have hlbl : dartLbl a b p1 = dartLbl a b p2 := hp1.2.trans hp2.2.symm
        rcases p1 with ⟨i1, k1⟩; rcases p2 with ⟨i2, k2⟩
        dsimp only at heq; subst heq
        congr 1
        rcases hnondeg i1 with ⟨ha, hb, hab⟩
        fin_cases k1 <;> fin_cases k2 <;> simp [dartLbl] at hlbl ⊢
        · exact absurd hlbl hab
        · exact absurd hlbl hb
        · exact absurd hlbl.symm hab
        · exact absurd hlbl ha
        · exact absurd hlbl hb
        · exact absurd hlbl ha
      · intro i hi
        simp only [Finset.mem_filter, freqOf, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with ⟨hiC, rfl | rfl | rfl⟩
        · exact ⟨(i, 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hiC, Finset.mem_univ _⟩, rfl⟩, rfl⟩
        · exact ⟨(i, 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hiC, Finset.mem_univ _⟩, rfl⟩, rfl⟩
        · exact ⟨(i, 2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hiC, Finset.mem_univ _⟩, rfl⟩, rfl⟩
    rw [hbij]
    exact heven v
  choose f hfin hfout using fun v => exists_fpf_involution (D.filter (fun p => dartLbl a b p = v)) (hDv_even v)
  refine ⟨⟨fun p => if p.1 ∈ C then f (dartLbl a b p) p else p, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p hp
    have hpD : p ∈ D.filter (fun q => dartLbl a b q = dartLbl a b p) := by simp [D, hp]
    have hmem := (hfin (dartLbl a b p) p hpD).1
    simp only [Finset.mem_filter, D, Finset.mem_product, Finset.mem_univ, and_true] at hmem
    simp [hp, hmem.1]
  · intro p hp
    have hpD : p ∈ D.filter (fun q => dartLbl a b q = dartLbl a b p) := by simp [D, hp]
    rcases hfin (dartLbl a b p) p hpD with ⟨hmem, hinv, _⟩
    simp only [Finset.mem_filter, D, Finset.mem_product, Finset.mem_univ, and_true] at hmem
    simp [hp, hmem.1, hmem.2, hinv]
  · intro p hp
    have hpD : p ∈ D.filter (fun q => dartLbl a b q = dartLbl a b p) := by simp [D, hp]
    simpa [hp] using (hfin (dartLbl a b p) p hpD).2.2
  · intro p hp
    have hpD : p ∈ D.filter (fun q => dartLbl a b q = dartLbl a b p) := by simp [D, hp]
    have hmem := (hfin (dartLbl a b p) p hpD).1
    simp only [Finset.mem_filter] at hmem
    simp [hp, hmem.2]
  · intro p hp
    simp [hp]

def pStep {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)} {C : Finset (Fin (4 * e))}
    (P : Pairing a b C) (u w : Fin (4 * e)) : Prop :=
  u ∈ C ∧ w ∈ C ∧ ∃ k : Fin 3, (P.mate (u, k)).1 = w

def pStepSkip {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)} {C : Finset (Fin (4 * e))}
    (P : Pairing a b C) (d : Fin (4 * e) × Fin 3) (u w : Fin (4 * e)) : Prop :=
  u ∈ C ∧ w ∈ C ∧ ∃ k : Fin 3, (u, k) ≠ d ∧ (u, k) ≠ P.mate d ∧ (P.mate (u, k)).1 = w

lemma no_bridge {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    {C : Finset (Fin (4 * e))} (P : Pairing a b C)
    {d : Fin (4 * e) × Fin 3} (hd : d.1 ∈ C) :
    Relation.EqvGen (pStepSkip P d) d.1 (P.mate d).1 := by
  classical
  let S : Finset (Fin (4 * e)) := C.filter (fun x => Relation.EqvGen (pStepSkip P d) d.1 x)
  have hdS : d.1 ∈ S := by simp [S, hd, Relation.EqvGen.refl]
  by_contra hnot
  have hmS : (P.mate d).1 ∉ S := by
    simp only [S, Finset.mem_filter, not_and]
    intro _; exact hnot
  have hunique : ∀ p : Fin (4 * e) × Fin 3, p.1 ∈ S → (P.mate p).1 ∉ S → p = d := by
    intro p hpS hmpS
    have hpC : p.1 ∈ C := (Finset.mem_filter.mp hpS).1
    have hmpC : (P.mate p).1 ∈ C := P.mem p hpC
    by_contra hne_d
    have hne_md : p ≠ P.mate d := by
      intro heq
      have h1 : (P.mate p).1 = d.1 := by rw [heq, P.invol d hd]
      exact hmpS (h1 ▸ hdS)
    have hstep : pStepSkip P d p.1 (P.mate p).1 := ⟨hpC, hmpC, p.2, hne_d, hne_md, rfl⟩
    have hreach : Relation.EqvGen (pStepSkip P d) d.1 (P.mate p).1 :=
      Relation.EqvGen.trans _ p.1 _ (Finset.mem_filter.mp hpS).2 (Relation.EqvGen.rel _ _ hstep)
    exact hmpS (Finset.mem_filter.mpr ⟨hmpC, hreach⟩)
  let DS : Finset (Fin (4 * e) × Fin 3) := S ×ˢ Finset.univ
  have hsum0 : (∑ p ∈ DS, dartLbl a b p) = 0 := by
    rw [Finset.sum_product]
    exact Finset.sum_eq_zero (fun i _ => dartLbl_sum_zero a b i)
  have hbound : DS.filter (fun p => (P.mate p).1 ∉ S) = {d} := by
    ext p
    simp only [Finset.mem_filter, DS, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_singleton]
    constructor
    · rintro ⟨hpS, hmpS⟩; exact hunique p hpS hmpS
    · rintro rfl; exact ⟨hdS, hmS⟩
  let Dint := DS.filter (fun p => (P.mate p).1 ∈ S)
  have hint0 : (∑ p ∈ Dint, dartLbl a b p) = 0 := by
    have hmate_mem : ∀ p ∈ Dint, P.mate p ∈ Dint := by
      intro p hp
      simp only [Dint, Finset.mem_filter, DS, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
      have hpC : p.1 ∈ C := (Finset.mem_filter.mp hp.1).1
      exact ⟨hp.2, by rw [P.invol p hpC]; exact hp.1⟩
    have haux : ∀ (T : Finset (Fin (4 * e) × Fin 3)),
        (∀ p ∈ T, p.1 ∈ C ∧ P.mate p ∈ T) → (∑ p ∈ T, dartLbl a b p) = 0 := by
      intro T
      induction hT : T.card using Nat.strong_induction_on generalizing T with
      | ind m ih =>
        intro hcl
        by_cases hm0 : m = 0
        · have : T = ∅ := Finset.card_eq_zero.mp (hT.trans hm0)
          subst this; simp
        · obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
          have hpC : p.1 ∈ C := (hcl p hp).1
          have hmp : P.mate p ∈ T := (hcl p hp).2
          have hne : P.mate p ≠ p := P.ne_self p hpC
          let T' := (T.erase p).erase (P.mate p)
          have hmp' : P.mate p ∈ T.erase p := Finset.mem_erase.mpr ⟨hne, hmp⟩
          have hcard' : T'.card < m := by
            rw [Finset.card_erase_of_mem hmp', Finset.card_erase_of_mem hp]; omega
          have hcl' : ∀ q ∈ T', q.1 ∈ C ∧ P.mate q ∈ T' := by
            intro q hq
            have hqT : q ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
            have hqC : q.1 ∈ C := (hcl q hqT).1
            have hmqT : P.mate q ∈ T := (hcl q hqT).2
            have hne1 : P.mate q ≠ p := by
              intro h; have := congrArg P.mate h; rw [P.invol q hqC] at this
              exact (Finset.ne_of_mem_erase hq) this
            have hne2 : P.mate q ≠ P.mate p := by
              intro h; have := congrArg P.mate h; rw [P.invol q hqC, P.invol p hpC] at this
              exact (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)) this
            exact ⟨hqC, Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hmqT⟩⟩⟩
          have hsum' : (∑ q ∈ T', dartLbl a b q) = 0 := ih T'.card hcard' T' rfl hcl'
          rw [← Finset.add_sum_erase T _ hp, ← Finset.add_sum_erase (T.erase p) _ hmp', hsum', add_zero,
              P.pres_lbl p hpC, zmod2_add_self]
    exact haux Dint (fun p hp => by
      have hpS : p.1 ∈ S := by
        simp only [Dint, Finset.mem_filter, DS, Finset.mem_product, Finset.mem_univ, and_true] at hp
        exact hp.1
      exact ⟨(Finset.mem_filter.mp hpS).1, hmate_mem p hp⟩)
  have hsplit := Finset.sum_filter_add_sum_filter_not DS (fun p => (P.mate p).1 ∈ S) (dartLbl a b)
  rw [hsum0, show DS.filter (fun p => (P.mate p).1 ∈ S) = Dint from rfl, hint0, zero_add, hbound,
      Finset.sum_singleton] at hsplit
  exact dartLbl_ne_zero hnondeg d hsplit

noncomputable def numComps {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)} {C : Finset (Fin (4 * e))}
    (P : Pairing a b C) : Nat :=
  (C.image (fun u => C.filter (fun w =>
    @decide (Relation.EqvGen (pStep P) u w) (Classical.propDecidable _) = true))).card

lemma exists_connected_pairing {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b)
    (heven : ∀ v : Fin n → F2, Even (C.filter (fun i => v ∈ freqOf a b i)).card) :
    ∃ P : Pairing a b C, ∀ u ∈ C, ∀ w ∈ C, Relation.EqvGen (pStep P) u w := by
  classical
  obtain ⟨P0⟩ := exists_pairing hnondeg heven
  suffices h : ∀ k : Nat, ∀ P : Pairing a b C, numComps P = k →
      ∃ P' : Pairing a b C, ∀ u ∈ C, ∀ w ∈ C, Relation.EqvGen (pStep P') u w by
    exact h (numComps P0) P0 rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro P hk
    by_cases hconn : ∀ u ∈ C, ∀ w ∈ C, Relation.EqvGen (pStep P) u w
    · exact ⟨P, hconn⟩
    · push Not at hconn
      rcases hconn with ⟨u0, hu0, w0, hw0, hnot⟩
      have hex_edge : ∃ u1 ∈ C, ∃ v1 ∈ C, adjOf a b u1 v1 ∧ ¬ Relation.EqvGen (pStep P) u1 v1 := by
        by_contra hall
        push Not at hall
        have heqv := partsOf_eqv hC hu0 hw0
        have hlift : ∀ x y, Relation.EqvGen (adjOf a b) x y → x ∈ C → Relation.EqvGen (pStep P) x y := by
          intro x y hxy
          induction hxy with
          | rel x y h =>
            intro hx
            exact hall x hx y (partsOf_closed hC hx h) h
          | refl x => intro _; exact Relation.EqvGen.refl x
          | symm x y h ih' =>
            intro hy
            have hx : x ∈ C := by
              rcases mem_partsOf_iff.mp hC with ⟨r, rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hy ⊢
              exact Relation.EqvGen.trans r y x hy (Relation.EqvGen.symm x y h)
            exact Relation.EqvGen.symm x y (ih' hx)
          | trans x y z h1 _ ih1 ih2 =>
            intro hx
            have hy : y ∈ C := by
              rcases mem_partsOf_iff.mp hC with ⟨r, rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx ⊢
              exact Relation.EqvGen.trans r x y hx h1
            exact Relation.EqvGen.trans x y z (ih1 hx) (ih2 hy)
        exact hnot (hlift u0 w0 heqv hu0)
      rcases hex_edge with ⟨u1, hu1, v1, hv1, ⟨v, hv_u1, hv_v1⟩, hsep⟩
      have hd1_ex : ∃ k1 : Fin 3, dartLbl a b (u1, k1) = v := by
        simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv_u1
        rcases hv_u1 with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      have hd2_ex : ∃ k2 : Fin 3, dartLbl a b (v1, k2) = v := by
        simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv_v1
        rcases hv_v1 with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      rcases hd1_ex with ⟨k1, hk1⟩
      rcases hd2_ex with ⟨k2, hk2⟩
      let d1 : Fin (4 * e) × Fin 3 := (u1, k1)
      let d2 : Fin (4 * e) × Fin 3 := (v1, k2)
      let m1 := P.mate d1
      let m2 := P.mate d2
      have hm1C : m1.1 ∈ C := P.mem d1 hu1
      have hm2C : m2.1 ∈ C := P.mem d2 hv1
      have hreach_d1_m1 : Relation.EqvGen (pStep P) u1 m1.1 :=
        Relation.EqvGen.rel _ _ ⟨hu1, hm1C, k1, rfl⟩
      have hreach_d2_m2 : Relation.EqvGen (pStep P) v1 m2.1 :=
        Relation.EqvGen.rel _ _ ⟨hv1, hm2C, k2, rfl⟩
      have h12 : d1 ≠ d2 := fun h => hsep (by
        have : u1 = v1 := congrArg Prod.fst h
        rw [this]; exact Relation.EqvGen.refl _)
      have h1m2 : d1 ≠ m2 := fun h => hsep (by
        have : u1 = m2.1 := congrArg Prod.fst h
        rw [this]; exact Relation.EqvGen.symm _ _ hreach_d2_m2)
      have hm12 : m1 ≠ d2 := fun h => hsep (by
        have : m1.1 = v1 := congrArg Prod.fst h
        rw [← this]; exact hreach_d1_m1)
      have hm1m2 : m1 ≠ m2 := fun h => hsep (by
        have : m1.1 = m2.1 := congrArg Prod.fst h
        exact Relation.EqvGen.trans _ m1.1 _ hreach_d1_m1 (this ▸ Relation.EqvGen.symm _ _ hreach_d2_m2))
      have hd1m1 : d1 ≠ m1 := (P.ne_self d1 hu1).symm
      have hd2m2 : d2 ≠ m2 := (P.ne_self d2 hv1).symm
      let mate' : Fin (4 * e) × Fin 3 → Fin (4 * e) × Fin 3 := fun p =>
        if p = d1 then d2
        else if p = d2 then d1
        else if p = m1 then m2
        else if p = m2 then m1
        else P.mate p
      let P' : Pairing a b C := {
        mate := mate'
        mem := fun p hp => by
          dsimp only [mate']; split_ifs
          · exact hv1
          · exact hu1
          · exact hm2C
          · exact hm1C
          · exact P.mem p hp
        invol := fun p hp => by
          dsimp only [mate']
          by_cases h1 : p = d1
          · subst h1; simp [h12, h12.symm]
          · by_cases h2 : p = d2
            · subst h2; simp [h12, h12.symm]
            · by_cases h3 : p = m1
              · subst h3; simp [h12, h12.symm, hm12, hm12.symm, h1m2, h1m2.symm, hm1m2, hm1m2.symm, hd1m1, hd1m1.symm, hd2m2, hd2m2.symm]
              · by_cases h4 : p = m2
                · subst h4; simp [h12, h12.symm, hm12, hm12.symm, h1m2, h1m2.symm, hm1m2, hm1m2.symm, hd1m1, hd1m1.symm, hd2m2, hd2m2.symm]
                · have hm_ne1 : P.mate p ≠ d1 := fun h => h3 (by rw [← P.invol p hp, h])
                  have hm_ne2 : P.mate p ≠ d2 := fun h => h4 (by rw [← P.invol p hp, h])
                  have hm_ne3 : P.mate p ≠ m1 := fun h => h1 (by have := congrArg P.mate h; rw [P.invol p hp, P.invol d1 hu1] at this; exact this)
                  have hm_ne4 : P.mate p ≠ m2 := fun h => h2 (by have := congrArg P.mate h; rw [P.invol p hp, P.invol d2 hv1] at this; exact this)
                  simp [h1, h2, h3, h4, hm_ne1, hm_ne2, hm_ne3, hm_ne4, P.invol p hp]
        ne_self := fun p hp => by
          dsimp only [mate']
          by_cases h1 : p = d1
          · subst h1; simp [h12, h12.symm]
          · by_cases h2 : p = d2
            · subst h2; simp [h12, h12.symm]
            · by_cases h3 : p = m1
              · subst h3; simp [h12, h12.symm, hm12, hm12.symm, h1m2, h1m2.symm, hm1m2, hm1m2.symm, hd1m1, hd1m1.symm, hd2m2, hd2m2.symm]
              · by_cases h4 : p = m2
                · subst h4; simp [h12, h12.symm, hm12, hm12.symm, h1m2, h1m2.symm, hm1m2, hm1m2.symm, hd1m1, hd1m1.symm, hd2m2, hd2m2.symm]
                · simp [h1, h2, h3, h4, P.ne_self p hp]
        pres_lbl := fun p hp => by
          dsimp only [mate']
          by_cases h1 : p = d1
          · subst h1; simp [d1, d2, hk1, hk2]
          · by_cases h2 : p = d2
            · subst h2; simp [h12, h12.symm, d1, d2, hk1, hk2]
            · by_cases h3 : p = m1
              · subst h3; simp [h12, h12.symm, hm12, hm12.symm, h1m2, h1m2.symm, hm1m2, hm1m2.symm, hd1m1, hd1m1.symm, hd2m2, hd2m2.symm, m1, m2, P.pres_lbl d1 hu1, P.pres_lbl d2 hv1, d1, d2, hk1, hk2]
              · by_cases h4 : p = m2
                · subst h4; simp [h12, h12.symm, hm12, hm12.symm, h1m2, h1m2.symm, hm1m2, hm1m2.symm, hd1m1, hd1m1.symm, hd2m2, hd2m2.symm, m1, m2, P.pres_lbl d1 hu1, P.pres_lbl d2 hv1, d1, d2, hk1, hk2]
                · simp [h1, h2, h3, h4, P.pres_lbl p hp]
        out_id := fun p hp => by
          dsimp only [mate']
          have h1 : p ≠ d1 := fun h => hp (h ▸ hu1)
          have h2 : p ≠ d2 := fun h => hp (h ▸ hv1)
          have h3 : p ≠ m1 := fun h => hp (h ▸ hm1C)
          have h4 : p ≠ m2 := fun h => hp (h ▸ hm2C)
          simp [h1, h2, h3, h4, P.out_id p hp]
      }
      have hskip_to_P : ∀ d x y, Relation.EqvGen (pStepSkip P d) x y → Relation.EqvGen (pStep P) x y := by
        intro d x y h
        induction h with
        | rel x1 y1 h' => rcases h' with ⟨hx', hy', l, _, _, hlm⟩; exact Relation.EqvGen.rel _ _ ⟨hx', hy', l, hlm⟩
        | refl _ => exact Relation.EqvGen.refl _
        | symm _ _ _ ih1 => exact Relation.EqvGen.symm _ _ ih1
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      have hlift_d1 : Relation.EqvGen (pStep P') u1 m1.1 := by
        have hnb := no_bridge hnondeg P (d := d1) hu1
        have hlift_nb : ∀ a1 b1, Relation.EqvGen (pStepSkip P d1) a1 b1 →
            Relation.EqvGen (pStep P) u1 a1 → Relation.EqvGen (pStep P') a1 b1 := by
          intro a1 b1 hab
          induction hab with
          | rel a1 b1 h =>
            intro ha1
            rcases h with ⟨haC, hbC, l, hl1, hl2, hlm⟩
            have hl3 : (a1, l) ≠ d2 := fun h => hsep (by have : a1 = v1 := congrArg Prod.fst h; exact this ▸ ha1)
            have hl4 : (a1, l) ≠ m2 := fun h => hsep (by
              have : a1 = m2.1 := congrArg Prod.fst h
              exact Relation.EqvGen.trans _ a1 _ ha1 (this ▸ Relation.EqvGen.symm _ _ hreach_d2_m2))
            apply Relation.EqvGen.rel
            refine ⟨haC, hbC, l, ?_⟩
            change (mate' (a1, l)).1 = b1
            simp [mate', m1, m2, hl1, hl2, hl3, hl4, hlm]
          | refl a1 => intro _; exact Relation.EqvGen.refl a1
          | symm a1 b1 h ih' =>
            intro ha1
            have hb1 : Relation.EqvGen (pStep P) u1 a1 :=
              Relation.EqvGen.trans _ b1 _ ha1 (Relation.EqvGen.symm _ _ (hskip_to_P d1 a1 b1 h))
            exact Relation.EqvGen.symm _ _ (ih' hb1)
          | trans a1 b1 c1 h1' _ ih1 ih2 =>
            intro ha1
            have hb1 : Relation.EqvGen (pStep P) u1 b1 :=
              Relation.EqvGen.trans _ a1 _ ha1 (hskip_to_P d1 a1 b1 h1')
            exact Relation.EqvGen.trans _ _ _ (ih1 ha1) (ih2 hb1)
        exact hlift_nb d1.1 m1.1 hnb (Relation.EqvGen.refl u1)
      have hlift_d2 : Relation.EqvGen (pStep P') v1 m2.1 := by
        have hnb := no_bridge hnondeg P (d := d2) hv1
        have hlift_nb : ∀ a1 b1, Relation.EqvGen (pStepSkip P d2) a1 b1 →
            Relation.EqvGen (pStep P) v1 a1 → Relation.EqvGen (pStep P') a1 b1 := by
          intro a1 b1 hab
          induction hab with
          | rel a1 b1 h =>
            intro ha1
            rcases h with ⟨haC, hbC, l, hl1, hl2, hlm⟩
            have hl3 : (a1, l) ≠ d1 := fun h => hsep (by have : a1 = u1 := congrArg Prod.fst h; exact Relation.EqvGen.symm _ _ (this ▸ ha1))
            have hl4 : (a1, l) ≠ m1 := fun h => hsep (by
              have : a1 = m1.1 := congrArg Prod.fst h
              exact Relation.EqvGen.trans _ m1.1 _ hreach_d1_m1 (this ▸ Relation.EqvGen.symm _ _ ha1))
            apply Relation.EqvGen.rel
            refine ⟨haC, hbC, l, ?_⟩
            change (mate' (a1, l)).1 = b1
            simp [mate', m1, m2, hl1, hl2, hl3, hl4, hlm]
          | refl a1 => intro _; exact Relation.EqvGen.refl a1
          | symm a1 b1 h ih' =>
            intro ha1
            have hb1 : Relation.EqvGen (pStep P) v1 a1 :=
              Relation.EqvGen.trans _ b1 _ ha1 (Relation.EqvGen.symm _ _ (hskip_to_P d2 a1 b1 h))
            exact Relation.EqvGen.symm _ _ (ih' hb1)
          | trans a1 b1 c1 h1' _ ih1 ih2 =>
            intro ha1
            have hb1 : Relation.EqvGen (pStep P) v1 b1 :=
              Relation.EqvGen.trans _ a1 _ ha1 (hskip_to_P d2 a1 b1 h1')
            exact Relation.EqvGen.trans _ _ _ (ih1 ha1) (ih2 hb1)
        exact hlift_nb d2.1 m2.1 hnb (Relation.EqvGen.refl v1)
      have hstep_to_P' : ∀ x y, pStep P x y → Relation.EqvGen (pStep P') x y := by
        intro x y ⟨hx, hy, j, hj⟩
        by_cases h1 : (x, j) = d1
        · have hx1 : x = u1 := congrArg Prod.fst h1
          have hy1 : y = m1.1 := by rw [← hj, h1]
          subst hx1; subst hy1; exact hlift_d1
        · by_cases h2 : (x, j) = m1
          · have hx1 : x = m1.1 := congrArg Prod.fst h2
            have hy1 : y = u1 := by rw [← hj, h2, P.invol d1 hu1]
            subst hx1; subst hy1; exact Relation.EqvGen.symm _ _ hlift_d1
          · by_cases h3 : (x, j) = d2
            · have hx1 : x = v1 := congrArg Prod.fst h3
              have hy1 : y = m2.1 := by rw [← hj, h3]
              subst hx1; subst hy1; exact hlift_d2
            · by_cases h4 : (x, j) = m2
              · have hx1 : x = m2.1 := congrArg Prod.fst h4
                have hy1 : y = v1 := by rw [← hj, h4, P.invol d2 hv1]
                subst hx1; subst hy1; exact Relation.EqvGen.symm _ _ hlift_d2
              · apply Relation.EqvGen.rel
                refine ⟨hx, hy, j, ?_⟩
                change (mate' (x, j)).1 = y
                simp [mate', h1, h2, h3, h4, hj]
      have hreach_to_P' : ∀ x y, Relation.EqvGen (pStep P) x y → Relation.EqvGen (pStep P') x y := by
        intro x y hxy
        induction hxy with
        | rel x y h => exact hstep_to_P' x y h
        | refl x => exact Relation.EqvGen.refl x
        | symm _ _ _ ih1 => exact Relation.EqvGen.symm _ _ ih1
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      have hmerge : Relation.EqvGen (pStep P') u1 v1 := by
        apply Relation.EqvGen.rel
        refine ⟨hu1, hv1, k1, ?_⟩
        change (mate' d1).1 = v1
        simp [mate', d2]
      let fP : Fin (4 * e) → Finset (Fin (4 * e)) := fun u =>
        C.filter (fun w => @decide (Relation.EqvGen (pStep P) u w) (Classical.propDecidable _) = true)
      let fP' : Fin (4 * e) → Finset (Fin (4 * e)) := fun u =>
        C.filter (fun w => @decide (Relation.EqvGen (pStep P') u w) (Classical.propDecidable _) = true)
      have hcard_lt : numComps P' < numComps P := by
        let g : Finset (Fin (4 * e)) → Finset (Fin (4 * e)) := fun S => S.biUnion fP'
        have hg_eq : ∀ u ∈ C, g (fP u) = fP' u := by
          intro u hu
          ext w
          simp only [g, Finset.mem_biUnion, fP, fP', Finset.mem_filter, decide_eq_true_eq]
          constructor
          · rintro ⟨x, ⟨_, hux⟩, hwC, hxw⟩
            exact ⟨hwC, Relation.EqvGen.trans _ _ _ (hreach_to_P' u x hux) hxw⟩
          · rintro ⟨hwC, huw⟩
            exact ⟨u, ⟨hu, Relation.EqvGen.refl u⟩, hwC, huw⟩
        have hsurj : C.image fP' ⊆ (C.image fP).image g := by
          intro S hS
          rcases Finset.mem_image.mp hS with ⟨u, hu, rfl⟩
          exact Finset.mem_image.mpr ⟨fP u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, hg_eq u hu⟩
        have hne_fg : fP u1 ≠ fP v1 := by
          intro heq
          have hv_in : v1 ∈ fP v1 := by simp [fP, hv1, Relation.EqvGen.refl]
          rw [← heq] at hv_in
          simp only [fP, Finset.mem_filter, decide_eq_true_eq] at hv_in
          exact hsep hv_in.2
        have hsame : g (fP u1) = g (fP v1) := by
          rw [hg_eq u1 hu1, hg_eq v1 hv1]
          ext w
          simp only [fP', Finset.mem_filter, decide_eq_true_eq]
          exact ⟨fun ⟨hw, h⟩ => ⟨hw, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hmerge) h⟩,
                 fun ⟨hw, h⟩ => ⟨hw, Relation.EqvGen.trans _ _ _ hmerge h⟩⟩
        have hsub2 : (C.image fP).image g = ((C.image fP).erase (fP v1)).image g := by
          ext S
          simp only [Finset.mem_image, Finset.mem_erase]
          constructor
          · rintro ⟨T, hT, rfl⟩
            by_cases hTv : T = fP v1
            · subst hTv
              exact ⟨fP u1, ⟨hne_fg, ⟨u1, hu1, rfl⟩⟩, hsame⟩
            · exact ⟨T, ⟨hTv, hT⟩, rfl⟩
          · rintro ⟨T, ⟨_, hT⟩, rfl⟩
            exact ⟨T, hT, rfl⟩
        have hfv_mem : fP v1 ∈ C.image fP := Finset.mem_image.mpr ⟨v1, hv1, rfl⟩
        calc numComps P'
            = (C.image fP').card := rfl
          _ ≤ ((C.image fP).image g).card := Finset.card_le_card hsurj
          _ = (((C.image fP).erase (fP v1)).image g).card := by rw [hsub2]
          _ ≤ ((C.image fP).erase (fP v1)).card := Finset.card_image_le
          _ < (C.image fP).card := Finset.card_erase_lt_of_mem hfv_mem
          _ = numComps P := rfl
      exact ih (numComps P') (hk ▸ hcard_lt) P' rfl

lemma card_image_le_half_of_fpf_invol {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (f : α → α) (g : α → β)
    (hinv : ∀ x ∈ U, f x ∈ U ∧ f (f x) = x ∧ f x ≠ x ∧ g (f x) = g x) :
    2 * (U.image g).card ≤ U.card := by
  induction hn : U.card using Nat.strong_induction_on generalizing U with
  | ind m ih =>
    by_cases hm0 : m = 0
    · have : U = ∅ := Finset.card_eq_zero.mp (hn.trans hm0)
      subst this; simp
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
      rcases hinv x hx with ⟨hfx, hffx, hne, hgx⟩
      let U' := (U.erase x).erase (f x)
      have hfx' : f x ∈ U.erase x := Finset.mem_erase.mpr ⟨hne, hfx⟩
      have hcard' : U'.card = m - 2 := by
        rw [Finset.card_erase_of_mem hfx', Finset.card_erase_of_mem hx]; omega
      have hinv' : ∀ y ∈ U', f y ∈ U' ∧ f (f y) = y ∧ f y ≠ y ∧ g (f y) = g y := by
        intro y hy
        have hyU : y ∈ U := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
        rcases hinv y hyU with ⟨hfy, hffy, hney, hgy⟩
        have hne1 : f y ≠ x := by
          intro h; have := congrArg f h; rw [hffy] at this
          exact (Finset.ne_of_mem_erase hy) this
        have hne2 : f y ≠ f x := by
          intro h; have := congrArg f h; rw [hffy, hffx] at this
          exact (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)) this
        exact ⟨Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hfy⟩⟩, hffy, hney, hgy⟩
      have hih := ih U'.card (by omega) U' hinv' rfl
      have hsub : U.image g ⊆ insert (g x) (U'.image g) := by
        intro b hb
        rcases Finset.mem_image.mp hb with ⟨y, hy, rfl⟩
        by_cases hyx : y = x
        · subst hyx; exact Finset.mem_insert_self _ _
        · by_cases hyfx : y = f x
          · subst hyfx; rw [hgx]; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨y, Finset.mem_erase.mpr ⟨hyfx, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩, rfl⟩)
      have hle : (U.image g).card ≤ (U'.image g).card + 1 :=
        (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      have hge2 : 2 ≤ U.card := Finset.one_lt_card.mpr ⟨x, hx, f x, hfx, hne.symm⟩
      omega

lemma rk_comp_le {n e : Nat} {a b : Fin (4 * e) → (Fin n → F2)}
    (hnondeg : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b)
    (heven : ∀ v : Fin n → F2, Even (C.filter (fun i => v ∈ freqOf a b i)).card) :
    rkOf a b C ≤ C.card / 2 + 1 := by
  classical
  obtain ⟨P, hconn⟩ := exists_connected_pairing hnondeg hC heven
  obtain ⟨r, hr⟩ := partsOf_nonempty hC
  let D : Finset (Fin (4 * e) × Fin 3) := C ×ˢ Finset.univ
  have hbuild : ∀ (S : Finset (Fin (4 * e))), S ⊆ C → S.Nonempty →
      ∃ T : Finset (Fin (4 * e) × Fin 3),
        T ⊆ D ∧
        (∀ p ∈ T, P.mate p ∈ T) ∧
        (∀ p ∈ T, p.1 ∈ C \ S ∨ (P.mate p).1 ∈ C \ S) ∧
        T.card = 2 * (C \ S).card ∧
        (∀ (W : Submodule F2 (Fin n → F2)),
          (∀ p ∈ D, p ∉ T → (p.1 ∈ C \ S ∨ (P.mate p).1 ∈ C \ S) → dartLbl a b p ∈ W) →
          (∀ p ∈ D, p.1 ∈ C \ S → dartLbl a b p ∈ W)) := by
    intro S hSC hSne
    induction hm : (C \ S).card using Nat.strong_induction_on generalizing S with
    | ind m ih =>
      by_cases hm0 : m = 0
      · have hdiff : C \ S = ∅ := Finset.card_eq_zero.mp (hm.trans hm0)
        refine ⟨∅, Finset.empty_subset _, by simp, by simp, by simp [hm0], ?_⟩
        intro W _ p _ hp; rw [hdiff] at hp; simp at hp
      · have hcross : ∃ d : Fin (4 * e) × Fin 3, d.1 ∈ S ∧ (P.mate d).1 ∈ C \ S := by
          obtain ⟨u, huS⟩ := hSne
          obtain ⟨w, hwCS⟩ := Finset.card_pos.mp (by omega : 0 < (C \ S).card)
          have hwC : w ∈ C := (Finset.mem_sdiff.mp hwCS).1
          have hwS : w ∉ S := (Finset.mem_sdiff.mp hwCS).2
          have hreach := hconn u (hSC huS) w hwC
          have hsym : ∀ a1 b1, Relation.EqvGen (pStep P) a1 b1 →
              (a1 ∈ S ∧ b1 ∉ S ∨ b1 ∈ S ∧ a1 ∉ S) →
              ∃ d : Fin (4 * e) × Fin 3, d.1 ∈ S ∧ (P.mate d).1 ∈ C \ S := by
            intro a1 b1 hab
            induction hab with
            | rel a1 b1 h' =>
              rintro (⟨haS, hbNS⟩ | ⟨hbS, haNS⟩)
              · rcases h' with ⟨_, hbC, k, hk⟩
                exact ⟨(a1, k), haS, Finset.mem_sdiff.mpr ⟨hk ▸ hbC, hk ▸ hbNS⟩⟩
              · rcases h' with ⟨haC, _, k, hk⟩
                let q := P.mate (a1, k)
                have hq1 : q.1 = b1 := hk
                have hmq1 : (P.mate q).1 = a1 := by rw [P.invol (a1, k) haC]
                exact ⟨q, hq1 ▸ hbS, Finset.mem_sdiff.mpr ⟨hmq1 ▸ haC, hmq1 ▸ haNS⟩⟩
            | refl _ => rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact absurd h1 h2
            | symm _ _ _ ih1 => rintro (h' | h'); exact ih1 (Or.inr h'); exact ih1 (Or.inl h')
            | trans a1 b1 c1 _ _ ih1 ih2 =>
              rintro (⟨haS, hcNS⟩ | ⟨hcS, haNS⟩)
              · by_cases hbS : b1 ∈ S
                · exact ih2 (Or.inl ⟨hbS, hcNS⟩)
                · exact ih1 (Or.inl ⟨haS, hbS⟩)
              · by_cases hbS : b1 ∈ S
                · exact ih1 (Or.inr ⟨hbS, haNS⟩)
                · exact ih2 (Or.inr ⟨hcS, hbS⟩)
          exact hsym u w hreach (Or.inl ⟨huS, hwS⟩)
        rcases hcross with ⟨d, hdS, hmdCS⟩
        let w := (P.mate d).1
        have hwC : w ∈ C := (Finset.mem_sdiff.mp hmdCS).1
        have hwS : w ∉ S := (Finset.mem_sdiff.mp hmdCS).2
        have hdC : d.1 ∈ C := hSC hdS
        let S' := insert w S
        have hS'C : S' ⊆ C := Finset.insert_subset hwC hSC
        have hS'ne : S'.Nonempty := ⟨w, Finset.mem_insert_self w S⟩
        have hdiff_eq : C \ S' = (C \ S).erase w := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, S', Finset.mem_insert, not_or]; tauto
        have hdiff' : (C \ S').card = m - 1 := by
          rw [hdiff_eq, Finset.card_erase_of_mem hmdCS, hm]
        obtain ⟨T', hT'D, hT'sym, hT'out, hT'card, hT'span⟩ :=
          ih (C \ S').card (by omega) S' hS'C hS'ne rfl
        have hd_not_T' : d ∉ T' := by
          intro h
          rcases hT'out d h with h1 | h2
          · exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_insert_of_mem hdS)
          · exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_insert_self w S)
        have hmd_not_T' : P.mate d ∉ T' := by
          intro h
          exact hd_not_T' (by rw [← P.invol d hdC]; exact hT'sym (P.mate d) h)
        have hd_ne_md : d ≠ P.mate d := (P.ne_self d hdC).symm
        let T := insert d (insert (P.mate d) T')
        refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          simp only [T, Finset.mem_insert] at hp
          rcases hp with rfl | rfl | hp'
          · exact Finset.mem_product.mpr ⟨hdC, Finset.mem_univ _⟩
          · exact Finset.mem_product.mpr ⟨hwC, Finset.mem_univ _⟩
          · exact hT'D hp'
        · intro p hp
          simp only [T, Finset.mem_insert] at hp ⊢
          rcases hp with rfl | rfl | hp'
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (P.invol d hdC)
          · exact Or.inr (Or.inr (hT'sym p hp'))
        · intro p hp
          simp only [T, Finset.mem_insert] at hp
          rcases hp with rfl | rfl | hp'
          · exact Or.inr hmdCS
          · exact Or.inl hmdCS
          · rcases hT'out p hp' with h1 | h2
            · exact Or.inl (Finset.mem_of_mem_erase (hdiff_eq ▸ h1))
            · exact Or.inr (Finset.mem_of_mem_erase (hdiff_eq ▸ h2))
        · rw [Finset.card_insert_of_notMem (by simp [hd_ne_md, hd_not_T']),
              Finset.card_insert_of_notMem hmd_not_T', hT'card, hdiff']
          omega
        · intro W hW
          have hW' : ∀ p ∈ D, p ∉ T' → (p.1 ∈ C \ S' ∨ (P.mate p).1 ∈ C \ S') → dartLbl a b p ∈ W := by
            intro p hpD hpT' hpCS'
            have hp_ne_d : p ≠ d := by
              intro h; subst h
              rcases hpCS' with h1 | h2
              · exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_insert_of_mem hdS)
              · exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_insert_self w S)
            have hp_ne_md : p ≠ P.mate d := by
              intro h; subst h
              rcases hpCS' with h1 | h2
              · exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_insert_self w S)
              · rw [P.invol d hdC] at h2
                exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_insert_of_mem hdS)
            have hpT : p ∉ T := by simp [T, hp_ne_d, hp_ne_md, hpT']
            have hpCS : p.1 ∈ C \ S ∨ (P.mate p).1 ∈ C \ S := by
              rcases hpCS' with h1 | h2
              · exact Or.inl (Finset.mem_of_mem_erase (hdiff_eq ▸ h1))
              · exact Or.inr (Finset.mem_of_mem_erase (hdiff_eq ▸ h2))
            exact hW p hpD hpT hpCS
          have hS'done : ∀ p ∈ D, p.1 ∈ C \ S' → dartLbl a b p ∈ W := hT'span W hW'

          have hw_other : ∀ k : Fin 3, (w, k) ≠ P.mate d → dartLbl a b (w, k) ∈ W := by
            intro k hk
            let q : Fin (4 * e) × Fin 3 := (w, k)
            have hqD : q ∈ D := Finset.mem_product.mpr ⟨hwC, Finset.mem_univ _⟩
            by_cases hqT : q ∈ T
            · have hq_ne_d : q ≠ d := fun h => hwS (by rw [show w = q.1 from rfl, congrArg Prod.fst h]; exact hdS)
              have hqT' : q ∈ T' := by
                simp only [T, Finset.mem_insert] at hqT
                rcases hqT with h1 | h2 | h3
                · exact absurd h1 hq_ne_d
                · exact absurd h2 hk
                · exact h3
              have hmq_CS' : (P.mate q).1 ∈ C \ S' := by
                rcases hT'out q hqT' with h1 | h2
                · exact absurd (Finset.mem_insert_self w S) (Finset.mem_sdiff.mp h1).2
                · exact h2
              have hmqD : P.mate q ∈ D := Finset.mem_product.mpr ⟨P.mem q hwC, Finset.mem_univ _⟩
              rw [← P.pres_lbl q hwC]
              exact hS'done (P.mate q) hmqD hmq_CS'
            · exact hW q hqD hqT (Or.inl hmdCS)

          have hw_all : ∀ k : Fin 3, dartLbl a b (w, k) ∈ W := by
            intro k
            by_cases hk : (w, k) = P.mate d
            · have hsum := dartLbl_sum_zero a b w
              rw [Fin.sum_univ_three] at hsum

              fin_cases k
              · change dartLbl a b (w, 0) ∈ W
                have h1 : dartLbl a b (w, 1) ∈ W := hw_other 1 (by intro h; rw [← hk] at h; simp at h)
                have h2 : dartLbl a b (w, 2) ∈ W := hw_other 2 (by intro h; rw [← hk] at h; simp at h)
                have heq : dartLbl a b (w, 0) = dartLbl a b (w, 1) + dartLbl a b (w, 2) := by
                  apply zmod2_add_eq_zero.mp
                  simpa [add_assoc] using hsum
                rw [heq]; exact W.add_mem h1 h2
              · change dartLbl a b (w, 1) ∈ W
                have h0 : dartLbl a b (w, 0) ∈ W := hw_other 0 (by intro h; rw [← hk] at h; simp at h)
                have h2 : dartLbl a b (w, 2) ∈ W := hw_other 2 (by intro h; rw [← hk] at h; simp at h)
                have heq : dartLbl a b (w, 1) = dartLbl a b (w, 0) + dartLbl a b (w, 2) := by
                  apply zmod2_add_eq_zero.mp
                  have : dartLbl a b (w, 1) + (dartLbl a b (w, 0) + dartLbl a b (w, 2)) =
                      dartLbl a b (w, 0) + dartLbl a b (w, 1) + dartLbl a b (w, 2) := by abel
                  rw [this]; exact hsum
                rw [heq]; exact W.add_mem h0 h2
              · change dartLbl a b (w, 2) ∈ W
                have h0 : dartLbl a b (w, 0) ∈ W := hw_other 0 (by intro h; rw [← hk] at h; simp at h)
                have h1 : dartLbl a b (w, 1) ∈ W := hw_other 1 (by intro h; rw [← hk] at h; simp at h)
                have heq : dartLbl a b (w, 2) = dartLbl a b (w, 0) + dartLbl a b (w, 1) := by
                  apply zmod2_add_eq_zero.mp
                  rw [add_comm]; exact hsum
                rw [heq]; exact W.add_mem h0 h1
            · exact hw_other k hk

          intro p hpD hpCS
          by_cases hpw : p.1 = w
          · have : p = (w, p.2) := Prod.ext hpw rfl
            rw [this]; exact hw_all p.2
          · exact hS'done p hpD (by rw [hdiff_eq]; exact Finset.mem_erase.mpr ⟨hpw, hpCS⟩)

  obtain ⟨T, hTD, hTsym, hTout, hTcard, hTspan⟩ :=
    hbuild {r} (Finset.singleton_subset_iff.mpr hr) (Finset.singleton_nonempty r)
  let U := D \ T
  let W : Submodule F2 (Fin n → F2) := Submodule.span F2 (↑(U.image (dartLbl a b)) : Set (Fin n → F2))
  have hnonr : ∀ p ∈ D, p.1 ∈ C \ {r} → dartLbl a b p ∈ W := by
    apply hTspan W
    intro p hpD hpT _
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hpD, hpT⟩, rfl⟩))
  have hallD : ∀ p ∈ D, dartLbl a b p ∈ W := by
    intro p hpD
    have hpC : p.1 ∈ C := (Finset.mem_product.mp hpD).1
    by_cases hpr : p.1 = r
    · by_cases hpT : p ∈ T
      · have hmpCS : (P.mate p).1 ∈ C \ {r} := by
          rcases hTout p hpT with h1 | h2
          · exact absurd (Finset.mem_singleton.mpr hpr) (Finset.mem_sdiff.mp h1).2
          · exact h2
        rw [← P.pres_lbl p hpC]
        exact hnonr (P.mate p) (Finset.mem_product.mpr ⟨P.mem p hpC, Finset.mem_univ _⟩) hmpCS
      · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hpD, hpT⟩, rfl⟩))
    · exact hnonr p hpD (Finset.mem_sdiff.mpr ⟨hpC, by simp [hpr]⟩)
  have hle_W : spanOf a b C ≤ W := by
    rw [spanOf, Submodule.span_le]
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hallD (i, 0) (Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩)
    · exact hallD (i, 1) (Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩)
  have hU_card : U.card = C.card + 2 := by
    have hDcard : D.card = 3 * C.card := by simp [D, mul_comm]
    have hCr : (C \ {r}).card = C.card - 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hr), Finset.card_singleton]
    have hCpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨r, hr⟩
    rw [Finset.card_sdiff_of_subset hTD, hDcard, hTcard, hCr]
    omega
  have himg_le : 2 * (U.image (dartLbl a b)).card ≤ U.card := by
    apply card_image_le_half_of_fpf_invol U P.mate (dartLbl a b)
    intro p hp
    have hpD : p ∈ D := (Finset.mem_sdiff.mp hp).1
    have hpT : p ∉ T := (Finset.mem_sdiff.mp hp).2
    have hpC : p.1 ∈ C := (Finset.mem_product.mp hpD).1
    have hmpT : P.mate p ∉ T := fun h => hpT (by rw [← P.invol p hpC]; exact hTsym _ h)
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨P.mem p hpC, Finset.mem_univ _⟩, hmpT⟩,
           P.invol p hpC, P.ne_self p hpC, P.pres_lbl p hpC⟩
  have hfin_W : Module.finrank F2 W ≤ (U.image (dartLbl a b)).card := by
    simpa [W] using finrank_span_le_card (R := F2) (↑(U.image (dartLbl a b)) : Set (Fin n → F2))
  have hfin_C : rkOf a b C ≤ Module.finrank F2 W := Submodule.finrank_mono hle_W
  omega

lemma spanOf_union {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2))
    (S1 S2 : Finset (Fin (4 * e))) :
    spanOf a b (S1 ∪ S2) = spanOf a b S1 ⊔ spanOf a b S2 := by
  unfold spanOf
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Finset.mem_coe, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨i, hi | hi, rfl⟩ | ⟨i, hi | hi, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩))
    · exact Or.inl ⟨i, Or.inl hi, rfl⟩
    · exact Or.inr ⟨i, Or.inl hi, rfl⟩
    · exact Or.inl ⟨i, Or.inr hi, rfl⟩
    · exact Or.inr ⟨i, Or.inr hi, rfl⟩

lemma rkOf_union_le {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2))
    (S1 S2 : Finset (Fin (4 * e))) :
    rkOf a b (S1 ∪ S2) ≤ rkOf a b S1 + rkOf a b S2 := by
  unfold rkOf
  rw [spanOf_union]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (spanOf a b S1) (spanOf a b S2)
  omega

lemma rkOf_submod {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2))
    {S1 S2 C : Finset (Fin (4 * e))} (hsub : S1 ⊆ S2) :
    rkOf a b (S2 ∪ C) + rkOf a b S1 ≤ rkOf a b S2 + rkOf a b (S1 ∪ C) := by
  unfold rkOf
  rw [spanOf_union, spanOf_union]
  have hle : spanOf a b S1 ≤ spanOf a b S2 := by
    apply Submodule.span_mono
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hv ⊢
    rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inl ⟨i, hsub hi, rfl⟩
    · exact Or.inr ⟨i, hsub hi, rfl⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (spanOf a b S2) (spanOf a b C)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (spanOf a b S1) (spanOf a b C)
  have hinf : Module.finrank F2 (spanOf a b S1 ⊓ spanOf a b C : Submodule F2 (Fin n → F2)) ≤
      Module.finrank F2 (spanOf a b S2 ⊓ spanOf a b C : Submodule F2 (Fin n → F2)) :=
    Submodule.finrank_mono (inf_le_inf_right (spanOf a b C) hle)
  omega

lemma rkOf_biUnion_le {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2))
    (A : Finset (Finset (Fin (4 * e)))) (S : Finset (Fin (4 * e))) :
    rkOf a b (S ∪ A.biUnion id) ≤ rkOf a b S + ∑ C ∈ A, rkOf a b C := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert C A hCA ih =>
    rw [Finset.biUnion_insert, id_eq, ← Finset.union_assoc, Finset.sum_insert hCA]
    have h1 := rkOf_union_le a b (S ∪ A.biUnion id) C
    rw [Finset.union_right_comm] at h1
    omega

lemma rkOf_biUnion_add_two {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2))
    (K : Finset (Fin (4 * e))) (B : Finset (Finset (Fin (4 * e))))
    (hB : ∀ C ∈ B, rkOf a b (K ∪ C) ≤ rkOf a b K + 2) :
    rkOf a b (K ∪ B.biUnion id) ≤ rkOf a b K + 2 * B.card := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert C B hCB ih =>
    rw [Finset.biUnion_insert, id_eq, Finset.card_insert_of_notMem hCB]
    have hih := ih (fun C' hC' => hB C' (Finset.mem_insert_of_mem hC'))
    have hC := hB C (Finset.mem_insert_self C B)
    have hsub : K ⊆ K ∪ B.biUnion id := Finset.subset_union_left
    have hsm := rkOf_submod a b (C := C) hsub
    have hunion : K ∪ (C ∪ B.biUnion id) = (K ∪ B.biUnion id) ∪ C := by
      ext x; simp [or_comm, or_left_comm]
    rw [hunion]
    omega

lemma greedy_keep {n e : Nat} (a b : Fin (4 * e) → (Fin n → F2))
    (A : Finset (Finset (Fin (4 * e))))
    (hA : ∀ C ∈ A, rkOf a b C ≤ 3) :
    ∃ keep ⊆ A,
      (∀ C ∈ keep, rkOf a b C = 3) ∧
      rkOf a b (keep.biUnion id) = 3 * keep.card ∧
      (∀ C ∈ A \ keep, rkOf a b (keep.biUnion id ∪ C) ≤ rkOf a b (keep.biUnion id) + 2) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, by simp, ?_, by simp⟩
    rw [Finset.biUnion_empty, Finset.card_empty, mul_zero, rkOf, spanOf, Finset.image_empty, Finset.image_empty, Finset.union_empty, Finset.coe_empty, Submodule.span_empty, finrank_bot]
  | insert C A hCA ih =>
    obtain ⟨keep, hkeepA, hrk3, hsum3, hrej⟩ := ih (fun C' hC' => hA C' (Finset.mem_insert_of_mem hC'))
    have hC_le : rkOf a b C ≤ 3 := hA C (Finset.mem_insert_self C A)
    have hstep_le : rkOf a b (keep.biUnion id ∪ C) ≤ rkOf a b (keep.biUnion id) + 3 :=
      (rkOf_union_le a b _ C).trans (by omega)
    by_cases hgain : rkOf a b (keep.biUnion id ∪ C) = rkOf a b (keep.biUnion id) + 3
    · have hC_not_keep : C ∉ keep := fun h => hCA (hkeepA h)
      refine ⟨insert C keep, Finset.insert_subset_insert C hkeepA, ?_, ?_, ?_⟩
      · intro C' hC'
        rcases Finset.mem_insert.mp hC' with hC'eq | hC'k
        · rw [hC'eq]
          have hle2 := rkOf_union_le a b (keep.biUnion id) C
          omega
        · exact hrk3 C' hC'k
      · rw [Finset.biUnion_insert, id_eq, Finset.union_comm, hgain, hsum3,
            Finset.card_insert_of_notMem hC_not_keep]
        omega
      · intro C' hC'
        have hC'A : C' ∈ A \ keep := by
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hC' ⊢
          rcases hC' with ⟨rfl | h1, hne, hnk⟩
          · exact absurd rfl hne
          · exact ⟨h1, hnk⟩
        have hsub : keep.biUnion id ⊆ (insert C keep).biUnion id :=
          Finset.biUnion_subset_biUnion_of_subset_left id (Finset.subset_insert C keep)
        have hsm := rkOf_submod a b (C := C') hsub
        have hr := hrej C' hC'A
        omega
    · refine ⟨keep, Finset.Subset.trans hkeepA (Finset.subset_insert C A), hrk3, hsum3, ?_⟩
      intro C' hC'
      simp only [Finset.mem_sdiff, Finset.mem_insert] at hC'
      rcases hC' with ⟨rfl | hC'A, hC'nk⟩
      · omega
      · exact hrej C' (Finset.mem_sdiff.mpr ⟨hC'A, hC'nk⟩)

def vec5 (m : Nat) : Fin 5 → F2 :=
  fun k => if m.testBit k.val then 1 else 0

def q3a : Fin 8 → (Fin 5 → F2)
  | ⟨0, _⟩ => vec5 19
  | ⟨1, _⟩ => vec5 19
  | ⟨2, _⟩ => vec5 21
  | ⟨3, _⟩ => vec5 24
  | ⟨4, _⟩ => vec5 6
  | ⟨5, _⟩ => vec5 8
  | ⟨6, _⟩ => vec5 16
  | ⟨7, _⟩ => vec5 24

def q3b : Fin 8 → (Fin 5 → F2)
  | ⟨0, _⟩ => vec5 21
  | ⟨1, _⟩ => vec5 10
  | ⟨2, _⟩ => vec5 1
  | ⟨3, _⟩ => vec5 25
  | ⟨4, _⟩ => vec5 4
  | ⟨5, _⟩ => vec5 2
  | ⟨6, _⟩ => vec5 20
  | ⟨7, _⟩ => vec5 8

def q3P : Fin 8 → (Fin 5 → F2)
  | ⟨0, _⟩ => vec5 6
  | ⟨7, _⟩ => vec5 16
  | _ => 0

def q3d : Fin 8 → F2
  | ⟨0, _⟩ => 1
  | ⟨7, _⟩ => 1
  | _ => 0

lemma q3_nondeg : ∀ r : Fin 8, q3a r ≠ 0 ∧ q3b r ≠ 0 ∧ q3a r ≠ q3b r := by
  decide

lemma q3_err_card : ∀ x : Fin 5 → F2,
    ((Finset.univ : Finset (Fin 8)).filter (fun r =>
      dotProduct (q3P r) x + q3d r ≠ dotProduct (q3a r) x * dotProduct (q3b r) x)).card = 2 := by
  decide

lemma q3_basis (t : Fin 5) :
    ∃ r : Fin 8, q3a r = Pi.single t (1 : F2) ∨ q3b r = Pi.single t (1 : F2) := by
  fin_cases t
  · exact ⟨⟨2, by omega⟩, Or.inr (by decide)⟩
  · exact ⟨⟨5, by omega⟩, Or.inr (by decide)⟩
  · exact ⟨⟨4, by omega⟩, Or.inr (by decide)⟩
  · exact ⟨⟨5, by omega⟩, Or.inl (by decide)⟩
  · exact ⟨⟨6, by omega⟩, Or.inl (by decide)⟩

def embed5 (g : Nat) (q : Nat) (v : Fin 5 → F2) : Fin (5 * g) → F2 :=
  fun k => if k.val / 5 = q then v ⟨k.val % 5, Nat.mod_lt _ (by omega)⟩ else 0

lemma dotProduct_embed5 (g : Nat) (q : Nat) (hq : q < g) (v : Fin 5 → F2) (x : Fin (5 * g) → F2) :
    dotProduct (embed5 g q v) x =
      dotProduct v (fun t : Fin 5 => x ⟨5 * q + t.val, by omega⟩) := by
  unfold dotProduct embed5
  have hsplit : (∑ k : Fin (5 * g), (if k.val / 5 = q then v ⟨k.val % 5, Nat.mod_lt _ (by omega)⟩ else 0) * x k) =
      ∑ k ∈ (Finset.univ : Finset (Fin (5 * g))).filter (fun k => k.val / 5 = q),
        v ⟨k.val % 5, Nat.mod_lt _ (by omega)⟩ * x k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [hsplit]
  symm
  apply Finset.sum_bij (fun (t : Fin 5) _ => (⟨5 * q + t.val, by omega⟩ : Fin (5 * g)))
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro t1 _ t2 _ h
    ext
    have := congrArg Fin.val h
    dsimp only at this
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨⟨k.val % 5, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
    ext; dsimp only; omega
  · intro t _
    have hmod : (5 * q + t.val) % 5 = t.val := by omega
    congr 2
    ext; exact hmod.symm

lemma embed5_add (g q : Nat) (u v : Fin 5 → F2) :
    embed5 g q (u + v) = embed5 g q u + embed5 g q v := by
  funext k
  unfold embed5
  simp only [Pi.add_apply]
  split_ifs <;> simp

lemma embed5_injective {g q : Nat} (hq : q < g) {u v : Fin 5 → F2}
    (h : embed5 g q u = embed5 g q v) : u = v := by
  funext t
  have hk := congrFun h ⟨5 * q + t.val, by omega⟩
  unfold embed5 at hk
  have hdiv : (5 * q + t.val) / 5 = q := by omega
  have hmod : (5 * q + t.val) % 5 = t.val := by omega
  simp only [hdiv, ↓reduceIte] at hk
  have hfin : (⟨(5 * q + t.val) % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) = t := by ext; exact hmod
  rwa [hfin] at hk

lemma embed5_ne_zero {g q : Nat} (hq : q < g) {u : Fin 5 → F2} (hu : u ≠ 0) :
    embed5 g q u ≠ 0 := by
  intro h
  have h0 : embed5 g q 0 = 0 := by funext k; unfold embed5; split_ifs <;> rfl
  exact hu (embed5_injective hq (h.trans h0.symm))

lemma embed5_disjoint {g q1 q2 : Nat} (hq1 : q1 < g) (hne : q1 ≠ q2)
    {u v : Fin 5 → F2} (hu : u ≠ 0) :
    embed5 g q1 u ≠ embed5 g q2 v := by
  intro h
  have hex : ∃ t : Fin 5, u t ≠ 0 := by
    by_contra hall; push Not at hall; exact hu (funext hall)
  rcases hex with ⟨t, ht⟩
  have hk := congrFun h ⟨5 * q1 + t.val, by omega⟩
  unfold embed5 at hk
  have hdiv1 : (5 * q1 + t.val) / 5 = q1 := by omega
  have hmod : (5 * q1 + t.val) % 5 = t.val := by omega
  simp only [hdiv1, hne, ↓reduceIte] at hk
  have hfin : (⟨(5 * q1 + t.val) % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) = t := by ext; exact hmod
  rw [hfin] at hk
  exact ht hk

lemma q3_adj_chain :
    (∃ v ∈ ({q3a 0, q3b 0, q3a 0 + q3b 0} : Finset (Fin 5 → F2)), v ∈ ({q3a 1, q3b 1, q3a 1 + q3b 1} : Finset (Fin 5 → F2))) ∧
    (∃ v ∈ ({q3a 0, q3b 0, q3a 0 + q3b 0} : Finset (Fin 5 → F2)), v ∈ ({q3a 2, q3b 2, q3a 2 + q3b 2} : Finset (Fin 5 → F2))) ∧
    (∃ v ∈ ({q3a 2, q3b 2, q3a 2 + q3b 2} : Finset (Fin 5 → F2)), v ∈ ({q3a 3, q3b 3, q3a 3 + q3b 3} : Finset (Fin 5 → F2))) ∧
    (∃ v ∈ ({q3a 0, q3b 0, q3a 0 + q3b 0} : Finset (Fin 5 → F2)), v ∈ ({q3a 4, q3b 4, q3a 4 + q3b 4} : Finset (Fin 5 → F2))) ∧
    (∃ v ∈ ({q3a 4, q3b 4, q3a 4 + q3b 4} : Finset (Fin 5 → F2)), v ∈ ({q3a 5, q3b 5, q3a 5 + q3b 5} : Finset (Fin 5 → F2))) ∧
    (∃ v ∈ ({q3a 4, q3b 4, q3a 4 + q3b 4} : Finset (Fin 5 → F2)), v ∈ ({q3a 6, q3b 6, q3a 6 + q3b 6} : Finset (Fin 5 → F2))) ∧
    (∃ v ∈ ({q3a 5, q3b 5, q3a 5 + q3b 5} : Finset (Fin 5 → F2)), v ∈ ({q3a 7, q3b 7, q3a 7 + q3b 7} : Finset (Fin 5 → F2))) := by
  decide

lemma q3_construction (g : Nat) :
    ∃ a b : Fin (4 * (2 * g)) → (Fin (5 * g) → F2),
      ((∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) ∧
        ∃ (P : Fin (4 * (2 * g)) → (Fin (5 * g) → F2)) (d : Fin (4 * (2 * g)) → F2),
          ∀ x : Fin (5 * g) → F2,
            ((Finset.univ : Finset (Fin (4 * (2 * g)))).filter (fun i =>
              dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ 2 * g) ∧
      rkOf a b Finset.univ = 5 * g ∧
      (partsOf a b).card = g ∧
      (∀ C ∈ partsOf a b, C.card = 8) := by
  let a : Fin (4 * (2 * g)) → (Fin (5 * g) → F2) := fun i =>
    embed5 g (i.val / 8) (q3a ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩)
  let b : Fin (4 * (2 * g)) → (Fin (5 * g) → F2) := fun i =>
    embed5 g (i.val / 8) (q3b ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩)
  let P : Fin (4 * (2 * g)) → (Fin (5 * g) → F2) := fun i =>
    embed5 g (i.val / 8) (q3P ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩)
  let d : Fin (4 * (2 * g)) → F2 := fun i =>
    q3d ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  ·
    constructor
    · intro i
      have hq : i.val / 8 < g := by omega
      rcases q3_nondeg ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩ with ⟨ha, hb, hab⟩
      exact ⟨embed5_ne_zero hq ha, embed5_ne_zero hq hb, fun h => hab (embed5_injective hq h)⟩
    · refine ⟨P, d, ?_⟩
      intro x

      have hcard_eq : ((Finset.univ : Finset (Fin (4 * (2 * g)))).filter (fun i =>
          dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card =
          ∑ q : Fin g, ((Finset.univ : Finset (Fin 8)).filter (fun r =>
            dotProduct (q3P r) (fun t : Fin 5 => x ⟨5 * q.val + t.val, by omega⟩) + q3d r ≠
            dotProduct (q3a r) (fun t : Fin 5 => x ⟨5 * q.val + t.val, by omega⟩) *
            dotProduct (q3b r) (fun t : Fin 5 => x ⟨5 * q.val + t.val, by omega⟩))).card := by
        rw [Finset.card_filter]
        simp_rw [Finset.card_filter]
        rw [← Finset.sum_product']
        apply Finset.sum_bij (fun (i : Fin (4 * (2 * g))) _ =>
          ((⟨i.val / 8, by omega⟩ : Fin g), (⟨i.val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8)))
        · intro _ _; exact Finset.mem_univ _
        · intro i1 _ i2 _ h
          ext
          have h1 := congrArg (fun p => p.1.val) h
          have h2 := congrArg (fun p => p.2.val) h
          dsimp only at h1 h2
          omega
        · intro p _
          refine ⟨⟨8 * p.1.val + p.2.val, by omega⟩, Finset.mem_univ _, ?_⟩
          ext <;> dsimp only <;> omega
        · intro i _
          have hq : i.val / 8 < g := by omega
          simp only [a, b, P, d, dotProduct_embed5 g (i.val / 8) hq]
      rw [hcard_eq]
      have h2 : ∀ q : Fin g, ((Finset.univ : Finset (Fin 8)).filter (fun r =>
            dotProduct (q3P r) (fun t : Fin 5 => x ⟨5 * q.val + t.val, by omega⟩) + q3d r ≠
            dotProduct (q3a r) (fun t : Fin 5 => x ⟨5 * q.val + t.val, by omega⟩) *
            dotProduct (q3b r) (fun t : Fin 5 => x ⟨5 * q.val + t.val, by omega⟩))).card = 2 :=
        fun q => q3_err_card _
      simp_rw [h2]
      simp [Finset.sum_const, mul_comm]
  ·
    have htop : spanOf a b Finset.univ = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have hv : v = ∑ k : Fin (5 * g), v k • Pi.single k (1 : F2) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      rw [hv]
      apply Submodule.sum_mem
      intro k _
      apply Submodule.smul_mem
      let q := k.val / 5
      let t : Fin 5 := ⟨k.val % 5, Nat.mod_lt _ (by omega)⟩
      have hq : q < g := by omega
      obtain ⟨r, hr⟩ := q3_basis t
      let idx : Fin (4 * (2 * g)) := ⟨8 * q + r.val, by omega⟩
      have hidx_q : idx.val / 8 = q := by dsimp only [idx]; omega
      have hidx_r : (⟨idx.val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8) = r := by
        ext; dsimp only [idx]; omega
      have hembed_single : embed5 g q (Pi.single t (1 : F2)) = Pi.single k (1 : F2) := by
        funext j
        unfold embed5
        by_cases hjk : j = k
        · subst hjk
          simp [q, t]
        · rw [Pi.single_eq_of_ne hjk]
          split_ifs with hdiv
          · have hmod : (⟨j.val % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) ≠ t := by
              intro h
              have hm : j.val % 5 = k.val % 5 := congrArg Fin.val h
              exact hjk (Fin.ext (by omega))
            exact Pi.single_eq_of_ne hmod _
          · rfl
      apply Submodule.subset_span
      simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      rcases hr with ha_eq | hb_eq
      · left; exact ⟨idx, by simp [a, hidx_q, hidx_r, ha_eq, hembed_single]⟩
      · right; exact ⟨idx, by simp [b, hidx_q, hidx_r, hb_eq, hembed_single]⟩
    unfold rkOf
    rw [htop, finrank_top]
    simp
  ·
    have heqv_iff : ∀ i j : Fin (4 * (2 * g)), Relation.EqvGen (adjOf a b) i j ↔ i.val / 8 = j.val / 8 := by
      intro i j
      constructor
      · intro h
        induction h with
        | rel x y hxy =>
          rcases hxy with ⟨v, hvx, hvy⟩
          by_contra hne
          have hqx : x.val / 8 < g := by omega
          have hmem : ∀ z : Fin (4 * (2 * g)), v ∈ freqOf a b z →
              ∃ u : Fin 5 → F2, u ≠ 0 ∧ v = embed5 g (z.val / 8) u := by
            intro z hvz
            rcases q3_nondeg ⟨z.val % 8, Nat.mod_lt _ (by omega)⟩ with ⟨ha, hb, hab⟩
            simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hvz
            rcases hvz with rfl | rfl | rfl
            · exact ⟨q3a _, ha, rfl⟩
            · exact ⟨q3b _, hb, rfl⟩
            · exact ⟨q3a _ + q3b _, fun h => hab (zmod2_add_eq_zero.mp h), (embed5_add _ _ _ _).symm⟩
          rcases hmem x hvx with ⟨ux, hux, hvx_eq⟩
          rcases hmem y hvy with ⟨uy, _, hvy_eq⟩
          exact embed5_disjoint hqx hne hux (hvx_eq.symm.trans hvy_eq)
        | refl _ => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
      · intro hq
        let q := i.val / 8
        have hqg : q < g := by omega
        let hmk : Fin 8 → Fin (4 * (2 * g)) := fun r => ⟨8 * q + r.val, by omega⟩
        have hadj_lift : ∀ r1 r2 : Fin 8,
            (∃ v ∈ ({q3a r1, q3b r1, q3a r1 + q3b r1} : Finset (Fin 5 → F2)),
              v ∈ ({q3a r2, q3b r2, q3a r2 + q3b r2} : Finset (Fin 5 → F2))) →
            Relation.EqvGen (adjOf a b) (hmk r1) (hmk r2) := by
          intro r1 r2 ⟨v, hv1, hv2⟩
          apply Relation.EqvGen.rel
          refine ⟨embed5 g q v, ?_, ?_⟩
          · have h1q : (hmk r1).val / 8 = q := by dsimp only [hmk]; omega
            have h1r : (⟨(hmk r1).val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8) = r1 := by ext; dsimp only [hmk]; omega
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv1
            simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, a, b, h1q, h1r]
            rcases hv1 with rfl | rfl | rfl
            · left; rfl
            · right; left; rfl
            · right; right; exact embed5_add _ _ _ _
          · have h2q : (hmk r2).val / 8 = q := by dsimp only [hmk]; omega
            have h2r : (⟨(hmk r2).val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8) = r2 := by ext; dsimp only [hmk]; omega
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv2
            simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, a, b, h2q, h2r]
            rcases hv2 with rfl | rfl | rfl
            · left; rfl
            · right; left; rfl
            · right; right; exact embed5_add _ _ _ _
        rcases q3_adj_chain with ⟨c01, c02, c23, c04, c45, c46, c57⟩
        have h0r : ∀ r : Fin 8, Relation.EqvGen (adjOf a b) (hmk 0) (hmk r) := by
          intro r
          fin_cases r
          · exact Relation.EqvGen.refl _
          · exact hadj_lift 0 1 c01
          · exact hadj_lift 0 2 c02
          · exact Relation.EqvGen.trans _ (hmk 2) _ (hadj_lift 0 2 c02) (hadj_lift 2 3 c23)
          · exact hadj_lift 0 4 c04
          · exact Relation.EqvGen.trans _ (hmk 4) _ (hadj_lift 0 4 c04) (hadj_lift 4 5 c45)
          · exact Relation.EqvGen.trans _ (hmk 4) _ (hadj_lift 0 4 c04) (hadj_lift 4 6 c46)
          · exact Relation.EqvGen.trans _ (hmk 5) _
              (Relation.EqvGen.trans _ (hmk 4) _ (hadj_lift 0 4 c04) (hadj_lift 4 5 c45))
              (hadj_lift 5 7 c57)
        have hi_eq : i = hmk ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩ := by ext; dsimp only [hmk, q]; omega
        have hj_eq : j = hmk ⟨j.val % 8, Nat.mod_lt _ (by omega)⟩ := by ext; dsimp only [hmk, q]; omega
        rw [hi_eq, hj_eq]
        exact Relation.EqvGen.trans _ (hmk 0) _ (Relation.EqvGen.symm _ _ (h0r _)) (h0r _)
    have hparts_eq : partsOf a b = (Finset.univ : Finset (Fin g)).image
        (fun q : Fin g => (Finset.univ : Finset (Fin (4 * (2 * g)))).filter (fun j => j.val / 8 = q.val)) := by
      ext C
      simp only [partsOf, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨⟨i.val / 8, by omega⟩, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, heqv_iff]
        exact eq_comm
      · rintro ⟨q, rfl⟩
        refine ⟨⟨8 * q.val, by omega⟩, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, heqv_iff]
        have hq8 : (8 * q.val) / 8 = q.val := by omega
        rw [hq8]
        exact eq_comm
    rw [hparts_eq, Finset.card_image_of_injective]
    · simp
    · intro q1 q2 h
      dsimp only at h
      have hmem : (⟨8 * q1.val, by omega⟩ : Fin (4 * (2 * g))) ∈
          (Finset.univ : Finset (Fin (4 * (2 * g)))).filter (fun j => j.val / 8 = q1.val) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [h] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      ext; omega
  ·
    intro C hC
    have heqv_iff : ∀ i j : Fin (4 * (2 * g)), Relation.EqvGen (adjOf a b) i j ↔ i.val / 8 = j.val / 8 := by
      intro i j
      constructor
      · intro h
        induction h with
        | rel x y hxy =>
          rcases hxy with ⟨v, hvx, hvy⟩
          by_contra hne
          have hqx : x.val / 8 < g := by omega
          have hmem : ∀ z : Fin (4 * (2 * g)), v ∈ freqOf a b z →
              ∃ u : Fin 5 → F2, u ≠ 0 ∧ v = embed5 g (z.val / 8) u := by
            intro z hvz
            rcases q3_nondeg ⟨z.val % 8, Nat.mod_lt _ (by omega)⟩ with ⟨ha, hb, hab⟩
            simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hvz
            rcases hvz with rfl | rfl | rfl
            · exact ⟨q3a _, ha, rfl⟩
            · exact ⟨q3b _, hb, rfl⟩
            · exact ⟨q3a _ + q3b _, fun h => hab (zmod2_add_eq_zero.mp h), (embed5_add _ _ _ _).symm⟩
          rcases hmem x hvx with ⟨ux, hux, hvx_eq⟩
          rcases hmem y hvy with ⟨uy, _, hvy_eq⟩
          exact embed5_disjoint hqx hne hux (hvx_eq.symm.trans hvy_eq)
        | refl _ => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
      · intro hq
        let q := i.val / 8
        have hqg : q < g := by omega
        let hmk : Fin 8 → Fin (4 * (2 * g)) := fun r => ⟨8 * q + r.val, by omega⟩
        have hadj_lift : ∀ r1 r2 : Fin 8,
            (∃ v ∈ ({q3a r1, q3b r1, q3a r1 + q3b r1} : Finset (Fin 5 → F2)),
              v ∈ ({q3a r2, q3b r2, q3a r2 + q3b r2} : Finset (Fin 5 → F2))) →
            Relation.EqvGen (adjOf a b) (hmk r1) (hmk r2) := by
          intro r1 r2 ⟨v, hv1, hv2⟩
          apply Relation.EqvGen.rel
          refine ⟨embed5 g q v, ?_, ?_⟩
          · have h1q : (hmk r1).val / 8 = q := by dsimp only [hmk]; omega
            have h1r : (⟨(hmk r1).val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8) = r1 := by ext; dsimp only [hmk]; omega
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv1
            simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, a, b, h1q, h1r]
            rcases hv1 with rfl | rfl | rfl
            · left; rfl
            · right; left; rfl
            · right; right; exact embed5_add _ _ _ _
          · have h2q : (hmk r2).val / 8 = q := by dsimp only [hmk]; omega
            have h2r : (⟨(hmk r2).val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8) = r2 := by ext; dsimp only [hmk]; omega
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv2
            simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, a, b, h2q, h2r]
            rcases hv2 with rfl | rfl | rfl
            · left; rfl
            · right; left; rfl
            · right; right; exact embed5_add _ _ _ _
        rcases q3_adj_chain with ⟨c01, c02, c23, c04, c45, c46, c57⟩
        have h0r : ∀ r : Fin 8, Relation.EqvGen (adjOf a b) (hmk 0) (hmk r) := by
          intro r
          fin_cases r
          · exact Relation.EqvGen.refl _
          · exact hadj_lift 0 1 c01
          · exact hadj_lift 0 2 c02
          · exact Relation.EqvGen.trans _ (hmk 2) _ (hadj_lift 0 2 c02) (hadj_lift 2 3 c23)
          · exact hadj_lift 0 4 c04
          · exact Relation.EqvGen.trans _ (hmk 4) _ (hadj_lift 0 4 c04) (hadj_lift 4 5 c45)
          · exact Relation.EqvGen.trans _ (hmk 4) _ (hadj_lift 0 4 c04) (hadj_lift 4 6 c46)
          · exact Relation.EqvGen.trans _ (hmk 5) _
              (Relation.EqvGen.trans _ (hmk 4) _ (hadj_lift 0 4 c04) (hadj_lift 4 5 c45))
              (hadj_lift 5 7 c57)
        have hi_eq : i = hmk ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩ := by ext; dsimp only [hmk, q]; omega
        have hj_eq : j = hmk ⟨j.val % 8, Nat.mod_lt _ (by omega)⟩ := by ext; dsimp only [hmk, q]; omega
        rw [hi_eq, hj_eq]
        exact Relation.EqvGen.trans _ (hmk 0) _ (Relation.EqvGen.symm _ _ (h0r _)) (h0r _)
    rcases mem_partsOf_iff.mp hC with ⟨i, rfl⟩
    have hbij : (Finset.univ.filter (fun j : Fin (4 * (2 * g)) =>
        @decide (Relation.EqvGen (adjOf a b) i j) (Classical.propDecidable _) = true)).card =
        (Finset.univ : Finset (Fin 8)).card := by
      symm
      apply Finset.card_bij (fun (r : Fin 8) _ => (⟨8 * (i.val / 8) + r.val, by omega⟩ : Fin (4 * (2 * g))))
      · intro r _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, heqv_iff]
        omega
      · intro r1 _ r2 _ h
        ext; have := congrArg Fin.val h; dsimp only at this; omega
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, heqv_iff] at hj
        refine ⟨⟨j.val % 8, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
        ext; dsimp only; omega
    simpa using hbij

end PEqualNP.Outside.L_lib_965_aux

theorem PEqualNP.Outside.L_lib_965 : (let F := ZMod 2
let eligible := fun (n e : Nat) (a b : Fin (4*e) → (Fin n → F)) =>
  (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) ∧
  ∃ (P : Fin (4*e) → (Fin n → F)) (d : Fin (4*e) → F), ∀ x : Fin n → F,
    ((Finset.univ : Finset (Fin (4*e))).filter (fun i =>
      dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ e
let parts := fun (n e : Nat) (a b : Fin (4*e) → (Fin n → F)) =>
  let freq := fun i : Fin (4*e) => ({a i, b i, a i + b i} : Finset (Fin n → F))
  let adj := fun (i j : Fin (4*e)) => ∃ v ∈ freq i, v ∈ freq j
  (Finset.univ : Finset (Fin (4*e))).image (fun i => (Finset.univ : Finset (Fin (4*e))).filter
    (fun j => @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
let rk := fun (n e : Nat) (a b : Fin (4*e) → (Fin n → F)) (S : Finset (Fin (4*e))) =>
  Module.finrank F (Submodule.span F (↑(S.image a ∪ S.image b) : Set (Fin n → F)))
(∀ (n e : Nat) (a b : Fin (4*e) → (Fin n → F)), eligible n e a b →
  let cs := parts n e a b
  let r := rk n e a b Finset.univ
  r ≤ 2*e + cs.card ∧ cs.card ≤ e ∧
    ∃ keep : Finset (Finset (Fin (4*e))), keep ⊆ cs ∧
      (∀ C ∈ keep, C.card = 4 ∧ rk n e a b C = 3) ∧
      rk n e a b (keep.biUnion id) = 3*keep.card ∧ e ≤ keep.card + (3*e-r) + (e-cs.card)) ∧
(∀ g : Nat, ∃ a b : Fin (4*(2*g)) → (Fin (5*g) → F),
  eligible (5*g) (2*g) a b ∧ rk (5*g) (2*g) a b Finset.univ = 5*g ∧
  (parts (5*g) (2*g) a b).card = g ∧ (∀ C ∈ parts (5*g) (2*g) a b, C.card = 8))) := by
  dsimp only
  constructor
  · intro n e a b ⟨hnondeg, happrox⟩
    change let cs := L_lib_965_aux.partsOf a b
      let r := L_lib_965_aux.rkOf a b Finset.univ
      r ≤ 2 * e + cs.card ∧ cs.card ≤ e ∧
        ∃ keep : Finset (Finset (Fin (4 * e))), keep ⊆ cs ∧
          (∀ C ∈ keep, C.card = 4 ∧ L_lib_965_aux.rkOf a b C = 3) ∧
          L_lib_965_aux.rkOf a b (keep.biUnion id) = 3 * keep.card ∧ e ≤ keep.card + (3 * e - r) + (e - cs.card)
    dsimp only
    obtain ⟨s1, s2, hs1, hs2, hbal⟩ := L_lib_965_aux.eligible_signs hnondeg happrox
    have hcomp_props : ∀ C ∈ L_lib_965_aux.partsOf a b, 4 ∣ C.card ∧ 4 ≤ C.card ∧ L_lib_965_aux.rkOf a b C ≤ C.card / 2 + 1 := by
      intro C hC
      obtain ⟨heven, hdiv4⟩ := L_lib_965_aux.comp_parity_and_div4 hnondeg s1 s2 hs1 hs2 hbal hC
      have hne := L_lib_965_aux.partsOf_nonempty hC
      have hpos : 0 < C.card := Finset.card_pos.mpr hne
      have hge4 : 4 ≤ C.card := by rcases hdiv4 with ⟨k, hk⟩; omega
      exact ⟨hdiv4, hge4, L_lib_965_aux.rk_comp_le hnondeg hC heven⟩
    have hsum_card := L_lib_965_aux.partsOf_sum_card a b
    have hcs_le : (L_lib_965_aux.partsOf a b).card ≤ e := by
      have h4 : 4 * (L_lib_965_aux.partsOf a b).card ≤ ∑ C ∈ L_lib_965_aux.partsOf a b, C.card := by
        calc 4 * (L_lib_965_aux.partsOf a b).card
            = ∑ _C ∈ L_lib_965_aux.partsOf a b, 4 := by simp [Finset.sum_const, mul_comm]
          _ ≤ ∑ C ∈ L_lib_965_aux.partsOf a b, C.card := Finset.sum_le_sum (fun C hC => (hcomp_props C hC).2.1)
      omega
    have hr_le : L_lib_965_aux.rkOf a b Finset.univ ≤ 2 * e + (L_lib_965_aux.partsOf a b).card := by
      have h1 : L_lib_965_aux.rkOf a b Finset.univ ≤ ∑ C ∈ L_lib_965_aux.partsOf a b, L_lib_965_aux.rkOf a b C := by
        have h := L_lib_965_aux.rkOf_biUnion_le a b (L_lib_965_aux.partsOf a b) ∅
        rw [Finset.empty_union, L_lib_965_aux.partsOf_biUnion] at h
        have h0 : L_lib_965_aux.rkOf a b ∅ = 0 := by
          rw [L_lib_965_aux.rkOf, L_lib_965_aux.spanOf, Finset.image_empty, Finset.image_empty, Finset.union_empty, Finset.coe_empty, Submodule.span_empty, finrank_bot]
        omega
      have h2 : ∑ C ∈ L_lib_965_aux.partsOf a b, L_lib_965_aux.rkOf a b C ≤ ∑ C ∈ L_lib_965_aux.partsOf a b, (C.card / 2 + 1) :=
        Finset.sum_le_sum (fun C hC => (hcomp_props C hC).2.2)
      have h3 : 2 * ∑ C ∈ L_lib_965_aux.partsOf a b, (C.card / 2) = ∑ C ∈ L_lib_965_aux.partsOf a b, C.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C hC
        rcases (hcomp_props C hC).1 with ⟨k, hk⟩
        omega
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h2
      omega
    refine ⟨hr_le, hcs_le, ?_⟩
    let small := (L_lib_965_aux.partsOf a b).filter (fun C => C.card = 4)
    let large := (L_lib_965_aux.partsOf a b).filter (fun C => C.card ≠ 4)
    have hsmall_rk : ∀ C ∈ small, L_lib_965_aux.rkOf a b C ≤ 3 := by
      intro C hC
      simp only [small, Finset.mem_filter] at hC
      have hle := (hcomp_props C hC.1).2.2
      omega
    obtain ⟨keep, hkeep_sub, hkeep_rk3, hkeep_sum, hkeep_rej⟩ := L_lib_965_aux.greedy_keep a b small hsmall_rk
    have hkeep_cs : keep ⊆ L_lib_965_aux.partsOf a b := Finset.Subset.trans hkeep_sub (Finset.filter_subset _ _)
    refine ⟨keep, hkeep_cs, ?_, hkeep_sum, ?_⟩
    · intro C hC
      have hCs : C ∈ small := hkeep_sub hC
      simp only [small, Finset.mem_filter] at hCs
      exact ⟨hCs.2, hkeep_rk3 C hC⟩
    · have huniv_eq : Finset.univ = (keep.biUnion id ∪ (small \ keep).biUnion id) ∪ large.biUnion id := by
        rw [← L_lib_965_aux.partsOf_biUnion a b]
        ext i
        simp only [Finset.mem_union, Finset.mem_biUnion, id_eq, Finset.mem_sdiff, small, large, Finset.mem_filter]
        constructor
        · rintro ⟨C, hC, hiC⟩
          by_cases h4 : C.card = 4
          · by_cases hk : C ∈ keep
            · exact Or.inl (Or.inl ⟨C, hk, hiC⟩)
            · exact Or.inl (Or.inr ⟨C, ⟨⟨hC, h4⟩, hk⟩, hiC⟩)
          · exact Or.inr ⟨C, ⟨hC, h4⟩, hiC⟩
        · rintro ((⟨C, hk, hiC⟩ | ⟨C, ⟨⟨hC, _⟩, _⟩, hiC⟩) | ⟨C, ⟨hC, _⟩, hiC⟩)
          · exact ⟨C, hkeep_cs hk, hiC⟩
          · exact ⟨C, hC, hiC⟩
          · exact ⟨C, hC, hiC⟩
      have hstep1 : L_lib_965_aux.rkOf a b (keep.biUnion id ∪ (small \ keep).biUnion id) ≤
          3 * keep.card + 2 * (small \ keep).card := by
        have h := L_lib_965_aux.rkOf_biUnion_add_two a b (keep.biUnion id) (small \ keep) hkeep_rej
        omega
      have hstep2 : L_lib_965_aux.rkOf a b Finset.univ ≤
          L_lib_965_aux.rkOf a b (keep.biUnion id ∪ (small \ keep).biUnion id) + ∑ C ∈ large, L_lib_965_aux.rkOf a b C := by
        rw [huniv_eq]
        exact L_lib_965_aux.rkOf_biUnion_le a b large _
      have hlarge_rk : ∑ C ∈ large, L_lib_965_aux.rkOf a b C ≤ ∑ C ∈ large, (C.card / 2 + 1) :=
        Finset.sum_le_sum (fun C hC => (hcomp_props C (Finset.mem_filter.mp hC).1).2.2)
      have hcs_split : (L_lib_965_aux.partsOf a b).card = small.card + large.card := by
        have h := Finset.sum_filter_add_sum_filter_not (L_lib_965_aux.partsOf a b) (fun C => C.card = 4) (fun _ => 1)
        simpa [small, large] using h.symm
      have hsum_split : ∑ C ∈ L_lib_965_aux.partsOf a b, C.card = 4 * small.card + ∑ C ∈ large, C.card := by
        have h := Finset.sum_filter_add_sum_filter_not (L_lib_965_aux.partsOf a b) (fun C => C.card = 4) Finset.card
        have hsm : ∑ C ∈ small, C.card = 4 * small.card := by
          calc ∑ C ∈ small, C.card
              = ∑ _C ∈ small, 4 := Finset.sum_congr rfl (fun C hC => (Finset.mem_filter.mp hC).2)
            _ = 4 * small.card := by simp [Finset.sum_const, mul_comm]
        rw [show (L_lib_965_aux.partsOf a b).filter (fun C => C.card = 4) = small from rfl,
            show (L_lib_965_aux.partsOf a b).filter (fun C => ¬ C.card = 4) = large from rfl, hsm] at h
        exact h.symm
      have hlarge_ge8 : ∀ C ∈ large, 8 ≤ C.card := by
        intro C hC
        simp only [large, Finset.mem_filter] at hC
        rcases (hcomp_props C hC.1).1 with ⟨k, hk⟩
        have hge4 := (hcomp_props C hC.1).2.1
        omega
      have hlarge_sum_ge : 8 * large.card ≤ ∑ C ∈ large, C.card := by
        calc 8 * large.card
            = ∑ _C ∈ large, 8 := by simp [Finset.sum_const, mul_comm]
          _ ≤ ∑ C ∈ large, C.card := Finset.sum_le_sum hlarge_ge8
      have hlarge_half : 2 * ∑ C ∈ large, (C.card / 2) = ∑ C ∈ large, C.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C hC
        rcases (hcomp_props C (Finset.mem_filter.mp hC).1).1 with ⟨k, hk⟩
        omega
      have hkeep_card_le : keep.card ≤ small.card := Finset.card_le_card hkeep_sub
      have hsdiff_card : (small \ keep).card = small.card - keep.card := Finset.card_sdiff_of_subset hkeep_sub
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hlarge_rk
      omega
  · exact L_lib_965_aux.q3_construction

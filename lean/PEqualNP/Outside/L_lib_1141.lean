import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1141_aux

def desc {n : Nat} (par : Fin n → Fin n) (e v : Fin n) : Prop :=
  ∃ k : Nat, par^[k] v = e

lemma iterate_par_le {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i) :
    ∀ k v, par^[k] v ≤ v
  | 0, _ => le_rfl
  | k + 1, v => by
    rw [Function.iterate_succ_apply]
    exact (iterate_par_le hpar k (par v)).trans (hpar v)

lemma desc_self {n : Nat} (par : Fin n → Fin n) (e : Fin n) : desc par e e :=
  ⟨0, rfl⟩

lemma par_not_desc {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i)
    {e : Fin n} (he : par e < e) : ¬ desc par e (par e) := by
  rintro ⟨k, hk⟩
  have hle := iterate_par_le hpar k (par e)
  rw [hk] at hle
  exact not_lt_of_ge hle he

lemma desc_iff_par_desc {n : Nat} {par : Fin n → Fin n}
    {e j : Fin n} (hj : j ≠ e) : desc par e j ↔ desc par e (par j) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd hk hj
    | succ k' =>
      rw [Function.iterate_succ_apply] at hk
      exact ⟨k', hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

lemma card_split_prod {n : Nat} (A : Finset (Fin n))
    (P Q : Finset (Fin n) → Prop) [DecidablePred P] [DecidablePred Q] :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun x => P (x ∩ A) ∧ Q (x ∩ (Finset.univ \ A)))).card =
    (A.powerset.filter P).card * ((Finset.univ \ A).powerset.filter Q).card := by
  let B := Finset.univ \ A
  rw [← Finset.card_product]
  refine Finset.card_nbij (fun x => (x ∩ A, x ∩ B)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.inter_subset_right, hx.1⟩, ⟨Finset.inter_subset_right, hx.2⟩⟩
  · intro x _ y _ hxy
    have h1 : x ∩ A = y ∩ A := congrArg Prod.fst hxy
    have h2 : x ∩ B = y ∩ B := congrArg Prod.snd hxy
    ext v
    by_cases hv : v ∈ A
    · have := Finset.ext_iff.mp h1 v
      simpa [hv] using this
    · have hvB : v ∈ B := by simp [B, hv]
      have := Finset.ext_iff.mp h2 v
      simpa [hvB] using this
  · rintro ⟨xA, xB⟩ hAB
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hAB
    rcases hAB with ⟨⟨hxA, hPA⟩, ⟨hxB, hQB⟩⟩
    have h1 : (xA ∪ xB) ∩ A = xA := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hv | hv, hvA⟩
        · exact hv
        · exfalso
          have hvB := hxB hv
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hvB
          exact hvB hvA
      · intro hv
        exact ⟨Or.inl hv, hxA hv⟩
    have h2 : (xA ∪ xB) ∩ (Finset.univ \ A) = xB := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hv | hv, hvB⟩
        · exfalso
          have hvA := hxA hv
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hvB
          exact hvB hvA
        · exact hv
      · intro hv
        exact ⟨Or.inr hv, hxB hv⟩
    refine ⟨xA ∪ xB, ?_, Prod.ext h1 h2⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, h1, h2]
    exact ⟨hPA, hQB⟩

lemma card_split_bool {α : Type*} [DecidableEq α] (S : Finset α) (f : α → Bool) :
    S.card = (S.filter (fun x => f x = false)).card + (S.filter (fun x => f x = true)).card := by
  have hdisj : Disjoint (S.filter (fun x => f x = false)) (S.filter (fun x => f x = true)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.false_ne_true h2.2
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  cases hfx : f x <;> simp

lemma bool_rank_one (f : Bool → Bool → Bool)
    (h : (f false false).toNat * (f true true).toNat =
         (f false true).toNat * (f true false).toNat) :
    ∃ p q : Bool → Bool, ∀ a b, f a b = (p a && q b) := by
  refine ⟨fun a => f a false || f a true, fun b => f false b || f true b, fun a b => ?_⟩
  dsimp only
  cases a <;> cases b <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;>
    simp_all

def xsOf {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun x =>
    ∀ i, allow i (decide (par i ∈ x)) (decide (i ∈ x)) = true)

def pinOf {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (r : Fin n) (b : Bool) (S B : Finset (Fin n)) : Nat :=
  ((xsOf par allow).filter (fun x => decide (r ∈ x) = b ∧ x ∩ S = B)).card

def indepOf {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (r : Fin n) (S : Finset (Fin n)) : Prop :=
  ∀ B ⊆ S, pinOf par allow r false S B * pinOf par allow r true ∅ ∅ =
    pinOf par allow r true S B * pinOf par allow r false ∅ ∅

def jointOf {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (i : Fin n) (a b : Bool) : Nat :=
  ((xsOf par allow).filter (fun x => decide (par i ∈ x) = a ∧ decide (i ∈ x) = b)).card

def splitsOf {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (i : Fin n) : Prop :=
  jointOf par allow i false false * jointOf par allow i true true =
    jointOf par allow i false true * jointOf par allow i true false

def validSys {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (u : Fin n → Bool → Bool) (E : Finset (Fin n)) (x : Finset (Fin n)) : Prop :=
  (∀ v, u v (decide (v ∈ x)) = true) ∧
    (∀ j ∈ E, allow j (decide (par j ∈ x)) (decide (j ∈ x)) = true)

lemma cut_one_edge {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i)
    (allow : Fin n → Bool → Bool → Bool)
    (u : Fin n → Bool → Bool) (E : Finset (Fin n))
    (hE_lt : ∀ j ∈ E, par j < j)
    (hxs : ∀ x, x ∈ xsOf par allow ↔ validSys par allow u E x)
    {i : Fin n} (hiE : i ∈ E) (hsplit : splitsOf par allow i) :
    ∃ u' : Fin n → Bool → Bool, ∀ x, x ∈ xsOf par allow ↔ validSys par allow u' (E.erase i) x := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun v => desc par i v)
  let A : Finset (Fin n) := Finset.univ \ D
  have hB_eq : Finset.univ \ A = D := by
    ext v; simp [A]
  have hi_lt : par i < i := hE_lt i hiE
  have hi_ne : par i ≠ i := ne_of_lt hi_lt
  have hiD : i ∈ D := by simp [D, desc_self]
  have hpiA : par i ∈ A := by
    simp only [A, D, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
    exact par_not_desc hpar hi_lt
  have hsep : ∀ j ∈ E.erase i, j ∈ A ↔ par j ∈ A := by
    intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [A, D, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
    exact not_congr (desc_iff_par_desc hne)
  let validA : Finset (Fin n) → Prop := fun xA =>
    (∀ v ∈ A, u v (decide (v ∈ xA)) = true) ∧
    (∀ j ∈ E.erase i, j ∈ A → allow j (decide (par j ∈ xA)) (decide (j ∈ xA)) = true)
  let validD : Finset (Fin n) → Prop := fun xD =>
    (∀ v ∈ D, u v (decide (v ∈ xD)) = true) ∧
    (∀ j ∈ E.erase i, j ∈ D → allow j (decide (par j ∈ xD)) (decide (j ∈ xD)) = true)
  have hsys_split : ∀ x : Finset (Fin n),
      validSys par allow u (E.erase i) x ↔ validA (x ∩ A) ∧ validD (x ∩ D) := by
    intro x
    constructor
    · rintro ⟨hu, hE'⟩
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro v hv
        have hmem : (v ∈ x ∩ A) ↔ (v ∈ x) := by simp [hv]
        simpa [hmem] using hu v
      · intro j hj hjA
        have hpjA : par j ∈ A := (hsep j hj).mp hjA
        have h1 : (par j ∈ x ∩ A) ↔ (par j ∈ x) := by simp [hpjA]
        have h2 : (j ∈ x ∩ A) ↔ (j ∈ x) := by simp [hjA]
        simpa [h1, h2] using hE' j hj
      · intro v hv
        have hmem : (v ∈ x ∩ D) ↔ (v ∈ x) := by simp [hv]
        simpa [hmem] using hu v
      · intro j hj hjD
        have hjNA : j ∉ A := by simp [A, hjD]
        have hpjNA : par j ∉ A := fun h => hjNA ((hsep j hj).mpr h)
        have hpjD : par j ∈ D := by
          by_contra h
          exact hpjNA (by simp [A, h])
        have h1 : (par j ∈ x ∩ D) ↔ (par j ∈ x) := by simp [hpjD]
        have h2 : (j ∈ x ∩ D) ↔ (j ∈ x) := by simp [hjD]
        simpa [h1, h2] using hE' j hj
    · rintro ⟨⟨huA, hEA⟩, ⟨huD, hED⟩⟩
      refine ⟨?_, ?_⟩
      · intro v
        by_cases hv : v ∈ A
        · have hmem : (v ∈ x ∩ A) ↔ (v ∈ x) := by simp [hv]
          simpa [hmem] using huA v hv
        · have hvD : v ∈ D := by
            by_contra h
            exact hv (by simp [A, h])
          have hmem : (v ∈ x ∩ D) ↔ (v ∈ x) := by simp [hvD]
          simpa [hmem] using huD v hvD
      · intro j hj
        by_cases hjA : j ∈ A
        · have hpjA : par j ∈ A := (hsep j hj).mp hjA
          have h1 : (par j ∈ x ∩ A) ↔ (par j ∈ x) := by simp [hpjA]
          have h2 : (j ∈ x ∩ A) ↔ (j ∈ x) := by simp [hjA]
          simpa [h1, h2] using hEA j hj hjA
        · have hjD : j ∈ D := by
            by_contra h
            exact hjA (by simp [A, h])
          have hpjNA : par j ∉ A := fun h => hjA ((hsep j hj).mpr h)
          have hpjD : par j ∈ D := by
            by_contra h
            exact hpjNA (by simp [A, h])
          have h1 : (par j ∈ x ∩ D) ↔ (par j ∈ x) := by simp [hpjD]
          have h2 : (j ∈ x ∩ D) ↔ (j ∈ x) := by simp [hjD]
          simpa [h1, h2] using hED j hj hjD
  have hxs_split : ∀ x : Finset (Fin n),
      x ∈ xsOf par allow ↔
        validA (x ∩ A) ∧ validD (x ∩ D) ∧
          allow i (decide (par i ∈ x)) (decide (i ∈ x)) = true := by
    intro x
    rw [hxs x]
    constructor
    · rintro ⟨hu, hE⟩
      have hsub : validSys par allow u (E.erase i) x :=
        ⟨hu, fun j hj => hE j (Finset.mem_of_mem_erase hj)⟩
      exact ⟨((hsys_split x).mp hsub).1, ((hsys_split x).mp hsub).2, hE i hiE⟩
    · rintro ⟨hA, hD, hi_ok⟩
      have hsub := (hsys_split x).mpr ⟨hA, hD⟩
      refine ⟨hsub.1, fun j hj => ?_⟩
      by_cases hji : j = i
      · rw [hji]; exact hi_ok
      · exact hsub.2 j (Finset.mem_erase.mpr ⟨hji, hj⟩)
  let cA : Bool → Nat := fun a =>
    (A.powerset.filter (fun xA => validA xA ∧ decide (par i ∈ xA) = a)).card
  let cD : Bool → Nat := fun b =>
    (D.powerset.filter (fun xD => validD xD ∧ decide (i ∈ xD) = b)).card
  have hjoint : ∀ a b : Bool,
      jointOf par allow i a b = cA a * cD b * (allow i a b).toNat := by
    intro a b
    unfold jointOf
    cases hab : allow i a b
    · simp only [Bool.toNat_false, mul_zero]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [hxs_split x] at hx
      rintro ⟨h1, h2⟩
      rw [h1, h2, hab] at hx
      exact Bool.false_ne_true hx.2.2
    · simp only [Bool.toNat_true, mul_one]
      have hfilt : (xsOf par allow).filter (fun x => decide (par i ∈ x) = a ∧ decide (i ∈ x) = b) =
          (Finset.univ : Finset (Finset (Fin n))).filter
            (fun x => (validA (x ∩ A) ∧ decide (par i ∈ x ∩ A) = a) ∧
                      (validD (x ∩ (Finset.univ \ A)) ∧ decide (i ∈ x ∩ (Finset.univ \ A)) = b)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxs_split, hB_eq]
        have h1 : (par i ∈ x ∩ A) ↔ (par i ∈ x) := by simp [hpiA]
        have h2 : (i ∈ x ∩ D) ↔ (i ∈ x) := by simp [hiD]
        simp only [h1, h2]
        constructor
        · rintro ⟨⟨hA, hD, _⟩, ha, hb⟩
          exact ⟨⟨hA, ha⟩, ⟨hD, hb⟩⟩
        · rintro ⟨⟨hA, ha⟩, ⟨hD, hb⟩⟩
          exact ⟨⟨hA, hD, by rw [ha, hb, hab]⟩, ha, hb⟩
      rw [hfilt, card_split_prod A
        (fun xA => validA xA ∧ decide (par i ∈ xA) = a)
        (fun xD => validD xD ∧ decide (i ∈ xD) = b), hB_eq]
  have hsp := hsplit
  unfold splitsOf at hsp
  rw [hjoint false false, hjoint true true, hjoint false true, hjoint true false] at hsp
  by_cases hA0 : cA false = 0
  · refine ⟨fun v b => if v = i then u v b && allow i true b else u v b, fun x => ?_⟩
    rw [hxs_split x]
    have hforced : validA (x ∩ A) → decide (par i ∈ x) = true := by
      intro hA
      by_contra hne
      have hfl : decide (par i ∈ x) = false := by cases h : decide (par i ∈ x) <;> simp_all
      have hmem : x ∩ A ∈ A.powerset.filter (fun xA => validA xA ∧ decide (par i ∈ xA) = false) := by
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.inter_subset_right, hA, by simpa [hpiA] using hfl⟩
      have hpos : 0 < cA false := Finset.card_pos.mpr ⟨x ∩ A, hmem⟩
      omega
    constructor
    · rintro ⟨hA, hD, hi_ok⟩
      have hsub := (hsys_split x).mpr ⟨hA, hD⟩
      refine ⟨fun v => ?_, hsub.2⟩
      by_cases hvi : v = i
      · rw [hvi]
        simp only [ite_true, Bool.and_eq_true]
        have hff := hforced hA
        rw [hff] at hi_ok
        exact ⟨hsub.1 i, hi_ok⟩
      · simp only [hvi, ite_false]
        exact hsub.1 v
    · rintro ⟨hu', hE'⟩
      have hu : ∀ v, u v (decide (v ∈ x)) = true := by
        intro v
        have hv := hu' v
        by_cases hvi : v = i
        · rw [hvi] at hv
          simp only [ite_true, Bool.and_eq_true] at hv
          rw [hvi]; exact hv.1
        · simpa [hvi] using hv
      have hAD := (hsys_split x).mp ⟨hu, hE'⟩
      have hi' := hu' i
      simp only [ite_true, Bool.and_eq_true] at hi'
      exact ⟨hAD.1, hAD.2, by rw [hforced hAD.1]; exact hi'.2⟩
  · by_cases hA1 : cA true = 0
    · refine ⟨fun v b => if v = i then u v b && allow i false b else u v b, fun x => ?_⟩
      rw [hxs_split x]
      have hforced : validA (x ∩ A) → decide (par i ∈ x) = false := by
        intro hA
        by_contra hne
        have htr : decide (par i ∈ x) = true := by cases h : decide (par i ∈ x) <;> simp_all
        have hmem : x ∩ A ∈ A.powerset.filter (fun xA => validA xA ∧ decide (par i ∈ xA) = true) := by
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.inter_subset_right, hA, by simpa [hpiA] using htr⟩
        have hpos : 0 < cA true := Finset.card_pos.mpr ⟨x ∩ A, hmem⟩
        omega
      constructor
      · rintro ⟨hA, hD, hi_ok⟩
        have hsub := (hsys_split x).mpr ⟨hA, hD⟩
        refine ⟨fun v => ?_, hsub.2⟩
        by_cases hvi : v = i
        · rw [hvi]
          simp only [ite_true, Bool.and_eq_true]
          have hff := hforced hA
          rw [hff] at hi_ok
          exact ⟨hsub.1 i, hi_ok⟩
        · simp only [hvi, ite_false]
          exact hsub.1 v
      · rintro ⟨hu', hE'⟩
        have hu : ∀ v, u v (decide (v ∈ x)) = true := by
          intro v
          have hv := hu' v
          by_cases hvi : v = i
          · rw [hvi] at hv
            simp only [ite_true, Bool.and_eq_true] at hv
            rw [hvi]; exact hv.1
          · simpa [hvi] using hv
        have hAD := (hsys_split x).mp ⟨hu, hE'⟩
        have hi' := hu' i
        simp only [ite_true, Bool.and_eq_true] at hi'
        exact ⟨hAD.1, hAD.2, by rw [hforced hAD.1]; exact hi'.2⟩
    · by_cases hD0 : cD false = 0
      · refine ⟨fun v b => if v = par i then u v b && allow i b true else u v b, fun x => ?_⟩
        rw [hxs_split x]
        have hforced : validD (x ∩ D) → decide (i ∈ x) = true := by
          intro hD
          by_contra hne
          have hfl : decide (i ∈ x) = false := by cases h : decide (i ∈ x) <;> simp_all
          have hmem : x ∩ D ∈ D.powerset.filter (fun xD => validD xD ∧ decide (i ∈ xD) = false) := by
            simp only [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.inter_subset_right, hD, by simpa [hiD] using hfl⟩
          have hpos : 0 < cD false := Finset.card_pos.mpr ⟨x ∩ D, hmem⟩
          omega
        constructor
        · rintro ⟨hA, hD, hi_ok⟩
          have hsub := (hsys_split x).mpr ⟨hA, hD⟩
          refine ⟨fun v => ?_, hsub.2⟩
          by_cases hvp : v = par i
          · rw [hvp]
            simp only [ite_true, Bool.and_eq_true]
            have hff := hforced hD
            rw [hff] at hi_ok
            exact ⟨hsub.1 (par i), hi_ok⟩
          · simp only [hvp, ite_false]
            exact hsub.1 v
        · rintro ⟨hu', hE'⟩
          have hu : ∀ v, u v (decide (v ∈ x)) = true := by
            intro v
            have hv := hu' v
            by_cases hvp : v = par i
            · rw [hvp] at hv
              simp only [ite_true, Bool.and_eq_true] at hv
              rw [hvp]; exact hv.1
            · simpa [hvp] using hv
          have hAD := (hsys_split x).mp ⟨hu, hE'⟩
          have hp' := hu' (par i)
          simp only [ite_true, Bool.and_eq_true] at hp'
          exact ⟨hAD.1, hAD.2, by rw [hforced hAD.2]; exact hp'.2⟩
      · by_cases hD1 : cD true = 0
        · refine ⟨fun v b => if v = par i then u v b && allow i b false else u v b, fun x => ?_⟩
          rw [hxs_split x]
          have hforced : validD (x ∩ D) → decide (i ∈ x) = false := by
            intro hD
            by_contra hne
            have htr : decide (i ∈ x) = true := by cases h : decide (i ∈ x) <;> simp_all
            have hmem : x ∩ D ∈ D.powerset.filter (fun xD => validD xD ∧ decide (i ∈ xD) = true) := by
              simp only [Finset.mem_filter, Finset.mem_powerset]
              exact ⟨Finset.inter_subset_right, hD, by simpa [hiD] using htr⟩
            have hpos : 0 < cD true := Finset.card_pos.mpr ⟨x ∩ D, hmem⟩
            omega
          constructor
          · rintro ⟨hA, hD, hi_ok⟩
            have hsub := (hsys_split x).mpr ⟨hA, hD⟩
            refine ⟨fun v => ?_, hsub.2⟩
            by_cases hvp : v = par i
            · rw [hvp]
              simp only [ite_true, Bool.and_eq_true]
              have hff := hforced hD
              rw [hff] at hi_ok
              exact ⟨hsub.1 (par i), hi_ok⟩
            · simp only [hvp, ite_false]
              exact hsub.1 v
          · rintro ⟨hu', hE'⟩
            have hu : ∀ v, u v (decide (v ∈ x)) = true := by
              intro v
              have hv := hu' v
              by_cases hvp : v = par i
              · rw [hvp] at hv
                simp only [ite_true, Bool.and_eq_true] at hv
                rw [hvp]; exact hv.1
              · simpa [hvp] using hv
            have hAD := (hsys_split x).mp ⟨hu, hE'⟩
            have hp' := hu' (par i)
            simp only [ite_true, Bool.and_eq_true] at hp'
            exact ⟨hAD.1, hAD.2, by rw [hforced hAD.2]; exact hp'.2⟩
        · have hP_pos : 0 < cA false * cA true * cD false * cD true := by
            exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hA0)
              (Nat.pos_of_ne_zero hA1)) (Nat.pos_of_ne_zero hD0)) (Nat.pos_of_ne_zero hD1)
          have hmul : (cA false * cA true * cD false * cD true) *
              ((allow i false false).toNat * (allow i true true).toNat) =
              (cA false * cA true * cD false * cD true) *
              ((allow i false true).toNat * (allow i true false).toNat) := by
            calc (cA false * cA true * cD false * cD true) *
                  ((allow i false false).toNat * (allow i true true).toNat)
                = cA false * cD false * (allow i false false).toNat *
                  (cA true * cD true * (allow i true true).toNat) := by ring
              _ = cA false * cD true * (allow i false true).toNat *
                  (cA true * cD false * (allow i true false).toNat) := hsp
              _ = (cA false * cA true * cD false * cD true) *
                  ((allow i false true).toNat * (allow i true false).toNat) := by ring
          have hw := Nat.eq_of_mul_eq_mul_left hP_pos hmul
          rcases bool_rank_one (allow i) hw with ⟨p, q, hpq⟩
          refine ⟨fun v b => u v b && (if v = par i then p b else true) &&
            (if v = i then q b else true), fun x => ?_⟩
          rw [hxs x]
          constructor
          · rintro ⟨hu, hE⟩
            refine ⟨fun v => ?_, fun j hj => hE j (Finset.mem_of_mem_erase hj)⟩
            have hi_ok := hE i hiE
            rw [hpq, Bool.and_eq_true] at hi_ok
            simp only [Bool.and_eq_true]
            refine ⟨⟨hu v, ?_⟩, ?_⟩
            · split_ifs with hvp
              · rw [hvp]; exact hi_ok.1
              · rfl
            · split_ifs with hvi
              · rw [hvi]; exact hi_ok.2
              · rfl
          · rintro ⟨hu', hE'⟩
            refine ⟨fun v => ?_, fun j hj => ?_⟩
            · have hv := hu' v
              simp only [Bool.and_eq_true] at hv
              exact hv.1.1
            · by_cases hji : j = i
              · rw [hji, hpq, Bool.and_eq_true]
                have hpv := hu' (par i)
                have hiv := hu' i
                simp only [ite_true, hi_ne, ite_false, Bool.and_eq_true] at hpv
                simp only [ite_true, Bool.and_eq_true] at hiv
                exact ⟨hpv.1.2, hiv.2⟩
              · exact hE' j (Finset.mem_erase.mpr ⟨hji, hj⟩)

lemma cut_all_splits {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i)
    (allow : Fin n → Bool → Bool → Bool) :
    ∃ u : Fin n → Bool → Bool, ∀ x : Finset (Fin n),
      x ∈ xsOf par allow ↔
        (∀ v, u v (decide (v ∈ x)) = true) ∧
        (∀ j, par j < j → ¬ splitsOf par allow j →
          allow j (decide (par j ∈ x)) (decide (j ∈ x)) = true) := by
  classical
  let E0 : Finset (Fin n) := Finset.univ.filter (fun j => par j < j)
  let S : Finset (Fin n) := E0.filter (fun j => splitsOf par allow j)
  have hbase : ∀ x, x ∈ xsOf par allow ↔
      validSys par allow (fun v b => if par v = v then allow v b b else true) E0 x := by
    intro x
    simp only [xsOf, Finset.mem_filter, Finset.mem_univ, true_and, validSys, E0]
    constructor
    · intro hx
      refine ⟨fun v => ?_, fun j _ => hx j⟩
      split_ifs with hvv
      · simpa [hvv] using hx v
      · rfl
    · rintro ⟨hu, hE⟩ j
      by_cases hjj : par j = j
      · have hv := hu j
        simp only [hjj, ite_true] at hv
        simpa [hjj] using hv
      · exact hE j (lt_of_le_of_ne (hpar j) hjj)
  have hind : ∀ T : Finset (Fin n), T ⊆ S →
      ∃ u : Fin n → Bool → Bool, ∀ x, x ∈ xsOf par allow ↔ validSys par allow u (E0 \ T) x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun v b => if par v = v then allow v b b else true, fun x => ?_⟩
      simpa using hbase x
    | @insert a s ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a s)
      have hsS : s ⊆ S := fun y hy => hsub (Finset.mem_insert_of_mem hy)
      rcases ih hsS with ⟨u, hu⟩
      have haE0 : a ∈ E0 := (Finset.mem_filter.mp haS).1
      have hasp : splitsOf par allow a := (Finset.mem_filter.mp haS).2
      have ha_mem : a ∈ E0 \ s := Finset.mem_sdiff.mpr ⟨haE0, ha⟩
      have hlt : ∀ j ∈ E0 \ s, par j < j := fun j hj =>
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
      rcases cut_one_edge hpar allow u (E0 \ s) hlt hu ha_mem hasp with ⟨u', hu'⟩
      refine ⟨u', fun x => ?_⟩
      have heq : (E0 \ s).erase a = E0 \ insert a s := by
        ext j; simp [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]; tauto
      rw [← heq]
      exact hu' x
  rcases hind S Finset.Subset.rfl with ⟨u, hu⟩
  refine ⟨u, fun x => ?_⟩
  rw [hu x]
  simp only [validSys, Finset.mem_sdiff, E0, S, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hlt hns => h2 j ⟨hlt, fun h => hns h.2⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j ⟨hlt, hns⟩ => h2 j hlt (fun hsp => hns ⟨hlt, hsp⟩)⟩

lemma cut_implies_indep {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i)
    (allow : Fin n → Bool → Bool → Bool) (r : Fin n) (T : Finset (Fin n))
    (U : Finset (Fin n)) (hrU : r ∈ U) (hUT : Disjoint U T)
    (hcut : ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splitsOf par allow i) :
    indepOf par allow r T := by
  classical
  rcases cut_all_splits hpar allow with ⟨u, hxs⟩
  let Uc := Finset.univ \ U
  have hT_sub : T ⊆ Uc := by
    intro v hv
    simp only [Uc, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact Finset.disjoint_right.mp hUT hv
  have hsep : ∀ j, par j < j → ¬ splitsOf par allow j → (j ∈ U ↔ par j ∈ U) := by
    intro j _ hns
    by_contra hiff
    have hne : (decide (j ∈ U) != decide (par j ∈ U)) = true := by
      by_cases h1 : j ∈ U <;> by_cases h2 : par j ∈ U <;> simp_all
    exact hns (hcut j hne)
  let validU : Finset (Fin n) → Prop := fun xU =>
    (∀ v ∈ U, u v (decide (v ∈ xU)) = true) ∧
    (∀ j ∈ U, par j < j → ¬ splitsOf par allow j →
      allow j (decide (par j ∈ xU)) (decide (j ∈ xU)) = true)
  let validUc : Finset (Fin n) → Prop := fun xUc =>
    (∀ v ∈ Uc, u v (decide (v ∈ xUc)) = true) ∧
    (∀ j ∈ Uc, par j < j → ¬ splitsOf par allow j →
      allow j (decide (par j ∈ xUc)) (decide (j ∈ xUc)) = true)
  have hxs_split : ∀ x : Finset (Fin n),
      x ∈ xsOf par allow ↔ validU (x ∩ U) ∧ validUc (x ∩ Uc) := by
    intro x
    rw [hxs x]
    constructor
    · rintro ⟨hu, hE⟩
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro v hv; simpa [hv] using hu v
      · intro j hj hlt hns
        have hpj : par j ∈ U := (hsep j hlt hns).mp hj
        simpa [hj, hpj] using hE j hlt hns
      · intro v hv; simpa [hv] using hu v
      · intro j hj hlt hns
        have hjNU : j ∉ U := (Finset.mem_sdiff.mp hj).2
        have hpjNU : par j ∉ U := fun h => hjNU ((hsep j hlt hns).mpr h)
        have hpj : par j ∈ Uc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpjNU⟩
        simpa [hj, hpj] using hE j hlt hns
    · rintro ⟨⟨huU, hEU⟩, ⟨huUc, hEUc⟩⟩
      refine ⟨fun v => ?_, fun j hlt hns => ?_⟩
      · by_cases hv : v ∈ U
        · simpa [hv] using huU v hv
        · have hvUc : v ∈ Uc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
          simpa [hvUc] using huUc v hvUc
      · by_cases hj : j ∈ U
        · have hpj : par j ∈ U := (hsep j hlt hns).mp hj
          simpa [hj, hpj] using hEU j hj hlt hns
        · have hjUc : j ∈ Uc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
          have hpjNU : par j ∉ U := fun h => hj ((hsep j hlt hns).mpr h)
          have hpjUc : par j ∈ Uc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpjNU⟩
          simpa [hjUc, hpjUc] using hEUc j hjUc hlt hns
  let cU : Bool → Nat := fun b =>
    (U.powerset.filter (fun xU => validU xU ∧ decide (r ∈ xU) = b)).card
  let cUc : Finset (Fin n) → Finset (Fin n) → Nat := fun S B =>
    (Uc.powerset.filter (fun xUc => validUc xUc ∧ xUc ∩ S = B)).card
  have hpin : ∀ (b : Bool) (S B : Finset (Fin n)), S ⊆ Uc →
      pinOf par allow r b S B = cU b * cUc S B := by
    intro b S B hSUc
    unfold pinOf
    have hfilt : (xsOf par allow).filter (fun x => decide (r ∈ x) = b ∧ x ∩ S = B) =
        (Finset.univ : Finset (Finset (Fin n))).filter
          (fun x => (validU (x ∩ U) ∧ decide (r ∈ x ∩ U) = b) ∧
                    (validUc (x ∩ Uc) ∧ (x ∩ Uc) ∩ S = B)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxs_split]
      have hr : (r ∈ x ∩ U) ↔ (r ∈ x) := by simp [hrU]
      have hS : (x ∩ Uc) ∩ S = x ∩ S := by
        rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hSUc]
      simp only [hr, hS]
      tauto
    rw [hfilt, card_split_prod U
      (fun xU => validU xU ∧ decide (r ∈ xU) = b)
      (fun xUc => validUc xUc ∧ xUc ∩ S = B)]
  intro B _
  rw [hpin false T B hT_sub, hpin true ∅ ∅ (Finset.empty_subset Uc),
      hpin true T B hT_sub, hpin false ∅ ∅ (Finset.empty_subset Uc)]
  ring

lemma indep_singleton {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (r : Fin n) (T : Finset (Fin n)) (hT : indepOf par allow r T) :
    ∀ i ∈ T, indepOf par allow r {i} := by
  intro i hiT B' hB'
  have hsum : ∀ b : Bool,
      pinOf par allow r b {i} B' =
        (T.powerset.filter (fun B => B ∩ {i} = B')).sum (fun B => pinOf par allow r b T B) := by
    intro b
    unfold pinOf
    have hmap : ∀ x ∈ (xsOf par allow).filter (fun x => decide (r ∈ x) = b ∧ x ∩ {i} = B'),
        x ∩ T ∈ T.powerset.filter (fun B => B ∩ {i} = B') := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_powerset] at hx ⊢
      refine ⟨Finset.inter_subset_right, ?_⟩
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr hiT)]
      exact hx.2.2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl fun B hB => ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hrb, _⟩, hxT⟩
      exact ⟨hx, hrb, hxT⟩
    · rintro ⟨hx, hrb, hxT⟩
      refine ⟨⟨hx, hrb, ?_⟩, hxT⟩
      have h1 : x ∩ {i} = (x ∩ T) ∩ {i} := by
        rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr hiT)]
      rw [h1, hxT, hB.2]
  rw [hsum false, hsum true, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun B hB => ?_
  exact hT B (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)

def goodAdj {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (u v : Fin n) : Prop :=
  (par u < u ∧ ¬ splitsOf par allow u ∧ par u = v) ∨
  (par v < v ∧ ¬ splitsOf par allow v ∧ par v = u)

def IsPath {α : Type*} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ IsPath R (y :: rest)

lemma isPath_append_left {α : Type*} {R : α → α → Prop} :
    ∀ (l1 l2 : List α), IsPath R (l1 ++ l2) → IsPath R l1
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: y :: rest, l2, h => ⟨h.1, isPath_append_left (y :: rest) l2 h.2⟩

lemma isPath_concat {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α} {b c : α}, IsPath R l → l.getLast? = some b → R b c → IsPath R (l ++ [c])
  | [], _, _, _, hlast, _ => by simp at hlast
  | [x], b, c, _, hlast, hbc => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    exact ⟨hbc, trivial⟩
  | x :: y :: rest, b, c, h, hlast, hbc => by
    have hlast' : (y :: rest).getLast? = some b := by simpa using hlast
    exact ⟨h.1, isPath_concat h.2 hlast' hbc⟩

lemma isPath_last_edge {α : Type*} {R : α → α → Prop} :
    ∀ (q0 : List α) (v w : α), IsPath R ((q0 ++ [v]) ++ [w]) → R v w
  | [], v, w, h => h.1
  | _ :: rest, v, w, h => by
    cases rest with
    | nil => exact h.2.1
    | cons y ys => exact isPath_last_edge (y :: ys) v w h.2

lemma exists_nodup_path {α : Type*} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) :
    ∃ p : List α, p.head? = some a ∧ p.getLast? = some b ∧ IsPath R p ∧ p.Nodup := by
  classical
  induction h with
  | refl =>
    exact ⟨[a], rfl, rfl, trivial, List.nodup_singleton a⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨p, hhead, hlast, hpath, hnodup⟩
    by_cases hc : c ∈ p
    · rcases List.append_of_mem hc with ⟨p1, p2, rfl⟩
      refine ⟨p1 ++ [c], ?_, ?_, ?_, ?_⟩
      · cases p1 with
        | nil => simpa using hhead
        | cons x xs => simpa using hhead
      · simp
      · have hp : IsPath R ((p1 ++ [c]) ++ p2) := by simpa [List.append_assoc] using hpath
        exact isPath_append_left (p1 ++ [c]) p2 hp
      · have hsub : (p1 ++ [c]).Sublist ((p1 ++ [c]) ++ p2) := List.sublist_append_left _ _
        have hnd : ((p1 ++ [c]) ++ p2).Nodup := by simpa [List.append_assoc] using hnodup
        exact hnd.sublist hsub
    · refine ⟨p ++ [c], ?_, ?_, ?_, ?_⟩
      · cases p with
        | nil => simp at hhead
        | cons x xs => simpa using hhead
      · simp
      · exact isPath_concat hpath hlast hbc
      · rw [List.nodup_append]
        exact ⟨hnodup, List.nodup_singleton c, fun x hx y hy => by
          simp only [List.mem_singleton] at hy
          subst hy
          exact fun h => hc (h ▸ hx)⟩

def pairCount {n : Nat} (xs : Finset (Finset (Fin n))) (u v : Fin n) (a b : Bool) : Int :=
  ((xs.filter (fun x => decide (u ∈ x) = a ∧ decide (v ∈ x) = b)).card : Int)

def margCount {n : Nat} (xs : Finset (Finset (Fin n))) (v : Fin n) (c : Bool) : Int :=
  ((xs.filter (fun x => decide (v ∈ x) = c)).card : Int)

def pairDet {n : Nat} (xs : Finset (Finset (Fin n))) (u v : Fin n) : Int :=
  pairCount xs u v false false * pairCount xs u v true true -
    pairCount xs u v false true * pairCount xs u v true false

lemma markov_det_mul {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    (A : Finset (Fin n)) (e u v w : Fin n) (edgeOk : Bool → Bool → Bool)
    (huA : u ∈ A) (hvA : v ∈ A) (hwB : w ∈ Finset.univ \ A)
    (hedge : ∀ x : Finset (Fin n),
      allow e (decide (par e ∈ x)) (decide (e ∈ x)) =
        edgeOk (decide (v ∈ x)) (decide (w ∈ x)))
    (hsep : ∀ j : Fin n, j ≠ e → (j ∈ A ↔ par j ∈ A)) :
    let xs := xsOf par allow
    pairDet xs u w * (margCount xs v false * margCount xs v true) =
      pairDet xs u v * pairDet xs v w := by
  classical
  intro xs
  let B := Finset.univ \ A
  let validA : Finset (Fin n) → Prop := fun xA =>
    ∀ j ∈ A, j ≠ e → allow j (decide (par j ∈ xA)) (decide (j ∈ xA)) = true
  let validB : Finset (Fin n) → Prop := fun xB =>
    ∀ j ∈ B, j ≠ e → allow j (decide (par j ∈ xB)) (decide (j ∈ xB)) = true
  have hxs_split : ∀ x : Finset (Fin n),
      x ∈ xs ↔ validA (x ∩ A) ∧ validB (x ∩ B) ∧
        edgeOk (decide (v ∈ x)) (decide (w ∈ x)) = true := by
    intro x
    simp only [xs, xsOf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨?_, ?_, ?_⟩
      · intro j hj hne
        have hpj : par j ∈ A := (hsep j hne).mp hj
        simpa [hj, hpj] using hx j
      · intro j hj hne
        have hjNA : j ∉ A := (Finset.mem_sdiff.mp hj).2
        have hpjNA : par j ∉ A := fun h => hjNA ((hsep j hne).mpr h)
        have hpj : par j ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpjNA⟩
        simpa [hj, hpj] using hx j
      · rw [← hedge x]
        exact hx e
    · rintro ⟨hA, hB, hok⟩ j
      by_cases hje : j = e
      · rw [hje, hedge x]; exact hok
      · by_cases hjA : j ∈ A
        · have hpj : par j ∈ A := (hsep j hje).mp hjA
          simpa [hjA, hpj] using hA j hjA hje
        · have hjB : j ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjA⟩
          have hpjNA : par j ∉ A := fun h => hjA ((hsep j hje).mpr h)
          have hpjB : par j ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpjNA⟩
          simpa [hjB, hpjB] using hB j hjB hje
  let L : Bool → Bool → Int := fun a c =>
    ((A.powerset.filter (fun xA => validA xA ∧ decide (u ∈ xA) = a ∧ decide (v ∈ xA) = c)).card : Int)
  let R : Bool → Bool → Int := fun c b =>
    ((B.powerset.filter (fun xB => validB xB ∧ decide (w ∈ xB) = b ∧ edgeOk c b = true)).card : Int)
  let triple : Bool → Bool → Bool → Int := fun a c b =>
    ((xs.filter (fun x => decide (u ∈ x) = a ∧ decide (v ∈ x) = c ∧ decide (w ∈ x) = b)).card : Int)
  have htriple : ∀ a c b, triple a c b = L a c * R c b := by
    intro a c b
    dsimp only [triple, L, R]
    norm_cast
    have hfilt : xs.filter (fun x => decide (u ∈ x) = a ∧ decide (v ∈ x) = c ∧ decide (w ∈ x) = b) =
        (Finset.univ : Finset (Finset (Fin n))).filter
          (fun x => (validA (x ∩ A) ∧ decide (u ∈ x ∩ A) = a ∧ decide (v ∈ x ∩ A) = c) ∧
                    (validB (x ∩ B) ∧ decide (w ∈ x ∩ B) = b ∧ edgeOk c b = true)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxs_split]
      have hu : (u ∈ x ∩ A) ↔ (u ∈ x) := by simp [huA]
      have hv : (v ∈ x ∩ A) ↔ (v ∈ x) := by simp [hvA]
      have hw : (w ∈ x ∩ B) ↔ (w ∈ x) := by simp [B, hwB]
      simp only [hu, hv, hw]
      constructor
      · rintro ⟨⟨hA, hB, hok⟩, ha, hc, hb⟩
        exact ⟨⟨hA, ha, hc⟩, ⟨hB, hb, by rw [← hc, ← hb]; exact hok⟩⟩
      · rintro ⟨⟨hA, ha, hc⟩, ⟨hB, hb, hok⟩⟩
        exact ⟨⟨hA, hB, by rw [hc, hb]; exact hok⟩, ha, hc, hb⟩
    rw [hfilt]
    exact card_split_prod A
      (fun xA => validA xA ∧ decide (u ∈ xA) = a ∧ decide (v ∈ xA) = c)
      (fun xB => validB xB ∧ decide (w ∈ xB) = b ∧ edgeOk c b = true)
  have huw : ∀ a b, pairCount xs u w a b = L a false * R false b + L a true * R true b := by
    intro a b
    rw [← htriple a false b, ← htriple a true b]
    dsimp only [pairCount, triple]
    norm_cast
    have hsp := card_split_bool (xs.filter (fun x => decide (u ∈ x) = a ∧ decide (w ∈ x) = b))
      (fun x => decide (v ∈ x))
    rw [hsp]
    congr 1 <;> congr 1 <;> ext x <;> simp only [Finset.mem_filter] <;> tauto
  have huv : ∀ a c, pairCount xs u v a c = L a c * R c false + L a c * R c true := by
    intro a c
    rw [← htriple a c false, ← htriple a c true]
    dsimp only [pairCount, triple]
    norm_cast
    have hsp := card_split_bool (xs.filter (fun x => decide (u ∈ x) = a ∧ decide (v ∈ x) = c))
      (fun x => decide (w ∈ x))
    rw [hsp]
    congr 1 <;> congr 1 <;> ext x <;> simp only [Finset.mem_filter] <;> tauto
  have hvw : ∀ c b, pairCount xs v w c b = L false c * R c b + L true c * R c b := by
    intro c b
    rw [← htriple false c b, ← htriple true c b]
    dsimp only [pairCount, triple]
    norm_cast
    have hsp := card_split_bool (xs.filter (fun x => decide (v ∈ x) = c ∧ decide (w ∈ x) = b))
      (fun x => decide (u ∈ x))
    rw [hsp]
    congr 1 <;> congr 1 <;> ext x <;> simp only [Finset.mem_filter] <;> tauto
  have hmv : ∀ c, margCount xs v c =
      (L false c + L true c) * (R c false + R c true) := by
    intro c
    have hsp : margCount xs v c = pairCount xs u v false c + pairCount xs u v true c := by
      dsimp only [margCount, pairCount]
      norm_cast
      have h := card_split_bool (xs.filter (fun x => decide (v ∈ x) = c)) (fun x => decide (u ∈ x))
      rw [h]
      congr 1 <;> congr 1 <;> ext x <;> simp only [Finset.mem_filter] <;> tauto
    rw [hsp, huv false c, huv true c]
    ring
  unfold pairDet
  rw [huw false false, huw true true, huw false true, huw true false,
      huv false false, huv true true, huv false true, huv true false,
      hvw false false, hvw true true, hvw false true, hvw true false,
      hmv false, hmv true]
  ring

lemma adj_det_ne_zero {n : Nat} (par : Fin n → Fin n) (allow : Fin n → Bool → Bool → Bool)
    {u v : Fin n} (h : goodAdj par allow u v) :
    pairDet (xsOf par allow) u v ≠ 0 := by
  unfold pairDet pairCount
  rcases h with ⟨_, hns, rfl⟩ | ⟨_, hns, rfl⟩
  · have hswap : ∀ a b : Bool,
        ((xsOf par allow).filter (fun x => decide (u ∈ x) = a ∧ decide (par u ∈ x) = b)).card =
          jointOf par allow u b a := by
      intro a b
      unfold jointOf
      congr 1; ext x; simp only [Finset.mem_filter]; tauto
    rw [hswap false false, hswap true true, hswap false true, hswap true false]
    intro hzero
    apply hns
    unfold splitsOf
    have : (jointOf par allow u false false : Int) * (jointOf par allow u true true : Int) =
        (jointOf par allow u true false : Int) * (jointOf par allow u false true : Int) := by
      linarith
    have hnat : jointOf par allow u false false * jointOf par allow u true true =
        jointOf par allow u true false * jointOf par allow u false true := by
      exact_mod_cast this
    rw [mul_comm (jointOf par allow u true false)] at hnat
    exact hnat
  · have hsame : ∀ a b : Bool,
        ((xsOf par allow).filter (fun x => decide (par v ∈ x) = a ∧ decide (v ∈ x) = b)).card =
          jointOf par allow v a b := fun _ _ => rfl
    rw [hsame false false, hsame true true, hsame false true, hsame true false]
    intro hzero
    apply hns
    unfold splitsOf
    have : (jointOf par allow v false false : Int) * (jointOf par allow v true true : Int) =
        (jointOf par allow v false true : Int) * (jointOf par allow v true false : Int) := by
      linarith
    exact_mod_cast this

lemma path_mem_iff {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (hstep : ∀ x y, R x y → (P x ↔ P y)) :
    ∀ {l : List α} {a b : α}, IsPath R l → l.head? = some a → l.getLast? = some b →
      (P a ↔ P b)
  | [], _, _, _, hhead, _ => by simp at hhead
  | [x], a, b, _, hhead, hlast => by
    simp at hhead hlast
    subst hhead; subst hlast
    rfl
  | x :: y :: rest, a, b, hch, hhead, hlast => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlast' : (y :: rest).getLast? = some b := by simpa using hlast
    exact (hstep x y hch.1).trans (path_mem_iff hstep hch.2 rfl hlast')

lemma path_det_ne_zero {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i)
    (allow : Fin n → Bool → Bool → Bool) :
    ∀ (L : Nat) (p : List (Fin n)) (u w : Fin n),
      p.length = L → 2 ≤ L → p.head? = some u → p.getLast? = some w →
      IsPath (goodAdj par allow) p → p.Nodup →
      pairDet (xsOf par allow) u w ≠ 0 := by
  classical
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro p u w hlen hL2 hhead hlast hch hnd
    have hp_ne : p ≠ [] := by intro h; subst h; simp at hlen; omega
    rcases List.eq_nil_or_concat p with rfl | ⟨q, w', rfl⟩
    · exact absurd rfl hp_ne
    rw [List.concat_eq_append] at hlen hhead hlast hch hnd
    have hww : w' = w := by simpa using hlast
    subst w'
    have hq_ne : q ≠ [] := by
      intro h; subst h; simp at hlen; omega
    rcases List.eq_nil_or_concat q with rfl | ⟨q0, v, rfl⟩
    · exact absurd rfl hq_ne
    rw [List.concat_eq_append] at hlen hhead hlast hch hnd
    have hch_q : IsPath (goodAdj par allow) (q0 ++ [v]) := isPath_append_left (q0 ++ [v]) [w] hch
    have hvw : goodAdj par allow v w := isPath_last_edge q0 v w hch
    cases q0 with
    | nil =>
      have huv : v = u := by simpa using hhead
      subst v
      exact adj_det_ne_zero par allow hvw
    | cons a as =>
      have hlen_q : ((a :: as) ++ [v]).length < L := by
        simp at hlen ⊢; omega
      have hL2_q : 2 ≤ ((a :: as) ++ [v]).length := by simp
      have hhead_q : ((a :: as) ++ [v]).head? = some u := by simpa using hhead
      have hlast_q : ((a :: as) ++ [v]).getLast? = some v := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil v [])]; rfl
      have hnd_q : ((a :: as) ++ [v]).Nodup := by
        have hsub : ((a :: as) ++ [v]).Sublist (((a :: as) ++ [v]) ++ [w]) :=
          List.sublist_append_left _ _
        exact hnd.sublist hsub
      have hdet_uv : pairDet (xsOf par allow) u v ≠ 0 :=
        ih _ hlen_q _ u v rfl hL2_q hhead_q hlast_q hch_q hnd_q
      have hdet_vw : pairDet (xsOf par allow) v w ≠ 0 :=
        adj_det_ne_zero par allow hvw
      have hw_notin : w ∉ (a :: as) ++ [v] := by
        rw [List.nodup_append] at hnd
        intro hw_in
        exact hnd.2.2 w hw_in w (List.mem_singleton_self w) rfl
      have hch_restr : IsPath (fun x y => goodAdj par allow x y ∧ x ≠ w ∧ y ≠ w)
          ((a :: as) ++ [v]) := by
        have hmem_pair : ∀ (l : List (Fin n)), IsPath (goodAdj par allow) l → w ∉ l →
            IsPath (fun x y => goodAdj par allow x y ∧ x ≠ w ∧ y ≠ w) l := by
          intro l hl hwl
          induction l with
          | nil => trivial
          | cons x xs ih_l =>
            cases xs with
            | nil => trivial
            | cons y ys =>
              refine ⟨⟨hl.1, fun h => hwl (h ▸ List.mem_cons_self),
                fun h => hwl (List.mem_cons_of_mem _ (h ▸ List.mem_cons_self))⟩,
                ih_l hl.2 (fun h => hwl (List.mem_cons_of_mem _ h))⟩
        exact hmem_pair _ hch_q hw_notin
      have hmul : pairDet (xsOf par allow) u w *
          (margCount (xsOf par allow) v false * margCount (xsOf par allow) v true) =
          pairDet (xsOf par allow) u v * pairDet (xsOf par allow) v w := by
        rcases hvw with ⟨hv_lt, _, hv_eq⟩ | ⟨hw_lt, _, hw_eq⟩
        · let A : Finset (Fin n) := Finset.univ.filter (fun z => desc par v z)
          have hvA : v ∈ A := by simp [A, desc_self]
          have hwB : w ∈ Finset.univ \ A := by
            simp only [A, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
            rw [← hv_eq]
            exact par_not_desc hpar hv_lt
          have hsep : ∀ j : Fin n, j ≠ v → (j ∈ A ↔ par j ∈ A) := by
            intro j hj
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
            exact desc_iff_par_desc hj
          have huA : u ∈ A := by
            have hstep : ∀ x y, (goodAdj par allow x y ∧ x ≠ w ∧ y ≠ w) → (x ∈ A ↔ y ∈ A) := by
              intro x y ⟨hadj, hxw, hyw⟩
              rcases hadj with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
              · have hxv : x ≠ v := fun h => by subst h; exact hyw hv_eq
                exact hsep x hxv
              · have hyv : y ≠ v := fun h => by subst h; exact hxw hv_eq
                exact (hsep y hyv).symm
            exact (path_mem_iff hstep hch_restr hhead_q hlast_q).mpr hvA
          exact markov_det_mul par allow A v u v w (fun b1 b2 => allow v b2 b1)
            huA hvA hwB (fun x => by rw [hv_eq]) hsep
        · let B : Finset (Fin n) := Finset.univ.filter (fun z => desc par w z)
          let A : Finset (Fin n) := Finset.univ \ B
          have hvA : v ∈ A := by
            simp only [A, B, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
            rw [← hw_eq]
            exact par_not_desc hpar hw_lt
          have hwB : w ∈ Finset.univ \ A := by
            simp [A, B, desc_self]
          have hsep : ∀ j : Fin n, j ≠ w → (j ∈ A ↔ par j ∈ A) := by
            intro j hj
            simp only [A, B, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
            exact not_congr (desc_iff_par_desc hj)
          have huA : u ∈ A := by
            have hstep : ∀ x y, (goodAdj par allow x y ∧ x ≠ w ∧ y ≠ w) → (x ∈ A ↔ y ∈ A) := by
              intro x y ⟨hadj, hxw, hyw⟩
              rcases hadj with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
              · exact hsep x hxw
              · exact (hsep y hyw).symm
            exact (path_mem_iff hstep hch_restr hhead_q hlast_q).mpr hvA
          exact markov_det_mul par allow A w u v w (fun b1 b2 => allow w b1 b2)
            huA hvA hwB (fun x => by rw [hw_eq]) hsep
      intro hzero
      rw [hzero, zero_mul] at hmul
      exact mul_ne_zero hdet_uv hdet_vw hmul.symm

lemma singletons_imply_cut {n : Nat} {par : Fin n → Fin n} (hpar : ∀ i, par i ≤ i)
    (allow : Fin n → Bool → Bool → Bool) (r : Fin n) (T : Finset (Fin n)) (hrT : r ∉ T)
    (hsing : ∀ i ∈ T, indepOf par allow r {i}) :
    ∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splitsOf par allow i := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun v => Relation.ReflTransGen (goodAdj par allow) r v)
  refine ⟨U, ?_, ?_, ?_⟩
  · simp [U, Relation.ReflTransGen.refl]
  · rw [Finset.disjoint_left]
    intro t htU htT
    have hrt : r ≠ t := fun h => hrT (h ▸ htT)
    have hreach : Relation.ReflTransGen (goodAdj par allow) r t := (Finset.mem_filter.mp htU).2
    rcases exists_nodup_path hreach with ⟨p, hhead, hlast, hch, hnd⟩
    have hlen2 : 2 ≤ p.length := by
      cases p with
      | nil => simp at hhead
      | cons a as =>
        cases as with
        | nil =>
          simp at hhead hlast
          exact absurd (hhead.symm.trans hlast) hrt
        | cons b bs => simp
    have hdet_ne : pairDet (xsOf par allow) r t ≠ 0 :=
      path_det_ne_zero hpar allow p.length p r t rfl hlen2 hhead hlast hch hnd
    have hind := hsing t htT ∅ (Finset.empty_subset {t})
    have hpin0 : ∀ a : Bool,
        (pinOf par allow r a {t} ∅ : Int) = pairCount (xsOf par allow) r t a false := by
      intro a
      unfold pinOf pairCount
      norm_cast
      congr 1; ext x
      simp only [Finset.mem_filter]
      have hmt : (x ∩ {t} = ∅) ↔ (decide (t ∈ x) = false) := by
        simp [Finset.ext_iff]
      rw [hmt]
    have hpinAll : ∀ a : Bool,
        (pinOf par allow r a ∅ ∅ : Int) =
          pairCount (xsOf par allow) r t a false + pairCount (xsOf par allow) r t a true := by
      intro a
      unfold pinOf pairCount
      norm_cast
      have h1 : (xsOf par allow).filter (fun x => decide (r ∈ x) = a ∧ x ∩ ∅ = ∅) =
          (xsOf par allow).filter (fun x => decide (r ∈ x) = a) := by
        ext x; simp
      rw [h1, card_split_bool ((xsOf par allow).filter (fun x => decide (r ∈ x) = a))
        (fun x => decide (t ∈ x))]
      congr 1 <;> congr 1 <;> ext x <;> simp only [Finset.mem_filter] <;> tauto
    have hindZ : (pinOf par allow r false {t} ∅ : Int) * (pinOf par allow r true ∅ ∅ : Int) =
        (pinOf par allow r true {t} ∅ : Int) * (pinOf par allow r false ∅ ∅ : Int) := by
      exact_mod_cast hind
    rw [hpin0 false, hpin0 true, hpinAll false, hpinAll true] at hindZ
    apply hdet_ne
    unfold pairDet
    linarith
  · intro i hne
    by_contra hns
    have hiff : i ∈ U ↔ par i ∈ U := by
      have hi_ne : i ≠ par i := by
        intro heq
        rw [← heq] at hne
        simp at hne
      have hi_lt : par i < i := lt_of_le_of_ne (hpar i) hi_ne.symm
      have hadj1 : goodAdj par allow i (par i) := Or.inl ⟨hi_lt, hns, rfl⟩
      have hadj2 : goodAdj par allow (par i) i := Or.inr ⟨hi_lt, hns, rfl⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Relation.ReflTransGen.tail h hadj1,
             fun h => Relation.ReflTransGen.tail h hadj2⟩
    by_cases h1 : i ∈ U
    · have h2 : par i ∈ U := hiff.mp h1
      simp [h1, h2] at hne
    · have h2 : par i ∉ U := fun h => h1 (hiff.mpr h)
      simp [h1, h2] at hne

theorem main :
∀ (n : Nat) (par : Fin n → Fin n), (∀ i, par i ≤ i) →
  ∀ (allow : Fin n → Bool → Bool → Bool) (r : Fin n) (T : Finset (Fin n)), r ∉ T →
  let xs := (Finset.univ : Finset (Finset (Fin n))).filter (fun x =>
    ∀ i, allow i (decide (par i ∈ x)) (decide (i ∈ x)) = true)
  let pin := fun (b : Bool) (S B : Finset (Fin n)) =>
    (xs.filter (fun x => decide (r ∈ x) = b ∧ x ∩ S = B)).card
  let independent := fun (S : Finset (Fin n)) =>
    ∀ B ⊆ S, pin false S B * pin true ∅ ∅ = pin true S B * pin false ∅ ∅
  let joint := fun (i : Fin n) (a b : Bool) =>
    (xs.filter (fun x => decide (par i ∈ x) = a ∧ decide (i ∈ x) = b)).card
  let splits := fun (i : Fin n) =>
    joint i false false * joint i true true = joint i false true * joint i true false
  (independent T ↔ ∀ i ∈ T, independent {i}) ∧
    (independent T ↔ ∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splits i) := by
  intro n par hpar allow r T hrT
  dsimp only
  have h1 : (∀ B ⊆ T, pinOf par allow r false T B * pinOf par allow r true ∅ ∅ =
      pinOf par allow r true T B * pinOf par allow r false ∅ ∅) →
      ∀ i ∈ T, ∀ B ⊆ {i}, pinOf par allow r false {i} B * pinOf par allow r true ∅ ∅ =
        pinOf par allow r true {i} B * pinOf par allow r false ∅ ∅ :=
    indep_singleton par allow r T
  have h2 : (∀ i ∈ T, indepOf par allow r {i}) →
      ∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
        ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splitsOf par allow i :=
    singletons_imply_cut hpar allow r T hrT
  have h3 : (∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splitsOf par allow i) →
      indepOf par allow r T := by
    rintro ⟨U, hrU, hUT, hcut⟩
    exact cut_implies_indep hpar allow r T U hrU hUT hcut
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end PEqualNP.Outside.L_lib_1141_aux

theorem PEqualNP.Outside.L_lib_1141 : ∀ (n : Nat) (par : Fin n → Fin n), (∀ i, par i ≤ i) →
  ∀ (allow : Fin n → Bool → Bool → Bool) (r : Fin n) (T : Finset (Fin n)), r ∉ T →
  let xs := (Finset.univ : Finset (Finset (Fin n))).filter (fun x =>
    ∀ i, allow i (decide (par i ∈ x)) (decide (i ∈ x)) = true)
  let pin := fun (b : Bool) (S B : Finset (Fin n)) =>
    (xs.filter (fun x => decide (r ∈ x) = b ∧ x ∩ S = B)).card
  let independent := fun (S : Finset (Fin n)) =>
    ∀ B ⊆ S, pin false S B * pin true ∅ ∅ = pin true S B * pin false ∅ ∅
  let joint := fun (i : Fin n) (a b : Bool) =>
    (xs.filter (fun x => decide (par i ∈ x) = a ∧ decide (i ∈ x) = b)).card
  let splits := fun (i : Fin n) =>
    joint i false false * joint i true true = joint i false true * joint i true false
  (independent T ↔ ∀ i ∈ T, independent {i}) ∧
    (independent T ↔ ∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splits i) :=
  PEqualNP.Outside.L_lib_1141_aux.main

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finset.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_meta_33607

def esList (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i, j)))

lemma mem_esList_iff {n : ℕ} {p : Fin n × Fin n} :
    p ∈ esList n ↔ p.1 < p.2 := by
  simp only [esList, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    decide_eq_true_eq, true_and]
  constructor
  · rintro ⟨i, j, hij, rfl⟩; exact hij
  · intro h; exact ⟨p.1, p.2, h, rfl⟩

lemma esList_nodup (n : ℕ) : (esList n).Nodup := by
  unfold esList
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    exact (List.Nodup.filter _ (List.nodup_finRange n)).map (fun a b h => (Prod.ext_iff.mp h).2)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_finRange]
    intro p hp1 hp2
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and] at hp1 hp2
    rcases hp1 with ⟨b1, _, rfl⟩
    rcases hp2 with ⟨b2, _, h2⟩
    have hfst := (Prod.ext_iff.mp h2).1
    have hval : j = i := by
      have := congrArg Fin.val hfst
      simpa using this
    exact absurd hval.symm (by omega)

lemma esList_length (n : ℕ) : (esList n).length = n.choose 2 := by
  rw [← List.toFinset_card_of_nodup (esList_nodup n)]
  have hcard : ((esList n).toFinset).card = ((Finset.univ : Finset (Fin n)).powersetCard 2).card := by
    refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin n))) ?_ ?_ ?_
    · intro p hp
      have hlt : p.1 < p.2 := mem_esList_iff.mp (List.mem_toFinset.mp hp)
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hlt.ne⟩
    · intro p1 hp1 p2 hp2 heq
      have h1 : p1.1 < p1.2 := mem_esList_iff.mp (List.mem_toFinset.mp hp1)
      have h2 : p2.1 < p2.2 := mem_esList_iff.mp (List.mem_toFinset.mp hp2)
      have m1 : p1.1 ∈ ({p2.1, p2.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
      have m2 : p1.2 ∈ ({p2.1, p2.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have m3 : p2.1 ∈ ({p1.1, p1.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
      have m4 : p2.2 ∈ ({p1.1, p1.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
      ext
      · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
      · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      rcases Finset.card_eq_two.mp hs.2 with ⟨a, b, hab, rfl⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), List.mem_toFinset.mpr (mem_esList_iff.mpr hlt), rfl⟩
      · exact ⟨(b, a), List.mem_toFinset.mpr (mem_esList_iff.mpr hgt), Finset.pair_comm b a⟩
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma row_foldl_lt {n M k L r : ℕ} (hk : 0 < k) (G : Fin n → Fin n → Bool) (j : Fin (n + 2 * M)) :
    ∀ (l : List ((Fin n × Fin n) × ℕ)) (acc : ℕ),
      acc < 2 ^ k →
      (l.foldl (fun acc z =>
        let keep := if G z.1.1 z.1.2 then (j.val = z.1.1.val ∨ j.val = z.1.2.val)
          else (j.val = n + 2 * z.2 ∨ j.val = n + 2 * z.2 + 1)
        if keep then acc ||| (1 <<< ((L * z.2 + (2 * r - 2)) % k)) else acc) acc) < 2 ^ k := by
  intro l
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons z zs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    by_cases hkeep : (if G z.1.1 z.1.2 = true then j.val = z.1.1.val ∨ j.val = z.1.2.val
      else j.val = n + 2 * z.2 ∨ j.val = n + 2 * z.2 + 1)
    · simp only [hkeep, ↓reduceIte]
      apply Nat.or_lt_two_pow hacc
      have hmod : (L * z.2 + (2 * r - 2)) % k < k := Nat.mod_lt _ hk
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) hmod
    · simp only [hkeep, ↓reduceIte]
      exact hacc

lemma row_foldl_testBit {n M k L r : ℕ} (G : Fin n → Fin n → Bool) (j : Fin (n + 2 * M)) :
    ∀ (l : List ((Fin n × Fin n) × ℕ)) (acc p : ℕ),
      (l.foldl (fun acc z =>
        let keep := if G z.1.1 z.1.2 then (j.val = z.1.1.val ∨ j.val = z.1.2.val)
          else (j.val = n + 2 * z.2 ∨ j.val = n + 2 * z.2 + 1)
        if keep then acc ||| (1 <<< ((L * z.2 + (2 * r - 2)) % k)) else acc) acc).testBit p = true ↔
      acc.testBit p = true ∨
        ∃ z ∈ l, (if G z.1.1 z.1.2 = true then j.val = z.1.1.val ∨ j.val = z.1.2.val
          else j.val = n + 2 * z.2 ∨ j.val = n + 2 * z.2 + 1) ∧ (L * z.2 + (2 * r - 2)) % k = p := by
  intro l
  induction l with
  | nil => intro acc p; simp
  | cons z zs ih =>
    intro acc p
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hkeep : (if G z.1.1 z.1.2 = true then j.val = z.1.1.val ∨ j.val = z.1.2.val
      else j.val = n + 2 * z.2 ∨ j.val = n + 2 * z.2 + 1)
    · simp only [hkeep, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
      have hbit : (1 <<< ((L * z.2 + (2 * r - 2)) % k)).testBit p = true ↔
          (L * z.2 + (2 * r - 2)) % k = p := by
        rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
        simp
      rw [hbit]
      constructor
      · rintro ((hacc | hhit) | ⟨w, hw, hkw, hpw⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨z, Or.inl rfl, hkeep, hhit⟩
        · exact Or.inr ⟨w, Or.inr hw, hkw, hpw⟩
      · rintro (hacc | ⟨w, rfl | hw, hkw, hpw⟩)
        · exact Or.inl (Or.inl hacc)
        · exact Or.inl (Or.inr hpw)
        · exact Or.inr ⟨w, hw, hkw, hpw⟩
    · simp only [hkeep, ↓reduceIte]
      constructor
      · rintro (hacc | ⟨w, hw, hkw, hpw⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨w, Or.inr hw, hkw, hpw⟩
      · rintro (hacc | ⟨w, rfl | hw, hkw, hpw⟩)
        · exact Or.inl hacc
        · exact absurd hkw hkeep
        · exact Or.inr ⟨w, hw, hkw, hpw⟩

lemma mem_zipIdx_iff {α : Type*} {l : List α} {z : α × ℕ} :
    z ∈ l.zipIdx ↔ ∃ h : z.2 < l.length, z.1 = l[z.2] := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_zipIdx] at hi
    refine ⟨by simpa [List.getElem_zipIdx] using hi, ?_⟩
    simp [List.getElem_zipIdx]
  · rintro ⟨h, h1⟩
    refine ⟨z.2, by simp [h], ?_⟩
    ext
    · simp [List.getElem_zipIdx, h1]
    · simp [List.getElem_zipIdx]

lemma choose_two_sum_eq {α : Type*} [DecidableEq α] (𝒞 : Finset (Finset α))
    (h𝒞 : ∀ C ∈ 𝒞, 2 ≤ C.card) :
    ∑ C ∈ 𝒞, C.card.choose 2 ≤ (∑ C ∈ 𝒞, (C.card - 1) + 1).choose 2 ∧
    (2 ≤ 𝒞.card →
      ∑ C ∈ 𝒞, C.card.choose 2 + (∑ C ∈ 𝒞, (C.card - 1) - 1) ≤ (∑ C ∈ 𝒞, (C.card - 1) + 1).choose 2) := by
  induction 𝒞 using Finset.induction_on with
  | empty => simp
  | @insert C₀ 𝒞' hC₀ ih =>
    have h𝒞' : ∀ C ∈ 𝒞', 2 ≤ C.card := fun C hC => h𝒞 C (Finset.mem_insert_of_mem hC)
    have hC₀_ge : 2 ≤ C₀.card := h𝒞 C₀ (Finset.mem_insert_self _ _)
    obtain ⟨ih1, _⟩ := ih h𝒞'
    rw [Finset.sum_insert hC₀, Finset.sum_insert hC₀, Finset.card_insert_of_notMem hC₀]
    set a := C₀.card - 1
    set b := ∑ C ∈ 𝒞', (C.card - 1)
    have ha : 1 ≤ a := by omega
    have hC₀_eq : C₀.card = a + 1 := by omega
    have h_alg : (a + b + 1).choose 2 = (a + 1).choose 2 + (b + 1).choose 2 + a * b := by
      have h2dvd : ∀ x : ℕ, 2 ∣ (x + 1) * x := fun x => by
        rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(2 * k + 1) * k, by ring⟩
        · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
      rw [Nat.choose_two_right, Nat.choose_two_right, Nat.choose_two_right]
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_add 2, Nat.mul_add 2, Nat.mul_div_cancel' (h2dvd _), Nat.mul_div_cancel' (h2dvd _), Nat.mul_div_cancel' (h2dvd _)]
      ring
    rw [hC₀_eq]
    constructor
    · have h0 : 0 ≤ a * b := Nat.zero_le _
      rw [h_alg]; linarith
    · intro hcard
      have h𝒞'_pos : 1 ≤ 𝒞'.card := by omega
      obtain ⟨C₁, hC₁⟩ := Finset.card_pos.mp h𝒞'_pos
      have hC₁_ge : 1 ≤ C₁.card - 1 := by have := h𝒞' C₁ hC₁; omega
      have hb : 1 ≤ b := by
        calc 1 ≤ C₁.card - 1 := hC₁_ge
          _ ≤ ∑ C ∈ 𝒞', (C.card - 1) := Finset.single_le_sum (f := fun C : Finset α => C.card - 1) (fun _ _ => Nat.zero_le _) hC₁
      obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le ha
      obtain ⟨b', hb'⟩ := Nat.exists_eq_add_of_le hb
      have hab : a + b - 1 ≤ a * b := by
        rw [ha', hb']
        simp only [add_mul, mul_add, one_mul, mul_one]
        omega
      rw [h_alg]
      linarith

lemma choose_two_add_sub {a : ℕ} (ha : 1 ≤ a) :
    (a + 1).choose 2 = a.choose 2 + a := by
  cases a with
  | zero => omega
  | succ m =>
    have h2dvd : ∀ x : ℕ, 2 ∣ (x + 1) * x := fun x => by
      rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨(2 * k + 1) * k, by ring⟩
      · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    rw [Nat.choose_two_right, Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_add 2, Nat.mul_div_cancel' (h2dvd _), Nat.mul_div_cancel' (h2dvd _)]
    ring

lemma choose_two_mono {a b : ℕ} (hab : a ≤ b) : a.choose 2 ≤ b.choose 2 := by
  rw [Nat.choose_two_right, Nat.choose_two_right]
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul hab (Nat.sub_le_sub_right hab 1)

lemma count_subsets_with_sizes {I : Type*} [Fintype I] [DecidableEq I] {M L : ℕ}
    (B : Fin M → Finset I)
    (hdisj : Pairwise (fun u v => Disjoint (B u) (B v)))
    (huniv : Finset.univ.biUnion B = Finset.univ)
    (hcardB : ∀ u, (B u).card = L)
    (D Z : Finset (Fin M)) (hDZ : Disjoint D Z) :
    Fintype.card { P : Finset I //
      (∀ u, (B u \ P).card ≤ 2) ∧
      Finset.univ.filter (fun u => (B u \ P).card = 2) = D ∧
      Finset.univ.filter (fun u => (B u \ P).card = 0) = Z } =
    (L.choose 2) ^ D.card * L ^ (M - D.card - Z.card) := by
  let target : Fin M → ℕ := fun u => if u ∈ D then 2 else if u ∈ Z then 0 else 1
  let Q := ∀ u : Fin M, { s : Finset I // s ⊆ B u ∧ s.card = target u }
  have e : { P : Finset I //
      (∀ u, (B u \ P).card ≤ 2) ∧
      Finset.univ.filter (fun u => (B u \ P).card = 2) = D ∧
      Finset.univ.filter (fun u => (B u \ P).card = 0) = Z } ≃ Q :=
    { toFun := fun P u => ⟨B u \ P.1, Finset.sdiff_subset, by
        have hle := P.2.1 u
        have hD := P.2.2.1
        have hZ := P.2.2.2
        dsimp only [target]
        by_cases huD : u ∈ D
        · simp only [huD, ↓reduceIte]
          rw [← hD] at huD
          exact (Finset.mem_filter.mp huD).2
        · by_cases huZ : u ∈ Z
          · simp only [huD, huZ, ↓reduceIte]
            rw [← hZ] at huZ
            exact (Finset.mem_filter.mp huZ).2
          · simp only [huD, huZ, ↓reduceIte]
            have hne2 : (B u \ P.1).card ≠ 2 := by
              intro heq; apply huD; rw [← hD]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, heq⟩
            have hne0 : (B u \ P.1).card ≠ 0 := by
              intro heq; apply huZ; rw [← hZ]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, heq⟩
            omega⟩
      invFun := fun f => ⟨Finset.univ \ Finset.univ.biUnion (fun u => (f u).1), by
        have hpart : ∀ u : Fin M, B u \ (Finset.univ \ Finset.univ.biUnion (fun v => (f v).1)) = (f u).1 := by
          intro u
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_not]
          constructor
          · rintro ⟨hxB, v, hxv⟩
            by_cases huv : v = u
            · subst huv; exact hxv
            · exact absurd (Finset.disjoint_left.mp (hdisj huv) ((f v).2.1 hxv) hxB) id
          · intro hxf
            exact ⟨(f u).2.1 hxf, u, hxf⟩
        refine ⟨?_, ?_, ?_⟩
        · intro u; rw [hpart u, (f u).2.2]; dsimp only [target]; split_ifs <;> omega
        · ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpart u, (f u).2.2]
          dsimp only [target]
          by_cases huD : u ∈ D
          · simp [huD]
          · by_cases huZ : u ∈ Z <;> simp [huD, huZ]
        · ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpart u, (f u).2.2]
          dsimp only [target]
          by_cases huD : u ∈ D
          · have : u ∉ Z := Finset.disjoint_left.mp hDZ huD
            simp [huD, this]
          · by_cases huZ : u ∈ Z <;> simp [huD, huZ]⟩
      left_inv := fun P => by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_exists, not_and]
        constructor
        · intro hx
          have hxm : x ∈ (Finset.univ : Finset I) := Finset.mem_univ x
          rw [← huniv, Finset.mem_biUnion] at hxm
          obtain ⟨u, _, hxu⟩ := hxm
          exact not_not.mp (hx u hxu)
        · intro hx u _ hnot
          exact hnot hx
      right_inv := fun f => by
        funext u
        apply Subtype.ext
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and, not_not]
        constructor
        · rintro ⟨hxB, v, hxv⟩
          by_cases huv : v = u
          · subst huv; exact hxv
          · exact absurd (Finset.disjoint_left.mp (hdisj huv) ((f v).2.1 hxv) hxB) id
        · intro hxf
          exact ⟨(f u).2.1 hxf, u, hxf⟩ }
  rw [Fintype.card_congr e, Fintype.card_pi]
  have hterm : ∀ u : Fin M, Fintype.card { s : Finset I // s ⊆ B u ∧ s.card = target u } =
      L.choose (target u) := by
    intro u
    have e2 : { s : Finset I // s ⊆ B u ∧ s.card = target u } ≃ (B u).powersetCard (target u) :=
      { toFun := fun s => ⟨s.1, Finset.mem_powersetCard.mpr s.2⟩
        invFun := fun s => ⟨s.1, Finset.mem_powersetCard.mp s.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e2, Fintype.card_coe, Finset.card_powersetCard, hcardB u]
  simp_rw [hterm]
  have hsplit : (Finset.univ : Finset (Fin M)) = D ∪ (Z ∪ (Finset.univ \ (D ∪ Z))) := by
    ext u; simp; tauto
  have hd1 : Disjoint D (Z ∪ (Finset.univ \ (D ∪ Z))) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hDZ, disjoint_sdiff_self_right.mono_right (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left)⟩
  have hd2 : Disjoint Z (Finset.univ \ (D ∪ Z)) :=
    disjoint_sdiff_self_right.mono_right (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_right)
  rw [hsplit, Finset.prod_union hd1, Finset.prod_union hd2]
  have hDprod : ∏ u ∈ D, L.choose (target u) = (L.choose 2) ^ D.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl ?_
    intro u hu
    simp [target, hu]
  have hZprod : ∏ u ∈ Z, L.choose (target u) = 1 := by
    refine Finset.prod_eq_one ?_
    intro u hu
    have huD : u ∉ D := Finset.disjoint_right.mp hDZ hu
    simp [target, huD, hu]
  have hOprod : ∏ u ∈ Finset.univ \ (D ∪ Z), L.choose (target u) = L ^ (M - D.card - Z.card) := by
    have hcardO : (Finset.univ \ (D ∪ Z)).card = M - D.card - Z.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_union_of_disjoint hDZ,
        Finset.card_univ, Fintype.card_fin]
      omega
    rw [← hcardO, ← Finset.prod_const]
    refine Finset.prod_congr rfl ?_
    intro u hu
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, not_or, true_and] at hu
    simp [target, hu.1, hu.2]
  rw [hDprod, hZprod, hOprod, one_mul]

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

set_option maxHeartbeats 800000 in
lemma main_proof (n t r δ : Nat) (ht3 : 3 ≤ t) (htn : t ≤ n) (hr4 : 4 ≤ r) (hδ : δ < t - 2)
    (G : Fin n → Fin n → Bool) :
    let es := esList n
    let items := es.zipIdx.toFinset
    let M := es.length
    let L := 5 * r - 2
    let k := L * M
    let m := n + 2 * M
    let I := Fin k
    let A := Bool × I
    let F := ZMod 2
    let Y := Fin m → F
    let T := t.choose 2
    let b := (L - 1) * M - (t - 1).choose 2 + δ
    let row := fun (j : Fin m) => es.zipIdx.foldl (fun acc z =>
      let keep := if G z.1.1 z.1.2 then (j.val = z.1.1.val ∨ j.val = z.1.2.val)
        else (j.val = n + 2 * z.2 ∨ j.val = n + 2 * z.2 + 1)
      if keep then acc ||| (1 <<< ((L * z.2 + (2 * r - 2)) % k)) else acc) (0 : Nat)
    let delay := fun col : Bool => if col then 3 * r + 1 else 2 * r - 2
    let reach := fun col : Bool => if col then 7 * r - 2 else 5 * r - 3
    let scope := fun a : A => (Finset.univ : Finset I).filter (fun i =>
      ∃ d : Fin (reach a.1 + 1), (a.2.val + d.val) % k = i.val)
    let col := fun (a : A) (j : Fin m) =>
      if (!a.1 && (row j).testBit ((a.2.val + delay a.1) % k)) then (1 : F) else 0
    let active := (Finset.univ : Finset A).filter (fun a => col a ≠ 0)
    let left := fun (P : Finset I) (a : A) => scope a \ P
    let good := fun (P : Finset I) => ∀ a ∈ active, (left P a).card ≤ 2
    let pairs := fun (P : Finset I) => (active.image (left P)).filter (fun e => e.card = 2)
    let rank := fun (V : Finset Y) => Module.finrank F (Submodule.span F (V : Set Y))
    let worst := fun (P : Finset I) => (Finset.univ : Finset (A → F)).sup (fun w =>
      rank ((pairs P).image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)))
    let works := fun (P : Finset I) => good P ∧ worst P ≤ t - 1 ∧ P.card + worst P ≤ b
    let block := fun (u : Nat) => (Finset.univ : Finset I).filter (fun i =>
      L * u ≤ i.val ∧ i.val < L * (u + 1))
    let decode := fun (P : Finset I) => (items.filter (fun z =>
      G z.1.1 z.1.2 = true ∧ (block z.2 \ P).card = 2)).biUnion (fun z =>
        ({z.1.1, z.1.2} : Finset (Fin n)))
    let edgesIn := fun (U : Finset (Fin n)) => (es.toFinset.filter (fun e =>
      e.1 ∈ U ∧ e.2 ∈ U ∧ G e.1 e.2 = true)).card
    (∀ j : Fin m, row j < 2 ^ k) ∧
    (∀ U : Finset (Fin n), Nat.card {P : Finset I // works P ∧ decode P = U} =
      if U.card = t then
        (Finset.range (T + 1)).sum (fun j => (Finset.range (M - j + 1)).sum (fun z =>
          if T - j + z ≤ δ then (edgesIn U).choose j * (M - j).choose z *
            (L.choose 2) ^ j * L ^ (M - j - z) else 0))
      else 0) ∧
    (δ = 0 → Nat.card {P : Finset I // works P} =
      ((Finset.univ : Finset (Fin n)).powersetCard t |>.filter (fun U => edgesIn U = T)).card *
        (L.choose 2) ^ T * L ^ (M - T)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro es items M L k m I A F Y T b row delay reach scope col active left good pairs rank worst works block decode edgesIn
  have hM_eq : M = n.choose 2 := esList_length n
  have hM_ge3 : 3 ≤ M := by
    rw [hM_eq]
    have : 3 = (3 : ℕ).choose 2 := by decide
    rw [this]
    exact Nat.choose_le_choose 2 (by omega)
  have hL_ge18 : 18 ≤ L := by dsimp only [L]; omega
  have hk_pos : 0 < k := Nat.mul_pos (by omega) (by omega)
  have hTM : T ≤ M := by
    dsimp only [T]
    rw [hM_eq]
    exact Nat.choose_le_choose 2 htn
  have hPart1 : ∀ j : Fin m, row j < 2 ^ k := by
    intro j
    exact row_foldl_lt hk_pos G j es.zipIdx 0 (Nat.pow_pos (by omega))

  let eAt : Fin M → Fin n × Fin n := fun u => es[u.val]
  have heAt_lt : ∀ u : Fin M, (eAt u).1 < (eAt u).2 := by
    intro u
    exact mem_esList_iff.mp (List.getElem_mem u.isLt)
  let aAt : Fin M → A := fun u => (false, ⟨L * u.val, by
    have : L * u.val < L * M := Nat.mul_lt_mul_of_pos_left u.isLt (by omega)
    exact this⟩)
  have haAt_inj : Function.Injective aAt := by
    intro u v huv
    have hval : (aAt u).2.val = (aAt v).2.val := congrArg (fun x => x.2.val) huv
    dsimp only [aAt] at hval
    have : u.val = v.val := Nat.eq_of_mul_eq_mul_left (by omega) hval
    exact Fin.ext this
  have hpos_lt : ∀ u : Fin M, L * u.val + (2 * r - 2) < k := by
    intro u
    have h1 : 2 * r - 2 < L := by dsimp only [L]; omega
    have h2 : L * u.val + L = L * (u.val + 1) := by ring
    have h3 : L * (u.val + 1) ≤ L * M := Nat.mul_le_mul_left L u.isLt
    omega
  have hcol_true : ∀ x : I, col (true, x) = 0 := by
    intro x; ext j; simp [col]
  have hrow_bit : ∀ (j : Fin m) (p : ℕ),
      (row j).testBit p = true ↔ ∃ u : Fin M,
        (if G (eAt u).1 (eAt u).2 = true then j.val = (eAt u).1.val ∨ j.val = (eAt u).2.val
         else j.val = n + 2 * u.val ∨ j.val = n + 2 * u.val + 1) ∧
        L * u.val + (2 * r - 2) = p := by
    intro j p
    dsimp only [row]
    rw [row_foldl_testBit]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨z, hz, hk_keep, hp⟩
      rw [mem_zipIdx_iff] at hz
      obtain ⟨hu, hzf⟩ := hz
      refine ⟨⟨z.2, hu⟩, ?_, ?_⟩
      · simpa [eAt, hzf] using hk_keep
      · rw [Nat.mod_eq_of_lt (hpos_lt ⟨z.2, hu⟩)] at hp
        exact hp
    · rintro ⟨u, hk_keep, hp⟩
      refine ⟨(eAt u, u.val), ?_, hk_keep, ?_⟩
      · rw [mem_zipIdx_iff]
        exact ⟨u.isLt, rfl⟩
      · rw [Nat.mod_eq_of_lt (hpos_lt u)]
        exact hp
  have hcol_aAt : ∀ (u : Fin M) (j : Fin m),
      col (aAt u) j =
        if (if G (eAt u).1 (eAt u).2 = true then j.val = (eAt u).1.val ∨ j.val = (eAt u).2.val
            else j.val = n + 2 * u.val ∨ j.val = n + 2 * u.val + 1)
        then (1 : F) else 0 := by
    intro u j
    dsimp only [col, aAt, delay]
    simp only [Bool.not_false, Bool.true_and, if_neg Bool.false_ne_true]
    rw [Nat.mod_eq_of_lt (hpos_lt u)]
    by_cases hkeep : (if G (eAt u).1 (eAt u).2 = true then j.val = (eAt u).1.val ∨ j.val = (eAt u).2.val
      else j.val = n + 2 * u.val ∨ j.val = n + 2 * u.val + 1)
    · have htb : (row j).testBit (L * u.val + (2 * r - 2)) = true :=
        (hrow_bit j _).mpr ⟨u, hkeep, rfl⟩
      simp [hkeep, htb]
    · have htb : (row j).testBit (L * u.val + (2 * r - 2)) = false := by
        cases hb : (row j).testBit (L * u.val + (2 * r - 2))
        · rfl
        · exfalso
          obtain ⟨v, hvk, hvp⟩ := (hrow_bit j _).mp hb
          have huv : u = v := by
            apply Fin.ext
            have : L * v.val = L * u.val := by omega
            exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm
          subst huv
          exact hkeep hvk
      simp [hkeep, htb]
  have haAt_ne : ∀ u : Fin M, col (aAt u) ≠ 0 := by
    intro u hzero
    by_cases hG : G (eAt u).1 (eAt u).2 = true
    · let j₀ : Fin m := ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩
      have h1 := congr_fun hzero j₀
      rw [hcol_aAt] at h1
      simp [hG, j₀] at h1
    · let j₀ : Fin m := ⟨n + 2 * u.val, by have := u.isLt; omega⟩
      have h1 := congr_fun hzero j₀
      rw [hcol_aAt] at h1
      simp [hG, j₀] at h1
  have hactive_eq : active = Finset.univ.image aAt := by
    ext a
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hne
      rcases a with ⟨b_col, x⟩
      cases b_col
      · have hex : ∃ j : Fin m, col (false, x) j ≠ 0 := by
          by_contra h0; push_neg at h0; exact hne (funext h0)
        obtain ⟨j, hj⟩ := hex
        dsimp only [col] at hj
        simp only [Bool.not_false, Bool.true_and, delay, ↓reduceIte] at hj
        have htb : (row j).testBit ((x.val + (2 * r - 2)) % k) = true := by
          cases hb : (row j).testBit ((x.val + (2 * r - 2)) % k)
          · simp [hb] at hj
          · rfl
        obtain ⟨u, _, hpu⟩ := (hrow_bit j _).mp htb
        have hx_lt : x.val + (2 * r - 2) < k := by
          by_contra hge
          have hge' : k ≤ x.val + (2 * r - 2) := by omega
          have hlt2 : x.val + (2 * r - 2) < 2 * k := by
            have := x.isLt
            have : 2 * r - 2 < L := by dsimp only [L]; omega
            have : L ≤ k := Nat.le_mul_of_pos_right L (by omega)
            omega
          have hmod : (x.val + (2 * r - 2)) % k = x.val + (2 * r - 2) - k := by
            rw [Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)]
          rw [hmod] at hpu
          have : 2 * r - 2 < k := by
            have : 2 * r - 2 < L := by dsimp only [L]; omega
            have : L ≤ k := Nat.le_mul_of_pos_right L (by omega)
            omega
          have := x.isLt
          omega
        rw [Nat.mod_eq_of_lt hx_lt] at hpu
        refine ⟨u, Prod.ext rfl (Fin.ext ?_)⟩
        dsimp only [aAt]; omega
      · exact absurd (hcol_true x) hne
    · rintro ⟨u, _, rfl⟩
      exact haAt_ne u
  have hscope_aAt : ∀ u : Fin M, scope (aAt u) = block u.val := by
    intro u
    ext i
    simp only [scope, block, Finset.mem_filter, Finset.mem_univ, true_and]
    have hreach : reach (aAt u).1 + 1 = L := by
      dsimp only [aAt, reach, L]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    constructor
    · rintro ⟨d, hd⟩
      have hd_lt : d.val < L := by rw [← hreach]; exact d.isLt
      have hsum_lt : L * u.val + d.val < k := by
        have h1 : L * u.val + L = L * (u.val + 1) := by ring
        have h2 : L * (u.val + 1) ≤ L * M := Nat.mul_le_mul_left L u.isLt
        omega
      dsimp only [aAt] at hd
      rw [Nat.mod_eq_of_lt hsum_lt] at hd
      have h1 : L * (u.val + 1) = L * u.val + L := by ring
      omega
    · rintro ⟨h1, h2⟩
      have hd_lt : i.val - L * u.val < reach (aAt u).1 + 1 := by
        rw [hreach]
        have : L * (u.val + 1) = L * u.val + L := by ring
        omega
      refine ⟨⟨i.val - L * u.val, hd_lt⟩, ?_⟩
      dsimp only [aAt]
      have hsum_lt : L * u.val + (i.val - L * u.val) < k := by omega
      rw [Nat.mod_eq_of_lt hsum_lt]
      omega
  have hblock_card : ∀ u : Fin M, (block u.val).card = L := by
    intro u
    rw [← Fintype.card_fin L, ← Finset.card_univ]
    refine Finset.card_bij (fun i hi => ⟨i.val - L * u.val, by
      simp only [block, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have : L * (u.val + 1) = L * u.val + L := by ring
      omega⟩) ?_ ?_ ?_
    · intro i _; exact Finset.mem_univ _
    · intro i₁ hi₁ i₂ hi₂ heq
      have h1 := (Finset.mem_filter.mp hi₁).2
      have h2 := (Finset.mem_filter.mp hi₂).2
      have hv : i₁.val - L * u.val = i₂.val - L * u.val := congrArg Fin.val heq
      ext; omega
    · intro d _
      have hd_lt : L * u.val + d.val < k := by
        have h1 : L * u.val + L = L * (u.val + 1) := by ring
        have h2 : L * (u.val + 1) ≤ L * M := Nat.mul_le_mul_left L u.isLt
        have := d.isLt
        omega
      refine ⟨⟨L * u.val + d.val, hd_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have h1 : L * u.val + L = L * (u.val + 1) := by ring
        have := d.isLt
        dsimp only
        omega
      · ext; simp
  have hblock_disj : Pairwise (fun u v : Fin M => Disjoint (block u.val) (block v.val)) := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro i hu hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : L * (u.val + 1) ≤ L * v.val := Nat.mul_le_mul_left L hlt
      omega
    · have : L * (v.val + 1) ≤ L * u.val := Nat.mul_le_mul_left L hgt
      omega
  have hblock_univ : (Finset.univ : Finset (Fin M)).biUnion (fun u => block u.val) = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, block, Finset.mem_filter]
    constructor
    · intro _; trivial
    · intro _
      have hdiv : i.val / L < M := Nat.div_lt_of_lt_mul i.isLt
      refine ⟨⟨i.val / L, hdiv⟩, ?_⟩
      have h1 : L * (i.val / L) + i.val % L = i.val := Nat.div_add_mod i.val L
      have h2 : i.val % L < L := Nat.mod_lt i.val (by omega)
      have h3 : L * (i.val / L + 1) = L * (i.val / L) + L := by ring
      have h4 : (⟨i.val / L, hdiv⟩ : Fin M).val = i.val / L := rfl
      rw [h4]
      omega

  have hgood_iff : ∀ P : Finset I, good P ↔ ∀ u : Fin M, (block u.val \ P).card ≤ 2 := by
    intro P
    dsimp only [good]
    rw [hactive_eq]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    refine forall_congr' (fun u => ?_)
    dsimp only [left]
    rw [hscope_aAt u]
  let Dset : Finset I → Finset (Fin M) := fun P => Finset.univ.filter (fun u => (block u.val \ P).card = 2)
  let Zset : Finset I → Finset (Fin M) := fun P => Finset.univ.filter (fun u => (block u.val \ P).card = 0)
  have hDZ_disj : ∀ P, Disjoint (Dset P) (Zset P) := by
    intro P
    rw [Finset.disjoint_left]
    intro u hD hZ
    have h1 := (Finset.mem_filter.mp hD).2
    have h2 := (Finset.mem_filter.mp hZ).2
    omega
  have hP_card : ∀ P : Finset I, good P →
      P.card + (Dset P).card = (L - 1) * M + (Zset P).card := by
    intro P hP
    have hP' := (hgood_iff P).mp hP
    have h_sum : (Finset.univ \ P).card = ∑ u : Fin M, (block u.val \ P).card := by
      have huniv_sdiff : Finset.univ \ P = (Finset.univ : Finset (Fin M)).biUnion (fun u => block u.val \ P) := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion, true_and]
        constructor
        · intro hi
          have him : i ∈ Finset.univ := Finset.mem_univ i
          rw [← hblock_univ, Finset.mem_biUnion] at him
          obtain ⟨u, _, hu⟩ := him
          exact ⟨u, hu, hi⟩
        · rintro ⟨u, hu, hi⟩; exact hi
      rw [huniv_sdiff, Finset.card_biUnion]
      intro u _ v _ huv
      exact (hblock_disj huv).mono Finset.sdiff_subset Finset.sdiff_subset
    have h_term : ∀ u : Fin M, (block u.val \ P).card + (if u ∈ Zset P then 1 else 0) =
        1 + (if u ∈ Dset P then 1 else 0) := by
      intro u
      have hle := hP' u
      dsimp only [Dset, Zset]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> omega
    have h_sum2 : (Finset.univ \ P).card + (Zset P).card = M + (Dset P).card := by
      rw [h_sum]
      have hZcard : (Zset P).card = ∑ u : Fin M, if u ∈ Zset P then 1 else 0 := by
        simp [Finset.card_filter]
      have hDcard : (Dset P).card = ∑ u : Fin M, if u ∈ Dset P then 1 else 0 := by
        simp [Finset.card_filter]
      rw [hZcard, hDcard, ← Finset.sum_add_distrib]
      have hMsum : M = ∑ _u : Fin M, 1 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      conv_rhs => arg 1; rw [hMsum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro u _; exact h_term u
    have hcompl : P.card + (Finset.univ \ P).card = k := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right, Finset.union_sdiff_of_subset (Finset.subset_univ P),
        Finset.card_univ, Fintype.card_fin]
    have hk_eq : k = L * M := rfl
    have hLM : L * M = (L - 1) * M + M := by
      have : L = (L - 1) + 1 := by omega
      calc L * M = ((L - 1) + 1) * M := by rw [← this]
        _ = (L - 1) * M + M := by ring
    omega
  have hpairs_eq : ∀ P : Finset I, pairs P = (Dset P).image (fun u => block u.val \ P) := by
    intro P
    ext e
    simp only [pairs, Finset.mem_filter, Finset.mem_image, Dset, Finset.mem_univ, true_and]
    rw [hactive_eq]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a, ⟨u, rfl⟩, rfl⟩, he2⟩
      dsimp only [left] at he2 ⊢
      rw [hscope_aAt u] at he2 ⊢
      exact ⟨u, he2, rfl⟩
    · rintro ⟨u, hu2, rfl⟩
      refine ⟨⟨aAt u, ⟨u, rfl⟩, ?_⟩, ?_⟩
      · dsimp only [left]; rw [hscope_aAt u]
      · exact hu2
  have hworst_eq : ∀ P : Finset I, worst P = rank ((Dset P).image (fun u => col (aAt u))) := by
    intro P
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro w _
      dsimp only [rank]
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      rintro y hy
      simp only [Finset.mem_coe, Finset.mem_image] at hy
      obtain ⟨e, he, rfl⟩ := hy
      rw [hpairs_eq] at he
      obtain ⟨u, huD, rfl⟩ := Finset.mem_image.mp he
      have hu_card : (block u.val \ P).card = 2 := (Finset.mem_filter.mp huD).2
      have hfilt : active.filter (fun a => left P a = block u.val \ P) = {aAt u} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton, hactive_eq, Finset.mem_image,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨v, rfl⟩, hv⟩
          dsimp only [left] at hv
          rw [hscope_aAt v] at hv
          have hne_empty : (block v.val \ P).Nonempty := by
            rw [← Finset.card_pos, hv, hu_card]; omega
          obtain ⟨x, hx⟩ := hne_empty
          have hxv : x ∈ block v.val := (Finset.mem_sdiff.mp hx).1
          have hxu : x ∈ block u.val := (Finset.mem_sdiff.mp (hv ▸ hx)).1
          have huv : v = u := by
            by_contra hne
            exact Finset.disjoint_left.mp (hblock_disj hne) hxv hxu
          subst huv; rfl
        · rintro rfl
          exact ⟨⟨u, rfl⟩, by dsimp only [left]; rw [hscope_aAt u]⟩
      rw [hfilt, Finset.sum_singleton]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨u, huD, rfl⟩)))
    · have hle := Finset.le_sup (f := fun w : A → F =>
        rank ((pairs P).image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)))
        (Finset.mem_univ (fun _ => (1 : F)))
      refine le_trans ?_ hle
      have himg : (Dset P).image (fun u => col (aAt u)) =
          (pairs P).image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), (1 : F) • col a) := by
        ext y
        simp only [Finset.mem_image, hpairs_eq]
        constructor
        · rintro ⟨u, huD, rfl⟩
          refine ⟨block u.val \ P, ⟨u, huD, rfl⟩, ?_⟩
          have hu_card : (block u.val \ P).card = 2 := (Finset.mem_filter.mp huD).2
          have hfilt : active.filter (fun a => left P a = block u.val \ P) = {aAt u} := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_singleton, hactive_eq, Finset.mem_image,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨⟨v, rfl⟩, hv⟩
              dsimp only [left] at hv
              rw [hscope_aAt v] at hv
              have hne_empty : (block v.val \ P).Nonempty := by
                rw [← Finset.card_pos, hv, hu_card]; omega
              obtain ⟨x, hx⟩ := hne_empty
              have hxv : x ∈ block v.val := (Finset.mem_sdiff.mp hx).1
              have hxu : x ∈ block u.val := (Finset.mem_sdiff.mp (hv ▸ hx)).1
              by_contra hne
              have : v ≠ u := fun h => hne (congrArg aAt h)
              exact Finset.disjoint_left.mp (hblock_disj this) hxv hxu
            · rintro rfl; exact ⟨⟨u, rfl⟩, by dsimp only [left]; rw [hscope_aAt u]⟩
          rw [hfilt, Finset.sum_singleton, one_smul]
        · rintro ⟨e, he, rfl⟩
          obtain ⟨u, huD, rfl⟩ := he
          refine ⟨u, huD, ?_⟩
          have hu_card : (block u.val \ P).card = 2 := (Finset.mem_filter.mp huD).2
          have hfilt : active.filter (fun a => left P a = block u.val \ P) = {aAt u} := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_singleton, hactive_eq, Finset.mem_image,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨⟨v, rfl⟩, hv⟩
              dsimp only [left] at hv
              rw [hscope_aAt v] at hv
              have hne_empty : (block v.val \ P).Nonempty := by
                rw [← Finset.card_pos, hv, hu_card]; omega
              obtain ⟨x, hx⟩ := hne_empty
              have hxv : x ∈ block v.val := (Finset.mem_sdiff.mp hx).1
              have hxu : x ∈ block u.val := (Finset.mem_sdiff.mp (hv ▸ hx)).1
              by_contra hne
              have : v ≠ u := fun h => hne (congrArg aAt h)
              exact Finset.disjoint_left.mp (hblock_disj this) hxv hxu
            · rintro rfl; exact ⟨⟨u, rfl⟩, by dsimp only [left]; rw [hscope_aAt u]⟩
          rw [hfilt, Finset.sum_singleton, one_smul]
      rw [himg]

  let actualEdges : Finset (Fin n) → Finset (Fin M) := fun U =>
    Finset.univ.filter (fun u => (eAt u).1 ∈ U ∧ (eAt u).2 ∈ U ∧ G (eAt u).1 (eAt u).2 = true)
  have hedgesIn_eq : ∀ U : Finset (Fin n), edgesIn U = (actualEdges U).card := by
    intro U
    dsimp only [edgesIn, actualEdges]
    symm
    refine Finset.card_bij (fun u _ => eAt u) ?_ ?_ ?_
    · intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem u.isLt), hu'.2⟩
    · intro u₁ _ u₂ _ heq
      exact Fin.ext ((List.Nodup.getElem_inj_iff (esList_nodup n)).mp heq)
    · intro e he
      have he' := Finset.mem_filter.mp he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp he'.1)
      exact ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'.2⟩, rfl⟩
  have hdecode_eq : ∀ P : Finset I,
      decode P = ((Dset P).filter (fun u => G (eAt u).1 (eAt u).2 = true)).biUnion
        (fun u => ({(eAt u).1, (eAt u).2} : Finset (Fin n))) := by
    intro P
    ext x
    simp only [decode, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Dset, items, List.mem_toFinset]
    constructor
    · rintro ⟨z, ⟨hz, hG, hcard⟩, hx⟩
      rw [mem_zipIdx_iff] at hz
      obtain ⟨hu, hzf⟩ := hz
      refine ⟨⟨z.2, hu⟩, ⟨hcard, ?_⟩, ?_⟩
      · simpa [eAt, hzf] using hG
      · simpa [eAt, hzf] using hx
    · rintro ⟨u, ⟨hcard, hG⟩, hx⟩
      refine ⟨(eAt u, u.val), ⟨?_, hG, hcard⟩, hx⟩
      rw [mem_zipIdx_iff]
      exact ⟨u.isLt, rfl⟩

  have hcol_single : ∀ u : Fin M,
      (G (eAt u).1 (eAt u).2 = true →
        col (aAt u) = Pi.single ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ (1 : F) +
                      Pi.single ⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ (1 : F)) ∧
      (G (eAt u).1 (eAt u).2 = false →
        col (aAt u) = Pi.single ⟨n + 2 * u.val, by have := u.isLt; omega⟩ (1 : F) +
                      Pi.single ⟨n + 2 * u.val + 1, by have := u.isLt; omega⟩ (1 : F)) := by
    intro u
    have hlt := heAt_lt u
    constructor
    · intro hG
      ext j
      rw [hcol_aAt, Pi.add_apply]
      simp only [hG, ↓reduceIte]
      by_cases h1 : j.val = (eAt u).1.val
      · have h2 : j.val ≠ (eAt u).2.val := by omega
        have hj1 : j = ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ := Fin.ext h1
        have hj2 : j ≠ ⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ := fun h => h2 (congrArg Fin.val h)
        rw [if_pos (Or.inl h1), Pi.single_eq_of_ne hj2, hj1, Pi.single_eq_same, add_zero]
      · by_cases h2 : j.val = (eAt u).2.val
        · have hj1 : j ≠ ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ := fun h => h1 (congrArg Fin.val h)
          have hj2 : j = ⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ := Fin.ext h2
          rw [if_pos (Or.inr h2), Pi.single_eq_of_ne hj1, hj2, Pi.single_eq_same, zero_add]
        · have hj1 : j ≠ ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ := fun h => h1 (congrArg Fin.val h)
          have hj2 : j ≠ ⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ := fun h => h2 (congrArg Fin.val h)
          rw [if_neg (not_or.mpr ⟨h1, h2⟩), Pi.single_eq_of_ne hj1, Pi.single_eq_of_ne hj2, add_zero]
    · intro hG
      ext j
      rw [hcol_aAt, Pi.add_apply]
      simp only [hG, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : j.val = n + 2 * u.val
      · have h2 : j.val ≠ n + 2 * u.val + 1 := by omega
        have hj1 : j = ⟨n + 2 * u.val, by have := u.isLt; omega⟩ := Fin.ext h1
        have hj2 : j ≠ ⟨n + 2 * u.val + 1, by have := u.isLt; omega⟩ := fun h => h2 (congrArg Fin.val h)
        rw [if_pos (Or.inl h1), Pi.single_eq_of_ne hj2, hj1, Pi.single_eq_same, add_zero]
      · by_cases h2 : j.val = n + 2 * u.val + 1
        · have hj1 : j ≠ ⟨n + 2 * u.val, by have := u.isLt; omega⟩ := fun h => h1 (congrArg Fin.val h)
          have hj2 : j = ⟨n + 2 * u.val + 1, by have := u.isLt; omega⟩ := Fin.ext h2
          rw [if_pos (Or.inr h2), Pi.single_eq_of_ne hj1, hj2, Pi.single_eq_same, zero_add]
        · have hj1 : j ≠ ⟨n + 2 * u.val, by have := u.isLt; omega⟩ := fun h => h1 (congrArg Fin.val h)
          have hj2 : j ≠ ⟨n + 2 * u.val + 1, by have := u.isLt; omega⟩ := fun h => h2 (congrArg Fin.val h)
          rw [if_neg (not_or.mpr ⟨h1, h2⟩), Pi.single_eq_of_ne hj1, Pi.single_eq_of_ne hj2, add_zero]
  have hworks_forward : ∀ P : Finset I, works P →
      (decode P).card = t ∧
      Dset P ⊆ actualEdges (decode P) ∧
      T - (Dset P).card + (Zset P).card ≤ δ := by
    intro P ⟨hgood, hworst_le, hcard_le⟩
    let DG := (Dset P).filter (fun u => G (eAt u).1 (eAt u).2 = true)
    let Dpriv := (Dset P).filter (fun u => G (eAt u).1 (eAt u).2 = false)
    have hD_split : (Dset P).card = DG.card + Dpriv.card := by
      have := Finset.card_filter_add_card_filter_not (s := Dset P) (p := fun u => G (eAt u).1 (eAt u).2 = true)
      simpa [DG, Dpriv] using this.symm
    let U := decode P
    have hU_eq : U = DG.biUnion (fun u => ({(eAt u).1, (eAt u).2} : Finset (Fin n))) :=
      hdecode_eq P
    let adj : Fin n → Fin n → Prop := fun x y =>
      ∃ u ∈ DG, (eAt u = (x, y) ∨ eAt u = (y, x))
    let Eqv : Fin n → Fin n → Prop := Relation.ReflTransGen adj
    have hEqv_symm : Symmetric Eqv := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single ?_) ih
        rcases hbc with ⟨u, hu, h1 | h2⟩
        · exact ⟨u, hu, Or.inr h1⟩
        · exact ⟨u, hu, Or.inl h2⟩
    let comp : Fin n → Finset (Fin n) := fun x => U.filter (fun y => Eqv x y)
    let 𝒞 : Finset (Finset (Fin n)) := U.image comp
    have h𝒞_ge2 : ∀ C ∈ 𝒞, 2 ≤ C.card := by
      intro C hC
      obtain ⟨x, hxU, rfl⟩ := Finset.mem_image.mp hC
      rw [hU_eq, Finset.mem_biUnion] at hxU
      obtain ⟨u, huDG, hxu⟩ := hxU
      have hlt := heAt_lt u
      have hx1 : (eAt u).1 ∈ comp x := by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [hU_eq]; exact Finset.mem_biUnion.mpr ⟨u, huDG, Finset.mem_insert_self _ _⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hxu
          rcases hxu with rfl | rfl
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.single ⟨u, huDG, Or.inr rfl⟩
      have hx2 : (eAt u).2 ∈ comp x := by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [hU_eq]; exact Finset.mem_biUnion.mpr ⟨u, huDG, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hxu
          rcases hxu with rfl | rfl
          · exact Relation.ReflTransGen.single ⟨u, huDG, Or.inl rfl⟩
          · exact Relation.ReflTransGen.refl
      exact Finset.one_lt_card.mpr ⟨(eAt u).1, hx1, (eAt u).2, hx2, hlt.ne⟩
    have hcomp_eq : ∀ x y : Fin n, x ∈ U → y ∈ U → (Eqv x y ↔ comp x = comp y) := by
      intro x y hx hy
      constructor
      · intro hxy
        ext z
        simp only [comp, Finset.mem_filter]
        constructor
        · rintro ⟨hz, hxz⟩; exact ⟨hz, Relation.ReflTransGen.trans (hEqv_symm hxy) hxz⟩
        · rintro ⟨hz, hyz⟩; exact ⟨hz, Relation.ReflTransGen.trans hxy hyz⟩
      · intro heq
        have hy_mem : y ∈ comp y := Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩
        rw [← heq] at hy_mem
        exact (Finset.mem_filter.mp hy_mem).2
    have h𝒞_part : ∀ C₁ ∈ 𝒞, ∀ C₂ ∈ 𝒞, C₁ ≠ C₂ → Disjoint C₁ C₂ := by
      intro C₁ hC₁ C₂ hC₂ hne
      obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hC₁
      obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hC₂
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have hz1' := (Finset.mem_filter.mp hz1).2
      have hz2' := (Finset.mem_filter.mp hz2).2
      have h12 : Eqv x₁ x₂ := Relation.ReflTransGen.trans hz1' (hEqv_symm hz2')
      exact hne ((hcomp_eq x₁ x₂ hx₁ hx₂).mp h12)
    have h𝒞_union : 𝒞.biUnion id = U := by
      ext z
      simp only [Finset.mem_biUnion, id_eq]
      constructor
      · rintro ⟨C, hC, hz⟩
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hC
        exact (Finset.mem_filter.mp hz).1
      · intro hz; exact ⟨comp z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.mem_filter.mpr ⟨hz, Relation.ReflTransGen.refl⟩⟩
    have hU_card_sum : U.card = ∑ C ∈ 𝒞, C.card := by
      conv_lhs => rw [← h𝒞_union]
      exact Finset.card_biUnion (fun C₁ h₁ C₂ h₂ hne => h𝒞_part C₁ h₁ C₂ h₂ hne)
    let root : Finset (Fin n) → Fin n := fun C =>
      if h : C.Nonempty then h.choose else ⟨0, by omega⟩
    have hroot_mem : ∀ C ∈ 𝒞, root C ∈ C := by
      intro C hC
      have hne : C.Nonempty := Finset.card_pos.mp (by have := h𝒞_ge2 C hC; omega)
      dsimp only [root]
      rw [dif_pos hne]
      exact hne.choose_spec
    let nonRoots : Finset (Fin n) := U.filter (fun x => x ≠ root (comp x))
    have hnonRoots_card : nonRoots.card = ∑ C ∈ 𝒞, (C.card - 1) := by
      have hunion : nonRoots = 𝒞.biUnion (fun C => C.erase (root C)) := by
        ext x
        simp only [nonRoots, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
        constructor
        · rintro ⟨hxU, hxne⟩
          refine ⟨comp x, Finset.mem_image.mpr ⟨x, hxU, rfl⟩, hxne, Finset.mem_filter.mpr ⟨hxU, Relation.ReflTransGen.refl⟩⟩
        · rintro ⟨C, hC, hxne, hxC⟩
          obtain ⟨y, hyU, rfl⟩ := Finset.mem_image.mp hC
          have hxU := (Finset.mem_filter.mp hxC).1
          have hyx : Eqv y x := (Finset.mem_filter.mp hxC).2
          have hce : comp y = comp x := (hcomp_eq y x hyU hxU).mp hyx
          exact ⟨hxU, hce ▸ hxne⟩
      rw [hunion, Finset.card_biUnion]
      · refine Finset.sum_congr rfl ?_
        intro C hC
        exact Finset.card_erase_of_mem (hroot_mem C hC)
      · intro C₁ h₁ C₂ h₂ hne
        exact (h𝒞_part C₁ h₁ C₂ h₂ hne).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    let Wspan := Submodule.span F (((Dset P).image (fun u => col (aAt u))) : Set Y)
    have h_path_in_span : ∀ x y : Fin n, Eqv x y →
        Pi.single ⟨x.val, by have := x.isLt; omega⟩ (1 : F) +
        Pi.single ⟨y.val, by have := y.isLt; omega⟩ (1 : F) ∈ Wspan := by
      intro x y hxy
      induction hxy with
      | refl =>
        have hsum : (Pi.single ⟨x.val, by have := x.isLt; omega⟩ (1 : F) : Y) +
            (Pi.single ⟨x.val, by have := x.isLt; omega⟩ (1 : F) : Y) = (0 : Y) := by
          ext j
          simp only [Pi.add_apply, Pi.single_apply]
          split_ifs <;> (try simp) <;> try exact zmod2_one_add_one
        rw [hsum]
        exact Wspan.zero_mem
      | @tail b c _ hbc ih =>
        have hstep : (Pi.single ⟨b.val, by have := b.isLt; omega⟩ (1 : F) : Y) +
            (Pi.single ⟨c.val, by have := c.isLt; omega⟩ (1 : F) : Y) ∈ Wspan := by
          rcases hbc with ⟨u, huDG, he⟩
          have huD : u ∈ Dset P := (Finset.mem_filter.mp huDG).1
          have hG : G (eAt u).1 (eAt u).2 = true := (Finset.mem_filter.mp huDG).2
          have hcol_mem : col (aAt u) ∈ Wspan :=
            Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨u, huD, rfl⟩))
          have hcol_u := (hcol_single u).1 hG
          rcases he with he | he
          · have h1 : (eAt u).1 = b := congrArg Prod.fst he
            have h2 : (eAt u).2 = c := congrArg Prod.snd he
            rw [hcol_u] at hcol_mem
            simpa [h1, h2] using hcol_mem
          · have h1 : (eAt u).1 = c := congrArg Prod.fst he
            have h2 : (eAt u).2 = b := congrArg Prod.snd he
            rw [hcol_u] at hcol_mem
            rw [add_comm]
            simpa [h1, h2] using hcol_mem
        have htot := Wspan.add_mem ih hstep
        have hcancel : ((Pi.single ⟨x.val, by have := x.isLt; omega⟩ (1 : F) : Y) +
              (Pi.single ⟨b.val, by have := b.isLt; omega⟩ (1 : F) : Y)) +
            ((Pi.single ⟨b.val, by have := b.isLt; omega⟩ (1 : F) : Y) +
              (Pi.single ⟨c.val, by have := c.isLt; omega⟩ (1 : F) : Y)) =
            (Pi.single ⟨x.val, by have := x.isLt; omega⟩ (1 : F) : Y) +
              (Pi.single ⟨c.val, by have := c.isLt; omega⟩ (1 : F) : Y) := by
          ext j
          simp only [Pi.add_apply, Pi.single_apply]
          split_ifs <;> (try simp) <;> try exact zmod2_one_add_one
        rwa [hcancel] at htot
    let idxType := nonRoots ⊕ Dpriv
    let vec : idxType → Y := Sum.elim
      (fun x => Pi.single ⟨(root (comp x.1)).val, by have := (root (comp x.1)).isLt; omega⟩ (1 : F) +
                Pi.single ⟨x.1.val, by have := x.1.isLt; omega⟩ (1 : F))
      (fun u => col (aAt u.1))
    have hvec_mem : ∀ i : idxType, vec i ∈ Wspan := by
      rintro (x | u)
      · have hxU : x.1 ∈ U := (Finset.mem_filter.mp x.2).1
        have hcompC : comp x.1 ∈ 𝒞 := Finset.mem_image.mpr ⟨x.1, hxU, rfl⟩
        have hr_mem : root (comp x.1) ∈ comp x.1 := hroot_mem _ hcompC
        exact h_path_in_span (root (comp x.1)) x.1 (hEqv_symm (Finset.mem_filter.mp hr_mem).2)
      · have huD : u.1 ∈ Dset P := (Finset.mem_filter.mp u.2).1
        exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨u.1, huD, rfl⟩))
    have hvec_indep : LinearIndependent F vec := by
      rw [Fintype.linearIndependent_iff]
      intro α hsum i
      rcases i with ⟨x, hx⟩ | ⟨u, hu⟩
      · have hxU : x ∈ U := (Finset.mem_filter.mp hx).1
        have hxne : x ≠ root (comp x) := (Finset.mem_filter.mp hx).2
        let j₀ : Fin m := ⟨x.val, by have := x.isLt; omega⟩
        have hj₀ := congr_fun hsum j₀
        rw [Finset.sum_apply] at hj₀
        change (∑ i', (α i' • vec i') j₀) = 0 at hj₀
        have hsingle : ∀ i' : idxType, (α i' • vec i') j₀ =
            if i' = Sum.inl ⟨x, hx⟩ then α (Sum.inl ⟨x, hx⟩) else 0 := by
          rintro (⟨y, hy⟩ | ⟨v, hv⟩)
          · have hyU : y ∈ U := (Finset.mem_filter.mp hy).1
            have hyne : y ≠ root (comp y) := (Finset.mem_filter.mp hy).2
            have hr_ne : root (comp y) ≠ x := by
              intro heq
              have hr_mem : root (comp y) ∈ comp y :=
                hroot_mem _ (Finset.mem_image.mpr ⟨y, hyU, rfl⟩)
              have hx_mem : x ∈ comp y := heq ▸ hr_mem
              have hyx : Eqv y x := (Finset.mem_filter.mp hx_mem).2
              have hcy : comp y = comp x := (hcomp_eq y x hyU hxU).mp hyx
              rw [hcy] at heq
              exact hxne heq.symm
            by_cases hxy : y = x
            · subst hxy
              have hval : (vec (Sum.inl ⟨y, hy⟩)) j₀ = 1 := by
                dsimp only [vec, Sum.elim_inl]
                rw [Pi.add_apply, Pi.single_apply, Pi.single_apply]
                have h1 : j₀ ≠ ⟨(root (comp y)).val, by have := (root (comp y)).isLt; omega⟩ :=
                  fun h => hr_ne (Fin.ext (congrArg Fin.val h).symm)
                split_ifs <;> simp_all [j₀, Fin.ext_iff]
              change α (Sum.inl ⟨y, hy⟩) * (vec (Sum.inl ⟨y, hy⟩)) j₀ = _
              rw [hval, mul_one, if_pos rfl]
            · have hval : (vec (Sum.inl ⟨y, hy⟩)) j₀ = 0 := by
                dsimp only [vec, Sum.elim_inl]
                rw [Pi.add_apply, Pi.single_apply, Pi.single_apply]
                have h1 : j₀ ≠ ⟨(root (comp y)).val, by have := (root (comp y)).isLt; omega⟩ :=
                  fun h => hr_ne (Fin.ext (congrArg Fin.val h).symm)
                have h2 : j₀ ≠ ⟨y.val, by have := y.isLt; omega⟩ :=
                  fun h => hxy (Fin.ext (congrArg Fin.val h).symm)
                simp [h1, h2]
              have hne_i : (Sum.inl ⟨y, hy⟩ : idxType) ≠ Sum.inl ⟨x, hx⟩ := by
                intro h; exact hxy (congrArg Subtype.val (Sum.inl.inj h))
              change α (Sum.inl ⟨y, hy⟩) * (vec (Sum.inl ⟨y, hy⟩)) j₀ = _
              rw [hval, mul_zero, if_neg hne_i]
          · have hvG : G (eAt v).1 (eAt v).2 = false := (Finset.mem_filter.mp hv).2
            have hcol_v := (hcol_single v).2 hvG
            have hval : (vec (Sum.inr ⟨v, hv⟩)) j₀ = 0 := by
              dsimp only [vec, Sum.elim_inr]
              rw [hcol_v, Pi.add_apply, Pi.single_apply, Pi.single_apply]
              have h1 : j₀ ≠ ⟨n + 2 * v.val, by have := v.isLt; omega⟩ := by
                intro h; have := congrArg Fin.val h; dsimp [j₀] at this; have := x.isLt; omega
              have h2 : j₀ ≠ ⟨n + 2 * v.val + 1, by have := v.isLt; omega⟩ := by
                intro h; have := congrArg Fin.val h; dsimp [j₀] at this; have := x.isLt; omega
              simp [h1, h2]
            change α (Sum.inr ⟨v, hv⟩) * (vec (Sum.inr ⟨v, hv⟩)) j₀ = _
            rw [hval, mul_zero]; rfl
        simp_rw [hsingle] at hj₀
        simpa using hj₀
      · have huG : G (eAt u).1 (eAt u).2 = false := (Finset.mem_filter.mp hu).2
        let j₀ : Fin m := ⟨n + 2 * u.val, by have := u.isLt; omega⟩
        have hj₀ := congr_fun hsum j₀
        rw [Finset.sum_apply] at hj₀
        change (∑ i', (α i' • vec i') j₀) = 0 at hj₀
        have hsingle : ∀ i' : idxType, (α i' • vec i') j₀ =
            if i' = Sum.inr ⟨u, hu⟩ then α (Sum.inr ⟨u, hu⟩) else 0 := by
          rintro (⟨y, hy⟩ | ⟨v, hv⟩)
          · have hval : (vec (Sum.inl ⟨y, hy⟩)) j₀ = 0 := by
              dsimp only [vec, Sum.elim_inl]
              rw [Pi.add_apply, Pi.single_apply, Pi.single_apply]
              have h1 : j₀ ≠ ⟨(root (comp y)).val, by have := (root (comp y)).isLt; omega⟩ := by
                intro h; have := congrArg Fin.val h; dsimp [j₀] at this; have := (root (comp y)).isLt; omega
              have h2 : j₀ ≠ ⟨y.val, by have := y.isLt; omega⟩ := by
                intro h; have := congrArg Fin.val h; dsimp [j₀] at this; have := y.isLt; omega
              simp [h1, h2]
            change α (Sum.inl ⟨y, hy⟩) * (vec (Sum.inl ⟨y, hy⟩)) j₀ = _
            rw [hval, mul_zero]; rfl
          · have hvG : G (eAt v).1 (eAt v).2 = false := (Finset.mem_filter.mp hv).2
            have hcol_v := (hcol_single v).2 hvG
            by_cases huv : v = u
            · subst huv
              have hval : (vec (Sum.inr ⟨v, hv⟩)) j₀ = 1 := by
                dsimp only [vec, Sum.elim_inr]
                rw [hcol_v, Pi.add_apply, Pi.single_apply, Pi.single_apply]
                have h2 : j₀ ≠ ⟨n + 2 * v.val + 1, by have := v.isLt; omega⟩ := by
                  intro h; have := congrArg Fin.val h; dsimp [j₀] at this; omega
                split_ifs <;> simp_all [j₀, Fin.ext_iff]
              change α (Sum.inr ⟨v, hv⟩) * (vec (Sum.inr ⟨v, hv⟩)) j₀ = _
              rw [hval, mul_one, if_pos rfl]
            · have hval : (vec (Sum.inr ⟨v, hv⟩)) j₀ = 0 := by
                dsimp only [vec, Sum.elim_inr]
                rw [hcol_v, Pi.add_apply, Pi.single_apply, Pi.single_apply]
                have hne_val : v.val ≠ u.val := fun h => huv (Fin.ext h)
                have h1 : j₀ ≠ ⟨n + 2 * v.val, by have := v.isLt; omega⟩ := by
                  intro h; have := congrArg Fin.val h; dsimp [j₀] at this; omega
                have h2 : j₀ ≠ ⟨n + 2 * v.val + 1, by have := v.isLt; omega⟩ := by
                  intro h; have := congrArg Fin.val h; dsimp [j₀] at this; omega
                simp [h1, h2]
              have hne_i : (Sum.inr ⟨v, hv⟩ : idxType) ≠ Sum.inr ⟨u, hu⟩ := by
                intro h; exact huv (congrArg Subtype.val (Sum.inr.inj h))
              change α (Sum.inr ⟨v, hv⟩) * (vec (Sum.inr ⟨v, hv⟩)) j₀ = _
              rw [hval, mul_zero, if_neg hne_i]
        simp_rw [hsingle] at hj₀
        simpa using hj₀
    have hvec_le_worst : nonRoots.card + Dpriv.card ≤ worst P := by
      have hcard_idx : Fintype.card idxType = nonRoots.card + Dpriv.card := by
        simp [idxType]
      rw [← hcard_idx, hworst_eq P]
      let f_lin : (idxType → F) →ₗ[F] Wspan :=
        { toFun := fun α => ⟨∑ i : idxType, α i • vec i, Wspan.sum_mem (fun i _ => Wspan.smul_mem _ (hvec_mem i))⟩
          map_add' := fun α₁ α₂ => by ext j; simp [add_smul, Finset.sum_add_distrib]
          map_smul' := fun c α => by ext j; simp [Finset.smul_sum, smul_smul] }
      have hf_inj : Function.Injective f_lin := by
        rw [injective_iff_map_eq_zero]
        intro α hα
        have h0 : ∑ i : idxType, α i • vec i = 0 := congrArg Subtype.val hα
        ext i
        exact (Fintype.linearIndependent_iff.mp hvec_indep) α h0 i
      have hle := LinearMap.finrank_le_finrank_of_injective hf_inj
      simpa [Module.finrank_pi] using hle
    have hjG_le : DG.card ≤ ∑ C ∈ 𝒞, C.card.choose 2 := by
      have hinj : DG.card ≤ (𝒞.biUnion (fun C => C.powersetCard 2)).card := by
        refine Finset.card_le_card_of_injOn (fun u => ({(eAt u).1, (eAt u).2} : Finset (Fin n))) ?_ ?_
        · intro u hu
          have hlt := heAt_lt u
          have hu_mem : (eAt u).1 ∈ U := by
            rw [hU_eq]; exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_insert_self _ _⟩
          refine Finset.mem_biUnion.mpr ⟨comp (eAt u).1, Finset.mem_image.mpr ⟨_, hu_mem, rfl⟩, ?_⟩
          rw [Finset.mem_powersetCard]
          refine ⟨?_, Finset.card_pair hlt.ne⟩
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hu_mem, Relation.ReflTransGen.refl⟩
          · refine Finset.mem_filter.mpr ⟨?_, Relation.ReflTransGen.single ⟨u, hu, Or.inl rfl⟩⟩
            rw [hU_eq]; exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        · intro u₁ hu₁ u₂ hu₂ heq
          dsimp only at heq
          have h1 := heAt_lt u₁
          have h2 := heAt_lt u₂
          have m1 : (eAt u₁).1 ∈ ({(eAt u₂).1, (eAt u₂).2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
          have m2 : (eAt u₁).2 ∈ ({(eAt u₂).1, (eAt u₂).2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have m3 : (eAt u₂).1 ∈ ({(eAt u₁).1, (eAt u₁).2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
          have m4 : (eAt u₂).2 ∈ ({(eAt u₁).1, (eAt u₁).2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
          have he_eq : eAt u₁ = eAt u₂ := by
            ext
            · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
            · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
          exact Fin.ext ((List.Nodup.getElem_inj_iff (esList_nodup n)).mp he_eq)
      exact hinj.trans (Finset.card_biUnion_le.trans (by simp_rw [Finset.card_powersetCard]; exact le_rfl))
    obtain ⟨halg1, halg2⟩ := choose_two_sum_eq 𝒞 h𝒞_ge2
    rw [← hnonRoots_card] at halg1 halg2
    set R := nonRoots.card
    have hR_le : R + Dpriv.card ≤ t - 1 := hvec_le_worst.trans hworst_le
    have hp_card := hP_card P hgood
    have hj_le_M : (Dset P).card ≤ M := by
      simpa using Finset.card_le_univ (Dset P)
    have hM_le_LM : M ≤ (L - 1) * M := by
      calc M = 1 * M := (one_mul M).symm
        _ ≤ (L - 1) * M := Nat.mul_le_mul_right M (by omega)
    have hT_le_M : (t - 1).choose 2 ≤ (L - 1) * M := by
      have : (t - 1).choose 2 ≤ t.choose 2 := choose_two_mono (by omega)
      omega
    have hineq : (t - 1).choose 2 + (Zset P).card + R ≤ DG.card + δ := by
      omega
    have hDG_le : DG.card ≤ R.choose 2 + R := by
      have : (R + 1).choose 2 = R.choose 2 + R := by
        cases R with
        | zero => simp
        | succ m => exact choose_two_add_sub (by omega)
      omega
    have hineq2 : (t - 1).choose 2 + (Zset P).card ≤ R.choose 2 + δ := by omega
    have hR_eq : R = t - 1 := by
      by_contra hne
      have hR_lt : R ≤ t - 2 := by omega
      have hch : R.choose 2 ≤ (t - 2).choose 2 := choose_two_mono hR_lt
      have hsplit_t : (t - 1).choose 2 = (t - 2).choose 2 + (t - 2) := by
        have : t - 1 = (t - 2) + 1 := by omega
        rw [this]
        exact choose_two_add_sub (by omega)
      omega
    have h𝒞_le1 : 𝒞.card ≤ 1 := by
      by_contra hge2
      have hge2' : 2 ≤ 𝒞.card := by omega
      have h2 := halg2 hge2'
      have hT_eq' : (t - 1 + 1).choose 2 = (t - 1).choose 2 + (t - 1) :=
        choose_two_add_sub (by omega)
      rw [hR_eq] at h2 hineq
      omega
    have h𝒞_eq1 : 𝒞.card = 1 := by
      have hpos : 0 < 𝒞.card := by
        by_contra h0
        have hce : 𝒞 = ∅ := Finset.card_eq_zero.mp (by omega)
        rw [hce, Finset.sum_empty] at hnonRoots_card
        omega
      omega
    have hU_card_t : U.card = t := by
      have h_sum_sub : ∀ (𝒞₀ : Finset (Finset (Fin n))), (∀ C ∈ 𝒞₀, 2 ≤ C.card) →
          ∑ C ∈ 𝒞₀, (C.card - 1) = (∑ C ∈ 𝒞₀, C.card) - 𝒞₀.card := by
        intro 𝒞₀
        induction 𝒞₀ using Finset.induction_on with
        | empty => intro _; simp
        | @insert C₀ 𝒞' hC₀ ih =>
          intro h𝒞₀
          have hC₀_ge := h𝒞₀ C₀ (Finset.mem_insert_self _ _)
          have h𝒞' : ∀ C ∈ 𝒞', 2 ≤ C.card := fun C hC => h𝒞₀ C (Finset.mem_insert_of_mem hC)
          have hsum_ge : 𝒞'.card ≤ ∑ C ∈ 𝒞', C.card := by
            calc 𝒞'.card = ∑ _C ∈ 𝒞', 1 := by simp
              _ ≤ ∑ C ∈ 𝒞', C.card := Finset.sum_le_sum (fun C hC => by have := h𝒞' C hC; omega)
          rw [Finset.sum_insert hC₀, Finset.sum_insert hC₀, Finset.card_insert_of_notMem hC₀, ih h𝒞']
          omega
      rw [hnonRoots_card, h_sum_sub 𝒞 h𝒞_ge2, ← hU_card_sum, h𝒞_eq1] at hR_eq
      omega
    have hDpriv_0 : Dpriv.card = 0 := by omega
    have hD_sub : Dset P ⊆ actualEdges U := by
      intro u huD
      have huDG : u ∈ DG := by
        have : Dpriv = ∅ := Finset.card_eq_zero.mp hDpriv_0
        by_cases hG : G (eAt u).1 (eAt u).2 = true
        · exact Finset.mem_filter.mpr ⟨huD, hG⟩
        · exfalso
          have hGb : G (eAt u).1 (eAt u).2 = false := Bool.eq_false_iff.mpr hG
          have : u ∈ Dpriv := Finset.mem_filter.mpr ⟨huD, hGb⟩
          rw [‹Dpriv = ∅›] at this
          simp at this
      have hG := (Finset.mem_filter.mp huDG).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, hG⟩
      · rw [hU_eq]; exact Finset.mem_biUnion.mpr ⟨u, huDG, Finset.mem_insert_self _ _⟩
      · rw [hU_eq]; exact Finset.mem_biUnion.mpr ⟨u, huDG, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    have hT_ineq : T - (Dset P).card + (Zset P).card ≤ δ := by
      have hT_eq : T = (t - 1).choose 2 + (t - 1) := by
        have : t = (t - 1) + 1 := by omega
        dsimp only [T]
        rw [this]
        exact choose_two_add_sub (by omega)
      have hD_eq_DG : (Dset P).card = DG.card := by omega
      have hDG_le_T : DG.card ≤ T := by
        calc DG.card ≤ (actualEdges U).card := Finset.card_le_card (by
              intro u hu
              have huD := (Finset.mem_filter.mp hu).1
              exact hD_sub huD)
          _ = edgesIn U := (hedgesIn_eq U).symm
          _ ≤ T := by
            dsimp only [edgesIn, T]
            rw [← hU_card_t]
            have hle : (es.toFinset.filter (fun e => e.1 ∈ U ∧ e.2 ∈ U ∧ G e.1 e.2 = true)).card ≤
                (U.powersetCard 2).card := by
              refine Finset.card_le_card_of_injOn (fun e => ({e.1, e.2} : Finset (Fin n))) ?_ ?_
              · intro e he
                have he' := Finset.mem_filter.mp he
                have hlt : e.1 < e.2 := mem_esList_iff.mp (List.mem_toFinset.mp he'.1)
                rw [Finset.mem_coe, Finset.mem_powersetCard]
                refine ⟨?_, Finset.card_pair hlt.ne⟩
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> tauto
              · intro e₁ he₁ e₂ he₂ heq
                dsimp only at heq
                have h1 : e₁.1 < e₁.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₁).1)
                have h2 : e₂.1 < e₂.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₂).1)
                have m1 : e₁.1 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
                have m2 : e₁.2 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
                have m3 : e₂.1 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
                have m4 : e₂.2 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
                simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
                ext
                · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
                · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
            rwa [Finset.card_powersetCard] at hle
      omega
    exact ⟨hU_card_t, hD_sub, hT_ineq⟩
  have hworks_backward : ∀ (U : Finset (Fin n)) (P : Finset I),
      U.card = t → (∀ u : Fin M, (block u.val \ P).card ≤ 2) →
      Dset P ⊆ actualEdges U → T - (Dset P).card + (Zset P).card ≤ δ →
      works P ∧ decode P = U := by
    intro U P hUt hP_good hD_sub hT_ineq
    have hgood : good P := (hgood_iff P).mpr hP_good
    obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
    let W_U : Submodule F Y :=
      { carrier := { v : Y | (∀ j : Fin m, (∀ x ∈ U, j.val ≠ x.val) → v j = 0) ∧
            ∑ x ∈ U, v ⟨x.val, by have := x.isLt; omega⟩ = 0 }
        zero_mem' := ⟨fun _ _ => rfl, by change ∑ x ∈ U, (0 : F) = 0; simp⟩, add_mem' := fun {v₁ v₂} hv₁ hv₂ => by
          refine ⟨fun j hj => ?_, ?_⟩
          · change v₁ j + v₂ j = 0; rw [hv₁.1 j hj, hv₂.1 j hj, add_zero]
          · change ∑ x ∈ U, (v₁ ⟨x.val, _⟩ + v₂ ⟨x.val, _⟩) = 0
            rw [Finset.sum_add_distrib, hv₁.2, hv₂.2, add_zero]
        smul_mem' := fun c {v} hv => by
          refine ⟨fun j hj => ?_, ?_⟩
          · change c * v j = 0; rw [hv.1 j hj, mul_zero]
          · change ∑ x ∈ U, c * v ⟨x.val, _⟩ = 0
            rw [← Finset.mul_sum, hv.2, mul_zero] }
    have hWU_rank : Module.finrank F W_U ≤ t - 1 := by
      let U' := U.erase u₀
      let res : W_U →ₗ[F] (U' → F) :=
        { toFun := fun v x => v.1 ⟨x.1.val, by have := x.1.isLt; omega⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hres_inj : Function.Injective res := by
        rw [injective_iff_map_eq_zero]
        intro v hv
        ext j
        by_cases hjU : ∃ x ∈ U, j.val = x.val
        · obtain ⟨x, hxU, hjx⟩ := hjU
          have hj_eq : j = ⟨x.val, by have := x.isLt; omega⟩ := Fin.ext hjx
          rw [hj_eq]
          by_cases hxu₀ : x = u₀
          · subst hxu₀
            have hsum := v.2.2
            rw [← Finset.add_sum_erase U _ hu₀] at hsum
            have hrest : ∑ y ∈ U.erase x, v.1 ⟨y.val, by have := y.isLt; omega⟩ = 0 := by
              refine Finset.sum_eq_zero ?_
              intro y hy
              exact congr_fun hv ⟨y, hy⟩
            rw [hrest, add_zero] at hsum
            exact hsum
          · exact congr_fun hv ⟨x, Finset.mem_erase.mpr ⟨hxu₀, hxU⟩⟩
        · push_neg at hjU
          exact v.2.1 j hjU
      have hle := LinearMap.finrank_le_finrank_of_injective hres_inj
      have hU'_card : U'.card = t - 1 := by
        rw [Finset.card_erase_of_mem hu₀, hUt]
      simpa [Module.finrank_pi, hU'_card] using hle
    have hworst_le : worst P ≤ t - 1 := by
      rw [hworst_eq P]
      dsimp only [rank]
      have hsub : Submodule.span F (((Dset P).image (fun u => col (aAt u))) : Set Y) ≤ W_U := by
        rw [Submodule.span_le]
        rintro v hv
        simp only [Finset.mem_coe, Finset.mem_image] at hv
        obtain ⟨u, huD, rfl⟩ := hv
        have huA := Finset.mem_filter.mp (hD_sub huD)
        have hx1 : (eAt u).1 ∈ U := huA.2.1
        have hx2 : (eAt u).2 ∈ U := huA.2.2.1
        have hG : G (eAt u).1 (eAt u).2 = true := huA.2.2.2
        have hcol_u := (hcol_single u).1 hG
        have hlt := heAt_lt u
        refine ⟨?_, ?_⟩
        · intro j hj
          rw [hcol_u, Pi.add_apply, Pi.single_apply, Pi.single_apply]
          have h1 : j ≠ ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ :=
            fun h => hj (eAt u).1 hx1 (congrArg Fin.val h)
          have h2 : j ≠ ⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ :=
            fun h => hj (eAt u).2 hx2 (congrArg Fin.val h)
          simp [h1, h2]
        · have hsum_s : ∑ x ∈ U, (col (aAt u)) ⟨x.val, by have := x.isLt; omega⟩ =
              ∑ x ∈ U, ((Pi.single (⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ : Fin m) (1 : F) : Y) ⟨x.val, by have := x.isLt; omega⟩ +
                        (Pi.single (⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ : Fin m) (1 : F) : Y) ⟨x.val, by have := x.isLt; omega⟩) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [hcol_u, Pi.add_apply]
          rw [hsum_s, Finset.sum_add_distrib]
          have hs1 : ∑ x ∈ U, (Pi.single (⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ : Fin m) (1 : F) : Y) ⟨x.val, by have := x.isLt; omega⟩ = 1 := by
            rw [Finset.sum_eq_single (eAt u).1]
            · simp
            · intro x _ hxne
              have : (⟨x.val, by have := x.isLt; omega⟩ : Fin m) ≠ ⟨(eAt u).1.val, by have := (eAt u).1.isLt; omega⟩ := by
                intro h; exact hxne (Fin.ext (congrArg (Fin.val : Fin m → ℕ) h))
              simp [this]
            · intro h; exact absurd hx1 h
          have hs2 : ∑ x ∈ U, (Pi.single (⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ : Fin m) (1 : F) : Y) ⟨x.val, by have := x.isLt; omega⟩ = 1 := by
            rw [Finset.sum_eq_single (eAt u).2]
            · simp
            · intro x _ hxne
              have : (⟨x.val, by have := x.isLt; omega⟩ : Fin m) ≠ ⟨(eAt u).2.val, by have := (eAt u).2.isLt; omega⟩ := by
                intro h; exact hxne (Fin.ext (congrArg (Fin.val : Fin m → ℕ) h))
              simp [this]
            · intro h; exact absurd hx2 h
          rw [hs1, hs2]
          exact zmod2_one_add_one
      exact (Submodule.finrank_mono hsub).trans hWU_rank
    have hT_eq : T = (t - 1).choose 2 + (t - 1) := by
      have : t = (t - 1) + 1 := by omega
      dsimp only [T]
      rw [this]
      exact choose_two_add_sub (by omega)
    have hp_card := hP_card P hgood
    have hD_le_T : (Dset P).card ≤ T := by
      calc (Dset P).card ≤ (actualEdges U).card := Finset.card_le_card hD_sub
        _ = edgesIn U := (hedgesIn_eq U).symm
        _ ≤ T := by
          dsimp only [edgesIn, T]
          rw [← hUt]
          have hle : (es.toFinset.filter (fun e => e.1 ∈ U ∧ e.2 ∈ U ∧ G e.1 e.2 = true)).card ≤
              (U.powersetCard 2).card := by
            refine Finset.card_le_card_of_injOn (fun e => ({e.1, e.2} : Finset (Fin n))) ?_ ?_
            · intro e he
              have he' := Finset.mem_filter.mp he
              have hlt : e.1 < e.2 := mem_esList_iff.mp (List.mem_toFinset.mp he'.1)
              rw [Finset.mem_coe, Finset.mem_powersetCard]
              refine ⟨?_, Finset.card_pair hlt.ne⟩
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> tauto
            · intro e₁ he₁ e₂ he₂ heq
              dsimp only at heq
              have h1 : e₁.1 < e₁.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₁).1)
              have h2 : e₂.1 < e₂.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₂).1)
              have m1 : e₁.1 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
              have m2 : e₁.2 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
              have m3 : e₂.1 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
              have m4 : e₂.2 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
              simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
              ext
              · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
              · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
          rwa [Finset.card_powersetCard] at hle
    have hcard_le : P.card + worst P ≤ b := by
      dsimp only [b]
      have h1 : (t - 1).choose 2 ≤ (L - 1) * M := by
        have : (t - 1).choose 2 ≤ T := choose_two_mono (by omega)
        have : 1 * M ≤ (L - 1) * M := Nat.mul_le_mul_right M (by omega)
        omega
      omega
    have hdecode_sub : decode P ⊆ U := by
      rw [hdecode_eq P]
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨u, hu, hxu⟩ := hx
      have huA := Finset.mem_filter.mp (hD_sub (Finset.mem_filter.mp hu).1)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxu
      rcases hxu with rfl | rfl
      · exact huA.2.1
      · exact huA.2.2.1
    have hdecode_eqU : decode P = U := by
      by_contra hne
      have hssub : decode P ⊂ U := ssubset_iff_subset_ne.mpr ⟨hdecode_sub, hne⟩
      obtain ⟨v, hvU, hvnot⟩ := Finset.exists_of_ssubset hssub
      have hD_le_t1 : (Dset P).card ≤ (t - 1).choose 2 := by
        have hle : (Dset P).card ≤ ((U.erase v).powersetCard 2).card := by
          refine Finset.card_le_card_of_injOn (fun u => ({(eAt u).1, (eAt u).2} : Finset (Fin n))) ?_ ?_
          · intro u huD
            have huA := Finset.mem_filter.mp (hD_sub huD)
            have hlt := heAt_lt u
            rw [Finset.mem_coe, Finset.mem_powersetCard]
            refine ⟨?_, Finset.card_pair hlt.ne⟩
            intro x hx
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hxv
              apply hvnot
              rw [hdecode_eq P, Finset.mem_biUnion]
              exact ⟨u, Finset.mem_filter.mpr ⟨huD, huA.2.2.2⟩, hxv ▸ hx⟩
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact huA.2.1
              · exact huA.2.2.1
          · intro u₁ hu₁ u₂ hu₂ heq
            dsimp only at heq
            have h1 := heAt_lt u₁
            have h2 := heAt_lt u₂
            have m1 : (eAt u₁).1 ∈ ({(eAt u₂).1, (eAt u₂).2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
            have m2 : (eAt u₁).2 ∈ ({(eAt u₂).1, (eAt u₂).2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            have m3 : (eAt u₂).1 ∈ ({(eAt u₁).1, (eAt u₁).2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
            have m4 : (eAt u₂).2 ∈ ({(eAt u₁).1, (eAt u₁).2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
            have he_eq : eAt u₁ = eAt u₂ := by
              ext
              · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
              · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
            exact Fin.ext ((List.Nodup.getElem_inj_iff (esList_nodup n)).mp he_eq)
        rwa [Finset.card_powersetCard, Finset.card_erase_of_mem hvU, hUt] at hle
      omega
    exact ⟨⟨hgood, hworst_le, hcard_le⟩, hdecode_eqU⟩

  have hPart2 : ∀ U : Finset (Fin n), Nat.card {P : Finset I // works P ∧ decode P = U} =
      if U.card = t then
        (Finset.range (T + 1)).sum (fun j => (Finset.range (M - j + 1)).sum (fun z =>
          if T - j + z ≤ δ then (edgesIn U).choose j * (M - j).choose z *
            (L.choose 2) ^ j * L ^ (M - j - z) else 0))
      else 0 := by
    intro U
    rw [Nat.card_eq_fintype_card]
    split_ifs with hUt
    · let S_good := { P : Finset I // (∀ u : Fin M, (block u.val \ P).card ≤ 2) ∧
          Dset P ⊆ actualEdges U ∧ T - (Dset P).card + (Zset P).card ≤ δ }
      have heq_sub : Fintype.card { P : Finset I // works P ∧ decode P = U } = Fintype.card S_good := by
        refine Fintype.card_congr ?_
        exact
          { toFun := fun P => ⟨P.1, (hgood_iff P.1).mp P.2.1.1,
              by
                have hf := hworks_forward P.1 P.2.1
                rw [P.2.2] at hf
                exact hf.2.1,
              (hworks_forward P.1 P.2.1).2.2⟩
            invFun := fun P => ⟨P.1, hworks_backward U P.1 hUt P.2.1 P.2.2.1 P.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [heq_sub]

      let validDZ : Finset (Finset (Fin M) × Finset (Fin M)) :=
        ((actualEdges U).powerset ×ˢ (Finset.univ : Finset (Fin M)).powerset).filter (fun dz =>
          Disjoint dz.1 dz.2 ∧ T - dz.1.card + dz.2.card ≤ δ)
      have hfib : Fintype.card S_good = ∑ dz ∈ validDZ,
          Fintype.card { P : Finset I // (∀ u : Fin M, (block u.val \ P).card ≤ 2) ∧ Dset P = dz.1 ∧ Zset P = dz.2 } := by
        let f : S_good → validDZ := fun P =>
          ⟨(Dset P.1, Zset P.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_powerset.mpr P.2.2.1, Finset.mem_powerset.mpr (Finset.subset_univ _)⟩,
            hDZ_disj P.1, P.2.2.2⟩⟩
        rw [Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm, Fintype.card_sigma]
        have hsum_eq : ∑ dz : validDZ, Fintype.card { P : S_good // f P = dz } =
            ∑ dz ∈ validDZ, Fintype.card { P : Finset I // (∀ u : Fin M, (block u.val \ P).card ≤ 2) ∧ Dset P = dz.1 ∧ Zset P = dz.2 } := by
          rw [← Finset.sum_attach (s := validDZ)]
          refine Finset.sum_congr rfl ?_
          rintro ⟨dz, hdz⟩ _
          refine Fintype.card_congr ?_
          have hdz' := Finset.mem_filter.mp hdz
          have hdz_mem := Finset.mem_product.mp hdz'.1
          have hdz_sub : dz.1 ⊆ actualEdges U := Finset.mem_powerset.mp hdz_mem.1
          have hdz_ineq : T - dz.1.card + dz.2.card ≤ δ := hdz'.2.2
          exact
            { toFun := fun P => ⟨P.1.1, P.1.2.1, congrArg (fun x => x.1.1) P.2, congrArg (fun x => x.1.2) P.2⟩
              invFun := fun P => ⟨⟨P.1, P.2.1, P.2.2.1.symm ▸ hdz_sub,
                by rw [P.2.2.1, P.2.2.2]; exact hdz_ineq⟩, Subtype.ext (Prod.ext P.2.2.1 P.2.2.2)⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        simpa [Fintype.card_coe] using hsum_eq
      rw [hfib]
      have hterm_dz : ∀ dz ∈ validDZ,
          Fintype.card { P : Finset I // (∀ u : Fin M, (block u.val \ P).card ≤ 2) ∧ Dset P = dz.1 ∧ Zset P = dz.2 } =
          (L.choose 2) ^ dz.1.card * L ^ (M - dz.1.card - dz.2.card) := by
        intro dz hdz
        have hdisj := (Finset.mem_filter.mp hdz).2.1
        exact count_subsets_with_sizes (fun u => block u.val) hblock_disj hblock_univ hblock_card dz.1 dz.2 hdisj
      rw [Finset.sum_congr rfl hterm_dz]

      have hgroup : ∑ dz ∈ validDZ, (L.choose 2) ^ dz.1.card * L ^ (M - dz.1.card - dz.2.card) =
          (Finset.range (T + 1)).sum (fun j => (Finset.range (M - j + 1)).sum (fun z =>
            if T - j + z ≤ δ then (actualEdges U).card.choose j * (M - j).choose z *
              (L.choose 2) ^ j * L ^ (M - j - z) else 0)) := by
        have hD_le_T : (actualEdges U).card ≤ T := by
          rw [← hedgesIn_eq U]
          dsimp only [edgesIn, T]
          rw [← hUt]
          have hle : (es.toFinset.filter (fun e => e.1 ∈ U ∧ e.2 ∈ U ∧ G e.1 e.2 = true)).card ≤
              (U.powersetCard 2).card := by
            refine Finset.card_le_card_of_injOn (fun e => ({e.1, e.2} : Finset (Fin n))) ?_ ?_
            · intro e he
              have he' := Finset.mem_filter.mp he
              have hlt : e.1 < e.2 := mem_esList_iff.mp (List.mem_toFinset.mp he'.1)
              rw [Finset.mem_coe, Finset.mem_powersetCard]
              refine ⟨?_, Finset.card_pair hlt.ne⟩
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> tauto
            · intro e₁ he₁ e₂ he₂ heq
              dsimp only at heq
              have h1 : e₁.1 < e₁.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₁).1)
              have h2 : e₂.1 < e₂.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₂).1)
              have m1 : e₁.1 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
              have m2 : e₁.2 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
              have m3 : e₂.1 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
              have m4 : e₂.2 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
              simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
              ext
              · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
              · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
          rwa [Finset.card_powersetCard] at hle
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun dz => (dz.1.card, dz.2.card))
          (t := Finset.range (T + 1) ×ˢ Finset.range (M + 1))]
        · rw [Finset.sum_product]
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj_le : j ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hsplit_z : ∑ z ∈ Finset.range (M + 1),
              ∑ dz ∈ validDZ.filter (fun dz => (dz.1.card, dz.2.card) = (j, z)),
                (L.choose 2) ^ dz.1.card * L ^ (M - dz.1.card - dz.2.card) =
              ∑ z ∈ Finset.range (M - j + 1),
                ∑ dz ∈ validDZ.filter (fun dz => (dz.1.card, dz.2.card) = (j, z)),
                  (L.choose 2) ^ dz.1.card * L ^ (M - dz.1.card - dz.2.card) := by
            symm
            refine Finset.sum_subset (Finset.range_mono (by omega : M - j + 1 ≤ M + 1)) ?_
            intro z hz hzn
            simp only [Finset.mem_range] at hz hzn
            refine Finset.sum_eq_zero ?_
            intro dz hdz
            exfalso
            have hdz1 := (Finset.mem_filter.mp hdz).1
            have hdz2 := (Finset.mem_filter.mp hdz).2
            have hdisj := (Finset.mem_filter.mp hdz1).2.1
            have hcard_le_M : dz.1.card + dz.2.card ≤ M := by
              rw [← Finset.card_union_of_disjoint hdisj]
              simpa using Finset.card_le_univ (dz.1 ∪ dz.2)
            have h1 : dz.1.card = j := congrArg Prod.fst hdz2
            have h2 : dz.2.card = z := congrArg Prod.snd hdz2
            omega
          rw [hsplit_z]
          refine Finset.sum_congr rfl ?_
          intro z hz
          by_cases hcond : T - j + z ≤ δ
          · simp only [hcond, ↓reduceIte]
            have hterm_eq : ∀ dz ∈ validDZ.filter (fun dz => (dz.1.card, dz.2.card) = (j, z)),
                (L.choose 2) ^ dz.1.card * L ^ (M - dz.1.card - dz.2.card) =
                (L.choose 2) ^ j * L ^ (M - j - z) := by
              intro dz hdz
              have h2 := (Finset.mem_filter.mp hdz).2
              have hfst : dz.1.card = j := congrArg Prod.fst h2
              have hsnd : dz.2.card = z := congrArg Prod.snd h2
              rw [hfst, hsnd]
            rw [Finset.sum_congr rfl hterm_eq, Finset.sum_const, smul_eq_mul]
            have hfilt_card : (validDZ.filter (fun dz => (dz.1.card, dz.2.card) = (j, z))).card =
                (actualEdges U).card.choose j * (M - j).choose z := by
              have h_eq_filt : validDZ.filter (fun dz => (dz.1.card, dz.2.card) = (j, z)) =
                  ((actualEdges U).powersetCard j).biUnion (fun D =>
                    ((Finset.univ \ D).powersetCard z).map ⟨fun Z => (D, Z), fun Z₁ Z₂ h => (Prod.ext_iff.mp h).2⟩) := by
                ext ⟨D, Z⟩
                simp only [Finset.mem_filter, validDZ, Finset.mem_product, Finset.mem_powerset,
                  Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_map, Function.Embedding.coeFn_mk,
                  Prod.ext_iff]
                constructor
                · rintro ⟨⟨⟨hDU, _⟩, hdisj, _⟩, rfl, rfl⟩
                  exact ⟨D, ⟨hDU, rfl⟩, Z, ⟨Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, hdisj.symm⟩, rfl⟩, rfl, rfl⟩
                · rintro ⟨D', ⟨hDU, hDj⟩, Z', ⟨hZD, hZz⟩, rfl, rfl⟩
                  have hdisj : Disjoint D' Z' := (Finset.subset_sdiff.mp hZD).2.symm
                  refine ⟨⟨⟨hDU, Finset.subset_univ _⟩, hdisj, ?_⟩, hDj, hZz⟩
                  change T - D'.card + Z'.card ≤ δ; rw [hDj, hZz]; exact hcond
              rw [h_eq_filt, Finset.card_biUnion]
              · have h_each : ∀ D ∈ (actualEdges U).powersetCard j,
                    (((Finset.univ \ D).powersetCard z).map ⟨fun Z => (D, Z), fun Z₁ Z₂ h => (Prod.ext_iff.mp h).2⟩).card =
                    (M - j).choose z := by
                  intro D hD
                  rw [Finset.card_map, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ,
                    Finset.card_univ, Fintype.card_fin, (Finset.mem_powersetCard.mp hD).2]
                rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
              · intro D₁ _ D₂ _ hne
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                rintro ⟨D', Z'⟩ h1 h2
                simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Prod.ext_iff] at h1 h2
                rcases h1 with ⟨_, _, rfl, _⟩
                rcases h2 with ⟨_, _, hD, _⟩
                exact hne hD.symm
            rw [hfilt_card]; ring
          · simp only [hcond, ↓reduceIte]
            refine Finset.sum_eq_zero ?_
            intro dz hdz
            exfalso
            have hdz1 := (Finset.mem_filter.mp hdz).1
            have hdz2 := (Finset.mem_filter.mp hdz).2
            have hineq := (Finset.mem_filter.mp hdz1).2.2
            have hfst : dz.1.card = j := congrArg Prod.fst hdz2
            have hsnd : dz.2.card = z := congrArg Prod.snd hdz2
            rw [hfst, hsnd] at hineq
            exact hcond hineq
        · intro dz hdz
          simp only [Finset.mem_product, Finset.mem_range]
          have hdz1 := (Finset.mem_filter.mp hdz).1
          have hDU := Finset.mem_powerset.mp (Finset.mem_product.mp hdz1).1
          have h1 : dz.1.card ≤ T := (Finset.card_le_card hDU).trans hD_le_T
          have h2 : dz.2.card ≤ M := by simpa using Finset.card_le_univ dz.2
          omega
      rw [hgroup, hedgesIn_eq U]
    · rw [Fintype.card_eq_zero_iff]
      exact ⟨fun P => hUt (P.2.2 ▸ (hworks_forward P.1 P.2.1).1)⟩

  have hPart3 : δ = 0 → Nat.card {P : Finset I // works P} =
      ((Finset.univ : Finset (Fin n)).powersetCard t |>.filter (fun U => edgesIn U = T)).card *
        (L.choose 2) ^ T * L ^ (M - T) := by
    intro hδ0
    rw [Nat.card_eq_fintype_card]
    let f : {P : Finset I // works P} → (Finset.univ : Finset (Fin n)).powersetCard t :=
      fun P => ⟨decode P.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (hworks_forward P.1 P.2).1⟩⟩
    rw [Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm, Fintype.card_sigma]
    have hfib : ∀ U : (Finset.univ : Finset (Fin n)).powersetCard t,
        Fintype.card {P : {P : Finset I // works P} // f P = U} =
        if edgesIn U.1 = T then (L.choose 2) ^ T * L ^ (M - T) else 0 := by
      intro U
      have hUt : U.1.card = t := (Finset.mem_powersetCard.mp U.2).2
      have heq : Fintype.card {P : {P : Finset I // works P} // f P = U} =
          Nat.card {P : Finset I // works P ∧ decode P = U.1} := by
        rw [Nat.card_eq_fintype_card]
        refine Fintype.card_congr ?_
        exact
          { toFun := fun P => ⟨P.1.1, P.1.2, congrArg Subtype.val P.2⟩
            invFun := fun P => ⟨⟨P.1, P.2.1⟩, Subtype.ext P.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [heq, hPart2 U.1]
      simp only [hUt, ↓reduceIte, hδ0, Nat.le_zero]
      have hsum_j : (Finset.range (T + 1)).sum (fun j => (Finset.range (M - j + 1)).sum (fun z =>
          if T - j + z = 0 then (edgesIn U.1).choose j * (M - j).choose z *
            (L.choose 2) ^ j * L ^ (M - j - z) else 0)) =
          (edgesIn U.1).choose T * (M - T).choose 0 * (L.choose 2) ^ T * L ^ (M - T - 0) := by
        rw [Finset.sum_eq_single T]
        · rw [Finset.sum_eq_single 0]
          · simp
          · intro z _ hz0
            have : T - T + z ≠ 0 := by omega
            rw [if_neg this]
          · intro h0; exfalso; apply h0; exact Finset.mem_range.mpr (by omega)
        · intro j hj hjT
          have hj_lt : j < T := by
            have := Finset.mem_range.mp hj
            omega
          refine Finset.sum_eq_zero ?_
          intro z _
          have : T - j + z ≠ 0 := by omega
          rw [if_neg this]
        · intro hT; exfalso; apply hT; exact Finset.mem_range.mpr (by omega)
      rw [hsum_j]
      simp only [Nat.choose_zero_right, mul_one, Nat.sub_zero]
      have hed_le : edgesIn U.1 ≤ T := by
        dsimp only [edgesIn, T]
        calc (es.toFinset.filter (fun e => e.1 ∈ U.1 ∧ e.2 ∈ U.1 ∧ G e.1 e.2 = true)).card
            ≤ (U.1.powersetCard 2).card := by
              refine Finset.card_le_card_of_injOn (fun e => ({e.1, e.2} : Finset (Fin n))) ?_ ?_
              · intro e he
                have he' := Finset.mem_filter.mp he
                have hlt : e.1 < e.2 := mem_esList_iff.mp (List.mem_toFinset.mp he'.1)
                rw [Finset.mem_coe, Finset.mem_powersetCard]
                refine ⟨?_, Finset.card_pair hlt.ne⟩
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> tauto
              · intro e₁ he₁ e₂ he₂ heq
                dsimp only at heq
                have h1 : e₁.1 < e₁.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₁).1)
                have h2 : e₂.1 < e₂.2 := mem_esList_iff.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he₂).1)
                have m1 : e₁.1 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
                have m2 : e₁.2 ∈ ({e₂.1, e₂.2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
                have m3 : e₂.1 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_self _ _
                have m4 : e₂.2 ∈ ({e₁.1, e₁.2} : Finset (Fin n)) := heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
                simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3 m4
                ext
                · rcases m1 with h | h <;> rcases m3 with h' | h' <;> omega
                · rcases m2 with h | h <;> rcases m4 with h' | h' <;> omega
          _ = U.1.card.choose 2 := Finset.card_powersetCard _ _
          _ = t.choose 2 := by rw [hUt]
      by_cases heqT : edgesIn U.1 = T
      · simp [heqT]
      · have hltT : edgesIn U.1 < T := lt_of_le_of_ne hed_le heqT
        simp [heqT, Nat.choose_eq_zero_of_lt hltT]
    simp_rw [hfib]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    have hcard_filt : ((Finset.univ : Finset ((Finset.univ : Finset (Fin n)).powersetCard t)).filter
        (fun U => edgesIn U.1 = T)).card =
        ((Finset.univ : Finset (Fin n)).powersetCard t |>.filter (fun U => edgesIn U = T)).card := by
      refine Finset.card_bij (fun U _ => U.1) ?_ ?_ ?_
      · intro U hU
        have hU' := Finset.mem_filter.mp hU
        exact Finset.mem_filter.mpr ⟨U.2, hU'.2⟩
      · intro U₁ _ U₂ _ h; exact Subtype.ext h
      · intro U hU
        have hU' := Finset.mem_filter.mp hU
        exact ⟨⟨U, hU'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU'.2⟩, rfl⟩
    rw [hcard_filt]
    ring
  exact ⟨hPart1, hPart2, hPart3⟩

end PEqualNP.Outside.L_meta_33607

theorem PEqualNP.Outside.L_meta_33607 : (∀ (n t r δ : Nat), 3 ≤ t → t ≤ n → 4 ≤ r → δ < t-2 →
  ∀ (G : Fin n → Fin n → Bool),
  let es := (List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
  let items := es.zipIdx.toFinset
  let M := es.length
  let L := 5*r-2
  let k := L*M
  let m := n+2*M
  let I := Fin k
  let A := Bool × I
  let F := ZMod 2
  let Y := Fin m → F
  let T := t.choose 2
  let b := (L-1)*M - (t-1).choose 2 + δ
  let row := fun (j : Fin m) => es.zipIdx.foldl (fun acc z =>
    let keep := if G z.1.1 z.1.2 then (j.val = z.1.1.val ∨ j.val = z.1.2.val)
      else (j.val = n+2*z.2 ∨ j.val = n+2*z.2+1)
    if keep then acc ||| (1 <<< ((L*z.2+(2*r-2))%k)) else acc) (0 : Nat)
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let scope := fun a : A => (Finset.univ : Finset I).filter (fun i =>
    ∃ d : Fin (reach a.1+1), (a.2.val+d.val)%k = i.val)
  let col := fun (a : A) (j : Fin m) =>
    if (!a.1 && (row j).testBit ((a.2.val+delay a.1)%k)) then (1 : F) else 0
  let active := (Finset.univ : Finset A).filter (fun a => col a ≠ 0)
  let left := fun (P : Finset I) (a : A) => scope a \ P
  let good := fun (P : Finset I) => ∀ a ∈ active, (left P a).card ≤ 2
  let pairs := fun (P : Finset I) => (active.image (left P)).filter (fun e => e.card = 2)
  let rank := fun (V : Finset Y) => Module.finrank F (Submodule.span F (V : Set Y))
  let worst := fun (P : Finset I) => (Finset.univ : Finset (A → F)).sup (fun w =>
    rank ((pairs P).image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)))
  let works := fun (P : Finset I) => good P ∧ worst P ≤ t-1 ∧ P.card + worst P ≤ b
  let block := fun (u : Nat) => (Finset.univ : Finset I).filter (fun i =>
    L*u ≤ i.val ∧ i.val < L*(u+1))
  let decode := fun (P : Finset I) => (items.filter (fun z =>
    G z.1.1 z.1.2 = true ∧ (block z.2 \ P).card = 2)).biUnion (fun z =>
      ({z.1.1, z.1.2} : Finset (Fin n)))
  let edgesIn := fun (U : Finset (Fin n)) => (es.toFinset.filter (fun e =>
    e.1 ∈ U ∧ e.2 ∈ U ∧ G e.1 e.2 = true)).card
  (∀ j : Fin m, row j < 2^k) ∧
  (∀ U : Finset (Fin n), Nat.card {P : Finset I // works P ∧ decode P = U} =
    if U.card = t then
      (Finset.range (T+1)).sum (fun j => (Finset.range (M-j+1)).sum (fun z =>
        if T-j+z ≤ δ then (edgesIn U).choose j * (M-j).choose z *
          (L.choose 2)^j * L^(M-j-z) else 0))
    else 0) ∧
  (δ = 0 → Nat.card {P : Finset I // works P} =
    ((Finset.univ : Finset (Fin n)).powersetCard t |>.filter (fun U => edgesIn U = T)).card *
      (L.choose 2)^T * L^(M-T))) :=
  PEqualNP.Outside.L_meta_33607.main_proof

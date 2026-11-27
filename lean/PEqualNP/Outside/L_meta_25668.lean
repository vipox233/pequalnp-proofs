import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25668_aux

lemma xor_four_corners (ai bi aj bj ri rj ci cj : Bool) :
    Bool.xor (Bool.xor (Bool.xor (ai && bi) (Bool.xor ri ci))
                       (Bool.xor (aj && bj) (Bool.xor rj cj)))
             (Bool.xor (Bool.xor (ai && bj) (Bool.xor ri cj))
                       (Bool.xor (aj && bi) (Bool.xor rj ci))) =
    ((Bool.xor ai aj) && (Bool.xor bi bj)) := by
  cases ai <;> cases bi <;> cases aj <;> cases bj <;>
    cases ri <;> cases rj <;> cases ci <;> cases cj <;> rfl

lemma xor_decide_compl {n : ℕ} (S : Finset (Fin n)) (i j : Fin n) :
    Bool.xor (decide (i ∈ Finset.univ \ S)) (decide (j ∈ Finset.univ \ S)) =
    Bool.xor (decide (i ∈ S)) (decide (j ∈ S)) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

lemma card_compl_fin {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ \ S).card = n - S.card := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]

lemma exists_perm_map_eq {n : ℕ} (X Y : Finset (Fin n)) (hcard : X.card = Y.card) :
    ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n, π i ∈ Y ↔ i ∈ X := by
  have hc1 : Fintype.card {i : Fin n // i ∈ X} = Fintype.card {j : Fin n // j ∈ Y} := by
    simp [Fintype.card_coe, hcard]
  have hc2 : Fintype.card {i : Fin n // i ∉ X} = Fintype.card {j : Fin n // j ∉ Y} := by
    have hX : (Finset.univ.filter (fun i : Fin n => i ∉ X)).card = n - X.card := by
      have heq : Finset.univ.filter (fun i : Fin n => i ∉ X) = Finset.univ \ X := by
        ext i; simp
      rw [heq, card_compl_fin]
    have hY : (Finset.univ.filter (fun j : Fin n => j ∉ Y)).card = n - Y.card := by
      have heq : Finset.univ.filter (fun j : Fin n => j ∉ Y) = Finset.univ \ Y := by
        ext j; simp
      rw [heq, card_compl_fin]
    rw [Fintype.card_subtype, Fintype.card_subtype, hX, hY, hcard]
  obtain ⟨e1⟩ := Fintype.truncEquivOfCardEq hc1
  obtain ⟨e2⟩ := Fintype.truncEquivOfCardEq hc2
  let eSplitX : Fin n ≃ {i : Fin n // i ∈ X} ⊕ {i : Fin n // i ∉ X} :=
    (Equiv.sumCompl (fun i : Fin n => i ∈ X)).symm
  let eSplitY : {j : Fin n // j ∈ Y} ⊕ {j : Fin n // j ∉ Y} ≃ Fin n :=
    Equiv.sumCompl (fun j : Fin n => j ∈ Y)
  let π : Equiv.Perm (Fin n) := (eSplitX.trans (Equiv.sumCongr e1 e2)).trans eSplitY
  refine ⟨π, fun i => ?_⟩
  by_cases hi : i ∈ X
  · have hpi : π i = (e1 ⟨i, hi⟩).val := by
      simp [π, eSplitX, eSplitY, Equiv.sumCompl, hi]
    rw [hpi]
    exact ⟨fun _ => hi, fun _ => (e1 ⟨i, hi⟩).property⟩
  · have hpi : π i = (e2 ⟨i, hi⟩).val := by
      simp [π, eSplitX, eSplitY, Equiv.sumCompl, hi]
    rw [hpi]
    exact ⟨fun hm => False.elim ((e2 ⟨i, hi⟩).property hm), fun hm => False.elim (hi hm)⟩

lemma forward_bound {n u t : ℕ} (A B : Finset (Fin n))
    (hA : 2 * A.card ≤ n) (hB : 2 * B.card ≤ n)
    (π : Equiv.Perm (Fin n)) (K L : Finset (Fin n))
    (hLK : L ⊆ K) (hLu : L.card ≤ u) (hKt : n ≤ K.card + t)
    (hrel : ∀ i ∈ K, ∀ j ∈ K,
      ((Bool.xor (decide (i ∈ A)) (decide (j ∈ A))) &&
       (Bool.xor (decide (π i ∈ B)) (decide (π j ∈ B)))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) :
    min (min A.card B.card) (max A.card B.card - min u (min A.card B.card)) ≤ t := by
  let r := A.card
  let c := B.card
  let a := min r c
  let b := max r c
  let T00 := Finset.univ.filter (fun i : Fin n => i ∉ A ∧ π i ∉ B)
  let T01 := Finset.univ.filter (fun i : Fin n => i ∉ A ∧ π i ∈ B)
  let T10 := Finset.univ.filter (fun i : Fin n => i ∈ A ∧ π i ∉ B)
  let T11 := Finset.univ.filter (fun i : Fin n => i ∈ A ∧ π i ∈ B)
  let x := T11.card
  have h10_11 : T10.card + x = r := by
    have hd : Disjoint T10 T11 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [T10, T11, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h1.2 h2.2
    have hu : T10 ∪ T11 = A := by
      ext i; simp only [T10, T11, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hpi : π i ∈ B <;> simp [hpi]
    rw [← Finset.card_union_of_disjoint hd, hu]
  have h01_11 : T01.card + x = c := by
    have hd : Disjoint T01 T11 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [T01, T11, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h1.1 h2.1
    have hu : T01 ∪ T11 = B.map π.symm.toEmbedding := by
      ext i
      simp only [T01, T11, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro (⟨_, hb⟩ | ⟨_, hb⟩)
        · exact ⟨π i, hb, π.symm_apply_apply i⟩
        · exact ⟨π i, hb, π.symm_apply_apply i⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases ha : π.symm j ∈ A <;> simp [ha, hj]
    rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_map]
  have hsumT : T00.card + T01.card + T10.card + x = n := by
    have hd01 : Disjoint T00 T01 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [T00, T01, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h1.2 h2.2
    have hd10 : Disjoint (T00 ∪ T01) T10 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [T00, T01, T10, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with h1 | h1
      · exact h1.1 h2.1
      · exact h1.1 h2.1
    have hd11 : Disjoint (T00 ∪ T01 ∪ T10) T11 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [T00, T01, T10, T11, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with (h1 | h1) | h1
      · exact h1.1 h2.1
      · exact h1.1 h2.1
      · exact h1.2 h2.2
    have hu : T00 ∪ T01 ∪ T10 ∪ T11 = Finset.univ := by
      ext i
      simp only [T00, T01, T10, T11, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases ha : i ∈ A <;> by_cases hb : π i ∈ B <;> simp [ha, hb]
    have hc := congrArg Finset.card hu
    rw [Finset.card_union_of_disjoint hd11, Finset.card_union_of_disjoint hd10,
        Finset.card_union_of_disjoint hd01, Finset.card_univ, Fintype.card_fin] at hc
    exact hc
  let K00 := K ∩ T00
  let K01 := K ∩ T01
  let K10 := K ∩ T10
  let K11 := K ∩ T11
  have hKsum : K00.card + K01.card + K10.card + K11.card = K.card := by
    have hd01 : Disjoint K00 K01 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [K00, K01, T00, T01, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h1.2.2 h2.2.2
    have hd10 : Disjoint (K00 ∪ K01) K10 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [K00, K01, K10, T00, T01, T10, Finset.mem_union, Finset.mem_inter,
                 Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with h1 | h1
      · exact h1.2.1 h2.2.1
      · exact h1.2.1 h2.2.1
    have hd11 : Disjoint (K00 ∪ K01 ∪ K10) K11 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [K00, K01, K10, K11, T00, T01, T10, T11, Finset.mem_union, Finset.mem_inter,
                 Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with (h1 | h1) | h1
      · exact h1.2.1 h2.2.1
      · exact h1.2.1 h2.2.1
      · exact h1.2.2 h2.2.2
    have hu : K00 ∪ K01 ∪ K10 ∪ K11 = K := by
      ext i
      simp only [K00, K01, K10, K11, T00, T01, T10, T11, Finset.mem_union, Finset.mem_inter,
                 Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hk : i ∈ K <;> by_cases ha : i ∈ A <;> by_cases hb : π i ∈ B <;> simp [hk, ha, hb]
    have hc := congrArg Finset.card hu
    rw [Finset.card_union_of_disjoint hd11, Finset.card_union_of_disjoint hd10,
        Finset.card_union_of_disjoint hd01] at hc
    exact hc
  have hle00 : K00.card ≤ T00.card := Finset.card_le_card Finset.inter_subset_right
  have hle01 : K01.card ≤ T01.card := Finset.card_le_card Finset.inter_subset_right
  have hle10 : K10.card ≤ T10.card := Finset.card_le_card Finset.inter_subset_right
  have hle11 : K11.card ≤ x := Finset.card_le_card Finset.inter_subset_right
  by_cases hcut : ∃ p ∈ K, ∃ q ∈ K, p ∈ L ∧ q ∉ L
  · rcases hcut with ⟨p, hpK, q, hqK, hpL, hqL⟩
    have hpq := hrel p hpK q hqK
    simp only [hpL, hqL, decide_true, decide_false, Bool.xor_false] at hpq
    have hbox_pq : (p ∈ A ↔ q ∉ A) ∧ (π p ∈ B ↔ π q ∉ B) := by
      by_cases hpa : p ∈ A <;> by_cases hqa : q ∈ A <;>
        by_cases hpb : π p ∈ B <;> by_cases hqb : π q ∈ B <;>
        simp [hpa, hqa, hpb, hqb] at hpq ⊢
    by_cases hcomp : (p ∈ A ↔ π p ∈ B)
    · have h01_empty : K01 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        simp only [K01, T01, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have hpz := hrel p hpK z hz.1
        have hqz := hrel q hqK z hz.1
        have hbox1 : ((Bool.xor (decide (p ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π p ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hpa : p ∈ A <;> simp [hpa, hcomp.mp, hz.2.1, hz.2.2] at *
          all_goals (by_cases hpb : π p ∈ B <;> simp [hpa, hpb, hz.2.1, hz.2.2] at hcomp ⊢)
        have hbox2 : ((Bool.xor (decide (q ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π q ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hqa : q ∈ A <;> by_cases hqb : π q ∈ B <;>
            by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hqa, hqb, hz.2.1, hz.2.2] at hcomp hbox_pq ⊢
        rw [hbox1] at hpz; rw [hbox2] at hqz
        by_cases hzL : z ∈ L <;> simp [hpL, hqL, hzL] at hpz hqz
      have h10_empty : K10 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        simp only [K10, T10, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have hpz := hrel p hpK z hz.1
        have hqz := hrel q hqK z hz.1
        have hbox1 : ((Bool.xor (decide (p ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π p ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hz.2.1, hz.2.2] at hcomp ⊢
        have hbox2 : ((Bool.xor (decide (q ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π q ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hqa : q ∈ A <;> by_cases hqb : π q ∈ B <;>
            by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hqa, hqb, hz.2.1, hz.2.2] at hcomp hbox_pq ⊢
        rw [hbox1] at hpz; rw [hbox2] at hqz
        by_cases hzL : z ∈ L <;> simp [hpL, hqL, hzL] at hpz hqz
      have hsub : K00 ⊆ L ∨ K11 ⊆ L := by
        by_cases hp00 : p ∈ T00
        · left
          intro z hz
          simp only [K00, T00, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz hp00
          have hpz := hrel p hpK z hz.1
          simp only [hp00.1, hp00.2, hz.2.1, hz.2.2, hpL, decide_false, decide_true,
                     Bool.xor_self, Bool.and_self] at hpz
          by_contra hzL
          simp [hzL] at hpz
        · right
          have hp11 : p ∈ T11 := by
            simp only [T00, T11, Finset.mem_filter, Finset.mem_univ, true_and] at hp00 ⊢
            by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;> simp [hpa, hpb] at hcomp hp00 ⊢
          intro z hz
          simp only [K11, T11, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz hp11
          have hpz := hrel p hpK z hz.1
          simp only [hp11.1, hp11.2, hz.2.1, hz.2.2, hpL, decide_true,
                     Bool.xor_self, Bool.and_self] at hpz
          by_contra hzL
          simp [hzL] at hpz
      have hcard_or : K00.card ≤ u ∨ K11.card ≤ u := by
        rcases hsub with h | h
        · left; exact Nat.le_trans (Finset.card_le_card h) hLu
        · right; exact Nat.le_trans (Finset.card_le_card h) hLu
      have hc01 : K01.card = 0 := by rw [h01_empty]; rfl
      have hc10 : K10.card = 0 := by rw [h10_empty]; rfl
      change min a (b - min u a) ≤ t
      dsimp only [a, b, r, c] at *
      omega
    · have h00_empty : K00 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        simp only [K00, T00, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have hpz := hrel p hpK z hz.1
        have hqz := hrel q hqK z hz.1
        have hbox1 : ((Bool.xor (decide (p ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π p ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hz.2.1, hz.2.2] at hcomp ⊢
        have hbox2 : ((Bool.xor (decide (q ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π q ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hqa : q ∈ A <;> by_cases hqb : π q ∈ B <;>
            by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hqa, hqb, hz.2.1, hz.2.2] at hcomp hbox_pq ⊢
        rw [hbox1] at hpz; rw [hbox2] at hqz
        by_cases hzL : z ∈ L <;> simp [hpL, hqL, hzL] at hpz hqz
      have h11_empty : K11 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        simp only [K11, T11, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have hpz := hrel p hpK z hz.1
        have hqz := hrel q hqK z hz.1
        have hbox1 : ((Bool.xor (decide (p ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π p ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hz.2.1, hz.2.2] at hcomp ⊢
        have hbox2 : ((Bool.xor (decide (q ∈ A)) (decide (z ∈ A))) &&
                      (Bool.xor (decide (π q ∈ B)) (decide (π z ∈ B)))) = false := by
          by_cases hqa : q ∈ A <;> by_cases hqb : π q ∈ B <;>
            by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;>
            simp [hpa, hpb, hqa, hqb, hz.2.1, hz.2.2] at hcomp hbox_pq ⊢
        rw [hbox1] at hpz; rw [hbox2] at hqz
        by_cases hzL : z ∈ L <;> simp [hpL, hqL, hzL] at hpz hqz
      have hsub : K01 ⊆ L ∨ K10 ⊆ L := by
        by_cases hp01 : p ∈ T01
        · left
          intro z hz
          simp only [K01, T01, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz hp01
          have hpz := hrel p hpK z hz.1
          simp only [hp01.1, hp01.2, hz.2.1, hz.2.2, hpL, decide_false, decide_true,
                     Bool.xor_self, Bool.and_self] at hpz
          by_contra hzL
          simp [hzL] at hpz
        · right
          have hp10 : p ∈ T10 := by
            simp only [T01, T10, Finset.mem_filter, Finset.mem_univ, true_and] at hp01 ⊢
            by_cases hpa : p ∈ A <;> by_cases hpb : π p ∈ B <;> simp [hpa, hpb] at hcomp hp01 ⊢
          intro z hz
          simp only [K10, T10, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz hp10
          have hpz := hrel p hpK z hz.1
          simp only [hp10.1, hp10.2, hz.2.1, hz.2.2, hpL, decide_false, decide_true,
                     Bool.xor_self, Bool.and_self] at hpz
          by_contra hzL
          simp [hzL] at hpz
      have hcard_or : K01.card ≤ u ∨ K10.card ≤ u := by
        rcases hsub with h | h
        · left; exact Nat.le_trans (Finset.card_le_card h) hLu
        · right; exact Nat.le_trans (Finset.card_le_card h) hLu
      have hc00 : K00.card = 0 := by rw [h00_empty]; rfl
      have hc11 : K11.card = 0 := by rw [h11_empty]; rfl
      change min a (b - min u a) ≤ t
      dsimp only [a, b, r, c] at *
      omega
  · have hno_edge : ∀ i ∈ K, ∀ j ∈ K,
        ((Bool.xor (decide (i ∈ A)) (decide (j ∈ A))) &&
         (Bool.xor (decide (π i ∈ B)) (decide (π j ∈ B)))) = false := by
      intro i hi j hj
      rw [hrel i hi j hj]
      by_cases hiL : i ∈ L <;> by_cases hjL : j ∈ L
      · simp [hiL, hjL]
      · exact False.elim (hcut ⟨i, hi, j, hj, hiL, hjL⟩)
      · exact False.elim (hcut ⟨j, hj, i, hi, hjL, hiL⟩)
      · simp [hiL, hjL]
    have h00_or_11 : K00.card = 0 ∨ K11.card = 0 := by
      by_contra hne
      have hne00 : K00.Nonempty := Finset.card_pos.mp (by omega)
      have hne11 : K11.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne00 with ⟨i, hi⟩
      rcases hne11 with ⟨j, hj⟩
      simp only [K00, K11, T00, T11, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have h := hno_edge i hi.1 j hj.1
      simp [hi.2.1, hi.2.2, hj.2.1, hj.2.2] at h
    have h01_or_10 : K01.card = 0 ∨ K10.card = 0 := by
      by_contra hne
      have hne01 : K01.Nonempty := Finset.card_pos.mp (by omega)
      have hne10 : K10.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne01 with ⟨i, hi⟩
      rcases hne10 with ⟨j, hj⟩
      simp only [K01, K10, T01, T10, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have h := hno_edge i hi.1 j hj.1
      simp [hi.2.1, hi.2.2, hj.2.1, hj.2.2] at h
    change min a (b - min u a) ≤ t
    dsimp only [a, b, r, c] at *
    omega

lemma backward_construct {n u t : ℕ} (A B : Finset (Fin n))
    (hA : 2 * A.card ≤ n) (hB : 2 * B.card ≤ n)
    (ht : min (min A.card B.card) (max A.card B.card - min u (min A.card B.card)) ≤ t) :
    ∃ (π : Equiv.Perm (Fin n)) (K L : Finset (Fin n)),
      L ⊆ K ∧ L.card ≤ u ∧ n ≤ K.card + t ∧
      ∀ i ∈ K, ∀ j ∈ K,
        ((Bool.xor (decide (i ∈ A)) (decide (j ∈ A))) &&
         (Bool.xor (decide (π i ∈ B)) (decide (π j ∈ B)))) =
        Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  by_cases hcase : min A.card B.card ≤ t
  · by_cases hle : A.card ≤ B.card
    · refine ⟨Equiv.refl (Fin n), Finset.univ \ A, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩
      · rw [card_compl_fin]
        omega
      · intro i hi j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi hj
        simp [hi, hj]
    · refine ⟨Equiv.refl (Fin n), Finset.univ \ B, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩
      · rw [card_compl_fin]
        omega
      · intro i hi j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi hj
        simp [hi, hj]
  · have hbt : max A.card B.card - min u (min A.card B.card) ≤ t := by omega
    by_cases hle : A.card ≤ B.card
    · obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq hle
      obtain ⟨π, hπ⟩ := exists_perm_map_eq A S hScard.symm
      obtain ⟨L, hLA, hLcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right u A.card)
      let T00 := Finset.univ.filter (fun i : Fin n => π i ∉ B)
      have hT00_card : T00.card = n - B.card := by
        have heq : T00 = (Finset.univ \ B).map π.symm.toEmbedding := by
          ext i
          simp only [T00, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                     Finset.mem_sdiff, Equiv.coe_toEmbedding]
          constructor
          · intro hni; exact ⟨π i, hni, π.symm_apply_apply i⟩
          · rintro ⟨j, hj, rfl⟩; simpa using hj
        rw [heq, Finset.card_map, card_compl_fin]
      have hdisj : Disjoint T00 L := by
        rw [Finset.disjoint_left]; intro i hi0 hiL
        simp only [T00, Finset.mem_filter, Finset.mem_univ, true_and] at hi0
        exact hi0 (hSB ((hπ i).mpr (hLA hiL)))
      refine ⟨π, T00 ∪ L, L, Finset.subset_union_right, by omega, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hT00_card, hLcard]
        omega
      · intro i hi j hj
        have hT00_notA : ∀ z ∈ T00, z ∉ A ∧ π z ∉ B ∧ z ∉ L := by
          intro z hz
          simp only [T00, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          refine ⟨fun hzA => hz (hSB ((hπ z).mpr hzA)), hz,
                  fun hzL => hz (hSB ((hπ z).mpr (hLA hzL)))⟩
        have hL_in : ∀ z ∈ L, z ∈ A ∧ π z ∈ B := by
          intro z hz
          exact ⟨hLA hz, hSB ((hπ z).mpr (hLA hz))⟩
        rcases Finset.mem_union.mp hi with hi0 | hiL <;>
          rcases Finset.mem_union.mp hj with hj0 | hjL
        · rcases hT00_notA i hi0 with ⟨hiA, hiB, hiL'⟩
          rcases hT00_notA j hj0 with ⟨hjA, hjB, hjL'⟩
          simp [hiA, hiB, hiL', hjA, hjB, hjL']
        · rcases hT00_notA i hi0 with ⟨hiA, hiB, hiL'⟩
          rcases hL_in j hjL with ⟨hjA, hjB⟩
          simp [hiA, hiB, hiL', hjA, hjB, hjL]
        · rcases hL_in i hiL with ⟨hiA, hiB⟩
          rcases hT00_notA j hj0 with ⟨hjA, hjB, hjL'⟩
          simp [hiA, hiB, hiL, hjA, hjB, hjL']
        · rcases hL_in i hiL with ⟨hiA, hiB⟩
          rcases hL_in j hjL with ⟨hjA, hjB⟩
          simp [hiA, hiB, hiL, hjA, hjB, hjL]
    · have hBA : B.card ≤ A.card := by omega
      obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hBA
      obtain ⟨π, hπ⟩ := exists_perm_map_eq S B hScard
      have hmin_le : min u B.card ≤ S.card := by rw [hScard]; exact Nat.min_le_right u B.card
      obtain ⟨L, hLS, hLcard⟩ := Finset.exists_subset_card_eq hmin_le
      let T00 := Finset.univ \ A
      have hT00_card : T00.card = n - A.card := card_compl_fin A
      have hdisj : Disjoint T00 L := by
        rw [Finset.disjoint_left]; intro i hi0 hiL
        simp only [T00, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi0
        exact hi0 (hSA (hLS hiL))
      refine ⟨π, T00 ∪ L, L, Finset.subset_union_right, by omega, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hT00_card, hLcard]
        omega
      · intro i hi j hj
        have hT00_notA : ∀ z ∈ T00, z ∉ A ∧ π z ∉ B ∧ z ∉ L := by
          intro z hz
          simp only [T00, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
          refine ⟨hz, fun hzB => hz (hSA ((hπ z).mp hzB)), fun hzL => hz (hSA (hLS hzL))⟩
        have hL_in : ∀ z ∈ L, z ∈ A ∧ π z ∈ B := by
          intro z hz
          exact ⟨hSA (hLS hz), (hπ z).mpr (hLS hz)⟩
        rcases Finset.mem_union.mp hi with hi0 | hiL <;>
          rcases Finset.mem_union.mp hj with hj0 | hjL
        · rcases hT00_notA i hi0 with ⟨hiA, hiB, hiL'⟩
          rcases hT00_notA j hj0 with ⟨hjA, hjB, hjL'⟩
          simp [hiA, hiB, hiL', hjA, hjB, hjL']
        · rcases hT00_notA i hi0 with ⟨hiA, hiB, hiL'⟩
          rcases hL_in j hjL with ⟨hjA, hjB⟩
          simp [hiA, hiB, hiL', hjA, hjB, hjL]
        · rcases hL_in i hiL with ⟨hiA, hiB⟩
          rcases hT00_notA j hj0 with ⟨hjA, hjB, hjL'⟩
          simp [hiA, hiB, hiL, hjA, hjB, hjL']
        · rcases hL_in i hiL with ⟨hiA, hiB⟩
          rcases hL_in j hjL with ⟨hjA, hjB⟩
          simp [hiA, hiB, hiL, hjA, hjB, hjL]

end PEqualNP.Outside.L_meta_25668_aux

theorem PEqualNP.Outside.L_meta_25668 : (∀ (n u t : ℕ) (A B : Finset (Fin n)) (rowFlip colFlip : Fin n → Bool),
  let G := fun (i j : Fin n) => Bool.xor ((decide (i ∈ A)) && (decide (j ∈ B))) (Bool.xor (rowFlip i) (colFlip j))
  let rows := min A.card (n - A.card)
  let cols := min B.card (n - B.card)
  let a := min rows cols
  let b := max rows cols
  (∃ (π : Equiv.Perm (Fin n)) (K L : Finset (Fin n)),
    L ⊆ K ∧ L.card ≤ u ∧ n ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ min a (b - min u a) ≤ t) := by
  intro n u t A B rowFlip colFlip G rows cols a b
  let A' := if A.card ≤ n - A.card then A else Finset.univ \ A
  let B' := if B.card ≤ n - B.card then B else Finset.univ \ B
  have hA'_card : A'.card = rows := by
    dsimp only [A', rows]
    by_cases h : A.card ≤ n - A.card
    · simp [h]
    · simp only [h, ↓reduceIte, PEqualNP.Outside.L_meta_25668_aux.card_compl_fin]
      omega
  have hB'_card : B'.card = cols := by
    dsimp only [B', cols]
    by_cases h : B.card ≤ n - B.card
    · simp [h]
    · simp only [h, ↓reduceIte, PEqualNP.Outside.L_meta_25668_aux.card_compl_fin]
      omega
  have hA_le : A.card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ A
  have hB_le : B.card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ B
  have h2A : 2 * A'.card ≤ n := by rw [hA'_card]; dsimp only [rows]; omega
  have h2B : 2 * B'.card ≤ n := by rw [hB'_card]; dsimp only [cols]; omega
  have hbox_eq : ∀ (π : Equiv.Perm (Fin n)) (i j : Fin n),
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      ((Bool.xor (decide (i ∈ A')) (decide (j ∈ A'))) &&
       (Bool.xor (decide (π i ∈ B')) (decide (π j ∈ B')))) := by
    intro π i j
    have h1 := PEqualNP.Outside.L_meta_25668_aux.xor_four_corners
      (decide (i ∈ A)) (decide (π i ∈ B)) (decide (j ∈ A)) (decide (π j ∈ B))
      (rowFlip i) (rowFlip j) (colFlip (π i)) (colFlip (π j))
    have hAeq : Bool.xor (decide (i ∈ A')) (decide (j ∈ A')) =
        Bool.xor (decide (i ∈ A)) (decide (j ∈ A)) := by
      dsimp only [A']
      by_cases h : A.card ≤ n - A.card
      · simp [h]
      · simp only [h, ↓reduceIte]
        exact PEqualNP.Outside.L_meta_25668_aux.xor_decide_compl A i j
    have hBeq : Bool.xor (decide (π i ∈ B')) (decide (π j ∈ B')) =
        Bool.xor (decide (π i ∈ B)) (decide (π j ∈ B)) := by
      dsimp only [B']
      by_cases h : B.card ≤ n - B.card
      · simp [h]
      · simp only [h, ↓reduceIte]
        exact PEqualNP.Outside.L_meta_25668_aux.xor_decide_compl B (π i) (π j)
    rw [hAeq, hBeq]
    exact h1
  have hab : min a (b - min u a) =
      min (min A'.card B'.card) (max A'.card B'.card - min u (min A'.card B'.card)) := by
    dsimp only [a, b]
    rw [hA'_card, hB'_card]
  rw [hab]
  constructor
  · rintro ⟨π, K, L, hLK, hLu, hKt, hrel⟩
    refine PEqualNP.Outside.L_meta_25668_aux.forward_bound A' B' h2A h2B π K L hLK hLu hKt ?_
    intro i hi j hj
    rw [← hbox_eq π i j]
    exact hrel i hi j hj
  · intro ht
    obtain ⟨π, K, L, hLK, hLu, hKt, hrel⟩ :=
      PEqualNP.Outside.L_meta_25668_aux.backward_construct A' B' h2A h2B ht
    refine ⟨π, K, L, hLK, hLu, hKt, ?_⟩
    intro i hi j hj
    rw [hbox_eq π i j]
    exact hrel i hi j hj

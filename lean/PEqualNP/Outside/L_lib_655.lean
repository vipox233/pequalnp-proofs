import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_lib_655_aux

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma nat_dist_sq_int (a c : ℕ) :
    (((Nat.dist a c) ^ 2 : ℕ) : ℤ) = ((a : ℤ) - (c : ℤ)) ^ 2 := by
  by_cases h : a ≤ c
  · rw [Nat.dist_eq_sub_of_le h]
    push_cast [h]
    ring
  · have h' : c ≤ a := by omega
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h']
    push_cast [h']
    ring

lemma testBit_eq_false_of_lt_two_pow {a k : ℕ} (h : a < 2 ^ k) : a.testBit k = false := by
  rw [Nat.testBit]
  have hdiv : a >>> k = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt h
  simp [hdiv]

lemma eq_of_testBit_lt {a c b : ℕ} (ha : a < 2 ^ b) (hc : c < 2 ^ b)
    (h : ∀ i : Fin b, a.testBit i.val = c.testBit i.val) : a = c := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < b
  · exact h ⟨k, hk⟩
  · have hle : 2 ^ b ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    rw [testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le ha hle),
      testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le hc hle)]

lemma exists_linear_map_avoiding {I : Type*} [Fintype I] [DecidableEq I] {f : ℕ}
    (Bad : Finset (I → ZMod 2))
    (h0 : (0 : I → ZMod 2) ∉ Bad)
    (hcard : Bad.card < 2 ^ f) :
    ∃ H : (I → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2), ∀ v ∈ Bad, H v ≠ 0 := by
  let Mat := Matrix (Fin f) I (ZMod 2)
  have hker_card : ∀ v ∈ Bad,
      2 ^ f * (Finset.univ.filter (fun M : Mat => M.mulVec v = 0)).card = Fintype.card Mat := by
    intro v hv
    have hvne : v ≠ 0 := fun h => h0 (h ▸ hv)
    have hex : ∃ i0 : I, v i0 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hvne (funext hall)
    rcases hex with ⟨i0, hi0⟩
    have hi01 : v i0 = 1 := zmod2_eq_one_of_ne_zero hi0
    let e : Mat ≃ (Fin f → ZMod 2) × {M : Mat // M.mulVec v = 0} :=
      { toFun := fun M =>
          (M.mulVec v,
           ⟨Matrix.of fun r i => if i = i0 then M r i0 + M.mulVec v r else M r i, by
              ext r
              change (∑ i : I, (if i = i0 then M r i0 + M.mulVec v r else M r i) * v i) = 0
              rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
              simp only [↓reduceIte, hi01, mul_one]
              have hrest : (∑ i ∈ Finset.univ.erase i0,
                  (if i = i0 then M r i0 + M.mulVec v r else M r i) * v i) =
                  ∑ i ∈ Finset.univ.erase i0, M r i * v i := by
                refine Finset.sum_congr rfl fun i hi => ?_
                simp [(Finset.mem_erase.mp hi).1]
              rw [hrest]
              have hmv : M.mulVec v r = M r i0 + ∑ i ∈ Finset.univ.erase i0, M r i * v i := by
                simp only [Matrix.mulVec, dotProduct]
                rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), hi01, mul_one]
              rw [hmv]
              have h1 : M r i0 + (M r i0 + ∑ i ∈ Finset.univ.erase i0, M r i * v i) +
                  ∑ i ∈ Finset.univ.erase i0, M r i * v i =
                  (M r i0 + M r i0) +
                  ((∑ i ∈ Finset.univ.erase i0, M r i * v i) +
                    ∑ i ∈ Finset.univ.erase i0, M r i * v i) := by ring
              rw [h1, zmod2_add_self, zmod2_add_self, add_zero]⟩)
        invFun := fun p =>
          Matrix.of fun r i => if i = i0 then p.2.1 r i0 + p.1 r else p.2.1 r i
        left_inv := fun M => by
          ext r i
          simp only [Matrix.of_apply]
          split_ifs with hi
          · subst i
            calc
              M r i0 + M.mulVec v r + M.mulVec v r
                  = M r i0 + (M.mulVec v r + M.mulVec v r) := by ring
              _ = M r i0 := by rw [zmod2_add_self, add_zero]
          · rfl
        right_inv := fun ⟨y, ⟨M, hM⟩⟩ => by
          have hmv : (Matrix.of fun r i => if i = i0 then M r i0 + y r else M r i).mulVec v = y := by
            ext r
            change (∑ i : I, (if i = i0 then M r i0 + y r else M r i) * v i) = y r
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
            simp only [↓reduceIte, hi01, mul_one]
            have hrest : (∑ i ∈ Finset.univ.erase i0,
                (if i = i0 then M r i0 + y r else M r i) * v i) =
                ∑ i ∈ Finset.univ.erase i0, M r i * v i := by
              refine Finset.sum_congr rfl fun i hi => ?_
              simp [(Finset.mem_erase.mp hi).1]
            rw [hrest]
            have hM0 : M r i0 + ∑ i ∈ Finset.univ.erase i0, M r i * v i = 0 := by
              have hr := congrFun hM r
              simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hr
              rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), hi01, mul_one] at hr
              exact hr
            calc
              M r i0 + y r + ∑ i ∈ Finset.univ.erase i0, M r i * v i
                  = (M r i0 + ∑ i ∈ Finset.univ.erase i0, M r i * v i) + y r := by ring
              _ = 0 + y r := by rw [hM0]
              _ = y r := zero_add _
          refine Prod.ext hmv ?_
          apply Subtype.ext
          ext r i
          simp only [Matrix.of_apply, hmv]
          split_ifs with hi
          · subst i
            calc
              M r i0 + y r + y r = M r i0 + (y r + y r) := by ring
              _ = M r i0 := by rw [zmod2_add_self, add_zero]
          · rfl }
    have hc := Fintype.card_congr e
    rw [Fintype.card_prod] at hc
    have h1 : Fintype.card (Fin f → ZMod 2) = 2 ^ f := by simp
    have h2 : Fintype.card {M : Mat // M.mulVec v = 0} =
        (Finset.univ.filter (fun M : Mat => M.mulVec v = 0)).card := by
      rw [Fintype.card_subtype]
    rw [h1, h2] at hc
    exact hc.symm
  let BadMat : Finset Mat := Finset.univ.filter (fun M : Mat => ∃ v ∈ Bad, M.mulVec v = 0)
  have hsub : BadMat ⊆ Bad.biUnion (fun v => Finset.univ.filter (fun M : Mat => M.mulVec v = 0)) := by
    intro M hM
    rcases (Finset.mem_filter.mp hM).2 with ⟨v, hv, hMv⟩
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMv⟩⟩
  have hlt : BadMat.card < Fintype.card Mat := by
    have hposMat : 0 < Fintype.card Mat := Fintype.card_pos
    have hmul : 2 ^ f * BadMat.card < 2 ^ f * Fintype.card Mat := by
      calc
        2 ^ f * BadMat.card
            ≤ 2 ^ f * ∑ v ∈ Bad, (Finset.univ.filter (fun M : Mat => M.mulVec v = 0)).card :=
          Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le)
        _ = ∑ v ∈ Bad, 2 ^ f * (Finset.univ.filter (fun M : Mat => M.mulVec v = 0)).card := by
          rw [Finset.mul_sum]
        _ = ∑ _v ∈ Bad, Fintype.card Mat := Finset.sum_congr rfl fun v hv => hker_card v hv
        _ = Bad.card * Fintype.card Mat := by rw [Finset.sum_const, smul_eq_mul]
        _ < 2 ^ f * Fintype.card Mat := Nat.mul_lt_mul_of_pos_right hcard hposMat
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hexM : ∃ M : Mat, M ∉ BadMat := by
    by_contra hall
    push Not at hall
    have hEq : BadMat = Finset.univ := by
      ext M; simp [hall M]
    rw [hEq, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  rcases hexM with ⟨M, hM⟩
  refine ⟨M.mulVecLin, fun v hv h0 => ?_⟩
  apply hM
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, h0⟩

end PEqualNP.Outside.L_lib_655_aux

open PEqualNP.Outside.L_lib_655_aux in
theorem PEqualNP.Outside.L_lib_655 :
    ∀ (m b h : ℕ), 0 < b →
  let Q := 2^b
  let X := Fin m → Fin Q
  let width := m*Q^2 / 2^h + 1
  let distance := fun (x y : X) => ∑ j : Fin m, (Nat.dist (x j).val (y j).val)^2
  let bucket := fun (x y : X) => distance x y / width
  let f := 1+m+b*width
  let vec := fun (x : X) (i : Fin m × Fin b) => if (x i.1).val.testBit i.2.val then
    (1 : ZMod 2) else 0
  (∀ x y : X, bucket x y < 2^h) ∧
    ∃ H : ((Fin m × Fin b) → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2),
      (∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ width →
        H (vec x) ≠ H (vec y)) ∧
      ∀ p q : X × X, p ≠ q → bucket p.1 p.2 = bucket q.1 q.2 →
        (∀ j, (p.1 j).val + (p.2 j).val = (q.1 j).val + (q.2 j).val) →
        H (vec p.1) = H (vec q.1) →
        bucket p.1 q.2 < bucket p.1 p.2 ∧ bucket q.1 p.2 < bucket p.1 p.2 := by
  intro m b h _ Q X width distance bucket f vec
  have hw_pos : 0 < width := Nat.succ_pos _
  have hbucket_lt : ∀ x y : X, bucket x y < 2 ^ h := by
    intro x y
    have hdist_le : distance x y ≤ m * Q ^ 2 := by
      calc
        distance x y = ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2 := rfl
        _ ≤ ∑ _j : Fin m, Q ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : (x j).val < Q := (x j).2
          have h2 : (y j).val < Q := (y j).2
          have hd : Nat.dist (x j).val (y j).val ≤ Q := by
            by_cases hle : (x j).val ≤ (y j).val
            · rw [Nat.dist_eq_sub_of_le hle]; omega
            · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
          exact Nat.pow_le_pow_left hd 2
        _ = m * Q ^ 2 := by simp
    have hmul_lt : distance x y < width * 2 ^ h := by
      have hdiv := Nat.div_add_mod (m * Q ^ 2) (2 ^ h)
      have hmod : (m * Q ^ 2) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (by positivity)
      have hwid : width * 2 ^ h = 2 ^ h * (m * Q ^ 2 / 2 ^ h) + 2 ^ h := by
        dsimp only [width]; ring
      omega
    exact Nat.div_lt_of_lt_mul hmul_lt
  let supp : ((Fin m × Fin b) → ZMod 2) → Finset (Fin m) := fun v =>
    Finset.univ.filter (fun j : Fin m => ∃ r : Fin b, v (j, r) ≠ 0)
  let Bad : Finset ((Fin m × Fin b) → ZMod 2) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ (supp v).card ≤ width)
  have h0_not_bad : (0 : (Fin m × Fin b) → ZMod 2) ∉ Bad := by
    simp [Bad]
  have hBad_card : Bad.card < 2 ^ f := by
    let Sgood : Finset (Finset (Fin m)) := Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ width)
    have hsub : Bad ⊆ Sgood.biUnion (fun S => Finset.univ.filter (fun v : (Fin m × Fin b) → ZMod 2 => supp v ⊆ S)) := by
      intro v hv
      have hle : (supp v).card ≤ width := (Finset.mem_filter.mp hv).2.2
      exact Finset.mem_biUnion.mpr ⟨supp v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.refl _⟩⟩
    have hfib : ∀ S ∈ Sgood,
        (Finset.univ.filter (fun v : (Fin m × Fin b) → ZMod 2 => supp v ⊆ S)).card ≤ 2 ^ (b * width) := by
      intro S hS
      have hSle : S.card ≤ width := (Finset.mem_filter.mp hS).2
      have hbij : (Finset.univ.filter (fun v : (Fin m × Fin b) → ZMod 2 => supp v ⊆ S)).card =
          Fintype.card (↥S × Fin b → ZMod 2) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun v _ p => v (p.1.1, p.2)) (fun _ _ => Finset.mem_univ _) ?_ ?_
        · intro v1 hv1 v2 hv2 heq
          have hs1 := (Finset.mem_filter.mp hv1).2
          have hs2 := (Finset.mem_filter.mp hv2).2
          ext ⟨j, r⟩
          by_cases hj : j ∈ S
          · exact congrFun heq (⟨j, hj⟩, r)
          · have h1 : v1 (j, r) = 0 := by
              by_contra hne
              exact hj (hs1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hne⟩))
            have h2 : v2 (j, r) = 0 := by
              by_contra hne
              exact hj (hs2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hne⟩))
            rw [h1, h2]
        · intro g _
          let v : (Fin m × Fin b) → ZMod 2 := fun p => if hj : p.1 ∈ S then g (⟨p.1, hj⟩, p.2) else 0
          refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩, ?_⟩
          · rcases (Finset.mem_filter.mp hj).2 with ⟨r, hr⟩
            by_contra hnot
            simp only [v, hnot, ↓reduceDIte] at hr
            exact hr rfl
          · ext ⟨⟨j, hj⟩, r⟩
            simp only [v, hj, ↓reduceDIte]
      rw [hbij]
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
      exact Nat.pow_le_pow_right (by omega) (by rw [mul_comm]; exact Nat.mul_le_mul_left b hSle)
    have hle : Bad.card ≤ 2 ^ (m + b * width) := by
      calc
        Bad.card ≤ ∑ S ∈ Sgood,
            (Finset.univ.filter (fun v : (Fin m × Fin b) → ZMod 2 => supp v ⊆ S)).card :=
          le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        _ ≤ ∑ _S ∈ Sgood, 2 ^ (b * width) := Finset.sum_le_sum hfib
        _ = Sgood.card * 2 ^ (b * width) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ m * 2 ^ (b * width) := by
          have hScard : Sgood.card ≤ 2 ^ m := by
            calc
              Sgood.card ≤ (Finset.univ : Finset (Finset (Fin m))).card := Finset.card_filter_le _ _
              _ = 2 ^ m := by simp
          exact Nat.mul_le_mul_right _ hScard
        _ = 2 ^ (m + b * width) := by rw [pow_add]
    have hpow : 2 ^ f = 2 * 2 ^ (m + b * width) := by
      have hf : f = (m + b * width) + 1 := by dsimp only [f]; omega
      rw [hf, pow_succ]; ring
    have hpos : 0 < 2 ^ (m + b * width) := by positivity
    omega
  rcases exists_linear_map_avoiding Bad h0_not_bad hBad_card with ⟨H, hH⟩
  have hvec_inj : Function.Injective vec := by
    intro x y heq
    ext j
    apply eq_of_testBit_lt (x j).2 (y j).2
    intro r
    have hr := congrFun heq (j, r)
    simp only [vec] at hr
    cases h1 : (x j).val.testBit r.val <;> cases h2 : (y j).val.testBit r.val <;> simp_all
  have hH_sep : ∀ x y : X, x ≠ y →
      (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ width →
      H (vec x) ≠ H (vec y) := by
    intro x y hne hcard heq
    have hdiff_ne : vec x + vec y ≠ 0 := by
      intro h0
      apply hne
      apply hvec_inj
      ext p
      have hp := congrFun h0 p
      simp only [Pi.add_apply, Pi.zero_apply] at hp
      have h2 := congrArg (fun t => t + vec y p) hp
      simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at h2
      exact h2
    have hsupp_sub : supp (vec x + vec y) ⊆ Finset.univ.filter (fun j : Fin m => x j ≠ y j) := by
      intro j hj
      rcases (Finset.mem_filter.mp hj).2 with ⟨r, hr⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hxy => ?_⟩
      simp only [Pi.add_apply, vec, hxy, zmod2_add_self] at hr
      exact hr rfl
    have hmem : vec x + vec y ∈ Bad :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff_ne,
        le_trans (Finset.card_le_card hsupp_sub) hcard⟩
    have hH0 : H (vec x + vec y) = 0 := by
      rw [map_add, heq]
      ext i
      simp only [Pi.add_apply, Pi.zero_apply, zmod2_add_self]
    exact hH _ hmem hH0
  refine ⟨hbucket_lt, H, hH_sep, ?_⟩
  intro p q hpq hbuck hsum hHeq
  have hp1_ne : p.1 ≠ q.1 := by
    intro h1
    apply hpq
    refine Prod.ext h1 ?_
    ext j
    have hj := hsum j
    rw [h1] at hj
    omega
  have hwt_gt : width < (Finset.univ.filter (fun j : Fin m => p.1 j ≠ q.1 j)).card := by
    by_contra hle
    push Not at hle
    exact hH_sep p.1 q.1 hp1_ne hle hHeq
  have hdist_pq1 : width + 1 ≤ distance p.1 q.1 := by
    have h1 : (Finset.univ.filter (fun j : Fin m => p.1 j ≠ q.1 j)).card ≤ distance p.1 q.1 := by
      calc
        (Finset.univ.filter (fun j : Fin m => p.1 j ≠ q.1 j)).card
            = ∑ _j ∈ Finset.univ.filter (fun j : Fin m => p.1 j ≠ q.1 j), 1 := by simp
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => p.1 j ≠ q.1 j),
              (Nat.dist (p.1 j).val (q.1 j).val) ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hne : (p.1 j).val ≠ (q.1 j).val := fun h => (Finset.mem_filter.mp hj).2 (Fin.ext h)
          have hd : 1 ≤ Nat.dist (p.1 j).val (q.1 j).val := by
            by_cases hle : (p.1 j).val ≤ (q.1 j).val
            · rw [Nat.dist_eq_sub_of_le hle]; omega
            · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
          nlinarith
        _ ≤ ∑ j : Fin m, (Nat.dist (p.1 j).val (q.1 j).val) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    omega
  have hcross_eq : distance p.1 q.2 = distance q.1 p.2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : ((p.1 j).val : ℤ) + ((p.2 j).val : ℤ) = ((q.1 j).val : ℤ) + ((q.2 j).val : ℤ) := by
      exact_mod_cast hsum j
    have hsq : (((Nat.dist (p.1 j).val (q.2 j).val) ^ 2 : ℕ) : ℤ) =
        (((Nat.dist (q.1 j).val (p.2 j).val) ^ 2 : ℕ) : ℤ) := by
      rw [nat_dist_sq_int, nat_dist_sq_int]
      have hdiff : ((p.1 j).val : ℤ) - ((q.2 j).val : ℤ) = ((q.1 j).val : ℤ) - ((p.2 j).val : ℤ) := by
        linarith
      rw [hdiff]
    exact_mod_cast hsq
  have hpara : distance p.1 p.2 + distance q.1 q.2 = 2 * distance p.1 q.2 + 2 * distance p.1 q.1 := by
    have hpara_int : ((distance p.1 p.2 + distance q.1 q.2 : ℕ) : ℤ) =
        ((2 * distance p.1 q.2 + 2 * distance p.1 q.1 : ℕ) : ℤ) := by
      dsimp only [distance]
      push_cast
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : ((p.1 j).val : ℤ) + ((p.2 j).val : ℤ) = ((q.1 j).val : ℤ) + ((q.2 j).val : ℤ) := by
        exact_mod_cast hsum j
      have h1 := nat_dist_sq_int (p.1 j).val (p.2 j).val
      have h2 := nat_dist_sq_int (q.1 j).val (q.2 j).val
      have h3 := nat_dist_sq_int (p.1 j).val (q.2 j).val
      have h4 := nat_dist_sq_int (p.1 j).val (q.1 j).val
      push_cast at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      nlinarith
    exact_mod_cast hpara_int
  have hlt_prod : distance p.1 q.2 < bucket p.1 p.2 * width := by
    have hp_le : distance p.1 p.2 < (bucket p.1 p.2 + 1) * width := by
      have h1 := Nat.div_add_mod (distance p.1 p.2) width
      have h2 := Nat.mod_lt (distance p.1 p.2) hw_pos
      dsimp only [bucket]
      nlinarith
    have hq_le : distance q.1 q.2 < (bucket p.1 p.2 + 1) * width := by
      rw [hbuck]
      have h1 := Nat.div_add_mod (distance q.1 q.2) width
      have h2 := Nat.mod_lt (distance q.1 q.2) hw_pos
      dsimp only [bucket]
      nlinarith
    have hmul_add : (bucket p.1 p.2 + 1) * width = bucket p.1 p.2 * width + width := by ring
    omega
  have hlt1 : bucket p.1 q.2 < bucket p.1 p.2 :=
    Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt_prod)
  have hlt2 : bucket q.1 p.2 < bucket p.1 p.2 := by
    dsimp only [bucket]
    rw [← hcross_eq]
    exact hlt1
  exact ⟨hlt1, hlt2⟩

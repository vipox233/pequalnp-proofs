import PEqualNP.Defs
import Mathlib.Tactic
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_pcx_292_aux

private abbrev V (n : ℕ) := Bool × Fin n

private def mateOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (j : Fin r) (v : V n) : V n :=
  if v.1 then (false, (M j).symm v.2) else (true, M j v.2)

private def borderOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) : Finset (V n) :=
  S.filter (fun v => ∃ j : Fin r, mateOf M j v ∉ S)

private def inBand (n D : ℕ) : Bool :=
  decide (16 * Nat.dist (2 * D) n ≤ n)

private def rowsOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n))
    (x z : V n → Bool) (j : Fin r) : Bool :=
  let word := fun v : V n => if v ∈ S then x v else z v
  let D := (Finset.univ.filter (fun i : Fin n => word (false, i) ≠ word (true, M j i))).card
  inBand n D

private def dataOf (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) : ℕ × ℕ :=
  ((borderOf M S).card, (Finset.univ.image (rowsOf M S)).card)

private theorem part1_upper {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) :
    (dataOf n r M S).2 ≤ (n + 1) ^ r * 2 ^ (dataOf n r M S).1 := by
  unfold dataOf
  dsimp only
  let B := borderOf M S
  let intPair (j : Fin r) : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => (false, i) ∈ S ∧ (true, M j i) ∈ S)
  let enc : (V n → Bool) → (↥B → Bool) × (Fin r → Fin (n + 1)) := fun x =>
    (fun v => x v.val,
     fun j => ⟨((intPair j).filter (fun i => x (false, i) ≠ x (true, M j i))).card, by
       have hle : ((intPair j).filter (fun i => x (false, i) ≠ x (true, M j i))).card ≤ n := by
         calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
           _ = n := Fintype.card_fin n
       omega⟩)
  have hfactor : ∀ x1 x2 : V n → Bool, enc x1 = enc x2 → rowsOf M S x1 = rowsOf M S x2 := by
    intro x1 x2 heq
    have hB : ∀ v ∈ B, x1 v = x2 v := fun v hv => congrFun (congrArg Prod.fst heq) ⟨v, hv⟩
    have hD : ∀ j : Fin r,
        ((intPair j).filter (fun i => x1 (false, i) ≠ x1 (true, M j i))).card =
        ((intPair j).filter (fun i => x2 (false, i) ≠ x2 (true, M j i))).card := fun j =>
      congrArg Fin.val (congrFun (congrArg Prod.snd heq) j)
    funext z j
    unfold rowsOf
    dsimp only
    congr 1
    let P1 := Finset.univ.filter (fun i : Fin n =>
      (if (false, i) ∈ S then x1 (false, i) else z (false, i)) ≠
      (if (true, M j i) ∈ S then x1 (true, M j i) else z (true, M j i)))
    let P2 := Finset.univ.filter (fun i : Fin n =>
      (if (false, i) ∈ S then x2 (false, i) else z (false, i)) ≠
      (if (true, M j i) ∈ S then x2 (true, M j i) else z (true, M j i)))
    have hsplit : ∀ (P : Finset (Fin n)),
        P.card = (P ∩ intPair j).card + (P \ intPair j).card := fun P =>
      (Finset.card_inter_add_card_sdiff P (intPair j)).symm
    change P1.card = P2.card
    rw [hsplit P1, hsplit P2]
    have hint1 : P1 ∩ intPair j = (intPair j).filter (fun i => x1 (false, i) ≠ x1 (true, M j i)) := by
      ext i
      simp only [P1, intPair, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, h1, h2⟩
        simp only [h1, h2, ↓reduceIte] at hne
        exact ⟨⟨h1, h2⟩, hne⟩
      · rintro ⟨⟨h1, h2⟩, hne⟩
        refine ⟨?_, h1, h2⟩
        simp only [h1, h2, ↓reduceIte]
        exact hne
    have hint2 : P2 ∩ intPair j = (intPair j).filter (fun i => x2 (false, i) ≠ x2 (true, M j i)) := by
      ext i
      simp only [P2, intPair, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, h1, h2⟩
        simp only [h1, h2, ↓reduceIte] at hne
        exact ⟨⟨h1, h2⟩, hne⟩
      · rintro ⟨⟨h1, h2⟩, hne⟩
        refine ⟨?_, h1, h2⟩
        simp only [h1, h2, ↓reduceIte]
        exact hne
    have hsdiff : P1 \ intPair j = P2 \ intPair j := by
      ext i
      simp only [P1, P2, intPair, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
      constructor <;> rintro ⟨hne, hnot⟩ <;> refine ⟨?_, hnot⟩
      · by_cases h1 : (false, i) ∈ S
        · have h2 : (true, M j i) ∉ S := hnot h1
          have hmemB : (false, i) ∈ B := by
            simp only [B, borderOf, Finset.mem_filter]
            exact ⟨h1, j, by simp [mateOf, h2]⟩
          simp only [h1, h2, ↓reduceIte] at hne ⊢
          rwa [← hB _ hmemB]
        · by_cases h2 : (true, M j i) ∈ S
          · have hmemB : (true, M j i) ∈ B := by
              simp only [B, borderOf, Finset.mem_filter]
              exact ⟨h2, j, by simp [mateOf, h1]⟩
            simp only [h1, h2, ↓reduceIte] at hne ⊢
            rwa [← hB _ hmemB]
          · simp only [h1, h2, ↓reduceIte] at hne ⊢; exact hne
      · by_cases h1 : (false, i) ∈ S
        · have h2 : (true, M j i) ∉ S := hnot h1
          have hmemB : (false, i) ∈ B := by
            simp only [B, borderOf, Finset.mem_filter]
            exact ⟨h1, j, by simp [mateOf, h2]⟩
          simp only [h1, h2, ↓reduceIte] at hne ⊢
          rwa [hB _ hmemB]
        · by_cases h2 : (true, M j i) ∈ S
          · have hmemB : (true, M j i) ∈ B := by
              simp only [B, borderOf, Finset.mem_filter]
              exact ⟨h2, j, by simp [mateOf, h1]⟩
            simp only [h1, h2, ↓reduceIte] at hne ⊢
            rwa [hB _ hmemB]
          · simp only [h1, h2, ↓reduceIte] at hne ⊢; exact hne
    rw [hint1, hint2, hD j, hsdiff]
  have hle : (Finset.univ.image (rowsOf M S)).card ≤ (Finset.univ.image enc).card := by
    have hsurj : ∀ y ∈ Finset.univ.image (rowsOf M S),
        ∃ e ∈ Finset.univ.image enc, ∃ x : V n → Bool, enc x = e ∧ rowsOf M S x = y := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, _, rfl⟩ := hy
      exact ⟨enc x, Finset.mem_image_of_mem enc (Finset.mem_univ x), x, rfl, rfl⟩
    classical
    let g : ((↥B → Bool) × (Fin r → Fin (n + 1))) → ((V n → Bool) → Fin r → Bool) := fun e =>
      if h : ∃ x, enc x = e then rowsOf M S h.choose else fun _ _ => false
    have hsub : Finset.univ.image (rowsOf M S) ⊆ (Finset.univ.image enc).image g := by
      intro y hy
      rw [Finset.mem_image] at hy ⊢
      obtain ⟨x, _, rfl⟩ := hy
      refine ⟨enc x, Finset.mem_image_of_mem enc (Finset.mem_univ x), ?_⟩
      have hex : ∃ x', enc x' = enc x := ⟨x, rfl⟩
      simp only [g, dif_pos hex]
      exact hfactor hex.choose x hex.choose_spec
    calc (Finset.univ.image (rowsOf M S)).card
        ≤ ((Finset.univ.image enc).image g).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.image enc).card := Finset.card_image_le
  have hcard_enc : (Finset.univ.image enc).card ≤ (n + 1) ^ r * 2 ^ B.card := by
    calc (Finset.univ.image enc).card
        ≤ Fintype.card ((↥B → Bool) × (Fin r → Fin (n + 1))) := Finset.card_le_univ _
      _ = 2 ^ B.card * (n + 1) ^ r := by
          simp [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]
      _ = (n + 1) ^ r * 2 ^ B.card := Nat.mul_comm _ _
  exact le_trans hle hcard_enc

private theorem inBand_iff {n D : ℕ} :
    inBand n D = true ↔ 15 * n ≤ 32 * D ∧ 32 * D ≤ 17 * n := by
  unfold inBand
  simp only [decide_eq_true_eq]
  rw [Nat.dist_eq_max_sub_min]
  by_cases h : 2 * D ≤ n
  · rw [max_eq_right h, min_eq_left h]; omega
  · rw [max_eq_left (by omega : n ≤ 2 * D), min_eq_right (by omega : n ≤ 2 * D)]; omega

private theorem single_band_lower {n r : ℕ} (hn : 32 ≤ n)
    (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) (j : Fin r) :
    let Bj := S.filter (fun v => mateOf M j v ∉ S)
    2 ^ Bj.card ≤ 2 * (dataOf n r M S).2 := by
  dsimp only
  set Bj := S.filter (fun v => mateOf M j v ∉ S)
  let I : Finset (Fin n) := Finset.univ.filter (fun i => (false, i) ∈ S ∧ (true, M j i) ∈ S)
  let O : Finset (Fin n) := Finset.univ.filter (fun i => (false, i) ∉ S ∧ (true, M j i) ∉ S)
  let P : Finset (Fin n) := Finset.univ.filter (fun i =>
    ((false, i) ∈ S ∧ (true, M j i) ∉ S) ∨ ((false, i) ∉ S ∧ (true, M j i) ∈ S))
  have hP_card : P.card = Bj.card := by
    refine Finset.card_bij (fun i _ => if (false, i) ∈ S then (false, i) else (true, M j i)) ?_ ?_ ?_
    · intro i hi
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Bj, Finset.mem_filter]
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1]; exact ⟨h1, by simp [mateOf, h2]⟩
      · rw [if_neg h1]; exact ⟨h2, by simp [mateOf, h1]⟩
    · intro i1 hi1 i2 hi2 heq
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
      split_ifs at heq with h1 h2 h2
      · exact (Prod.mk.inj heq).2
      · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
      · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
      · exact (M j).injective (Prod.mk.inj heq).2
    · intro v hv
      simp only [Bj, Finset.mem_filter] at hv
      rcases v with ⟨b, idx⟩
      cases b
      · simp only [mateOf, Bool.false_eq_true, ↓reduceIte] at hv
        refine ⟨idx, ?_, by simp [hv.1]⟩
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl hv
      · simp only [mateOf, ↓reduceIte] at hv
        refine ⟨(M j).symm idx, ?_, ?_⟩
        · simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨hv.2, by simpa using hv.1⟩
        · simp [hv.2]
  have hsum_n : I.card + P.card + O.card = n := by
    have hdisj1 : Disjoint I P := by
      rw [Finset.disjoint_left]; intro i hi hp
      simp only [I, P, Finset.mem_filter, Finset.mem_univ, true_and] at hi hp
      tauto
    have hdisj2 : Disjoint (I ∪ P) O := by
      rw [Finset.disjoint_left]; intro i hip ho
      simp only [I, P, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hip ho
      tauto
    have hunion : I ∪ P ∪ O = Finset.univ := by
      ext i
      simp only [I, P, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_cases h1 : (false, i) ∈ S <;> by_cases h2 : (true, M j i) ∈ S <;> tauto
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      hunion, Finset.card_univ, Fintype.card_fin]
  by_cases hp0 : P.card = 0
  · rw [← hP_card, hp0, pow_zero]
    have hne : (Finset.univ.image (rowsOf M S)).Nonempty :=
      ⟨rowsOf M S (fun _ => false), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hpos : 0 < (dataOf n r M S).2 := Finset.card_pos.mpr hne
    omega
  · have hp_pos : 0 < P.card := Nat.pos_of_ne_zero hp0
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hp_pos
    set T := 17 * n / 32
    set L := (15 * n + 31) / 32
    have hTL : T + L = n := by omega
    have hT_in : inBand n T = true := by rw [inBand_iff]; omega
    have hT_out : inBand n (T + 1) = false := by
      rw [Bool.eq_false_iff]; intro h; rw [inBand_iff] at h; omega
    have hL_in : inBand n L = true := by rw [inBand_iff]; omega
    have hL_out : inBand n (L - 1) = false := by
      rw [Bool.eq_false_iff]; intro h; rw [inBand_iff] at h; omega
    set c := min I.card T
    have hc_le : c ≤ I.card := min_le_left _ _
    obtain ⟨I_flip, hI_flip_sub, hI_flip_card⟩ := Finset.exists_subset_card_eq hc_le

    let xOf : (Finset (Fin n)) → (V n → Bool) := fun U v =>
      match v with
      | (false, i) =>
        if i ∈ I then decide (i ∈ I_flip)
        else if i ∈ P then decide (i ∈ U)
        else false
      | (true, idx) =>
        let i := (M j).symm idx
        if i ∈ I then false
        else if i ∈ P then decide (i ∈ U)
        else false

    let dom := (P.erase i0).powerset
    have hdom_card : dom.card = 2 ^ (P.card - 1) := by
      rw [Finset.card_powerset, Finset.card_erase_of_mem hi0]
    have hinj : Set.InjOn (fun U => rowsOf M S (xOf U)) (dom : Set (Finset (Fin n))) := by
      intro U1 hU1 U2 hU2 heq
      simp only [Finset.mem_coe, dom, Finset.mem_powerset] at hU1 hU2
      by_contra hne
      let Diff := symmDiff U1 U2
      have hDiff_sub : Diff ⊆ P.erase i0 := by
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact hU1 h1
        · exact hU2 h2
      have hDiff_P : Diff ⊆ P := Finset.Subset.trans hDiff_sub (Finset.erase_subset _ _)
      have hDiff_pos : 0 < Diff.card := by
        rw [Finset.card_pos]
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        exact hne (Finset.symmDiff_eq_empty.mp hemp)
      set k := Diff.card
      have hk_lt_P : k < P.card := by
        have h1 : Diff.card ≤ (P.erase i0).card := Finset.card_le_card hDiff_sub
        rw [Finset.card_erase_of_mem hi0] at h1
        omega
      let Same := (P \ Diff) ∪ O
      have hSame_card : Same.card = O.card + (P.card - k) := by
        have hdisj : Disjoint (P \ Diff) O := by
          rw [Finset.disjoint_left]; intro i hi ho
          simp only [Finset.mem_sdiff, P, O, Finset.mem_filter, Finset.mem_univ, true_and] at hi ho
          tauto
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff, Finset.inter_eq_left.mpr hDiff_P, add_comm]
      set Smax := O.card + (P.card - k)
      set m1 := (k - 1) / 2

      have hex_sm : ∃ (s m : ℕ), s ≤ Smax ∧ m ≤ k ∧
          inBand n (c + s + m) ≠ inBand n (c + s + (k - m)) := by
        by_cases hcase1 : T ≤ I.card
        · refine ⟨0, 0, Nat.zero_le _, Nat.zero_le _, ?_⟩
          have hcT : c = T := min_eq_right hcase1
          rw [hcT, add_zero, add_zero, Nat.sub_zero, hT_in]
          intro hcontra
          have h1 := inBand_iff.mp hcontra.symm
          omega
        · have hcI : c = I.card := min_eq_left (by omega)
          have hsum_c : c + Smax = n - k := by omega
          by_cases hcase2 : T < c + m1
          · refine ⟨0, T - c, Nat.zero_le _, by omega, ?_⟩
            have h1 : c + 0 + (T - c) = T := by omega
            have h2 : T + 1 ≤ c + 0 + (k - (T - c)) := by omega
            rw [h1, hT_in]
            intro hcontra
            have h3 := inBand_iff.mp hcontra.symm
            omega
          · by_cases hcase3 : T ≤ c + m1 + Smax
            · refine ⟨T - (c + m1), m1, by omega, by omega, ?_⟩
              have h1 : c + (T - (c + m1)) + m1 = T := by omega
              have h2 : T + 1 ≤ c + (T - (c + m1)) + (k - m1) := by omega
              rw [h1, hT_in]
              intro hcontra
              have h3 := inBand_iff.mp hcontra.symm
              omega
            · refine ⟨Smax, T + 1 - (c + Smax), le_rfl, by omega, ?_⟩
              have h1 : c + Smax + (T + 1 - (c + Smax)) = T + 1 := by omega
              have h2_lo : L ≤ c + Smax + (k - (T + 1 - (c + Smax))) := by omega
              have h2_hi : c + Smax + (k - (T + 1 - (c + Smax))) ≤ T := by omega
              rw [h1, hT_out]
              have hin2 : inBand n (c + Smax + (k - (T + 1 - (c + Smax)))) = true := by
                rw [inBand_iff]; omega
              rw [hin2]; decide
      obtain ⟨s, m, hs_le, hm_le, hsep⟩ := hex_sm
      have hs_le' : s ≤ Same.card := by rw [hSame_card]; exact hs_le
      obtain ⟨Same_sub, hSame_sub, hSame_scard⟩ := Finset.exists_subset_card_eq hs_le'
      obtain ⟨Diff_sub, hDiff_sub, hDiff_mcard⟩ := Finset.exists_subset_card_eq hm_le

      let wantP : Fin n → Bool := fun i =>
        if i ∈ Diff then xor (decide (i ∈ U1)) (decide (i ∈ Diff_sub))
        else xor (decide (i ∈ U1)) (decide (i ∈ Same_sub))
      let z : V n → Bool := fun v =>
        match v with
        | (false, i) =>
          if i ∈ O then decide (i ∈ Same_sub)
          else if i ∈ P then wantP i
          else false
        | (true, idx) =>
          let i := (M j).symm idx
          if i ∈ O then false
          else if i ∈ P then wantP i
          else false
      have hcount : ∀ (U : Finset (Fin n)) (hU : U = U1 ∨ U = U2),
          (Finset.univ.filter (fun i : Fin n =>
            (if (false, i) ∈ S then xOf U (false, i) else z (false, i)) ≠
            (if (true, M j i) ∈ S then xOf U (true, M j i) else z (true, M j i)))).card =
          c + s + (if U = U1 then m else k - m) := by
        intro U hU
        let Mset := Finset.univ.filter (fun i : Fin n =>
          (if (false, i) ∈ S then xOf U (false, i) else z (false, i)) ≠
          (if (true, M j i) ∈ S then xOf U (true, M j i) else z (true, M j i)))
        have hM_eq : Mset = I_flip ∪ Same_sub ∪ (if U = U1 then Diff_sub else Diff \ Diff_sub) := by
          ext i
          simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          by_cases h1 : (false, i) ∈ S <;> by_cases h2 : (true, M j i) ∈ S
          ·
            have hiI : i ∈ I := by simp [I, h1, h2]
            have hiP : i ∉ P := by simp [P, h1, h2]
            have hiO : i ∉ O := by simp [O, h1, h2]
            have hns : i ∉ Same_sub := fun h => by
              have := hSame_sub h
              simp only [Same, Finset.mem_union, Finset.mem_sdiff] at this
              rcases this with ⟨hp, _⟩ | ho
              · exact hiP hp
              · exact hiO ho
            have hnd : i ∉ Diff := fun h => hiP (hDiff_P h)
            have hnd_sub : i ∉ (if U = U1 then Diff_sub else Diff \ Diff_sub) := by
              split_ifs
              · exact fun h => hnd (hDiff_sub h)
              · exact fun h => hnd (Finset.sdiff_subset h)
            simp only [h1, h2, ↓reduceIte, xOf, hiI, Equiv.symm_apply_apply, hns, hnd_sub, or_false]
            simp
          ·
            have hiI : i ∉ I := by simp [I, h1, h2]
            have hiP : i ∈ P := by simp [P, h1, h2]
            have hiO : i ∉ O := by simp [O, h1, h2]
            have hni : i ∉ I_flip := fun h => hiI (hI_flip_sub h)
            simp only [h1, h2, ↓reduceIte, xOf, z, hiI, hiP, hiO, Equiv.symm_apply_apply, hni, false_or]
            by_cases hiD : i ∈ Diff
            · have hns : i ∉ Same_sub := fun h => by
                have := hSame_sub h
                simp only [Same, Finset.mem_union, Finset.mem_sdiff] at this
                rcases this with ⟨_, hnd⟩ | ho
                · exact hnd hiD
                · exact hiO ho
              simp only [wantP, hiD, ↓reduceIte, hns, false_or]
              rcases hU with hUeq | hUeq
              · subst U
                simp only [↓reduceIte]
                cases h1b : decide (i ∈ U1) <;> cases h2b : decide (i ∈ Diff_sub) <;> simp_all
              · subst U
                simp only [Ne.symm hne, ↓reduceIte, Finset.mem_sdiff, hiD, true_and]
                have hflip : decide (i ∈ U2) = !(decide (i ∈ U1)) := by
                  rw [Finset.mem_symmDiff] at hiD
                  by_cases hu1 : i ∈ U1 <;> by_cases hu2 : i ∈ U2 <;> simp_all
                rw [hflip]
                cases h1b : decide (i ∈ U1) <;> cases h2b : decide (i ∈ Diff_sub) <;> simp_all
            · have hnd_sub : i ∉ (if U = U1 then Diff_sub else Diff \ Diff_sub) := by
                split_ifs
                · exact fun h => hiD (hDiff_sub h)
                · exact fun h => hiD (Finset.sdiff_subset h)
              simp only [wantP, hiD, ↓reduceIte, hnd_sub, or_false]
              have hsameU : decide (i ∈ U) = decide (i ∈ U1) := by
                rcases hU with hUeq | hUeq
                · rw [hUeq]
                · rw [hUeq]
                  rw [Finset.mem_symmDiff] at hiD
                  by_cases hu1 : i ∈ U1 <;> by_cases hu2 : i ∈ U2 <;> simp_all
              rw [hsameU]
              cases h1b : decide (i ∈ U1) <;> cases h2b : decide (i ∈ Same_sub) <;> simp_all
          ·
            have hiI : i ∉ I := by simp [I, h1, h2]
            have hiP : i ∈ P := by simp [P, h1, h2]
            have hiO : i ∉ O := by simp [O, h1, h2]
            have hni : i ∉ I_flip := fun h => hiI (hI_flip_sub h)
            simp only [h1, h2, ↓reduceIte, xOf, z, hiI, hiP, hiO, Equiv.symm_apply_apply, hni, false_or]
            by_cases hiD : i ∈ Diff
            · have hns : i ∉ Same_sub := fun h => by
                have := hSame_sub h
                simp only [Same, Finset.mem_union, Finset.mem_sdiff] at this
                rcases this with ⟨_, hnd⟩ | ho
                · exact hnd hiD
                · exact hiO ho
              simp only [wantP, hiD, ↓reduceIte, hns, false_or]
              rcases hU with hUeq | hUeq
              · subst U
                simp only [↓reduceIte]
                cases h1b : decide (i ∈ U1) <;> cases h2b : decide (i ∈ Diff_sub) <;> simp_all
              · subst U
                simp only [Ne.symm hne, ↓reduceIte, Finset.mem_sdiff, hiD, true_and]
                have hflip : decide (i ∈ U2) = !(decide (i ∈ U1)) := by
                  rw [Finset.mem_symmDiff] at hiD
                  by_cases hu1 : i ∈ U1 <;> by_cases hu2 : i ∈ U2 <;> simp_all
                rw [hflip]
                cases h1b : decide (i ∈ U1) <;> cases h2b : decide (i ∈ Diff_sub) <;> simp_all
            · have hnd_sub : i ∉ (if U = U1 then Diff_sub else Diff \ Diff_sub) := by
                split_ifs
                · exact fun h => hiD (hDiff_sub h)
                · exact fun h => hiD (Finset.sdiff_subset h)
              simp only [wantP, hiD, ↓reduceIte, hnd_sub, or_false]
              have hsameU : decide (i ∈ U) = decide (i ∈ U1) := by
                rcases hU with hUeq | hUeq
                · rw [hUeq]
                · rw [hUeq]
                  rw [Finset.mem_symmDiff] at hiD
                  by_cases hu1 : i ∈ U1 <;> by_cases hu2 : i ∈ U2 <;> simp_all
              rw [hsameU]
              cases h1b : decide (i ∈ U1) <;> cases h2b : decide (i ∈ Same_sub) <;> simp_all
          ·
            have hiI : i ∉ I := by simp [I, h1, h2]
            have hiP : i ∉ P := by simp [P, h1, h2]
            have hiO : i ∈ O := by simp [O, h1, h2]
            have hni : i ∉ I_flip := fun h => hiI (hI_flip_sub h)
            have hnd : i ∉ Diff := fun h => hiP (hDiff_P h)
            have hnd_sub : i ∉ (if U = U1 then Diff_sub else Diff \ Diff_sub) := by
              split_ifs
              · exact fun h => hnd (hDiff_sub h)
              · exact fun h => hnd (Finset.sdiff_subset h)
            simp only [h1, h2, ↓reduceIte, z, hiO, Equiv.symm_apply_apply, hni, hnd_sub, false_or, or_false]
            simp
        have hd1 : Disjoint I_flip Same_sub := by
          rw [Finset.disjoint_left]; intro i hi1 hi2
          have hI1 := hI_flip_sub hi1
          have hS2 := hSame_sub hi2
          simp only [I, Same, P, O, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter,
            Finset.mem_univ, true_and] at hI1 hS2
          tauto
        have hd2 : Disjoint (I_flip ∪ Same_sub) (if U = U1 then Diff_sub else Diff \ Diff_sub) := by
          rw [Finset.disjoint_left]; intro i hi1 hi2
          have hiD : i ∈ Diff := by
            split_ifs at hi2
            · exact hDiff_sub hi2
            · exact Finset.sdiff_subset hi2
          have hiP := hDiff_P hiD
          rcases Finset.mem_union.mp hi1 with hI1 | hS1
          · have := hI_flip_sub hI1
            simp only [I, P, Finset.mem_filter, Finset.mem_univ, true_and] at this hiP; tauto
          · have := hSame_sub hS1
            simp only [Same, P, O, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter,
              Finset.mem_univ, true_and] at this hiP
            tauto
        change Mset.card = _
        rw [hM_eq, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
          hI_flip_card, hSame_scard]
        by_cases hU1 : U = U1
        · rw [if_pos hU1, if_pos hU1, hDiff_mcard]
        · rw [if_neg hU1, if_neg hU1, Finset.card_sdiff, Finset.inter_eq_left.mpr hDiff_sub, hDiff_mcard]
      have hrow1 : rowsOf M S (xOf U1) z j = inBand n (c + s + m) := by
        unfold rowsOf; dsimp only
        rw [hcount U1 (Or.inl rfl), if_pos rfl]
      have hrow2 : rowsOf M S (xOf U2) z j = inBand n (c + s + (k - m)) := by
        unfold rowsOf; dsimp only
        rw [hcount U2 (Or.inr rfl), if_neg (Ne.symm hne)]
      have heqj : rowsOf M S (xOf U1) z j = rowsOf M S (xOf U2) z j := congrFun (congrFun heq z) j
      rw [hrow1, hrow2] at heqj
      exact hsep heqj
    have hcard_le : 2 ^ (P.card - 1) ≤ (dataOf n r M S).2 := by
      unfold dataOf; dsimp only
      have hsub : dom.image (fun U => rowsOf M S (xOf U)) ⊆ Finset.univ.image (rowsOf M S) := by
        intro y hy
        rw [Finset.mem_image] at hy ⊢
        obtain ⟨U, _, rfl⟩ := hy
        exact ⟨xOf U, Finset.mem_univ _, rfl⟩
      calc 2 ^ (P.card - 1) = dom.card := hdom_card.symm
        _ = (dom.image (fun U => rowsOf M S (xOf U))).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ.image (rowsOf M S)).card := Finset.card_le_card hsub
    rw [← hP_card]
    have hpow : 2 ^ P.card = 2 * 2 ^ (P.card - 1) := by
      have : P.card = (P.card - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    omega

private theorem part1_lower {n r : ℕ} (hn : 32 ≤ n)
    (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) :
    2 ^ (dataOf n r M S).1 ≤ (2 * (dataOf n r M S).2) ^ r := by
  have hsub : borderOf M S ⊆ Finset.univ.biUnion (fun j : Fin r => S.filter (fun v => mateOf M j v ∉ S)) := by
    intro v hv
    simp only [borderOf, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨hvS, j, hj⟩ := hv
    exact ⟨j, hvS, hj⟩
  have hcard_le : (borderOf M S).card ≤ ∑ j : Fin r, (S.filter (fun v => mateOf M j v ∉ S)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc 2 ^ (dataOf n r M S).1
      ≤ 2 ^ (∑ j : Fin r, (S.filter (fun v => mateOf M j v ∉ S)).card) := Nat.pow_le_pow_right (by omega) hcard_le
    _ = ∏ j : Fin r, 2 ^ (S.filter (fun v => mateOf M j v ∉ S)).card := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ _j : Fin r, (2 * (dataOf n r M S).2) := Finset.prod_le_prod' fun j _ => single_band_lower hn M S j
    _ = (2 * (dataOf n r M S).2) ^ r := by simp

private theorem orbit_period_exists {n : ℕ} (σ : Equiv.Perm (Fin n)) (x0 : Fin n) :
    ∃ k : ℕ, 0 < k ∧ (σ ^ k) x0 = x0 := by
  have hnot : ¬ Function.Injective (fun k : ℕ => (σ ^ k) x0) := fun hinj => by
    have := Finite.of_injective _ hinj
    exact not_finite ℕ
  rw [Function.Injective] at hnot
  push_neg at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨b - a, by omega, ?_⟩
    have h1 : (σ ^ a) ((σ ^ (b - a)) x0) = (σ ^ a) x0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
      exact hab.symm
    exact (σ ^ a).injective h1
  · refine ⟨a - b, by omega, ?_⟩
    have h1 : (σ ^ b) ((σ ^ (a - b)) x0) = (σ ^ b) x0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hgt)]
      exact hab
    exact (σ ^ b).injective h1

private noncomputable def orbitList {n : ℕ} (σ : Equiv.Perm (Fin n)) (x0 : Fin n) : List (Fin n) :=
  let L := Nat.find (orbit_period_exists σ x0)
  (List.range L).map (fun t => (σ ^ t) x0)

private theorem orbitList_spec {n : ℕ} (σ : Equiv.Perm (Fin n)) (x0 : Fin n) :
    let orb := orbitList σ x0
    0 < orb.length ∧
    orb.Nodup ∧
    x0 ∈ orb ∧
    (∀ y ∈ orb, σ y ∈ orb) ∧
    (∀ y ∈ orb, σ.symm y ∈ orb) ∧
    ∀ idx (h : idx < orb.length),
      σ (orb[idx]) = orb[(idx + 1) % orb.length]'(Nat.mod_lt _ (by omega)) := by
  unfold orbitList
  have hex := orbit_period_exists σ x0
  set L := Nat.find (orbit_period_exists σ x0)
  have hL_spec : 0 < L ∧ (σ ^ L) x0 = x0 := Nat.find_spec (orbit_period_exists σ x0)
  have hL_min : ∀ m < L, 0 < m → (σ ^ m) x0 ≠ x0 := fun m hm hm0 => by
    have := Nat.find_min (orbit_period_exists σ x0) hm
    push_neg at this
    exact this hm0
  have hlen : ((List.range L).map (fun t => (σ ^ t) x0)).length = L := by simp
  have hnodup : ((List.range L).map (fun t => (σ ^ t) x0)).Nodup := by
    rw [List.nodup_map_iff_inj_on (List.nodup_range)]
    intro a ha b hb heq
    rw [List.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (σ ^ (b - a)) x0 = x0 := by
        apply (σ ^ a).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
        exact heq.symm
      exact hL_min (b - a) (by omega) (by omega) h1
    · have h1 : (σ ^ (a - b)) x0 = x0 := by
        apply (σ ^ b).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hgt)]
        exact heq
      exact hL_min (a - b) (by omega) (by omega) h1
  have hnext : ∀ idx (h : idx < L),
      σ ((σ ^ idx) x0) = (σ ^ ((idx + 1) % L)) x0 := by
    intro idx hidx
    have hstep : σ ((σ ^ idx) x0) = (σ ^ (idx + 1)) x0 := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hstep]
    by_cases hlt : idx + 1 < L
    · rw [Nat.mod_eq_of_lt hlt]
    · have heqL : idx + 1 = L := by omega
      rw [heqL, Nat.mod_self, hL_spec.2]; rfl
  refine ⟨by rw [hlen]; exact hL_spec.1, hnodup, ?_, ?_, ?_, ?_⟩
  · rw [List.mem_map]; exact ⟨0, List.mem_range.mpr hL_spec.1, rfl⟩
  · intro y hy
    rw [List.mem_map] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    rw [List.mem_range] at ht
    exact ⟨(t + 1) % L, List.mem_range.mpr (Nat.mod_lt _ hL_spec.1), (hnext t ht).symm⟩
  · intro y hy
    rw [List.mem_map] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    rw [List.mem_range] at ht
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨L - 1, List.mem_range.mpr (by omega), ?_⟩
      apply σ.injective
      rw [Equiv.apply_symm_apply, hnext (L - 1) (by omega)]
      have : (L - 1 + 1) % L = 0 := by
        have : L - 1 + 1 = L := by omega
        rw [this, Nat.mod_self]
      rw [this]
    · refine ⟨t - 1, List.mem_range.mpr (by omega), ?_⟩
      apply σ.injective
      rw [Equiv.apply_symm_apply, hnext (t - 1) (by omega)]
      have : (t - 1 + 1) % L = t := by
        have : t - 1 + 1 = t := by omega
        rw [this, Nat.mod_eq_of_lt ht]
      rw [this]
  · intro idx h
    have hidx : idx < L := by rw [← hlen]; exact h
    simp only [List.getElem_map, List.getElem_range]
    simpa [hlen] using hnext idx hidx

private theorem decomp_cycles {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ (rem : Finset (Fin n)), (∀ x ∈ rem, σ x ∈ rem) →
      ∃ blocks : List (List (Fin n)),
        (∀ B ∈ blocks, 0 < B.length ∧ B.Nodup ∧
          (∀ y ∈ B, σ y ∈ B) ∧ (∀ y ∈ B, σ.symm y ∈ B) ∧
          ∀ idx (h : idx < B.length), σ B[idx] = B[(idx + 1) % B.length]'(Nat.mod_lt _ (by omega))) ∧
        blocks.flatten.Nodup ∧
        (∀ x, x ∈ blocks.flatten ↔ x ∈ rem) := by
  intro rem
  induction hcard : rem.card using Nat.strong_induction_on generalizing rem with
  | ind m ih =>
    intro hclosed
    by_cases hemp : rem = ∅
    · subst hemp
      refine ⟨[], ?_, List.nodup_nil, fun _ => by simp⟩
      intro _ h
      cases h
    · have hne : rem.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      let x0 := hne.choose
      have hx0 : x0 ∈ rem := hne.choose_spec
      let orb := orbitList σ x0
      have horb := orbitList_spec σ x0
      have horb_sub : ∀ y ∈ orb, y ∈ rem := by
        intro y hy
        unfold orb orbitList at hy
        rw [List.mem_map] at hy
        obtain ⟨t, ht, rfl⟩ := hy
        clear ht
        induction t with
        | zero => exact hx0
        | succ t' iht =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact hclosed _ iht
      let rem' := rem \ orb.toFinset
      have hlt : rem'.card < m := by
        rw [← hcard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, fun heq => ?_⟩
        have hx0_in : x0 ∈ rem' := by rw [heq]; exact hx0
        simp only [rem', Finset.mem_sdiff, List.mem_toFinset] at hx0_in
        exact hx0_in.2 horb.2.2.1
      have hclosed' : ∀ x ∈ rem', σ x ∈ rem' := by
        intro x hx
        simp only [rem', Finset.mem_sdiff, List.mem_toFinset] at hx ⊢
        refine ⟨hclosed x hx.1, fun hmem => hx.2 ?_⟩
        have := horb.2.2.2.2.1 (σ x) hmem
        simpa using this
      obtain ⟨rest, hrest_ok, hrest_nd, hrest_mem⟩ := ih rem'.card hlt rem' rfl hclosed'
      refine ⟨orb :: rest, ?_, ?_, ?_⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hmem
        · exact ⟨horb.1, horb.2.1, horb.2.2.2.1, horb.2.2.2.2.1, horb.2.2.2.2.2⟩
        · exact hrest_ok B hmem
      · rw [List.flatten_cons, List.nodup_append]
        refine ⟨horb.2.1, hrest_nd, fun a ha b hb heq => ?_⟩
        subst heq
        have hb' := (hrest_mem a).mp hb
        simp only [rem', Finset.mem_sdiff, List.mem_toFinset] at hb'
        exact hb'.2 ha
      · intro x
        simp only [List.flatten_cons, List.mem_append, hrest_mem, rem', Finset.mem_sdiff, List.mem_toFinset]
        by_cases hx : x ∈ orb
        · simp [hx, horb_sub x hx]
        · simp [hx]

private theorem part2_two_matchings (n : ℕ) (hn : 32 ≤ n) (M : Fin 2 → Equiv.Perm (Fin n)) :
    ∃ order : V n ≃ Fin (2 * n), ∀ t : ℕ,
      (dataOf n 2 M (Finset.univ.filter (fun v => (order v).val < t))).2 ≤ 4 * (n + 1) ^ 2 := by
  let σ : Equiv.Perm (Fin n) := (M 0).trans (M 1).symm
  obtain ⟨blocks, hblocks_ok, hflat_nd, hflat_mem⟩ := decomp_cycles σ Finset.univ (fun _ _ => Finset.mem_univ _)
  let altOf (B : List (Fin n)) : List (V n) := B.flatMap (fun i => [(false, i), (true, M 0 i)])
  let verts : List (V n) := (blocks.map altOf).flatten
  have hverts_eq : verts = blocks.flatten.flatMap (fun i => [(false, i), (true, M 0 i)]) := by
    have haux : ∀ bs : List (List (Fin n)), (bs.map altOf).flatten =
        bs.flatten.flatMap (fun i => [(false, i), (true, M 0 i)]) := by
      intro bs
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [altOf, List.map_cons, List.flatten_cons, List.flatMap_append, ih]
    exact haux blocks
  have hflat_len : blocks.flatten.length = n := by
    have h1 := List.toFinset_card_of_nodup hflat_nd
    have h2 : blocks.flatten.toFinset = Finset.univ := by
      ext x; simp [hflat_mem]
    rw [h2, Finset.card_univ, Fintype.card_fin] at h1
    exact h1.symm
  have hverts_len : verts.length = 2 * n := by
    rw [hverts_eq]
    have haux : ∀ l : List (Fin n), (l.flatMap (fun i => [(false, i), (true, M 0 i)])).length = 2 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a ls ih => simp [ih]; omega
    rw [haux, hflat_len]
  have hverts_nd : verts.Nodup := by
    rw [hverts_eq]
    have haux : ∀ l : List (Fin n), l.Nodup → (l.flatMap (fun i => [(false, i), (true, M 0 i)])).Nodup := by
      intro l hl
      induction l with
      | nil => simp
      | cons a ls ih =>
        have ha : a ∉ ls := (List.nodup_cons.mp hl).1
        have hls : ls.Nodup := (List.nodup_cons.mp hl).2
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
        refine ⟨?_, ?_, ih hls⟩
        · intro hmem
          simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
          rcases hmem with ⟨hF, _⟩ | ⟨i, hi, ⟨_, hEq⟩ | ⟨hF, _⟩⟩
          · exact Bool.false_ne_true hF
          · subst hEq; exact ha hi
          · exact Bool.false_ne_true hF
        · simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
            not_exists, not_and]
          intro i hi hmem
          rcases hmem with ⟨htrue, _⟩ | ⟨_, hMeq⟩
          · exact Bool.false_ne_true.symm htrue
          · exact ha ((M 0).injective hMeq ▸ hi)
    exact haux _ hflat_nd
  have hverts_mem : ∀ v : V n, v ∈ verts := by
    intro v
    rw [hverts_eq, List.mem_flatMap]
    rcases v with ⟨b, idx⟩
    cases b
    · exact ⟨idx, (hflat_mem idx).mpr (Finset.mem_univ _), by simp⟩
    · exact ⟨(M 0).symm idx, (hflat_mem _).mpr (Finset.mem_univ _), by simp⟩
  let toV : Fin (2 * n) → V n := fun k => verts[k.val]'(by rw [hverts_len]; exact k.isLt)
  have htoV_bij : Function.Bijective toV := by
    constructor
    · intro k1 k2 heq
      have h := (List.Nodup.getElem_inj_iff hverts_nd).mp heq
      exact Fin.ext h
    · intro v
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp (hverts_mem v)
      exact ⟨⟨k, by rw [← hverts_len]; exact hk⟩, hget⟩
  let order : V n ≃ Fin (2 * n) := (Equiv.ofBijective toV htoV_bij).symm
  refine ⟨order, fun t => ?_⟩
  set S := Finset.univ.filter (fun v : V n => (order v).val < t)
  have hS_eq : S = (verts.take t).toFinset := by
    ext v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    have hv_eq : verts[(order v).val]'(by rw [hverts_len]; exact (order v).isLt) = v :=
      (Equiv.ofBijective toV htoV_bij).apply_symm_apply v
    constructor
    · intro hlt
      rw [← hv_eq]
      have hlt_take : (order v).val < (verts.take t).length := by
        rw [List.length_take, hverts_len]; exact lt_min hlt (order v).isLt
      have hget : (verts.take t)[(order v).val]'hlt_take = verts[(order v).val]'(by rw [hverts_len]; exact (order v).isLt) := List.getElem_take
      rw [← hget]
      exact List.getElem_mem hlt_take
    · intro hmem
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
      have hk_t : k < t := by rw [List.length_take] at hk; exact lt_of_lt_of_le hk (Nat.min_le_left _ _)
      have hk_v : k < verts.length := by rw [List.length_take] at hk; exact lt_of_lt_of_le hk (Nat.min_le_right _ _)
      rw [List.getElem_take] at hget
      have hkeq : k = (order v).val := (List.Nodup.getElem_inj_iff hverts_nd).mp (hget.trans hv_eq.symm)
      omega

  have hborder_le2 : (borderOf M S).card ≤ 2 := by

    have hcycle_closed : ∀ B ∈ blocks, ∀ v ∈ altOf B, ∀ j : Fin 2, mateOf M j v ∈ altOf B := by
      intro B hB v hv j
      have hBok := hblocks_ok B hB
      simp only [altOf, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
      obtain ⟨i, hiB, rfl | rfl⟩ := hv
      · match j with
        | ⟨0, _⟩ => exact ⟨i, hiB, Or.inr rfl⟩
        | ⟨1, _⟩ =>
          refine ⟨σ.symm i, hBok.2.2.2.1 i hiB, Or.inr ?_⟩
          change (true, M 1 i) = (true, M 0 (σ.symm i))
          simp only [σ, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      · match j with
        | ⟨0, _⟩ => exact ⟨i, hiB, Or.inl (by simp [mateOf])⟩
        | ⟨1, _⟩ =>
          refine ⟨σ i, hBok.2.2.1 i hiB, Or.inl ?_⟩
          change (false, (M 1).symm (M 0 i)) = (false, σ i)
          rfl
    have htake_flatten : ∀ (ls : List (List (V n))) (t : ℕ),
        ∃ (done : List (List (V n))) (part : List (V n)),
          (∀ C ∈ done, C ∈ ls) ∧
          (part = [] ∨ ∃ C ∈ ls, ∃ s < C.length, part = C.take s) ∧
          ls.flatten.take t = done.flatten ++ part := by
      intro ls
      induction ls with
      | nil => intro t; exact ⟨[], [], fun _ h => (by cases h), Or.inl rfl, by simp⟩
      | cons C cs ih =>
        intro t
        by_cases hlt : t < C.length
        · refine ⟨[], C.take t, fun _ h => (by cases h), Or.inr ⟨C, List.mem_cons_self .., t, hlt, rfl⟩, ?_⟩
          rw [List.flatten_cons, List.take_append_of_le_length (le_of_lt hlt), List.flatten_nil, List.nil_append]
        · obtain ⟨done, part, hdone, hpart, heq⟩ := ih (t - C.length)
          refine ⟨C :: done, part, ?_, ?_, ?_⟩
          · intro X hX
            rcases List.mem_cons.mp hX with rfl | hmem
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (hdone X hmem)
          · rcases hpart with rfl | ⟨X, hX, s, hs, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨X, List.mem_cons_of_mem _ hX, s, hs, rfl⟩
          · rw [List.flatten_cons, List.take_append, List.take_of_length_le (by omega),
              heq, List.flatten_cons, List.append_assoc]
    obtain ⟨done, part, hdone_mem, hpart_spec, htake_eq⟩ := htake_flatten (blocks.map altOf) t
    have hdone_closed : ∀ v ∈ done.flatten, ∀ j : Fin 2, mateOf M j v ∈ done.flatten := by
      intro v hv j
      rw [List.mem_flatten] at hv ⊢
      obtain ⟨C, hCdone, hvC⟩ := hv
      have hCmap := hdone_mem C hCdone
      rw [List.mem_map] at hCmap
      obtain ⟨B, hB, rfl⟩ := hCmap
      exact ⟨altOf B, hCdone, hcycle_closed B hB v hvC j⟩
    have hborder_in_part : ∀ v ∈ borderOf M S, v ∈ part := by
      intro v hv
      simp only [borderOf, Finset.mem_filter] at hv
      obtain ⟨hvS, j, hjout⟩ := hv
      rw [hS_eq, htake_eq, List.mem_toFinset, List.mem_append] at hvS
      rcases hvS with hv_done | hv_part
      · exfalso
        apply hjout
        rw [hS_eq, htake_eq, List.mem_toFinset, List.mem_append]
        exact Or.inl (hdone_closed v hv_done j)
      · exact hv_part
    rcases hpart_spec with rfl | ⟨C, hCmap, s, hs, rfl⟩
    · have hemp : borderOf M S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv; exact List.not_mem_nil (hborder_in_part v hv)
      rw [hemp, Finset.card_empty]; omega
    · rw [List.mem_map] at hCmap
      obtain ⟨B, hB, rfl⟩ := hCmap
      have hBok := hblocks_ok B hB
      have halt_len : (altOf B).length = 2 * B.length := by
        unfold altOf
        have haux : ∀ l : List (Fin n), (l.flatMap (fun i => [(false, i), (true, M 0 i)])).length = 2 * l.length := by
          intro l; induction l with
          | nil => simp
          | cons a ls ih => simp [ih]; omega
        exact haux B
      have halt_get : ∀ idx (hidx : idx < (altOf B).length),
          (altOf B)[idx] = if idx % 2 = 0 then (false, B[idx / 2]'(by omega))
            else (true, M 0 (B[idx / 2]'(by omega))) := by
        have haux : ∀ (l : List (Fin n)) (idx : ℕ) (hidx : idx < (l.flatMap (fun i => [(false, i), (true, M 0 i)])).length),
            (l.flatMap (fun i => [(false, i), (true, M 0 i)]))[idx] =
              if idx % 2 = 0 then (false, l[idx / 2]'(by
                have hlen : (l.flatMap (fun i => [(false, i), (true, M 0 i)])).length = 2 * l.length := by
                  induction l with
                  | nil => simp
                  | cons a ls ih => simp [ih]; omega
                omega))
              else (true, M 0 (l[idx / 2]'(by
                have hlen : (l.flatMap (fun i => [(false, i), (true, M 0 i)])).length = 2 * l.length := by
                  induction l with
                  | nil => simp
                  | cons a ls ih => simp [ih]; omega
                omega))) := by
          intro l
          induction l with
          | nil => intro idx hidx; simp at hidx
          | cons a ls ih =>
            intro idx hidx
            rcases idx with _ | idx'
            · simp
            · rcases idx' with _ | idx''
              · simp
              · simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
                have h := ih idx'' (by simpa using hidx)
                rw [h]
                have hmod : (idx'' + 1 + 1) % 2 = idx'' % 2 := by omega
                have hdiv : (idx'' + 1 + 1) / 2 = idx'' / 2 + 1 := by omega
                simp [hmod, hdiv]
        exact haux B
      by_cases hs0 : s = 0
      · subst hs0
        have hemp : borderOf M S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          have h := hborder_in_part v hv
          simp at h
        rw [hemp, Finset.card_empty]; omega
      · let e0 : V n := (altOf B)[0]'(by omega)
        let e1 : V n := (altOf B)[s - 1]'(by omega)
        have hsub2 : borderOf M S ⊆ {e0, e1} := by
          intro v hv
          have hv_part := hborder_in_part v hv
          obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hv_part
          have hr_s : r < s := by rw [List.length_take] at hr; exact lt_of_lt_of_le hr (Nat.min_le_left _ _)
          rw [List.getElem_take] at hget
          by_cases hr0 : r = 0
          · subst hr0; simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl (by rw [← hget])
          · by_cases hr1 : r = s - 1
            · subst hr1; simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (by rw [← hget])
            · exfalso
              have hrmid : 1 ≤ r ∧ r + 1 < s := by omega
              simp only [borderOf, Finset.mem_filter] at hv
              obtain ⟨_, j, hjout⟩ := hv
              apply hjout
              rw [hS_eq, htake_eq, List.mem_toFinset, List.mem_append]
              right
              have hmem_idx : ∀ (q : ℕ) (hq : q < s), (altOf B)[q]'(lt_trans hq hs) ∈ (altOf B).take s := fun q hq => by
                have hlt_tk : q < ((altOf B).take s).length := by rw [List.length_take]; omega
                have htk : ((altOf B).take s)[q]'hlt_tk = (altOf B)[q]'(lt_trans hq hs) := List.getElem_take
                rw [← htk]
                exact List.getElem_mem hlt_tk
              rw [← hget, halt_get r (lt_trans hr_s hs)]
              by_cases heven : r % 2 = 0
              · rw [if_pos heven]
                match j with
                | ⟨0, _⟩ =>
                  have h1 : mateOf M ⟨0, by omega⟩ (false, B[r / 2]'(by omega)) =
                      (altOf B)[r + 1]'(lt_trans (by omega : r + 1 < s) hs) := by
                    rw [halt_get (r + 1) (lt_trans (by omega : r + 1 < s) hs), if_neg (by omega)]
                    change (true, M 0 B[r / 2]) = (true, M 0 B[(r + 1) / 2])
                    have hd : (r + 1) / 2 = r / 2 := by omega
                    simp [hd]
                  rw [h1]; exact hmem_idx (r + 1) (by omega)
                | ⟨1, _⟩ =>
                  have h1 : mateOf M ⟨1, by omega⟩ (false, B[r / 2]'(by omega)) =
                      (altOf B)[r - 1]'(lt_trans (by omega : r - 1 < s) hs) := by
                    rw [halt_get (r - 1) (lt_trans (by omega : r - 1 < s) hs), if_neg (by omega)]
                    change (true, M 1 B[r / 2]) = (true, M 0 B[(r - 1) / 2])
                    have hstep := hBok.2.2.2.2 ((r - 1) / 2) (by omega)
                    have hidx_eq : ((r - 1) / 2 + 1) % B.length = r / 2 := by
                      rw [Nat.mod_eq_of_lt (by omega)]; omega
                    have hstep' : σ B[(r - 1) / 2] = B[r / 2] := by
                      simpa [hidx_eq] using hstep
                    have hM : M 1 B[r / 2] = M 0 B[(r - 1) / 2] := by
                      rw [← hstep']; simp [σ]
                    rw [hM]
                  rw [h1]; exact hmem_idx (r - 1) (by omega)
              · rw [if_neg heven]
                match j with
                | ⟨0, _⟩ =>
                  have h1 : mateOf M ⟨0, by omega⟩ (true, M 0 B[r / 2]) =
                      (altOf B)[r - 1]'(lt_trans (by omega : r - 1 < s) hs) := by
                    rw [halt_get (r - 1) (lt_trans (by omega : r - 1 < s) hs), if_pos (by omega)]
                    change (false, (M 0).symm (M 0 B[r / 2])) = (false, B[(r - 1) / 2])
                    have hd : (r - 1) / 2 = r / 2 := by omega
                    simp [hd]
                  rw [h1]; exact hmem_idx (r - 1) (by omega)
                | ⟨1, _⟩ =>
                  have h1 : mateOf M ⟨1, by omega⟩ (true, M 0 B[r / 2]) =
                      (altOf B)[r + 1]'(lt_trans (by omega : r + 1 < s) hs) := by
                    rw [halt_get (r + 1) (lt_trans (by omega : r + 1 < s) hs), if_pos (by omega)]
                    change (false, (M 1).symm (M 0 B[r / 2])) = (false, B[(r + 1) / 2])
                    have hstep := hBok.2.2.2.2 (r / 2) (by omega)
                    have hidx_eq : (r / 2 + 1) % B.length = (r + 1) / 2 := by
                      rw [Nat.mod_eq_of_lt (by omega)]; omega
                    have hstep' : σ B[r / 2] = B[(r + 1) / 2] := by
                      simpa [hidx_eq] using hstep
                    exact congrArg (Prod.mk false) hstep'
                  rw [h1]; exact hmem_idx (r + 1) (by omega)
        calc (borderOf M S).card ≤ ({e0, e1} : Finset (V n)).card := Finset.card_le_card hsub2
          _ ≤ 2 := Finset.card_le_two
  have hup := part1_upper M S
  have hpow : 2 ^ (dataOf n 2 M S).1 ≤ 4 := by
    calc 2 ^ (borderOf M S).card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hborder_le2
      _ = 4 := by norm_num
  calc (dataOf n 2 M S).2 ≤ (n + 1) ^ 2 * 2 ^ (dataOf n 2 M S).1 := hup
    _ ≤ (n + 1) ^ 2 * 4 := Nat.mul_le_mul_left _ hpow
    _ = 4 * (n + 1) ^ 2 := Nat.mul_comm _ _

private def ballCard (n r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (r + 1), Nat.choose n j

private theorem pow_101_le (n : ℕ) : 101 ^ n ≤ 2 ^ (n / 50 + 1) * 100 ^ n := by
  have h50 : (101 : ℕ) ^ 50 ≤ 2 * 100 ^ 50 := by norm_num
  have hdiv : n = 50 * (n / 50) + n % 50 := (Nat.div_add_mod n 50).symm
  have hmod : n % 50 < 50 := Nat.mod_lt n (by omega)
  have hpart1 : 101 ^ (50 * (n / 50)) ≤ 2 ^ (n / 50) * 100 ^ (50 * (n / 50)) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left h50 _
  have hpart2 : 101 ^ (n % 50) ≤ 2 * 100 ^ (n % 50) := by
    have hmul : 101 ^ (n % 50) * 100 ^ (50 - n % 50) ≤ 2 * 100 ^ 50 := by
      calc 101 ^ (n % 50) * 100 ^ (50 - n % 50)
          ≤ 101 ^ (n % 50) * 101 ^ (50 - n % 50) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ = 101 ^ 50 := by rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmod)]
        _ ≤ 2 * 100 ^ 50 := h50
    have h50eq : 100 ^ 50 = 100 ^ (n % 50) * 100 ^ (50 - n % 50) := by
      rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmod)]
    rw [h50eq, ← mul_assoc] at hmul
    exact Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos (by omega))
  conv_lhs => rw [hdiv, pow_add]
  calc 101 ^ (50 * (n / 50)) * 101 ^ (n % 50)
      ≤ (2 ^ (n / 50) * 100 ^ (50 * (n / 50))) * (2 * 100 ^ (n % 50)) :=
        Nat.mul_le_mul hpart1 hpart2
    _ = 2 ^ (n / 50 + 1) * (100 ^ (50 * (n / 50)) * 100 ^ (n % 50)) := by rw [pow_succ]; ring
    _ = 2 ^ (n / 50 + 1) * 100 ^ n := by rw [← pow_add, ← hdiv]

private theorem ballCard_le_pow2 {n r : ℕ} (hr : r ≤ n) :
    ballCard n r ≤ 2 ^ (n / 50 + 1 + 7 * r) := by
  have hbinom : 100 ^ (n - r) * ballCard n r ≤ 101 ^ n := by
    have hexp : (100 + 1 : ℕ) ^ n = ∑ j ∈ Finset.range (n + 1), 100 ^ (n - j) * Nat.choose n j := by
      have h1 := add_pow (1 : ℕ) 100 n
      rw [show (100 + 1 : ℕ) = 1 + 100 from rfl, h1]
      refine Finset.sum_congr rfl fun j _ => by simp only [one_pow, one_mul, Nat.cast_id]
    have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
    calc 100 ^ (n - r) * ballCard n r
        = ∑ j ∈ Finset.range (r + 1), 100 ^ (n - r) * Nat.choose n j := by
          unfold ballCard; rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (r + 1), 100 ^ (n - j) * Nat.choose n j := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ ∑ j ∈ Finset.range (n + 1), 100 ^ (n - j) * Nat.choose n j :=
          Finset.sum_le_sum_of_subset hsub
      _ = 101 ^ n := hexp.symm
  have h101 := pow_101_le n
  have hsplit : 100 ^ n = 100 ^ (n - r) * 100 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  have h100r : 100 ^ r ≤ 2 ^ (7 * r) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num : 100 ≤ 2 ^ 7) r
  have hmul : 100 ^ (n - r) * ballCard n r ≤ 100 ^ (n - r) * 2 ^ (n / 50 + 1 + 7 * r) := by
    calc 100 ^ (n - r) * ballCard n r
        ≤ 101 ^ n := hbinom
      _ ≤ 2 ^ (n / 50 + 1) * 100 ^ n := h101
      _ = 100 ^ (n - r) * (2 ^ (n / 50 + 1) * 100 ^ r) := by rw [hsplit]; ring
      _ ≤ 100 ^ (n - r) * (2 ^ (n / 50 + 1) * 2 ^ (7 * r)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h100r)
      _ = 100 ^ (n - r) * 2 ^ (n / 50 + 1 + 7 * r) := by rw [← pow_add]
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega))

private theorem choose_middle_ge {n b k : ℕ} (hnb : 6 * b + 6 ≤ n)
    (hk_lo : n / 2 ≤ k + b) (hk_hi : k ≤ n / 2 + b) :
    2 ^ n ≤ (n + 1) * 2 ^ b * Nat.choose n k := by
  set m := n / 2
  have h2n : 2 ^ n ≤ (n + 1) * Nat.choose n m := by
    have hsum : 2 ^ n = ∑ j ∈ Finset.range (n + 1), Nat.choose n j := (Nat.sum_range_choose n).symm
    rw [hsum]
    calc ∑ j ∈ Finset.range (n + 1), Nat.choose n j
        ≤ ∑ _j ∈ Finset.range (n + 1), Nat.choose n m :=
          Finset.sum_le_sum fun j _ => Nat.choose_le_middle j n
      _ = (n + 1) * Nat.choose n m := by simp
  have hdown : ∀ d ≤ b, Nat.choose n m ≤ 2 ^ d * Nat.choose n (m - d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d' ih =>
      intro hd
      have hprev := ih (by omega)
      have hstep : Nat.choose n (m - d') ≤ 2 * Nat.choose n (m - (d' + 1)) := by
        have hrel := Nat.choose_succ_right_eq n (m - (d' + 1))
        have heq : m - (d' + 1) + 1 = m - d' := by omega
        rw [heq] at hrel
        have hle_coef : n - (m - (d' + 1)) ≤ 2 * (m - d') := by omega
        have h1 : Nat.choose n (m - d') * (m - d') ≤ (2 * Nat.choose n (m - (d' + 1))) * (m - d') := by
          rw [hrel]
          calc Nat.choose n (m - (d' + 1)) * (n - (m - (d' + 1)))
              ≤ Nat.choose n (m - (d' + 1)) * (2 * (m - d')) := Nat.mul_le_mul_left _ hle_coef
            _ = (2 * Nat.choose n (m - (d' + 1))) * (m - d') := by ring
        exact Nat.le_of_mul_le_mul_right h1 (by omega)
      calc Nat.choose n m ≤ 2 ^ d' * Nat.choose n (m - d') := hprev
        _ ≤ 2 ^ d' * (2 * Nat.choose n (m - (d' + 1))) := Nat.mul_le_mul_left _ hstep
        _ = 2 ^ (d' + 1) * Nat.choose n (m - (d' + 1)) := by rw [pow_succ]; ring
  have hup : ∀ d ≤ b, Nat.choose n m ≤ 2 ^ d * Nat.choose n (m + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d' ih =>
      intro hd
      have hprev := ih (by omega)
      have hstep : Nat.choose n (m + d') ≤ 2 * Nat.choose n (m + (d' + 1)) := by
        have hrel := Nat.choose_succ_right_eq n (m + d')
        have heq : m + d' + 1 = m + (d' + 1) := by omega
        rw [heq] at hrel
        have hle_coef : m + (d' + 1) ≤ 2 * (n - (m + d')) := by omega
        have h1 : Nat.choose n (m + d') * (n - (m + d')) ≤ (2 * Nat.choose n (m + (d' + 1))) * (n - (m + d')) := by
          rw [← hrel]
          calc Nat.choose n (m + (d' + 1)) * (m + (d' + 1))
              ≤ Nat.choose n (m + (d' + 1)) * (2 * (n - (m + d'))) := Nat.mul_le_mul_left _ hle_coef
            _ = (2 * Nat.choose n (m + (d' + 1))) * (n - (m + d')) := by ring
        exact Nat.le_of_mul_le_mul_right h1 (by omega)
      calc Nat.choose n m ≤ 2 ^ d' * Nat.choose n (m + d') := hprev
        _ ≤ 2 ^ d' * (2 * Nat.choose n (m + (d' + 1))) := Nat.mul_le_mul_left _ hstep
        _ = 2 ^ (d' + 1) * Nat.choose n (m + (d' + 1)) := by rw [pow_succ]; ring
  have hcmp : Nat.choose n m ≤ 2 ^ b * Nat.choose n k := by
    by_cases hkm : k ≤ m
    · have hd : m - k ≤ b := by omega
      have h1 := hdown (m - k) hd
      have hsub : m - (m - k) = k := by omega
      rw [hsub] at h1
      exact le_trans h1 (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd))
    · have hd : k - m ≤ b := by omega
      have h1 := hup (k - m) hd
      have hadd : m + (k - m) = k := by omega
      rw [hadd] at h1
      exact le_trans h1 (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd))
  calc 2 ^ n ≤ (n + 1) * Nat.choose n m := h2n
    _ ≤ (n + 1) * (2 ^ b * Nat.choose n k) := Nat.mul_le_mul_left _ hcmp
    _ = (n + 1) * 2 ^ b * Nat.choose n k := by ring

private theorem perm_image_fiber_card {n : ℕ} (A Y : Finset (Fin n)) (hcard : A.card = Y.card) :
    Nat.choose n A.card *
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  let fib (Z : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π : Equiv.Perm (Fin n) => A.image π = Z)
  have hfib_eq : ∀ Z : Finset (Fin n), Z.card = A.card → (fib Z).card = (fib Y).card := by
    intro Z hZ
    have hZY : Z.card = Y.card := hZ.trans hcard
    have hc_eq : ((Finset.univ : Finset (Fin n)) \ Z).card = ((Finset.univ : Finset (Fin n)) \ Y).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ, hZY]
    let e1 : ↥Z ≃ ↥Y := Fintype.equivOfCardEq (by simp [hZY])
    let e2 : ↥((Finset.univ : Finset (Fin n)) \ Z) ≃ ↥((Finset.univ : Finset (Fin n)) \ Y) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hc_eq)
    let τ : Equiv.Perm (Fin n) := {
      toFun := fun x => if hx : x ∈ Z then (e1 ⟨x, hx⟩).val else (e2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩).val
      invFun := fun y => if hy : y ∈ Y then (e1.symm ⟨y, hy⟩).val else (e2.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩).val
      left_inv := fun x => by
        dsimp only
        by_cases hx : x ∈ Z
        · rw [dif_pos hx, dif_pos (e1 ⟨x, hx⟩).property]
          exact congrArg Subtype.val (e1.symm_apply_apply ⟨x, hx⟩)
        · have hx' : x ∈ (Finset.univ : Finset (Fin n)) \ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
          have hny : (e2 ⟨x, hx'⟩).val ∉ Y := (Finset.mem_sdiff.mp (e2 ⟨x, hx'⟩).property).2
          rw [dif_neg hx, dif_neg hny]
          exact congrArg Subtype.val (e2.symm_apply_apply ⟨x, hx'⟩)
      right_inv := fun y => by
        dsimp only
        by_cases hy : y ∈ Y
        · rw [dif_pos hy, dif_pos (e1.symm ⟨y, hy⟩).property]
          exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
        · have hy' : y ∈ (Finset.univ : Finset (Fin n)) \ Y := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩
          have hnz : (e2.symm ⟨y, hy'⟩).val ∉ Z := (Finset.mem_sdiff.mp (e2.symm ⟨y, hy'⟩).property).2
          rw [dif_neg hy, dif_neg hnz]
          exact congrArg Subtype.val (e2.apply_symm_apply ⟨y, hy'⟩)
    }
    have hτZ : Z.image τ = Y := by
      ext y
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (if hx' : x ∈ Z then (e1 ⟨x, hx'⟩).val else _) ∈ Y
        rw [dif_pos hx]
        exact (e1 ⟨x, hx⟩).property
      · intro hy
        refine ⟨(e1.symm ⟨y, hy⟩).val, (e1.symm ⟨y, hy⟩).property, ?_⟩
        change (if hx' : (e1.symm ⟨y, hy⟩).val ∈ Z then (e1 ⟨_, hx'⟩).val else _) = y
        rw [dif_pos (e1.symm ⟨y, hy⟩).property]
        exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
    refine Finset.card_bij (fun π _ => π.trans τ) ?_ ?_ ?_
    · intro π hπ
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      have himg : A.image (π.trans τ) = (A.image π).image τ := by
        ext y; simp [Equiv.trans_apply]
      rw [himg, hπ, hτZ]
    · intro π1 _ π2 _ heq
      apply Equiv.ext
      intro x
      exact τ.injective (by simpa [Equiv.trans_apply] using Equiv.ext_iff.mp heq x)
    · intro π hπ
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      refine ⟨π.trans τ.symm, ?_, by ext x; simp⟩
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
      have himg : A.image (π.trans τ.symm) = (A.image π).image τ.symm := by
        ext x; simp [Equiv.trans_apply]
      rw [himg, hπ, ← hτZ]
      ext x; simp
  have hpart : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
      (Finset.powersetCard A.card (Finset.univ : Finset (Fin n))).biUnion fib := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, fib, Finset.mem_filter, true_iff]
    exact ⟨A.image π, Finset.card_image_of_injective A π.injective, rfl⟩
  have hdisj : ((Finset.powersetCard A.card (Finset.univ : Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint fib := by
    intro Z1 _ Z2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π h1 h2
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  have htot := congrArg Finset.card hpart
  rw [Finset.card_univ, Finset.card_biUnion hdisj] at htot
  have hsum_eq : ∑ Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Z).card =
      Nat.choose n A.card * (fib Y).card := by
    calc ∑ Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Z).card
        = ∑ _Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Y).card :=
          Finset.sum_congr rfl fun Z hZ => hfib_eq Z (Finset.mem_powersetCard.mp hZ).2
      _ = (Finset.powersetCard A.card (Finset.univ : Finset (Fin n))).card * (fib Y).card := by simp
      _ = Nat.choose n A.card * (fib Y).card := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hsum_eq, ← htot]

private theorem card_finset_card_le {n r : ℕ} :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ r)).card ≤ ballCard n r := by
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ r) ⊆
      (Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ] at hT ⊢
    exact ⟨T.card, by omega, rfl⟩
  calc _ ≤ ((Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (r + 1), (Finset.powersetCard j (Finset.univ : Finset (Fin n))).card :=
        Finset.card_biUnion_le
    _ = ballCard n r := by
        unfold ballCard
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private theorem part3_three_matchings :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : Fin 3 → Equiv.Perm (Fin n),
      ∀ S : Finset (V n), S.card = n → 2 ^ (n / 16384) ≤ (dataOf n 3 M S).2 := by
  refine ⟨500000, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hn32 : 32 ≤ n := by omega
  let M0 : Equiv.Perm (Fin n) := Equiv.refl (Fin n)
  let M1 : Equiv.Perm (Fin n) := {
    toFun := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn0⟩
    invFun := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn0⟩
    left_inv := fun i => by
      apply Fin.ext; dsimp only
      have hi := i.isLt
      by_cases h : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt h]
        have : i.val + 1 + n - 1 = n + i.val := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hi]
      · have heq : i.val + 1 = n := by omega
        rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    right_inv := fun i => by
      apply Fin.ext; dsimp only
      have hi := i.isLt
      by_cases h0 : i.val = 0
      · have hm : (i.val + n - 1) % n = n - 1 := by
          rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hm, h0]
        have : n - 1 + 1 = n := by omega
        rw [this, Nat.mod_self]
      · have hm : (i.val + n - 1) % n = i.val - 1 := by
          have h1 : i.val + n - 1 = n + (i.val - 1) := by omega
          rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        have : i.val - 1 + 1 = i.val := by omega
        rw [this, Nat.mod_eq_of_lt hi]
  }
  let Mof : Equiv.Perm (Fin n) → (Fin 3 → Equiv.Perm (Fin n)) := fun π j =>
    match j with
    | ⟨0, _⟩ => M0
    | ⟨1, _⟩ => M1
    | ⟨2, _⟩ => π
  set b := n / 5000
  have hb_ge : 100 ≤ b := by omega

  let transOf (A : Finset (Fin n)) : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => decide (i ∈ A) ≠ decide (M1 i ∈ A))
  let candA : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun A => (transOf A).card ≤ 2 * b ∧ n / 2 ≤ A.card + b ∧ A.card ≤ n / 2 + b)
  let candB (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun B => (symmDiff A B).card ≤ b)
  let candPairs : Finset (Finset (Fin n) × Finset (Fin n)) :=
    candA.biUnion (fun A => (candB A).map ⟨fun B => (A, B), fun _ _ h => (Prod.mk.inj h).2⟩)
  let badFor (AB : Finset (Fin n) × Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π => (symmDiff (AB.1.image π) AB.2).card ≤ b)
  let badPerms : Finset (Equiv.Perm (Fin n)) := candPairs.biUnion badFor

  have hcandA_card : candA.card ≤ 2 * ballCard n (2 * b) := by
    let encA : Finset (Fin n) → Bool × Finset (Fin n) := fun A => (decide ((⟨0, hn0⟩ : Fin n) ∈ A), transOf A)
    have hencA_inj : Function.Injective encA := by
      intro A1 A2 heq
      have h0 : decide ((⟨0, hn0⟩ : Fin n) ∈ A1) = decide ((⟨0, hn0⟩ : Fin n) ∈ A2) := congrArg Prod.fst heq
      have hT : transOf A1 = transOf A2 := congrArg Prod.snd heq
      have hall : ∀ k (hk : k < n), decide ((⟨k, hk⟩ : Fin n) ∈ A1) = decide ((⟨k, hk⟩ : Fin n) ∈ A2) := by
        intro k
        induction k with
        | zero => intro _; exact h0
        | succ k' ih =>
          intro hk
          have hprev := ih (by omega)
          have hstep := Finset.ext_iff.mp hT ⟨k', by omega⟩
          simp only [transOf, Finset.mem_filter, Finset.mem_univ, true_and] at hstep
          have hM1 : M1 ⟨k', by omega⟩ = ⟨k' + 1, hk⟩ := by
            apply Fin.ext; dsimp only [M1]; exact Nat.mod_eq_of_lt hk
          rw [hM1, hprev] at hstep
          cases h1 : decide ((⟨k' + 1, hk⟩ : Fin n) ∈ A1) <;>
            cases h2 : decide ((⟨k' + 1, hk⟩ : Fin n) ∈ A2) <;>
            cases h3 : decide ((⟨k', by omega⟩ : Fin n) ∈ A2) <;> simp_all
      ext i
      have hi := hall i.val i.isLt
      simpa using hi
    let target := (Finset.univ : Finset Bool) ×ˢ
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ 2 * b))
    have hsub : candA.image encA ⊆ target := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨A, hA, rfl⟩ := hp
      simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      simp only [target, encA, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
      exact hA.1
    calc candA.card = (candA.image encA).card := (Finset.card_image_of_injective candA hencA_inj).symm
      _ ≤ target.card := Finset.card_le_card hsub
      _ = 2 * ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ 2 * b)).card := by
          simp [target, Finset.card_product]
      _ ≤ 2 * ballCard n (2 * b) := Nat.mul_le_mul_left 2 card_finset_card_le

  have hcandB_card : ∀ A : Finset (Fin n), (candB A).card ≤ ballCard n b := by
    intro A
    have hinj : Function.Injective (fun B : Finset (Fin n) => symmDiff A B) := by
      intro B1 B2 heq
      have h1 := congrArg (symmDiff A) heq
      rwa [symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left] at h1
    have hsub : (candB A).image (fun B => symmDiff A B) ⊆
        (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b) := by
      intro T hT
      rw [Finset.mem_image] at hT
      obtain ⟨B, hB, rfl⟩ := hT
      simp only [candB, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      exact hB
    calc (candB A).card = ((candB A).image (fun B => symmDiff A B)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b)).card :=
          Finset.card_le_card hsub
      _ ≤ ballCard n b := card_finset_card_le

  have hbadFor_bound : ∀ AB ∈ candPairs,
      2 ^ n * (badFor AB).card ≤
        (n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by
    intro AB hAB
    simp only [candPairs, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk] at hAB
    obtain ⟨A, hA, B, _, rfl⟩ := hAB
    simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    let candY := Finset.univ.filter (fun Y : Finset (Fin n) => Y.card = A.card ∧ (symmDiff Y B).card ≤ b)
    have hY_card : candY.card ≤ ballCard n b := by
      have hinj : Function.Injective (fun Y : Finset (Fin n) => symmDiff Y B) := by
        intro Y1 Y2 heq
        have h1 := congrArg (fun Z => symmDiff Z B) heq
        rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at h1
      have hsub : candY.image (fun Y => symmDiff Y B) ⊆
          (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b) := by
        intro T hT
        rw [Finset.mem_image] at hT
        obtain ⟨Y, hY, rfl⟩ := hT
        simp only [candY, Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
        exact hY.2
      calc candY.card = (candY.image (fun Y => symmDiff Y B)).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b)).card :=
            Finset.card_le_card hsub
        _ ≤ ballCard n b := card_finset_card_le
    have hbad_sub : badFor (A, B) ⊆
        candY.biUnion (fun Y => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)) := by
      intro π hπ
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, candY] at hπ ⊢
      exact ⟨A.image π, ⟨Finset.card_image_of_injective A π.injective, hπ⟩, rfl⟩
    have hchoose_mul : Nat.choose n A.card * (badFor (A, B)).card ≤
        ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by
      calc Nat.choose n A.card * (badFor (A, B)).card
          ≤ Nat.choose n A.card * (∑ Y ∈ candY, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card) :=
            Nat.mul_le_mul_left (Nat.choose n A.card) (le_trans (Finset.card_le_card hbad_sub) Finset.card_biUnion_le)
        _ = ∑ Y ∈ candY, Nat.choose n A.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card := by
            rw [Finset.mul_sum]
        _ = ∑ _Y ∈ candY, Fintype.card (Equiv.Perm (Fin n)) := by
            refine Finset.sum_congr rfl fun Y hY => ?_
            exact perm_image_fiber_card A Y (Finset.mem_filter.mp hY).2.1.symm
        _ = candY.card * Fintype.card (Equiv.Perm (Fin n)) := by simp
        _ ≤ ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := Nat.mul_le_mul_right _ hY_card
    have hmid := choose_middle_ge (n := n) (b := b) (k := A.card) (by omega) hA.2.1 hA.2.2
    calc 2 ^ n * (badFor (A, B)).card
        ≤ ((n + 1) * 2 ^ b * Nat.choose n A.card) * (badFor (A, B)).card :=
          Nat.mul_le_mul_right _ hmid
      _ = (n + 1) * 2 ^ b * (Nat.choose n A.card * (badFor (A, B)).card) := by ring
      _ ≤ (n + 1) * 2 ^ b * (ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Nat.mul_le_mul_left _ hchoose_mul
      _ = (n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by ring

  have hpairs_card : candPairs.card ≤ 2 * ballCard n (2 * b) * ballCard n b := by
    calc candPairs.card
        ≤ ∑ A ∈ candA, ((candB A).map ⟨fun B => (A, B), fun _ _ h => (Prod.mk.inj h).2⟩).card :=
          Finset.card_biUnion_le
      _ = ∑ A ∈ candA, (candB A).card := Finset.sum_congr rfl fun A _ => Finset.card_map _
      _ ≤ ∑ _A ∈ candA, ballCard n b := Finset.sum_le_sum fun A _ => hcandB_card A
      _ = candA.card * ballCard n b := by simp
      _ ≤ (2 * ballCard n (2 * b)) * ballCard n b := Nat.mul_le_mul_right _ hcandA_card
  have htot_bad : 2 ^ n * badPerms.card ≤
      2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b *
        Fintype.card (Equiv.Perm (Fin n)) := by
    calc 2 ^ n * badPerms.card
        ≤ 2 ^ n * (∑ AB ∈ candPairs, (badFor AB).card) :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ AB ∈ candPairs, 2 ^ n * (badFor AB).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _AB ∈ candPairs, ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Finset.sum_le_sum hbadFor_bound
      _ = candPairs.card * ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) := by simp
      _ ≤ (2 * ballCard n (2 * b) * ballCard n b) *
            ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Nat.mul_le_mul_right _ hpairs_card
      _ = 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b *
            Fintype.card (Equiv.Perm (Fin n)) := by ring

  have hcoef_lt : 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b < 2 ^ n := by
    have hb1 := ballCard_le_pow2 (n := n) (r := 2 * b) (by omega)
    have hb2 := ballCard_le_pow2 (n := n) (r := b) (by omega)
    have hn1_lt : n + 1 < 2 ^ (n / 50) := by
      have hk_ge : 10000 ≤ n / 50 := by omega
      have hlin : ∀ m : ℕ, 10 ≤ m → 60 * m < 2 ^ m := by
        intro m hm
        induction m with
        | zero => omega
        | succ m' ih =>
          by_cases h10 : m' < 10
          · have : m' = 9 := by omega
            subst this; norm_num
          · have hprev := ih (by omega)
            rw [pow_succ]; omega
      have h1 := hlin (n / 50) (by omega)
      omega
    have hexp_le : 1 + n / 50 + b + (n / 50 + 1 + 7 * (2 * b)) + (n / 50 + 1 + 7 * b) + (n / 50 + 1 + 7 * b) ≤ n := by
      omega
    calc 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b
        < 2 * 2 ^ (n / 50) * 2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
            2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) := by
          have hpos1 : 0 < 2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
              2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) := by positivity
          have hstep1 : 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b ≤
              2 * (n + 1) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) := by
            have hm1 : ballCard n (2 * b) * ballCard n b ≤
                2 ^ (n / 50 + 1 + 7 * (2 * b)) * 2 ^ (n / 50 + 1 + 7 * b) := Nat.mul_le_mul hb1 hb2
            have hm2 : ballCard n (2 * b) * ballCard n b * ballCard n b ≤
                2 ^ (n / 50 + 1 + 7 * (2 * b)) * 2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) :=
              Nat.mul_le_mul hm1 hb2
            have hm3 := Nat.mul_le_mul_left (2 * (n + 1) * 2 ^ b) hm2
            linarith
          have hstep2 : 2 * (n + 1) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) <
              2 * 2 ^ (n / 50) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) :=
            Nat.mul_lt_mul_of_pos_right (by omega) hpos1
          linarith
      _ = 2 ^ (1 + n / 50 + b + (n / 50 + 1 + 7 * (2 * b)) + (n / 50 + 1 + 7 * b) + (n / 50 + 1 + 7 * b)) := by
          simp only [pow_add, pow_one]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hexp_le
  have hbad_lt : badPerms.card < Fintype.card (Equiv.Perm (Fin n)) := by
    have hpos_perm : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    have hlt : 2 ^ n * badPerms.card < 2 ^ n * Fintype.card (Equiv.Perm (Fin n)) :=
      lt_of_le_of_lt htot_bad (Nat.mul_lt_mul_of_pos_right hcoef_lt hpos_perm)
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hex_good : ∃ π : Equiv.Perm (Fin n), π ∉ badPerms := by
    by_contra hall
    push_neg at hall
    have heq : badPerms = Finset.univ := by ext π; simp [hall π]
    rw [heq, Finset.card_univ] at hbad_lt
    exact lt_irrefl _ hbad_lt
  obtain ⟨π, hπ_good⟩ := hex_good
  refine ⟨Mof π, fun S hScard => ?_⟩
  have hborder_ge : b ≤ (borderOf (Mof π) S).card := by
    by_contra hlt
    have hle : (borderOf (Mof π) S).card ≤ b := by omega
    let A : Finset (Fin n) := Finset.univ.filter (fun i => (false, i) ∈ S)
    let B : Finset (Fin n) := Finset.univ.filter (fun i => (true, i) ∈ S)
    have hAB_sum : A.card + B.card = n := by
      have hpart : S = A.image (fun i => (false, i)) ∪ B.image (fun i => (true, i)) := by
        ext ⟨flag, i⟩
        cases flag <;> simp [A, B]
      have hdisj : Disjoint (A.image (fun i => (false, i))) (B.image (fun i => (true, i))) := by
        rw [Finset.disjoint_left]; intro v h1 h2
        simp only [Finset.mem_image] at h1 h2
        obtain ⟨_, _, rfl⟩ := h1; obtain ⟨_, _, heq⟩ := h2
        exact Bool.false_ne_true.symm (Prod.mk.inj heq).1
      have hc := congrArg Finset.card hpart
      rw [hScard, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective A (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_image_of_injective B (fun _ _ h => (Prod.mk.inj h).2)] at hc
      exact hc.symm

    have hsymAB : (symmDiff A B).card ≤ (borderOf (Mof π) S).card := by
      let f : Fin n → V n := fun i => if i ∈ A then (false, i) else (true, i)
      have hinj : Set.InjOn f ↑(symmDiff A B) := by
        intro i1 _ i2 _ heq
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · exact (Prod.mk.inj heq).2
        · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
        · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
        · exact (Prod.mk.inj heq).2
      have hsub : (symmDiff A B).image f ⊆ borderOf (Mof π) S := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨i, hi, rfl⟩ := hv
        rw [Finset.mem_symmDiff] at hi
        simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [borderOf, Finset.mem_filter]
        rcases hi with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · simp only [f, A, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
          exact ⟨h1, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, h2]⟩
        · simp only [f, A, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
          exact ⟨h2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, h1]⟩
      calc (symmDiff A B).card = ((symmDiff A B).image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub

    have hsymPi : (symmDiff (A.image π) B).card ≤ (borderOf (Mof π) S).card := by
      let f : Fin n → V n := fun y => if y ∈ A.image π then (false, π.symm y) else (true, y)
      have hinj : Set.InjOn f ↑(symmDiff (A.image π) B) := by
        intro y1 _ y2 _ heq
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · exact π.symm.injective (Prod.mk.inj heq).2
        · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
        · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
        · exact (Prod.mk.inj heq).2
      have hsub : (symmDiff (A.image π) B).image f ⊆ borderOf (Mof π) S := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        rw [Finset.mem_symmDiff] at hy
        simp only [borderOf, Finset.mem_filter]
        rcases hy with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · simp only [f, if_pos h1]
          rw [Finset.mem_image] at h1
          obtain ⟨i, hiA, rfl⟩ := h1
          simp only [Equiv.symm_apply_apply]
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA h2
          exact ⟨hiA, ⟨2, by omega⟩, by simp [mateOf, Mof, h2]⟩
        · simp only [f, if_neg h1]
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h2
          have hnotA : (false, π.symm y) ∉ S := fun hmem => h1 (Finset.mem_image.mpr
            ⟨π.symm y, by simp [A, hmem], by simp⟩)
          exact ⟨h2, ⟨2, by omega⟩, by simp [mateOf, Mof, hnotA]⟩
      calc (symmDiff (A.image π) B).card = ((symmDiff (A.image π) B).image f).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub

    have htrans_le : (transOf A).card ≤ 2 * (borderOf (Mof π) S).card := by
      let T1 := (transOf A).filter (fun i => (false, i) ∈ borderOf (Mof π) S)
      let T2 := (transOf A).filter (fun i => (false, M1 i) ∈ borderOf (Mof π) S ∨ (true, M1 i) ∈ borderOf (Mof π) S)
      have hcov : transOf A ⊆ T1 ∪ T2 := by
        intro i hi
        simp only [transOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [T1, T2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, transOf]
        by_cases hA1 : i ∈ A
        · have hA2 : M1 i ∉ A := by intro h; simp [hA1, h] at hi
          have hS1 : (false, i) ∈ S := (Finset.mem_filter.mp hA1).2
          have hS2 : (false, M1 i) ∉ S := fun h => hA2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          by_cases hB2 : (true, M1 i) ∈ S
          · right; refine ⟨hi, Or.inr ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hB2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, hS2]⟩
          · left; refine ⟨hi, ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hS1, ⟨1, by omega⟩, by simp [mateOf, Mof, hB2]⟩
        · have hA2 : M1 i ∈ A := by by_contra h; simp [hA1, h] at hi
          have hS1 : (false, i) ∉ S := fun h => hA1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hS2 : (false, M1 i) ∈ S := (Finset.mem_filter.mp hA2).2
          by_cases hB2 : (true, M1 i) ∈ S
          · right; refine ⟨hi, Or.inr ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hB2, ⟨1, by omega⟩, by simp [mateOf, Mof, hS1]⟩
          · right; refine ⟨hi, Or.inl ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hS2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, hB2]⟩
      have hT1_le : T1.card ≤ (borderOf (Mof π) S).card := by
        have hsub : T1.image (fun i => ((false, i) : V n)) ⊆ borderOf (Mof π) S := by
          intro v hv; rw [Finset.mem_image] at hv; obtain ⟨i, hi, rfl⟩ := hv
          exact (Finset.mem_filter.mp hi).2
        calc T1.card = (T1.image (fun i => ((false, i) : V n))).card :=
              (Finset.card_image_of_injective T1 (fun _ _ h => (Prod.mk.inj h).2)).symm
          _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub
      have hT2_le : T2.card ≤ (borderOf (Mof π) S).card := by
        let g : Fin n → V n := fun i => if (false, M1 i) ∈ borderOf (Mof π) S then (false, M1 i) else (true, M1 i)
        have hinj : Function.Injective g := by
          intro i1 i2 heq
          dsimp only [g] at heq
          split_ifs at heq with h1 h2 h2
          · exact M1.injective (Prod.mk.inj heq).2
          · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
          · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
          · exact M1.injective (Prod.mk.inj heq).2
        have hsub : T2.image g ⊆ borderOf (Mof π) S := by
          intro v hv; rw [Finset.mem_image] at hv; obtain ⟨i, hi, rfl⟩ := hv
          have hmem := (Finset.mem_filter.mp hi).2
          dsimp only [g]
          split_ifs with h1
          · exact h1
          · exact hmem.resolve_left h1
        calc T2.card = (T2.image g).card := (Finset.card_image_of_injective T2 hinj).symm
          _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub
      calc (transOf A).card ≤ (T1 ∪ T2).card := Finset.card_le_card hcov
        _ ≤ T1.card + T2.card := Finset.card_union_le T1 T2
        _ ≤ 2 * (borderOf (Mof π) S).card := by omega

    have hdiff_cards : A.card ≤ B.card + (symmDiff A B).card ∧ B.card ≤ A.card + (symmDiff A B).card := by
      have h1 : A ⊆ B ∪ symmDiff A B := by
        intro x hx; rw [Finset.mem_union, Finset.mem_symmDiff]
        by_cases hB : x ∈ B <;> simp [hx, hB]
      have h2 : B ⊆ A ∪ symmDiff A B := by
        intro x hx; rw [Finset.mem_union, Finset.mem_symmDiff]
        by_cases hA : x ∈ A <;> simp [hx, hA]
      exact ⟨le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _),
        le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)⟩
    have hA_cand : A ∈ candA := by
      simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hB_cand : B ∈ candB A := by
      simp only [candB, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hAB_mem : (A, B) ∈ candPairs := by
      simp only [candPairs, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨A, hA_cand, B, hB_cand, rfl⟩
    have hπ_bad : π ∈ badPerms := by
      simp only [badPerms, Finset.mem_biUnion]
      refine ⟨(A, B), hAB_mem, ?_⟩
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact hπ_good hπ_bad
  have hlow := part1_lower hn32 (Mof π) S
  have hexp : 3 * (n / 16384) + 3 ≤ b := by omega
  have hpow3 : 2 ^ (3 * (n / 16384) + 3) ≤ (2 * (dataOf n 3 (Mof π) S).2) ^ 3 := by
    calc 2 ^ (3 * (n / 16384) + 3)
        ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hexp
      _ ≤ 2 ^ (dataOf n 3 (Mof π) S).1 := Nat.pow_le_pow_right (by omega) hborder_ge
      _ ≤ (2 * (dataOf n 3 (Mof π) S).2) ^ 3 := hlow
  have hcube : (2 * 2 ^ (n / 16384)) ^ 3 ≤ (2 * (dataOf n 3 (Mof π) S).2) ^ 3 := by
    have heq : (2 * 2 ^ (n / 16384)) ^ 3 = 2 ^ (3 * (n / 16384) + 3) := by
      rw [mul_pow, ← pow_mul, mul_comm (n / 16384) 3, ← pow_add, Nat.add_comm]
    rw [heq]; exact hpow3
  by_contra hlt
  have hgt : 2 * (dataOf n 3 (Mof π) S).2 < 2 * 2 ^ (n / 16384) := by omega
  have hlt3 : (2 * (dataOf n 3 (Mof π) S).2) ^ 3 < (2 * 2 ^ (n / 16384)) ^ 3 :=
    Nat.pow_lt_pow_left hgt (by omega)
  omega

private theorem solve_pcx_292 :
    let data := fun (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) =>
      let V := Bool × Fin n
      let mate := fun (j : Fin r) (v : V) =>
        if v.1 then (false, (M j).symm v.2) else (true, M j v.2)
      let border := S.filter (fun v => ∃ j : Fin r, mate j v ∉ S)
      let rows := fun (x z : V → Bool) (j : Fin r) =>
        let word := fun v : V => if v ∈ S then x v else z v
        let D := (Finset.univ.filter (fun i : Fin n => word (false,i) ≠ word (true,M j i))).card
        decide (16 * Nat.dist (2*D) n ≤ n)
      (border.card, (Finset.univ.image rows).card)
    (∀ (n r : ℕ), 32 ≤ n → ∀ (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)),
      let q := data n r M S
      2^q.1 ≤ (2*q.2)^r ∧ q.2 ≤ (n+1)^r * 2^q.1) ∧
    (∀ n : ℕ, 32 ≤ n → ∀ M : Fin 2 → Equiv.Perm (Fin n),
      ∃ order : (Bool × Fin n) ≃ Fin (2*n), ∀ t : ℕ,
        (data n 2 M (Finset.univ.filter (fun v => (order v).val < t))).2 ≤ 4*(n+1)^2) ∧
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : Fin 3 → Equiv.Perm (Fin n),
      ∀ S : Finset (Bool × Fin n), S.card = n → 2^(n/16384) ≤ (data n 3 M S).2) :=
  ⟨fun _ _ hn M S => ⟨part1_lower hn M S, part1_upper M S⟩,
   part2_two_matchings,
   part3_three_matchings⟩

end PEqualNP.Outside.L_pcx_292_aux

theorem PEqualNP.Outside.L_pcx_292 :
    let data := fun (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) =>
      let V := Bool × Fin n
      let mate := fun (j : Fin r) (v : V) =>
        if v.1 then (false, (M j).symm v.2) else (true, M j v.2)
      let border := S.filter (fun v => ∃ j : Fin r, mate j v ∉ S)
      let rows := fun (x z : V → Bool) (j : Fin r) =>
        let word := fun v : V => if v ∈ S then x v else z v
        let D := (Finset.univ.filter (fun i : Fin n => word (false,i) ≠ word (true,M j i))).card
        decide (16 * Nat.dist (2*D) n ≤ n)
      (border.card, (Finset.univ.image rows).card)
    (∀ (n r : ℕ), 32 ≤ n → ∀ (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)),
      let q := data n r M S
      2^q.1 ≤ (2*q.2)^r ∧ q.2 ≤ (n+1)^r * 2^q.1) ∧
    (∀ n : ℕ, 32 ≤ n → ∀ M : Fin 2 → Equiv.Perm (Fin n),
      ∃ order : (Bool × Fin n) ≃ Fin (2*n), ∀ t : ℕ,
        (data n 2 M (Finset.univ.filter (fun v => (order v).val < t))).2 ≤ 4*(n+1)^2) ∧
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : Fin 3 → Equiv.Perm (Fin n),
      ∀ S : Finset (Bool × Fin n), S.card = n → 2^(n/16384) ≤ (data n 3 M S).2) :=
  PEqualNP.Outside.L_pcx_292_aux.solve_pcx_292

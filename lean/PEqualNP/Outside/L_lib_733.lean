import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_733_aux

private lemma sum_inv_two_pow_range (N : ℕ) :
    ∑ d ∈ Finset.range N, (1 : ℚ) / 2 ^ d = 2 - (1 : ℚ) / 2 ^ (N - 1) - (if N = 0 then 1 else 0) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    cases N with
    | zero => norm_num
    | succ k =>
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, sub_zero]
      rw [pow_succ]
      ring

private lemma sum_inv_two_pow_lt_two (T : Finset ℕ) :
    ∑ d ∈ T, (1 : ℚ) / 2 ^ d < 2 := by
  let N : ℕ := (T.sup id) + 1
  have hsub : T ⊆ Finset.range N := by
    intro d hd
    rw [Finset.mem_range]
    have hle : d ≤ T.sup id := Finset.le_sup (f := id) hd
    omega
  have hle_sum : ∑ d ∈ T, (1 : ℚ) / 2 ^ d ≤ ∑ d ∈ Finset.range N, (1 : ℚ) / 2 ^ d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
  rw [sum_inv_two_pow_range N] at hle_sum
  have hNpos : N ≠ 0 := Nat.succ_ne_zero _
  simp only [hNpos, ↓reduceIte, sub_zero] at hle_sum
  have hpos : (0 : ℚ) < (1 : ℚ) / 2 ^ (N - 1) := by positivity
  linarith

private lemma dyadic_finset_eq {A B : Finset ℕ}
    (heq : ∑ d ∈ A, (1 : ℚ) / 2 ^ d = ∑ d ∈ B, (1 : ℚ) / 2 ^ d) :
    A = B := by
  have hind : ∀ M : ℕ, ∀ A B : Finset ℕ,
      (∀ d ∈ A, d < M) → (∀ d ∈ B, d < M) →
      (∑ d ∈ A, (1 : ℚ) / 2 ^ d = ∑ d ∈ B, (1 : ℚ) / 2 ^ d) → A = B := by
    intro M
    induction M with
    | zero =>
      intro A B hA hB _
      ext d
      constructor
      · intro hd; exact absurd (hA d hd) (Nat.not_lt_zero d)
      · intro hd; exact absurd (hB d hd) (Nat.not_lt_zero d)
    | succ M ih =>
      intro A B hA hB hsum
      have hscale : ∀ T : Finset ℕ, (∀ d ∈ T, d < M + 1) →
          (∑ d ∈ T, (1 : ℚ) / 2 ^ d) * (2 : ℚ) ^ M =
            ((∑ d ∈ T, 2 ^ (M - d) : ℕ) : ℚ) := by
        intro T hT
        rw [Finset.sum_mul, Nat.cast_sum]
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hdle : d ≤ M := Nat.le_of_lt_succ (hT d hd)
        have hpow : (2 : ℚ) ^ M = (2 : ℚ) ^ d * (2 : ℚ) ^ (M - d) := by
          rw [← pow_add, Nat.add_sub_of_le hdle]
        have hne : (2 : ℚ) ^ d ≠ 0 := by positivity
        push_cast
        rw [hpow]
        field_simp [hne]
      have hnat_eq : (∑ d ∈ A, 2 ^ (M - d) : ℕ) = ∑ d ∈ B, 2 ^ (M - d) := by
        have hQ : ((∑ d ∈ A, 2 ^ (M - d) : ℕ) : ℚ) = ((∑ d ∈ B, 2 ^ (M - d) : ℕ) : ℚ) := by
          rw [← hscale A hA, ← hscale B hB, hsum]
        exact_mod_cast hQ
      have hpar : ∀ T : Finset ℕ, (∀ d ∈ T, d < M + 1) →
          (∑ d ∈ T, 2 ^ (M - d)) % 2 = if M ∈ T then 1 else 0 := by
        intro T hT
        have hmod : ∀ d ∈ T.erase M, 2 ∣ 2 ^ (M - d) := by
          intro d hd
          have hne : d ≠ M := (Finset.mem_erase.mp hd).1
          have hlt : d < M := by have := hT d (Finset.mem_erase.mp hd).2; omega
          have hpos : 1 ≤ M - d := by omega
          exact dvd_pow_self 2 (by omega)
        have hdvd : 2 ∣ ∑ d ∈ T.erase M, 2 ^ (M - d) := Finset.dvd_sum hmod
        by_cases hM : M ∈ T
        · rw [← Finset.add_sum_erase _ _ hM]
          simp only [hM, ↓reduceIte, Nat.sub_self, pow_zero]
          rcases hdvd with ⟨c, hc⟩
          rw [hc]
          omega
        · have her : T.erase M = T := Finset.erase_eq_of_notMem hM
          rw [her] at hdvd
          simp only [hM, ↓reduceIte]
          rcases hdvd with ⟨c, hc⟩
          rw [hc]
          omega
      have hM_iff : M ∈ A ↔ M ∈ B := by
        have h1 := hpar A hA
        have h2 := hpar B hB
        rw [hnat_eq] at h1
        by_cases hMA : M ∈ A <;> by_cases hMB : M ∈ B <;> simp_all
      have hsum_er : ∑ d ∈ A.erase M, (1 : ℚ) / 2 ^ d = ∑ d ∈ B.erase M, (1 : ℚ) / 2 ^ d := by
        by_cases hMA : M ∈ A
        · have hMB : M ∈ B := hM_iff.mp hMA
          have h1 := Finset.add_sum_erase A (fun d => (1 : ℚ) / 2 ^ d) hMA
          have h2 := Finset.add_sum_erase B (fun d => (1 : ℚ) / 2 ^ d) hMB
          linarith
        · have hMB : M ∉ B := fun h => hMA (hM_iff.mpr h)
          rw [Finset.erase_eq_of_notMem hMA, Finset.erase_eq_of_notMem hMB]
          exact hsum
      have her_eq : A.erase M = B.erase M := ih (A.erase M) (B.erase M)
        (fun d hd => by have h1 := (Finset.mem_erase.mp hd).1; have h2 := hA d (Finset.mem_erase.mp hd).2; omega)
        (fun d hd => by have h1 := (Finset.mem_erase.mp hd).1; have h2 := hB d (Finset.mem_erase.mp hd).2; omega)
        hsum_er
      ext d
      by_cases hdM : d = M
      · subst hdM; exact hM_iff
      · have := Finset.ext_iff.mp her_eq d
        simpa [Finset.mem_erase, hdM] using this
  let M : ℕ := max (A.sup id) (B.sup id) + 1
  exact hind M A B
    (fun d hd => lt_of_le_of_lt (le_trans (Finset.le_sup (f := id) hd) (le_max_left _ _)) (Nat.lt_succ_self _))
    (fun d hd => lt_of_le_of_lt (le_trans (Finset.le_sup (f := id) hd) (le_max_right _ _)) (Nat.lt_succ_self _))
    heq

private structure Block (m : ℕ) where
  depth : ℕ
  elems : Finset (Fin m)
  off : Fin m → ℕ

private def ValidBlock {m : ℕ} (leaf : Fin m → ℕ) (b : Block m) : Prop :=
  b.elems.Nonempty ∧
  (∀ i ∈ b.elems, leaf i = b.depth + b.off i) ∧
  (∀ i ∈ b.elems, b.off i < b.elems.card) ∧
  (∑ i ∈ b.elems, (1 : ℚ) / 2 ^ (b.off i)) = 1

private def ValidState {m : ℕ} (leaf : Fin m → ℕ) (bs : List (Block m)) : Prop :=
  (∀ b ∈ bs, ValidBlock leaf b) ∧
  (∀ p q : Fin bs.length, p ≠ q → Disjoint (bs.get p).elems (bs.get q).elems) ∧
  (∀ i : Fin m, ∃ b ∈ bs, i ∈ b.elems)

private lemma list_map_sum_eq_fin_sum {α : Type*} (l : List α) (f : α → ℚ) :
    (l.map f).sum = ∑ p : Fin l.length, f (l.get p) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Fin.sum_univ_succ, ih]
    rfl

private lemma state_sum_eq {m : ℕ} (leaf : Fin m → ℕ) (bs : List (Block m))
    (hval : ValidState leaf bs) :
    (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum = ∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i) := by
  have hblk_sum : ∀ b ∈ bs, (1 : ℚ) / 2 ^ b.depth = ∑ i ∈ b.elems, (1 : ℚ) / 2 ^ (leaf i) := by
    intro b hb
    rcases hval.1 b hb with ⟨_, hleaf, _, h1⟩
    calc
      (1 : ℚ) / 2 ^ b.depth = (1 : ℚ) / 2 ^ b.depth * (∑ i ∈ b.elems, (1 : ℚ) / 2 ^ (b.off i)) := by
        rw [h1, mul_one]
      _ = ∑ i ∈ b.elems, (1 : ℚ) / 2 ^ b.depth * ((1 : ℚ) / 2 ^ (b.off i)) := Finset.mul_sum _ _ _
      _ = ∑ i ∈ b.elems, (1 : ℚ) / 2 ^ (leaf i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hleaf i hi, pow_add]
        ring
  have hmap : (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum =
      ∑ p : Fin bs.length, ∑ i ∈ (bs.get p).elems, (1 : ℚ) / 2 ^ (leaf i) := by
    rw [list_map_sum_eq_fin_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    exact hblk_sum (bs.get p) (List.get_mem bs p)
  rw [hmap]
  have hunion : (Finset.univ : Finset (Fin bs.length)).biUnion (fun p => (bs.get p).elems) = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    rcases hval.2.2 i with ⟨b, hb, hi⟩
    rcases List.mem_iff_get.mp hb with ⟨p, rfl⟩
    exact ⟨p, hi⟩
  rw [← hunion, Finset.sum_biUnion]
  intro p _ q _ hpq
  exact hval.2.1 p q hpq

private lemma merge_to_nodup {m : ℕ} (leaf : Fin m → ℕ)
    (hlt : ∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i) < 2) :
    ∀ (k : ℕ) (bs : List (Block m)), bs.length = k → ValidState leaf bs →
      ∃ bs' : List (Block m), ValidState leaf bs' ∧ (bs'.map Block.depth).Nodup := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro bs hlen hval
    by_cases hnd : (bs.map Block.depth).Nodup
    · exact ⟨bs, hval, hnd⟩
    · have hex_dup : ∃ p q : Fin bs.length, p ≠ q ∧ (bs.get p).depth = (bs.get q).depth := by
        by_contra hall
        push_neg at hall
        apply hnd
        rw [List.nodup_iff_injective_get]
        intro p q hpq
        have hp' : p.val < bs.length := by simpa using p.isLt
        have hq' : q.val < bs.length := by simpa using q.isLt
        have hdeq : (bs.get ⟨p.val, hp'⟩).depth = (bs.get ⟨q.val, hq'⟩).depth := by
          simpa using hpq
        by_contra hne
        have hne' : (⟨p.val, hp'⟩ : Fin bs.length) ≠ ⟨q.val, hq'⟩ := fun h => hne (Fin.ext (congrArg (Fin.val : Fin bs.length → ℕ) h))
        exact hall ⟨p.val, hp'⟩ ⟨q.val, hq'⟩ hne' hdeq
      rcases hex_dup with ⟨p, q, hpq, hdeq⟩
      let b1 := bs.get p
      let b2 := bs.get q
      have hd_pos : 0 < b1.depth := by
        by_contra hd0
        have hdz : b1.depth = 0 := by omega
        have hsum_eq := state_sum_eq leaf bs hval
        have hge2 : (2 : ℚ) ≤ (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum := by
          rw [list_map_sum_eq_fin_sum]
          have hsub : ({p, q} : Finset (Fin bs.length)) ⊆ Finset.univ := Finset.subset_univ _
          have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r : Fin bs.length => (1 : ℚ) / 2 ^ (bs.get r).depth) hsub (fun r _ _ => by positivity)
          rw [Finset.sum_pair hpq] at hle
          have hp0 : (bs.get p).depth = 0 := hdz
          have hq0 : (bs.get q).depth = 0 := hdeq.symm.trans hdz
          have h1 : (1 : ℚ) / 2 ^ (bs.get p).depth = 1 := by rw [hp0]; norm_num
          have h2 : (1 : ℚ) / 2 ^ (bs.get q).depth = 1 := by rw [hq0]; norm_num
          linarith
        linarith
      let merged : Block m :=
        { depth := b1.depth - 1
          elems := b1.elems ∪ b2.elems
          off := fun i => if i ∈ b1.elems then b1.off i + 1 else b2.off i + 1 }
      have hdisj12 : Disjoint b1.elems b2.elems := hval.2.1 p q hpq
      have hvb1 := hval.1 b1 (List.get_mem bs p)
      have hvb2 := hval.1 b2 (List.get_mem bs q)
      have hv_merged : ValidBlock leaf merged := by
        refine ⟨hvb1.1.mono Finset.subset_union_left, ?_, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_union.mp hi with hi1 | hi2
          · simp only [merged, hi1, ↓reduceIte]
            have := hvb1.2.1 i hi1
            omega
          · have hni1 : i ∉ b1.elems := Finset.disjoint_right.mp hdisj12 hi2
            simp only [merged, hni1, ↓reduceIte]
            have := hvb2.2.1 i hi2
            have hdeq' : b2.depth = b1.depth := hdeq.symm
            omega
        · intro i hi
          have hcard_u : (b1.elems ∪ b2.elems).card = b1.elems.card + b2.elems.card :=
            Finset.card_union_of_disjoint hdisj12
          have hc1 : 0 < b1.elems.card := Finset.card_pos.mpr hvb1.1
          have hc2 : 0 < b2.elems.card := Finset.card_pos.mpr hvb2.1
          rcases Finset.mem_union.mp hi with hi1 | hi2
          · simp only [merged, hi1, ↓reduceIte]
            have := hvb1.2.2.1 i hi1
            omega
          · have hni1 : i ∉ b1.elems := Finset.disjoint_right.mp hdisj12 hi2
            simp only [merged, hni1, ↓reduceIte]
            have := hvb2.2.2.1 i hi2
            omega
        · dsimp only [merged]
          rw [Finset.sum_union hdisj12]
          have hs1 : ∑ i ∈ b1.elems, (1 : ℚ) / 2 ^ (if i ∈ b1.elems then b1.off i + 1 else b2.off i + 1) = (1 : ℚ) / 2 := by
            have hcongr : ∑ i ∈ b1.elems, (1 : ℚ) / 2 ^ (if i ∈ b1.elems then b1.off i + 1 else b2.off i + 1) =
                (1 : ℚ) / 2 * ∑ i ∈ b1.elems, (1 : ℚ) / 2 ^ (b1.off i) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp only [hi, ↓reduceIte, pow_succ]
              ring
            rw [hcongr, hvb1.2.2.2, mul_one]
          have hs2 : ∑ i ∈ b2.elems, (1 : ℚ) / 2 ^ (if i ∈ b1.elems then b1.off i + 1 else b2.off i + 1) = (1 : ℚ) / 2 := by
            have hcongr : ∑ i ∈ b2.elems, (1 : ℚ) / 2 ^ (if i ∈ b1.elems then b1.off i + 1 else b2.off i + 1) =
                (1 : ℚ) / 2 * ∑ i ∈ b2.elems, (1 : ℚ) / 2 ^ (b2.off i) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hni1 : i ∉ b1.elems := Finset.disjoint_right.mp hdisj12 hi
              simp only [hni1, ↓reduceIte, pow_succ]
              ring
            rw [hcongr, hvb2.2.2.2, mul_one]
          rw [hs1, hs2]
          norm_num
      let restIdx : List (Fin bs.length) := (List.finRange bs.length).filter (fun r => decide (r ≠ p ∧ r ≠ q))
      let bs1 : List (Block m) := merged :: restIdx.map bs.get
      have hrest_nodup : restIdx.Nodup := (List.nodup_finRange _).filter _
      have hrest_len : restIdx.length + 2 = bs.length := by
        have htoF : restIdx.toFinset = (Finset.univ.erase p).erase q := by
          ext r
          simp only [restIdx, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
                     decide_eq_true_eq, Finset.mem_erase, Finset.mem_univ, and_true, and_comm]
        have hcl : restIdx.length = restIdx.toFinset.card := (List.toFinset_card_of_nodup hrest_nodup).symm
        rw [hcl, htoF, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩),
            Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
        have h2le : 2 ≤ bs.length := by
          have : ({p, q} : Finset (Fin bs.length)).card ≤ (Finset.univ : Finset (Fin bs.length)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          rw [Finset.card_pair hpq, Finset.card_univ, Fintype.card_fin] at this
          exact this
        omega
      have hbs1_len : bs1.length < k := by
        simp only [bs1, List.length_cons, List.length_map]
        omega
      have hval1 : ValidState leaf bs1 := by
        refine ⟨?_, ?_, ?_⟩
        · intro b hb
          simp only [bs1, List.mem_cons, List.mem_map] at hb
          rcases hb with rfl | ⟨r, _, rfl⟩
          · exact hv_merged
          · exact hval.1 (bs.get r) (List.get_mem bs r)
        · intro u v huv
          have get_bs1 : ∀ w : Fin bs1.length,
              (w.val = 0 ∧ bs1.get w = merged) ∨
              (∃ (hw : w.val - 1 < restIdx.length),
                w.val ≠ 0 ∧ bs1.get w = bs.get (restIdx.get ⟨w.val - 1, hw⟩)) := by
            intro w
            cases hwf : w.val with
            | zero =>
              left
              refine ⟨rfl, ?_⟩
              simp [bs1, hwf]
            | succ n =>
              right
              have hwlt : n < restIdx.length := by
                have := w.isLt
                simp only [bs1, List.length_cons, List.length_map] at this
                omega
              refine ⟨hwlt, Nat.succ_ne_zero n, ?_⟩
              simp [bs1, hwf]
          rcases get_bs1 u with ⟨hu0, hueq⟩ | ⟨hu, hu0, hueq⟩ <;>
          rcases get_bs1 v with ⟨hv0, hveq⟩ | ⟨hv, hv0, hveq⟩
          · exact (huv (Fin.ext (hu0.trans hv0.symm))).elim
          · rw [hueq, hveq]
            have hr_mem : restIdx.get ⟨v.val - 1, hv⟩ ∈ restIdx := List.get_mem _ _
            have hr_ne : restIdx.get ⟨v.val - 1, hv⟩ ≠ p ∧ restIdx.get ⟨v.val - 1, hv⟩ ≠ q := by
              simpa [restIdx] using (List.mem_filter.mp hr_mem).2
            exact Finset.disjoint_union_left.mpr ⟨hval.2.1 p _ hr_ne.1.symm, hval.2.1 q _ hr_ne.2.symm⟩
          · rw [hueq, hveq]
            have hr_mem : restIdx.get ⟨u.val - 1, hu⟩ ∈ restIdx := List.get_mem _ _
            have hr_ne : restIdx.get ⟨u.val - 1, hu⟩ ≠ p ∧ restIdx.get ⟨u.val - 1, hu⟩ ≠ q := by
              simpa [restIdx] using (List.mem_filter.mp hr_mem).2
            exact Finset.disjoint_union_right.mpr ⟨hval.2.1 _ p hr_ne.1, hval.2.1 _ q hr_ne.2⟩
          · rw [hueq, hveq]
            apply hval.2.1
            intro heqr
            have hidx_eq : (⟨u.val - 1, hu⟩ : Fin restIdx.length) = ⟨v.val - 1, hv⟩ :=
              (List.nodup_iff_injective_get.mp hrest_nodup) heqr
            have hval_eq : u.val - 1 = v.val - 1 := congrArg Fin.val hidx_eq
            exact huv (Fin.ext (by omega))
        · intro i
          rcases hval.2.2 i with ⟨b, hb, hi⟩
          rcases List.mem_iff_get.mp hb with ⟨r, rfl⟩
          by_cases hrp : r = p
          · subst hrp
            exact ⟨merged, List.mem_cons_self .., Finset.mem_union_left _ hi⟩
          · by_cases hrq : r = q
            · subst hrq
              exact ⟨merged, List.mem_cons_self .., Finset.mem_union_right _ hi⟩
            · refine ⟨bs.get r, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r, ?_, rfl⟩), hi⟩
              simp [restIdx, hrp, hrq]
      exact ih bs1.length hbs1_len bs1 rfl hval1

end PEqualNP.Outside.L_lib_733_aux

open PEqualNP.Outside.L_lib_733_aux in
theorem PEqualNP.Outside.L_lib_733 :
∀ (m s : ℕ) (leaf : Fin m → ℕ) (root : Fin s → ℕ), Function.Injective root →
  (((∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i)) =
    ∑ j : Fin s, (1 : ℚ) / 2 ^ (root j)) ↔
    ∃ (group : Fin m → Fin s) (offset : Fin m → Fin m),
      (∀ i, leaf i = root (group i) + (offset i).val) ∧
      ∀ j : Fin s,
        (∑ i ∈ (Finset.univ.filter (fun k : Fin m => group k = j)),
          2 ^ (m - (offset i).val) : ℕ) = 2 ^ m) := by
  intro m s leaf root hroot
  constructor
  · intro hsum
    have hlt2 : ∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i) < 2 := by
      rw [hsum]
      have himg : ∑ j : Fin s, (1 : ℚ) / 2 ^ (root j) =
          ∑ d ∈ Finset.univ.image root, (1 : ℚ) / 2 ^ d := by
        symm
        exact Finset.sum_image (fun a _ b _ h => hroot h)
      rw [himg]
      exact sum_inv_two_pow_lt_two _
    let init : List (Block m) :=
      (List.finRange m).map (fun i => { depth := leaf i, elems := {i}, off := fun _ => 0 })
    have hinit_val : ValidState leaf init := by
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_map.mp hb with ⟨i, _, rfl⟩
        refine ⟨Finset.singleton_nonempty i, ?_, ?_, ?_⟩
        · intro x hx; simp [Finset.mem_singleton.mp hx]
        · intro x hx; simp
        · simp
      · intro p q hpq
        have hp' : p.val < m := by simpa [init] using p.isLt
        have hq' : q.val < m := by simpa [init] using q.isLt
        have hgetp : (init.get p).elems = {⟨p.val, hp'⟩} := by simp [init]
        have hgetq : (init.get q).elems = {⟨q.val, hq'⟩} := by simp [init]
        rw [hgetp, hgetq, Finset.disjoint_singleton]
        intro heq
        exact hpq (Fin.ext (congrArg (Fin.val : Fin m → ℕ) heq))
      · intro i
        refine ⟨{ depth := leaf i, elems := {i}, off := fun _ => 0 }, ?_, Finset.mem_singleton_self i⟩
        exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    rcases merge_to_nodup leaf hlt2 init.length init rfl hinit_val with ⟨bs, hval, hnd⟩
    have hA_eq_B : (bs.map Block.depth).toFinset = Finset.univ.image root := by
      apply dyadic_finset_eq
      have h1 : ∑ d ∈ (bs.map Block.depth).toFinset, (1 : ℚ) / 2 ^ d =
          (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum := by
        rw [List.sum_toFinset _ hnd, List.map_map]
        rfl
      have h2 : ∑ d ∈ Finset.univ.image root, (1 : ℚ) / 2 ^ d =
          ∑ j : Fin s, (1 : ℚ) / 2 ^ (root j) :=
        Finset.sum_image (fun a _ b _ h => hroot h)
      rw [h1, h2, state_sum_eq leaf bs hval, hsum]
    have huniq_blk : ∀ i : Fin m, ∃! p : Fin bs.length, i ∈ (bs.get p).elems := by
      intro i
      rcases hval.2.2 i with ⟨b, hb, hi⟩
      rcases List.mem_iff_get.mp hb with ⟨p, rfl⟩
      refine ⟨p, hi, ?_⟩
      intro q hq
      by_contra hne
      exact Finset.disjoint_left.mp (hval.2.1 q p hne) hq hi
    have hblk_to_root : ∀ p : Fin bs.length, ∃! j : Fin s, root j = (bs.get p).depth := by
      intro p
      have hmem : (bs.get p).depth ∈ Finset.univ.image root := by
        rw [← hA_eq_B, List.mem_toFinset]
        exact List.mem_map.mpr ⟨bs.get p, List.get_mem bs p, rfl⟩
      rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
      exact ⟨j, hj, fun j' hj' => hroot (hj'.trans hj.symm)⟩
    have hroot_to_blk : ∀ j : Fin s, ∃! p : Fin bs.length, (bs.get p).depth = root j := by
      intro j
      have hmem : root j ∈ (bs.map Block.depth).toFinset := by
        rw [hA_eq_B]; exact Finset.mem_image_of_mem root (Finset.mem_univ j)
      rw [List.mem_toFinset] at hmem
      rcases List.mem_map.mp hmem with ⟨b, hb, hbj⟩
      rcases List.mem_iff_get.mp hb with ⟨p, rfl⟩
      refine ⟨p, hbj, ?_⟩
      intro q hqj
      have hdeq : (bs.map Block.depth).get ⟨q.val, by simp⟩ =
          (bs.map Block.depth).get ⟨p.val, by simp⟩ := by
        simp only [List.get_eq_getElem, List.getElem_map]
        exact hqj.trans hbj.symm
      have := (List.nodup_iff_injective_get.mp hnd) hdeq
      exact Fin.ext (congrArg (Fin.val : Fin (bs.map Block.depth).length → ℕ) this)
    choose blkOf hblkOf_mem hblkOf_uniq using huniq_blk
    choose rootOf hrootOf_eq hrootOf_uniq using hblk_to_root
    let group : Fin m → Fin s := fun i => rootOf (blkOf i)
    have hoff_lt : ∀ i : Fin m, (bs.get (blkOf i)).off i < m := by
      intro i
      have hvb := hval.1 (bs.get (blkOf i)) (List.get_mem bs (blkOf i))
      have h1 := hvb.2.2.1 i (hblkOf_mem i)
      have h2 : (bs.get (blkOf i)).elems.card ≤ m := by
        simpa using Finset.card_le_univ (bs.get (blkOf i)).elems
      exact lt_of_lt_of_le h1 h2
    let offset : Fin m → Fin m := fun i => ⟨(bs.get (blkOf i)).off i, hoff_lt i⟩
    refine ⟨group, offset, ?_, ?_⟩
    · intro i
      have hvb := hval.1 (bs.get (blkOf i)) (List.get_mem bs (blkOf i))
      have hl := hvb.2.1 i (hblkOf_mem i)
      dsimp only [group, offset]
      rw [hrootOf_eq (blkOf i)]
      exact hl
    · intro j
      rcases hroot_to_blk j with ⟨p, hp_eq, hp_uniq⟩
      have hfilt_eq : Finset.univ.filter (fun k : Fin m => group k = j) = (bs.get p).elems := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, group]
        constructor
        · intro hgj
          have hp_eq' : blkOf i = p := hp_uniq (blkOf i) (by change (bs.get (blkOf i)).depth = root j; rw [← hrootOf_eq (blkOf i), hgj])
          rw [← hp_eq']
          exact hblkOf_mem i
        · intro hi
          have hpi : blkOf i = p := (hblkOf_uniq i p hi).symm
          rw [hpi]
          exact (hrootOf_uniq p j hp_eq.symm).symm
      rw [hfilt_eq]
      have hvb := hval.1 (bs.get p) (List.get_mem bs p)
      have hsumQ : ∑ i ∈ (bs.get p).elems, (1 : ℚ) / 2 ^ ((offset i).val) = 1 := by
        have hcongr : ∑ i ∈ (bs.get p).elems, (1 : ℚ) / 2 ^ ((offset i).val) =
            ∑ i ∈ (bs.get p).elems, (1 : ℚ) / 2 ^ ((bs.get p).off i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hpi : blkOf i = p := (hblkOf_uniq i p hi).symm
          simp [offset, hpi]
        rw [hcongr, hvb.2.2.2]
      have hnatQ : ((∑ i ∈ (bs.get p).elems, 2 ^ (m - (offset i).val) : ℕ) : ℚ) = ((2 ^ m : ℕ) : ℚ) := by
        have hmul := congrArg (fun x : ℚ => x * (2 : ℚ) ^ m) hsumQ
        simp only [one_mul, Finset.sum_mul] at hmul
        rw [Nat.cast_sum]
        push_cast
        rw [← hmul]
        refine Finset.sum_congr rfl ?_
        intro i _
        have hle : (offset i).val ≤ m := le_of_lt (offset i).isLt
        have hpow : (2 : ℚ) ^ m = (2 : ℚ) ^ (offset i).val * (2 : ℚ) ^ (m - (offset i).val) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        have hne : (2 : ℚ) ^ (offset i).val ≠ 0 := by positivity
        rw [hpow]
        field_simp [hne]
      exact_mod_cast hnatQ
  · rintro ⟨group, offset, hleaf, hblk⟩
    have hfib := (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin m)))
      (t := (Finset.univ : Finset (Fin s))) (g := group) (fun _ _ => Finset.mem_univ _)
      (fun i => (1 : ℚ) / 2 ^ (leaf i))).symm
    rw [hfib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hterm : ∑ i ∈ Finset.univ.filter (fun k : Fin m => group k = j), (1 : ℚ) / 2 ^ (leaf i) =
        ((∑ i ∈ Finset.univ.filter (fun k : Fin m => group k = j), 2 ^ (m - (offset i).val) : ℕ) : ℚ) /
          (2 : ℚ) ^ (root j + m) := by
      rw [Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hgi : group i = j := (Finset.mem_filter.mp hi).2
      have hl : leaf i = root j + (offset i).val := by rw [← hgi]; exact hleaf i
      have hle : (offset i).val ≤ m := le_of_lt (offset i).isLt
      have hpow : (2 : ℚ) ^ (root j + m) = (2 : ℚ) ^ (root j + (offset i).val) * (2 : ℚ) ^ (m - (offset i).val) := by
        rw [← pow_add]
        congr 1
        omega
      have hne1 : (2 : ℚ) ^ (root j + (offset i).val) ≠ 0 := by positivity
      have hne2 : (2 : ℚ) ^ (m - (offset i).val) ≠ 0 := by positivity
      push_cast
      rw [hl, hpow]
      field_simp [hne1, hne2]
    rw [hterm, hblk j]
    push_cast
    rw [pow_add]
    have hne1 : (2 : ℚ) ^ (root j) ≠ 0 := by positivity
    have hne2 : (2 : ℚ) ^ m ≠ 0 := by positivity
    field_simp [hne1, hne2]

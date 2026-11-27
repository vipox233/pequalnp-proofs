import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_865_aux

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

private lemma card_ne_zero {α : Type*} [Fintype α] [DecidableEq α] [Zero α] :
    Fintype.card {x : α // x ≠ 0} = Fintype.card α - 1 := by
  have h1 : Fintype.card {x : α // x ≠ 0} = (Finset.univ.filter (fun x : α => x ≠ 0)).card :=
    Fintype.card_subtype _
  rw [h1]
  have hdisj : Disjoint (Finset.univ.filter (fun x : α => x ≠ 0)) ({0} : Finset α) := by
    rw [Finset.disjoint_singleton_right]; simp
  have hunion : Finset.univ.filter (fun x : α => x ≠ 0) ∪ ({0} : Finset α) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, iff_true]
    exact ne_or_eq x 0
  have hsplit : Fintype.card α = (Finset.univ.filter (fun x : α => x ≠ 0)).card + 1 := by
    conv_lhs => rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  omega

private lemma zmod_two_mul_inv (a : ℕ) :
    let n := 2 * a + 1
    (2 : ZMod n) * ((a + 1 : ℕ) : ZMod n) = 1 := by
  dsimp only
  have h : (2 : ℕ) * (a + 1) = (2 * a + 1) + 1 := by omega
  have hcast : ((2 * (a + 1) : ℕ) : ZMod (2 * a + 1)) = (((2 * a + 1) + 1 : ℕ) : ZMod (2 * a + 1)) := by
    rw [h]
  rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one] at hcast
  rw [Nat.cast_mul, Nat.cast_ofNat] at hcast
  exact hcast

private lemma zmod_two_mul_cancel {a : ℕ} {x y : ZMod (2 * a + 1)}
    (h : (2 : ZMod (2 * a + 1)) * x = (2 : ZMod (2 * a + 1)) * y) : x = y := by
  have h1 := congrArg (fun z => ((a + 1 : ℕ) : ZMod (2 * a + 1)) * z) h
  have hinv := zmod_two_mul_inv a
  dsimp only at hinv
  have hmul : ∀ z : ZMod (2 * a + 1),
      ((a + 1 : ℕ) : ZMod (2 * a + 1)) * ((2 : ZMod (2 * a + 1)) * z) = z := by
    intro z
    calc ((a + 1 : ℕ) : ZMod (2 * a + 1)) * ((2 : ZMod (2 * a + 1)) * z)
        = ((2 : ZMod (2 * a + 1)) * ((a + 1 : ℕ) : ZMod (2 * a + 1))) * z := by ring
      _ = 1 * z := by rw [hinv]
      _ = z := one_mul z
  rw [hmul, hmul] at h1
  exact h1

private lemma zmod_natCast_eq_iff {n : ℕ} [NeZero n] {x y : ℕ} (hx : x < n) (hy : y < n) :
    (x : ZMod n) = (y : ZMod n) ↔ x = y := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hv
    exact hv
  · intro h; rw [h]

private lemma zmod_add_natCast_eq_iff {n : ℕ} [NeZero n] (k : ZMod n) {x y : ℕ}
    (hx : x < n) (hy : y < n) :
    k + (x : ZMod n) = k + (y : ZMod n) ↔ x = y := by
  constructor
  · intro h; exact (zmod_natCast_eq_iff hx hy).mp (add_left_cancel h)
  · intro h; rw [h]

private lemma zmod_next_step2_iff {a : ℕ} (z1 z2 : ZMod (2 * a + 1)) :
    (2 : ZMod (2 * a + 1)) * z1 + 1 = (2 : ZMod (2 * a + 1)) * z2 ↔
      z1 = z2 + (a : ZMod (2 * a + 1)) := by
  have h2a : (2 : ZMod (2 * a + 1)) * (a : ZMod (2 * a + 1)) + 1 = 0 := by
    have h : ((2 * a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 := ZMod.natCast_self (2 * a + 1)
    push_cast at h
    exact h
  constructor
  · intro h
    apply zmod_two_mul_cancel
    calc (2 : ZMod (2 * a + 1)) * z1
        = ((2 : ZMod (2 * a + 1)) * z1 + 1) + (2 : ZMod (2 * a + 1)) * (a : ZMod (2 * a + 1)) -
            ((2 : ZMod (2 * a + 1)) * (a : ZMod (2 * a + 1)) + 1) := by ring
      _ = (2 : ZMod (2 * a + 1)) * z2 + (2 : ZMod (2 * a + 1)) * (a : ZMod (2 * a + 1)) - 0 := by
            rw [h, h2a]
      _ = (2 : ZMod (2 * a + 1)) * (z2 + (a : ZMod (2 * a + 1))) := by ring
  · intro h
    rw [h]
    calc (2 : ZMod (2 * a + 1)) * (z2 + (a : ZMod (2 * a + 1))) + 1
        = (2 : ZMod (2 * a + 1)) * z2 + ((2 : ZMod (2 * a + 1)) * (a : ZMod (2 * a + 1)) + 1) := by ring
      _ = (2 : ZMod (2 * a + 1)) * z2 := by rw [h2a, add_zero]

private lemma ind_set_alternating {a : ℕ} (S : Finset (ZMod (2 * a + 1)))
    (hcard : S.card = a) (hind : ∀ z ∈ S, z + 1 ∉ S) :
    ∃ w : ZMod (2 * a + 1), ∀ t : Fin a, w + (2 * t.val : ℕ) ∈ S := by
  let n := 2 * a + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  have hex_gap : ∃ u : ZMod n, u ∉ S ∧ u - 1 ∉ S := by
    by_contra hall
    push Not at hall
    have hinj : (Finset.univ \ S).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (fun u => u - 1)
      · intro u hu
        have huS : u ∉ S := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hu)).2
        exact Finset.mem_coe.mpr (hall u huS)
      · intro u1 _ u2 _ heq
        exact sub_left_inj.mp heq
    have hcomp : S.card + (Finset.univ \ S).card = n := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ S), Finset.card_univ, ZMod.card]
      have hle : S.card ≤ n := by rw [hcard]; omega
      omega
    omega
  rcases hex_gap with ⟨u, hu0, hu1⟩
  let w := u + 1
  have hdisj_boxes : ∀ t1 t2 : Fin a, t1 ≠ t2 →
      Disjoint
        (if t1.val = 0 then ({w} : Finset (ZMod n)) else {w + (2 * t1.val - 1 : ℕ), w + (2 * t1.val : ℕ)})
        (if t2.val = 0 then ({w} : Finset (ZMod n)) else {w + (2 * t2.val - 1 : ℕ), w + (2 * t2.val : ℕ)}) := by
    intro t1 t2 hne
    have hval_ne : t1.val ≠ t2.val := fun h => hne (Fin.ext h)
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hmem : ∀ (t : Fin a),
        x ∈ (if t.val = 0 then ({w} : Finset (ZMod n)) else {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}) →
        ∃ d : ℕ, d < 2 * a - 1 ∧ x = w + (d : ZMod n) ∧ (d = 2 * t.val ∨ (0 < t.val ∧ d = 2 * t.val - 1)) := by
      intro t hxt
      split_ifs at hxt with ht0
      · rw [Finset.mem_singleton] at hxt
        refine ⟨0, by have := t.isLt; omega, by simpa using hxt, Or.inl (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
        rcases hxt with rfl | rfl
        · refine ⟨2 * t.val - 1, by have := t.isLt; omega, rfl, Or.inr ⟨by omega, rfl⟩⟩
        · refine ⟨2 * t.val, by have := t.isLt; omega, rfl, Or.inl rfl⟩
    obtain ⟨d1, hd1lt, hx_eq1, h1⟩ := hmem t1 hx1
    obtain ⟨d2, hd2lt, hx_eq2, h2⟩ := hmem t2 hx2
    have hd_eq : d1 = d2 := (zmod_add_natCast_eq_iff w (by omega : d1 < n) (by omega : d2 < n)).mp (hx_eq1.symm.trans hx_eq2)
    omega
  let box : Fin a → Finset (ZMod n) := fun t =>
    if t.val = 0 then {w} else {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}
  have hbox_le : ∀ t : Fin a, (S ∩ box t).card ≤ 1 := by
    intro t
    dsimp only [box]
    split_ifs with ht0
    · exact le_trans (Finset.card_le_card Finset.inter_subset_right) (by simp)
    · by_contra hgt
      push Not at hgt
      have hsub : {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} ⊆ S := by
        have hle2 : (S ∩ {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}).card ≤
            ({w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} : Finset (ZMod n)).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hcard2 : ({w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} : Finset (ZMod n)).card ≤ 2 :=
          Finset.card_le_two
        have heq_card : (S ∩ {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}).card =
            ({w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} : Finset (ZMod n)).card := by omega
        have heq_set := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (le_of_eq heq_card.symm)
        rw [← heq_set]
        exact Finset.inter_subset_left
      have hm1 : w + (2 * t.val - 1 : ℕ) ∈ S := hsub (Finset.mem_insert_self _ _)
      have hm2 : w + (2 * t.val : ℕ) ∈ S := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hsucc : w + (2 * t.val - 1 : ℕ) + 1 = w + (2 * t.val : ℕ) := by
        have hnat : (2 * t.val - 1 : ℕ) + 1 = 2 * t.val := by omega
        have hcast : (((2 * t.val - 1 : ℕ) + 1 : ℕ) : ZMod n) = ((2 * t.val : ℕ) : ZMod n) := by rw [hnat]
        rw [Nat.cast_add, Nat.cast_one] at hcast
        rw [add_assoc, hcast]
      exact hind _ hm1 (hsucc.symm ▸ hm2)
  have hcover : S ⊆ Finset.univ.biUnion box := by
    intro x hx
    let d : ℕ := (x - w).val
    have hd_lt : d < n := ZMod.val_lt (x - w)
    have hx_eq : x = w + (d : ZMod n) := by
      have hcast : (d : ZMod n) = x - w := ZMod.natCast_zmod_val (x - w)
      rw [hcast]; ring
    have hd_ne1 : d ≠ 2 * a := by
      intro h
      rw [h] at hx_eq
      have h2a : w + ((2 * a : ℕ) : ZMod n) = u := by
        dsimp only [w]
        have hn0 : ((2 * a + 1 : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
        push_cast at hn0 ⊢
        linear_combination hn0
      rw [h2a] at hx_eq
      exact hu0 (hx_eq ▸ hx)
    have hd_ne2 : d ≠ 2 * a - 1 := by
      intro h
      rw [h] at hx_eq
      have h2a1 : w + ((2 * a - 1 : ℕ) : ZMod n) = u - 1 := by
        dsimp only [w]
        have hn0 : ((2 * a + 1 : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
        have hsub : (2 * a - 1 : ℕ) + 2 = 2 * a + 1 := by
          have : 0 < a := by
            rcases Nat.eq_zero_or_pos a with rfl | hpos
            · rw [Finset.card_eq_zero.mp hcard] at hx; exact absurd hx (Finset.notMem_empty _)
            · exact hpos
          omega
        have hcast : (((2 * a - 1 : ℕ) + 2 : ℕ) : ZMod n) = 0 := by rw [hsub]; exact hn0
        push_cast at hcast
        linear_combination hcast
      rw [h2a1] at hx_eq
      exact hu1 (hx_eq ▸ hx)
    have hd_small : d < 2 * a - 1 := by omega
    rw [Finset.mem_biUnion]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp only [box]
      simp [hd0, hx_eq]
    · let t : ℕ := (d + 1) / 2
      have ht_lt : t < a := by omega
      have ht_pos : t ≠ 0 := by omega
      refine ⟨⟨t, ht_lt⟩, Finset.mem_univ _, ?_⟩
      dsimp only [box]
      simp only [ht_pos, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
      by_cases heven : d % 2 = 0
      · right; rw [hx_eq]; congr 1; congr 1; omega
      · left; rw [hx_eq]; congr 1; congr 1; omega
  have hsum_card : ∑ t : Fin a, (S ∩ box t).card = a := by
    have hunion : S = Finset.univ.biUnion (fun t : Fin a => S ∩ box t) := by
      rw [← Finset.inter_biUnion]
      exact (Finset.inter_eq_left.mpr hcover).symm
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin a)) (fun t => S ∩ box t) := by
      intro t1 _ t2 _ hne
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj_boxes t1 t2 hne)
    rw [← Finset.card_biUnion hdisj, ← hunion, hcard]
  have hbox_eq1 : ∀ t : Fin a, (S ∩ box t).card = 1 := by
    intro t
    by_contra hne
    have hlt : (S ∩ box t).card < 1 := lt_of_le_of_ne (hbox_le t) hne
    have hsum_lt : ∑ s : Fin a, (S ∩ box s).card < ∑ _s : Fin a, 1 :=
      Finset.sum_lt_sum (fun s _ => hbox_le s) ⟨t, Finset.mem_univ t, hlt⟩
    simp [hsum_card] at hsum_lt
  refine ⟨w, ?_⟩
  have hnat : ∀ (j : ℕ), j < a → w + (2 * j : ℕ) ∈ S := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h1 := hbox_eq1 ⟨0, hj⟩
      dsimp only [box] at h1
      simp only [↓reduceIte] at h1
      have hne : (S ∩ {w}).Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨x, hx⟩
      rw [Finset.mem_inter, Finset.mem_singleton] at hx
      simpa [hx.2] using hx.1
    | succ j ih =>
      intro hj
      have hprev : w + (2 * j : ℕ) ∈ S := ih (by omega)
      have hnot : w + (2 * j + 1 : ℕ) ∉ S := by
        have hsucc : w + (2 * j : ℕ) + 1 = w + (2 * j + 1 : ℕ) := by
          push_cast; ring
        rw [← hsucc]
        exact hind _ hprev
      have h1 := hbox_eq1 ⟨j + 1, hj⟩
      dsimp only [box] at h1
      have hne0 : j + 1 ≠ 0 := Nat.succ_ne_zero j
      simp only [hne0, ↓reduceIte] at h1
      have hne : (S ∩ {w + (2 * (j + 1) - 1 : ℕ), w + (2 * (j + 1) : ℕ)}).Nonempty :=
        Finset.card_pos.mp (by omega)
      rcases hne with ⟨x, hx⟩
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · have heq : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
        rw [heq] at hx
        exact absurd hx.1 hnot
      · exact hx.1
  exact fun t => hnat t.val t.isLt

private lemma ind_set_pair_alternating {a : ℕ} (ha : 2 ≤ a)
    (S : Finset (ZMod (2 * a + 1))) (pR : ZMod (2 * a + 1))
    (hcard : S.card = a - 1)
    (hsub : ∀ z ∈ S, z ≠ pR - 1 ∧ z ≠ pR ∧ z ≠ pR + 1 ∧ z ≠ pR - 2)
    (hind : ∀ z ∈ S, z + 1 ∉ S) :
    ∀ t : Fin (a - 1), pR + (2 + 2 * t.val : ℕ) ∈ S := by
  let n := 2 * a + 1
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let w := pR + 2
  let box : Fin (a - 1) → Finset (ZMod n) := fun t =>
    if t.val = 0 then {w} else {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}
  have hdisj_boxes : ∀ t1 t2 : Fin (a - 1), t1 ≠ t2 → Disjoint (box t1) (box t2) := by
    intro t1 t2 hne
    have hval_ne : t1.val ≠ t2.val := fun h => hne (Fin.ext h)
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hmem : ∀ (t : Fin (a - 1)), x ∈ box t →
        ∃ d : ℕ, d < 2 * a - 3 ∧ x = w + (d : ZMod n) ∧ (d = 2 * t.val ∨ (0 < t.val ∧ d = 2 * t.val - 1)) := by
      intro t hxt
      dsimp only [box] at hxt
      split_ifs at hxt with ht0
      · rw [Finset.mem_singleton] at hxt
        refine ⟨0, by omega, by simpa using hxt, Or.inl (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
        rcases hxt with rfl | rfl
        · refine ⟨2 * t.val - 1, by have := t.isLt; omega, rfl, Or.inr ⟨by omega, rfl⟩⟩
        · refine ⟨2 * t.val, by have := t.isLt; omega, rfl, Or.inl rfl⟩
    obtain ⟨d1, hd1lt, hx_eq1, h1⟩ := hmem t1 hx1
    obtain ⟨d2, hd2lt, hx_eq2, h2⟩ := hmem t2 hx2
    have hd_eq : d1 = d2 := (zmod_add_natCast_eq_iff w (by omega : d1 < n) (by omega : d2 < n)).mp (hx_eq1.symm.trans hx_eq2)
    omega
  have hbox_le : ∀ t : Fin (a - 1), (S ∩ box t).card ≤ 1 := by
    intro t
    dsimp only [box]
    split_ifs with ht0
    · exact le_trans (Finset.card_le_card Finset.inter_subset_right) (by simp)
    · by_contra hgt
      push Not at hgt
      have hsub' : {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} ⊆ S := by
        have hle2 : (S ∩ {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}).card ≤
            ({w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} : Finset (ZMod n)).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hcard2 : ({w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} : Finset (ZMod n)).card ≤ 2 :=
          Finset.card_le_two
        have heq_card : (S ∩ {w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)}).card =
            ({w + (2 * t.val - 1 : ℕ), w + (2 * t.val : ℕ)} : Finset (ZMod n)).card := by omega
        have heq_set := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (le_of_eq heq_card.symm)
        rw [← heq_set]
        exact Finset.inter_subset_left
      have hm1 : w + (2 * t.val - 1 : ℕ) ∈ S := hsub' (Finset.mem_insert_self _ _)
      have hm2 : w + (2 * t.val : ℕ) ∈ S := hsub' (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hsucc : w + (2 * t.val - 1 : ℕ) + 1 = w + (2 * t.val : ℕ) := by
        have hnat : (2 * t.val - 1 : ℕ) + 1 = 2 * t.val := by omega
        have hcast : (((2 * t.val - 1 : ℕ) + 1 : ℕ) : ZMod n) = ((2 * t.val : ℕ) : ZMod n) := by rw [hnat]
        rw [Nat.cast_add, Nat.cast_one] at hcast
        rw [add_assoc, hcast]
      exact hind _ hm1 (hsucc.symm ▸ hm2)
  have hcover : S ⊆ Finset.univ.biUnion box := by
    intro x hx
    rcases hsub x hx with ⟨hx1, hx2, hx3, hx4⟩
    let d : ℕ := (x - w).val
    have hd_lt : d < n := ZMod.val_lt (x - w)
    have hx_eq : x = w + (d : ZMod n) := by
      have hcast : (d : ZMod n) = x - w := ZMod.natCast_zmod_val (x - w)
      rw [hcast]; ring
    have hn0 : ((2 * a + 1 : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
    have hd_ne_a : d ≠ 2 * a := by
      intro h; rw [h] at hx_eq
      have heq : w + ((2 * a : ℕ) : ZMod n) = pR + 1 := by
        dsimp only [w]; push_cast at hn0 ⊢; linear_combination hn0
      exact hx3 (hx_eq.trans heq)
    have hd_ne_b : d ≠ 2 * a - 1 := by
      intro h; rw [h] at hx_eq
      have heq : w + ((2 * a - 1 : ℕ) : ZMod n) = pR := by
        dsimp only [w]
        have hcast : (((2 * a - 1 : ℕ) + 2 : ℕ) : ZMod n) = 0 := by rw [show 2 * a - 1 + 2 = 2 * a + 1 by omega]; exact hn0
        push_cast at hcast; linear_combination hcast
      exact hx2 (hx_eq.trans heq)
    have hd_ne_c : d ≠ 2 * a - 2 := by
      intro h; rw [h] at hx_eq
      have heq : w + ((2 * a - 2 : ℕ) : ZMod n) = pR - 1 := by
        dsimp only [w]
        have hcast : (((2 * a - 2 : ℕ) + 3 : ℕ) : ZMod n) = 0 := by rw [show 2 * a - 2 + 3 = 2 * a + 1 by omega]; exact hn0
        push_cast at hcast; linear_combination hcast
      exact hx1 (hx_eq.trans heq)
    have hd_ne_d : d ≠ 2 * a - 3 := by
      intro h; rw [h] at hx_eq
      have heq : w + ((2 * a - 3 : ℕ) : ZMod n) = pR - 2 := by
        dsimp only [w]
        have hcast : (((2 * a - 3 : ℕ) + 4 : ℕ) : ZMod n) = 0 := by rw [show 2 * a - 3 + 4 = 2 * a + 1 by omega]; exact hn0
        push_cast at hcast; linear_combination hcast
      exact hx4 (hx_eq.trans heq)
    have hd_small : d < 2 * a - 3 := by omega
    rw [Finset.mem_biUnion]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp only [box]; simp [hd0, hx_eq]
    · let t : ℕ := (d + 1) / 2
      have ht_lt : t < a - 1 := by omega
      have ht_pos : t ≠ 0 := by omega
      refine ⟨⟨t, ht_lt⟩, Finset.mem_univ _, ?_⟩
      dsimp only [box]
      simp only [ht_pos, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
      by_cases heven : d % 2 = 0
      · right; rw [hx_eq]; congr 1; congr 1; omega
      · left; rw [hx_eq]; congr 1; congr 1; omega
  have hsum_card : ∑ t : Fin (a - 1), (S ∩ box t).card = a - 1 := by
    have hunion : S = Finset.univ.biUnion (fun t : Fin (a - 1) => S ∩ box t) := by
      rw [← Finset.inter_biUnion]
      exact (Finset.inter_eq_left.mpr hcover).symm
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin (a - 1))) (fun t => S ∩ box t) := by
      intro t1 _ t2 _ hne
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj_boxes t1 t2 hne)
    rw [← Finset.card_biUnion hdisj, ← hunion, hcard]
  have hbox_eq1 : ∀ t : Fin (a - 1), (S ∩ box t).card = 1 := by
    intro t
    by_contra hne
    have hlt : (S ∩ box t).card < 1 := lt_of_le_of_ne (hbox_le t) hne
    have hsum_lt : ∑ s : Fin (a - 1), (S ∩ box s).card < ∑ _s : Fin (a - 1), 1 :=
      Finset.sum_lt_sum (fun s _ => hbox_le s) ⟨t, Finset.mem_univ t, hlt⟩
    simp [hsum_card] at hsum_lt
  have hmem_w : ∀ t : Fin (a - 1), w + (2 * t.val : ℕ) ∈ S := by
    have hnat : ∀ (j : ℕ), j < a - 1 → w + (2 * j : ℕ) ∈ S := by
      intro j
      induction j with
      | zero =>
        intro hj
        have h1 := hbox_eq1 ⟨0, hj⟩
        dsimp only [box] at h1
        simp only [↓reduceIte] at h1
        have hne : (S ∩ {w}).Nonempty := Finset.card_pos.mp (by omega)
        rcases hne with ⟨x, hx⟩
        rw [Finset.mem_inter, Finset.mem_singleton] at hx
        simpa [hx.2] using hx.1
      | succ j ih =>
        intro hj
        have hprev : w + (2 * j : ℕ) ∈ S := ih (by omega)
        have hnot : w + (2 * j + 1 : ℕ) ∉ S := by
          have hsucc : w + (2 * j : ℕ) + 1 = w + (2 * j + 1 : ℕ) := by push_cast; ring
          rw [← hsucc]
          exact hind _ hprev
        have h1 := hbox_eq1 ⟨j + 1, hj⟩
        dsimp only [box] at h1
        have hne0 : j + 1 ≠ 0 := Nat.succ_ne_zero j
        simp only [hne0, ↓reduceIte] at h1
        have hne : (S ∩ {w + (2 * (j + 1) - 1 : ℕ), w + (2 * (j + 1) : ℕ)}).Nonempty :=
          Finset.card_pos.mp (by omega)
        rcases hne with ⟨x, hx⟩
        rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx.2 with rfl | rfl
        · have heq : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
          rw [heq] at hx
          exact absurd hx.1 hnot
        · exact hx.1
    exact fun t => hnat t.val t.isLt
  intro t
  have h := hmem_w t
  have heq : pR + ((2 + 2 * t.val : ℕ) : ZMod n) = w + ((2 * t.val : ℕ) : ZMod n) := by
    dsimp only [w]; push_cast; ring
  rw [heq]
  exact h

private lemma card_good_eq {a m : ℕ} (ha : 2 ≤ a)
    (inst : DecidablePred (fun g : ZMod (2 * a + 1) → (Fin m → ZMod 2) =>
      (∃ k : ZMod (2 * a + 1), ∀ t : Fin a, g (k + (t.val : ZMod (2 * a + 1))) = 0) ∨
      (∃ k : ZMod (2 * a + 1), (∀ t : Fin (a - 1), g (k + 1 + (t.val : ZMod (2 * a + 1))) = 0) ∧
        g k = g (k + (a : ZMod (2 * a + 1)))))) :
    (@Finset.filter _ _ inst Finset.univ).card =
      1 + 2 * (2 * a + 1) * (2 ^ m - 1) * ((2 ^ m) ^ a - 1) := by
  classical
  let F := ZMod 2
  let n := 2 * a + 1
  let A := Fin m → F
  let q := 2 ^ m
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let good : (ZMod n → A) → Prop := fun g =>
    (∃ k : ZMod n, ∀ t : Fin a, g (k + (t.val : ZMod n)) = 0) ∨
    (∃ k : ZMod n, (∀ t : Fin (a - 1), g (k + 1 + (t.val : ZMod n)) = 0) ∧
      g k = g (k + (a : ZMod n)))
  have hdec : (@Finset.filter _ _ inst Finset.univ) = (Finset.univ : Finset (ZMod n → A)).filter good := by
    ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and, good]; rfl
  rw [hdec]
  let mark : (ZMod n → A) → ZMod n → Prop := fun g k =>
    g k ≠ 0 ∧ (∀ t : Fin (a - 1), g (k + 1 + (t.val : ZMod n)) = 0) ∧
      (g (k + (a : ZMod n)) = 0 ∨ g (k + (a : ZMod n)) = g k)
  have hgood_iff : ∀ g : ZMod n → A, good g ↔ g = 0 ∨ ∃ k : ZMod n, mark g k := by
    intro g
    constructor
    · intro hg
      by_cases hg0 : g = 0
      · exact Or.inl hg0
      · right
        have hrun_to_mark : ∀ k0 : ZMod n, (∀ t : Fin a, g (k0 + (t.val : ZMod n)) = 0) →
            ∃ k : ZMod n, mark g k := by
          intro k0 hk0
          have hex_nz : ∃ j : ℕ, g (k0 - ((j + 1 : ℕ) : ZMod n)) ≠ 0 := by
            by_contra hall
            push Not at hall
            apply hg0
            funext z
            let d : ℕ := (k0 - z).val
            by_cases hd0 : d = 0
            · have hz : z = k0 := by
                have hcast : (d : ZMod n) = k0 - z := ZMod.natCast_zmod_val _
                rw [hd0, Nat.cast_zero] at hcast
                linear_combination hcast
              rw [hz]; simpa using hk0 ⟨0, by omega⟩
            · have h := hall (d - 1)
              have hrew : k0 - (((d - 1 + 1 : ℕ) : ZMod n)) = z := by
                rw [show d - 1 + 1 = d by omega, ZMod.natCast_zmod_val]; ring
              rwa [hrew] at h
          let j := Nat.find hex_nz
          have hj_nz : g (k0 - ((j + 1 : ℕ) : ZMod n)) ≠ 0 := Nat.find_spec hex_nz
          have hj_min : ∀ j' < j, g (k0 - ((j' + 1 : ℕ) : ZMod n)) = 0 := by
            intro j' hj'
            by_contra hne
            exact Nat.find_min hex_nz hj' hne
          let k := k0 - ((j + 1 : ℕ) : ZMod n)
          have hzeros : ∀ r : ℕ, 1 ≤ r → r ≤ a → g (k + (r : ZMod n)) = 0 := by
            intro r hr1 hra
            by_cases hrj : r ≤ j
            · have hrew : k + (r : ZMod n) = k0 - (((j - r) + 1 : ℕ) : ZMod n) := by
                dsimp only [k]
                have : (j - r) + 1 + r = j + 1 := by omega
                have hcast : ((((j - r) + 1 : ℕ) : ZMod n) + (r : ZMod n)) = ((j + 1 : ℕ) : ZMod n) := by
                  rw [← Nat.cast_add, this]
                linear_combination hcast
              rw [hrew]
              exact hj_min (j - r) (by omega)
            · have hlt : r - (j + 1) < a := by omega
              have hrew : k + (r : ZMod n) = k0 + ((r - (j + 1) : ℕ) : ZMod n) := by
                dsimp only [k]
                have : r - (j + 1) + (j + 1) = r := by omega
                have hcast : (((r - (j + 1) : ℕ) : ZMod n) + ((j + 1 : ℕ) : ZMod n)) = (r : ZMod n) := by
                  rw [← Nat.cast_add, this]
                linear_combination -hcast
              rw [hrew]
              exact hk0 ⟨r - (j + 1), hlt⟩
          refine ⟨k, hj_nz, ?_, Or.inl (hzeros a (by omega) (le_refl a))⟩
          intro t
          have hrew : k + 1 + (t.val : ZMod n) = k + ((t.val + 1 : ℕ) : ZMod n) := by push_cast; ring
          rw [hrew]
          exact hzeros (t.val + 1) (Nat.succ_pos _) (by omega)
        rcases hg with ⟨k0, hk0⟩ | ⟨k0, hk0, hkeq⟩
        · exact hrun_to_mark k0 hk0
        · by_cases hgk0 : g k0 = 0
          · apply hrun_to_mark k0
            intro t
            cases ht : t.val with
            | zero => simpa [ht] using hgk0
            | succ t' =>
              have hrew : k0 + ((t' + 1 : ℕ) : ZMod n) = k0 + 1 + (t' : ZMod n) := by push_cast; ring
              rw [hrew]
              exact hk0 ⟨t', by omega⟩
          · exact ⟨k0, hgk0, hk0, Or.inr hkeq.symm⟩
    · rintro (rfl | ⟨k, hgk0, hk0, hka⟩)
      · left; exact ⟨0, fun _ => rfl⟩
      · rcases hka with h0 | heq
        · left
          refine ⟨k + 1, ?_⟩
          intro t
          by_cases hlt : t.val < a - 1
          · exact hk0 ⟨t.val, hlt⟩
          · have hteq : t.val = a - 1 := by omega
            have hrew : k + 1 + (t.val : ZMod n) = k + (a : ZMod n) := by
              rw [hteq]
              have : 1 + (a - 1) = a := by omega
              rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, this]
            rw [hrew]
            exact h0
        · right; exact ⟨k, hk0, heq.symm⟩
  let GoodNZ : Finset (ZMod n → A) := Finset.univ.filter (fun g => ∃ k : ZMod n, mark g k)
  have hgood_split : ((Finset.univ : Finset (ZMod n → A)).filter good).card = 1 + GoodNZ.card := by
    have hdisj : Disjoint ({0} : Finset (ZMod n → A)) GoodNZ := by
      rw [Finset.disjoint_singleton_left]
      simp [GoodNZ, mark]
    have hunion : ({0} : Finset (ZMod n → A)) ∪ GoodNZ = Finset.univ.filter good := by
      ext g
      simp only [Finset.mem_union, Finset.mem_singleton, GoodNZ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hgood_iff g).symm
    rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  rw [hgood_split]
  have hmark_gap : ∀ (g : ZMod n → A) (k1 k2 : ZMod n), mark g k1 → mark g k2 → k1 ≠ k2 →
      k2 = k1 + (a : ZMod n) ∨ k1 = k2 + (a : ZMod n) := by
    intro g k1 k2 hm1 hm2 hne
    let d : ℕ := (k2 - k1).val
    have hd_lt : d < n := ZMod.val_lt _
    have hd_ne0 : d ≠ 0 := by
      intro h0
      have hcast : (d : ZMod n) = k2 - k1 := ZMod.natCast_zmod_val _
      rw [h0, Nat.cast_zero] at hcast
      exact hne (by linear_combination hcast)
    have hk2_eq : k2 = k1 + (d : ZMod n) := by
      have hcast : (d : ZMod n) = k2 - k1 := ZMod.natCast_zmod_val _
      rw [hcast]; ring
    have hd_ge_a : a ≤ d := by
      by_contra hlt
      have hzero : g k2 = 0 := by
        rw [hk2_eq]
        have hrew : k1 + (d : ZMod n) = k1 + 1 + ((d - 1 : ℕ) : ZMod n) := by
          have : 1 + (d - 1) = d := by omega
          rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, this]
        rw [hrew]
        exact hm1.2.1 ⟨d - 1, by omega⟩
      exact hm2.1 hzero
    have hd_le : d ≤ a + 1 := by
      by_contra hgt
      have hzero : g k1 = 0 := by
        have hrew : k1 = k2 + 1 + ((n - d - 1 : ℕ) : ZMod n) := by
          rw [hk2_eq]
          have hsum : d + 1 + (n - d - 1) = n := by omega
          have hn0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
          have hcast : (d : ZMod n) + 1 + ((n - d - 1 : ℕ) : ZMod n) = 0 := by
            rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, hsum]; exact hn0
          linear_combination -hcast
        rw [hrew]
        exact hm2.2.1 ⟨n - d - 1, by omega⟩
      exact hm1.1 hzero
    by_cases hda : d = a
    · left; rw [hk2_eq, hda]
    · right
      have hda1 : d = a + 1 := by omega
      rw [hk2_eq, hda1]
      have hn0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
      have hcast : ((a + 1 : ℕ) : ZMod n) + (a : ZMod n) = 0 := by
        rw [← Nat.cast_add, show a + 1 + a = n by omega]; exact hn0
      linear_combination -hcast
  let Pairs1 : Finset ((ZMod n → A) × ZMod n) := Finset.univ.filter (fun p => mark p.1 p.2)
  let Pairs2 : Finset ((ZMod n → A) × ZMod n) :=
    Finset.univ.filter (fun p => mark p.1 p.2 ∧ mark p.1 (p.2 + (a : ZMod n)))
  have hinc_exc : GoodNZ.card + Pairs2.card = Pairs1.card := by
    have h1 : Pairs1.card = ∑ g : ZMod n → A, (Finset.univ.filter (fun k : ZMod n => mark g k)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      apply Finset.card_bij (fun p _ => p.2)
      · intro p hp
        simp only [Pairs1, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rcases hp with ⟨hm, rfl⟩; exact hm
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_filter] at hp1 hp2
        exact Prod.ext (hp1.2.trans hp2.2.symm) heq
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨(g, k), ?_, rfl⟩
        simp only [Pairs1, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hk, trivial⟩
    have h2 : Pairs2.card =
        ∑ g : ZMod n → A, (Finset.univ.filter (fun k : ZMod n => mark g k ∧ mark g (k + (a : ZMod n)))).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      apply Finset.card_bij (fun p _ => p.2)
      · intro p hp
        simp only [Pairs2, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rcases hp with ⟨hm, rfl⟩; exact hm
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_filter] at hp1 hp2
        exact Prod.ext (hp1.2.trans hp2.2.symm) heq
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨(g, k), ?_, rfl⟩
        simp only [Pairs2, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hk, trivial⟩
    have h0 : GoodNZ.card = ∑ g : ZMod n → A, if ∃ k : ZMod n, mark g k then 1 else 0 := by
      simp [GoodNZ]
    rw [h0, h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    let M1 : Finset (ZMod n) := Finset.univ.filter (fun k => mark g k)
    let M2 : Finset (ZMod n) := Finset.univ.filter (fun k => mark g k ∧ mark g (k + (a : ZMod n)))
    by_cases hex : ∃ k : ZMod n, mark g k
    · simp only [hex, ↓reduceIte]
      rcases hex with ⟨k0, hk0⟩
      by_cases hex2 : ∃ k : ZMod n, mark g k ∧ mark g (k + (a : ZMod n))
      · rcases hex2 with ⟨k, hmk, hmka⟩
        have hka_ne : k ≠ k + (a : ZMod n) := by
          intro heq
          have hrew : k + ((0 : ℕ) : ZMod n) = k + (a : ZMod n) := by simpa using heq
          have hnat := (zmod_add_natCast_eq_iff k (by omega : 0 < n) (by omega : a < n)).mp hrew
          omega
        have hM1_eq : M1 = {k, k + (a : ZMod n)} := by
          ext k'
          simp only [M1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hmk'
            by_cases h1 : k' = k
            · exact Or.inl h1
            · by_cases h2 : k' = k + (a : ZMod n)
              · exact Or.inr h2
              · exfalso
                rcases hmark_gap g k k' hmk hmk' (Ne.symm h1) with hEq | hEq
                · exact h2 hEq
                · have hrew : k' = k + (a : ZMod n) + 1 := by
                    have hn0 : ((2 * a + 1 : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
                    push_cast at hn0
                    linear_combination -hEq - hn0
                  have hzero : g k' = 0 := by
                    rw [hrew]
                    simpa using hmka.2.1 ⟨0, by omega⟩
                  exact hmk'.1 hzero
          · rintro (rfl | rfl)
            · exact hmk
            · exact hmka
        have hM2_eq : M2 = {k} := by
          ext k'
          simp only [M2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hmk', hmk'a⟩
            have hmem1 : k' ∈ M1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmk'⟩
            rw [hM1_eq, Finset.mem_insert, Finset.mem_singleton] at hmem1
            rcases hmem1 with rfl | rfl
            · rfl
            · exfalso
              have hmem2 : k + (a : ZMod n) + (a : ZMod n) ∈ M1 :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmk'a⟩
              rw [hM1_eq, Finset.mem_insert, Finset.mem_singleton] at hmem2
              rcases hmem2 with hEq | hEq
              · have hrew : k + ((2 * a : ℕ) : ZMod n) = k + ((0 : ℕ) : ZMod n) := by
                  push_cast; linear_combination hEq
                have hnat := (zmod_add_natCast_eq_iff k (by omega : 2 * a < n) (by omega : 0 < n)).mp hrew
                omega
              · have hrew : k + ((2 * a : ℕ) : ZMod n) = k + (a : ZMod n) := by
                  push_cast; linear_combination hEq
                have hnat := (zmod_add_natCast_eq_iff k (by omega : 2 * a < n) (by omega : a < n)).mp hrew
                omega
          · rintro rfl; exact ⟨hmk, hmka⟩
        change 1 + M2.card = M1.card
        rw [hM1_eq, hM2_eq, Finset.card_pair hka_ne, Finset.card_singleton]
      · have hM2_empty : M2 = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro k _ h
          exact hex2 ⟨k, h⟩
        have hM1_eq : M1 = {k0} := by
          ext k'
          simp only [M1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hmk'
            by_contra hne
            rcases hmark_gap g k0 k' hk0 hmk' (Ne.symm hne) with rfl | rfl
            · exact hex2 ⟨k0, hk0, hmk'⟩
            · exact hex2 ⟨k', hmk', hk0⟩
          · rintro rfl; exact hk0
        change 1 + M2.card = M1.card
        rw [hM1_eq, hM2_empty, Finset.card_singleton, Finset.card_empty]
    · simp only [hex, ↓reduceIte]
      have hM1_empty : M1 = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k _ h; exact hex ⟨k, h⟩
      have hM2_empty : M2 = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k _ h; exact hex ⟨k, h.1⟩
      change 0 + M2.card = M1.card
      rw [hM1_empty, hM2_empty, Finset.card_empty]
  have hA_card : Fintype.card A = q := by
    simp [A, F, q, Fintype.card_pi, ZMod.card]
  have hPairs1_card : Pairs1.card = 2 * n * (q - 1) * q ^ a := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ k : ZMod n,
        (Pairs1.filter (fun p => p.2 = k)).card = 2 * (q - 1) * q ^ a := by
      intro k
      have hbij : (Pairs1.filter (fun p => p.2 = k)).card =
          Fintype.card ({c : A // c ≠ 0} × Bool × (Fin a → A)) := by
        rw [← Finset.card_univ]
        apply Finset.card_bij
          (fun (p : (ZMod n → A) × ZMod n) hp =>
            have hmk : mark p.1 k := by
              simp only [Pairs1, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              rw [← hp.2]; exact hp.1
            (⟨p.1 k, hmk.1⟩, decide (p.1 (k + (a : ZMod n)) ≠ 0),
              fun t : Fin a => p.1 (k + ((a + 1 + t.val : ℕ) : ZMod n))))
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 heq
          simp only [Pairs1, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          rcases hp1 with ⟨hm1, hk1⟩
          rcases hp2 with ⟨hm2, hk2⟩
          rw [hk1] at hm1
          rw [hk2] at hm2
          have hc : p1.1 k = p2.1 k := congrArg (fun x => x.1.1) heq
          have hb : decide (p1.1 (k + (a : ZMod n)) ≠ 0) = decide (p2.1 (k + (a : ZMod n)) ≠ 0) :=
            congrArg (fun x => x.2.1) heq
          have hr : ∀ t : Fin a, p1.1 (k + ((a + 1 + t.val : ℕ) : ZMod n)) =
              p2.1 (k + ((a + 1 + t.val : ℕ) : ZMod n)) := fun t =>
            congrArg (fun x => x.2.2 t) heq
          apply Prod.ext _ (hk1.trans hk2.symm)
          funext z
          let d : ℕ := (z - k).val
          have hd_lt : d < n := ZMod.val_lt _
          have hz_eq : z = k + (d : ZMod n) := by
            have hcast : (d : ZMod n) = z - k := ZMod.natCast_zmod_val _
            rw [hcast]; ring
          rw [hz_eq]
          by_cases hd0 : d = 0
          · simpa [hd0] using hc
          · by_cases hda : d < a
            · have hrew : k + (d : ZMod n) = k + 1 + ((d - 1 : ℕ) : ZMod n) := by
                have : 1 + (d - 1) = d := by omega
                rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, this]
              rw [hrew, hm1.2.1 ⟨d - 1, by omega⟩, hm2.2.1 ⟨d - 1, by omega⟩]
            · by_cases hdeq : d = a
              · rw [hdeq]
                rcases hm1.2.2 with h1z | h1c <;> rcases hm2.2.2 with h2z | h2c
                · rw [h1z, h2z]
                · rw [h1z, h2c] at hb
                  simp [hm2.1] at hb
                · rw [h1c, h2z] at hb
                  simp [hm1.1] at hb
                · rw [h1c, h2c, hc]
              · have htlt : d - (a + 1) < a := by omega
                have hrew : d = a + 1 + (d - (a + 1)) := by omega
                conv_lhs => rw [hrew]
                conv_rhs => rw [hrew]
                exact hr ⟨d - (a + 1), htlt⟩
        · rintro ⟨⟨c, hc⟩, bit, rest⟩ _
          let g : ZMod n → A := fun z =>
            let d := (z - k).val
            if d = 0 then c
            else if d < a then 0
            else if d = a then (if bit then c else 0)
            else rest ⟨d - (a + 1), by have hlt := ZMod.val_lt (z - k); dsimp only [n] at hlt; omega⟩
          have hg_at : ∀ (d : ℕ) (hd : d < n), g (k + (d : ZMod n)) =
              if d = 0 then c
              else if d < a then 0
              else if d = a then (if bit then c else 0)
              else rest ⟨d - (a + 1), by dsimp only [n] at hd; omega⟩ := by
            intro d hd
            have hval : (k + (d : ZMod n) - k).val = d := by
              rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hd]
            dsimp only [g]
            simp only [hval]
          have hgk : g k = c := by
            have := hg_at 0 (by omega)
            simpa using this
          have hga : g (k + (a : ZMod n)) = if bit then c else 0 := by
            have := hg_at a (by omega)
            have hne0 : a ≠ 0 := by omega
            have hnlt : ¬ a < a := lt_irrefl a
            simpa [hne0, hnlt] using this
          have hmg : mark g k := by
            refine ⟨by rw [hgk]; exact hc, ?_, ?_⟩
            · intro t
              have hrew : k + 1 + (t.val : ZMod n) = k + ((t.val + 1 : ℕ) : ZMod n) := by push_cast; ring
              rw [hrew, hg_at (t.val + 1) (by omega)]
              have hlt : t.val + 1 < a := by omega
              simp [hlt]
            · rw [hga, hgk]
              cases bit <;> simp
          refine ⟨(g, k), ?_, ?_⟩
          · simp only [Pairs1, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hmg, trivial⟩
          · apply Prod.ext
            · exact Subtype.ext hgk
            · apply Prod.ext
              · change decide (g (k + (a : ZMod n)) ≠ 0) = bit
                rw [hga]; cases bit <;> simp [hc]
              · funext t
                change g (k + ((a + 1 + t.val : ℕ) : ZMod n)) = rest t
                rw [hg_at (a + 1 + t.val) (by omega)]
                have hne0 : a + 1 + t.val ≠ 0 := by omega
                have hnlt : ¬ a + 1 + t.val < a := by omega
                have hnea : a + 1 + t.val ≠ a := by omega
                simp only [hne0, hnlt, hnea, ↓reduceIte]
                congr 1; apply Fin.ext; dsimp only; omega
      rw [hbij, Fintype.card_prod, Fintype.card_prod, card_ne_zero, hA_card,
        Fintype.card_bool, Fintype.card_pi]
      simp [hA_card]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hfib k), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    ring
  have hPairs2_card : Pairs2.card = 2 * n * (q - 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ k : ZMod n,
        (Pairs2.filter (fun p => p.2 = k)).card = 2 * (q - 1) := by
      intro k
      have hbij : (Pairs2.filter (fun p => p.2 = k)).card =
          Fintype.card ({c : A // c ≠ 0} × Bool) := by
        rw [← Finset.card_univ]
        apply Finset.card_bij
          (fun (p : (ZMod n → A) × ZMod n) hp =>
            have hmk : mark p.1 k := by
              simp only [Pairs2, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              rw [← hp.2]; exact hp.1.1
            (⟨p.1 k, hmk.1⟩, decide (p.1 (k + ((2 * a : ℕ) : ZMod n)) ≠ 0)))
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 heq
          simp only [Pairs2, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          rcases hp1 with ⟨⟨hm1, hm1a⟩, hk1⟩
          rcases hp2 with ⟨⟨hm2, hm2a⟩, hk2⟩
          rw [hk1] at hm1 hm1a
          rw [hk2] at hm2 hm2a
          have hc : p1.1 k = p2.1 k := congrArg (fun x => x.1.1) heq
          have hb : decide (p1.1 (k + ((2 * a : ℕ) : ZMod n)) ≠ 0) =
              decide (p2.1 (k + ((2 * a : ℕ) : ZMod n)) ≠ 0) := congrArg Prod.snd heq
          have h1a_eq : p1.1 (k + (a : ZMod n)) = p1.1 k := hm1.2.2.resolve_left hm1a.1
          have h2a_eq : p2.1 (k + (a : ZMod n)) = p2.1 k := hm2.2.2.resolve_left hm2a.1
          apply Prod.ext _ (hk1.trans hk2.symm)
          funext z
          let d : ℕ := (z - k).val
          have hd_lt : d < n := ZMod.val_lt _
          have hz_eq : z = k + (d : ZMod n) := by
            have hcast : (d : ZMod n) = z - k := ZMod.natCast_zmod_val _
            rw [hcast]; ring
          rw [hz_eq]
          by_cases hd0 : d = 0
          · simpa [hd0] using hc
          · by_cases hda : d < a
            · have hrew : k + (d : ZMod n) = k + 1 + ((d - 1 : ℕ) : ZMod n) := by
                have : 1 + (d - 1) = d := by omega
                rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, this]
              rw [hrew, hm1.2.1 ⟨d - 1, by omega⟩, hm2.2.1 ⟨d - 1, by omega⟩]
            · by_cases hdeq : d = a
              · rw [hdeq, h1a_eq, h2a_eq, hc]
              · by_cases hd2a : d < 2 * a
                · have hrew : k + (d : ZMod n) = k + (a : ZMod n) + 1 + ((d - a - 1 : ℕ) : ZMod n) := by
                    have : a + 1 + (d - a - 1) = d := by omega
                    have hcast : (a : ZMod n) + 1 + ((d - a - 1 : ℕ) : ZMod n) = (d : ZMod n) := by
                      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, this]
                    linear_combination -hcast
                  rw [hrew, hm1a.2.1 ⟨d - a - 1, by omega⟩, hm2a.2.1 ⟨d - a - 1, by omega⟩]
                · have hd_is : d = 2 * a := by omega
                  rw [hd_is]
                  have hrew : k + (a : ZMod n) + (a : ZMod n) = k + ((2 * a : ℕ) : ZMod n) := by push_cast; ring
                  have h1_2a := hm1a.2.2
                  have h2_2a := hm2a.2.2
                  rw [hrew, h1a_eq] at h1_2a
                  rw [hrew, h2a_eq] at h2_2a
                  rcases h1_2a with h1z | h1c <;> rcases h2_2a with h2z | h2c
                  · rw [h1z, h2z]
                  · rw [h1z, h2c] at hb; simp [hm2.1] at hb
                  · rw [h1c, h2z] at hb; simp [hm1.1] at hb
                  · rw [h1c, h2c, hc]
        · rintro ⟨⟨c, hc⟩, bit⟩ _
          let g : ZMod n → A := fun z =>
            let d := (z - k).val
            if d = 0 ∨ d = a then c
            else if d = 2 * a then (if bit then c else 0)
            else 0
          have hg_at : ∀ d : ℕ, d < n → g (k + (d : ZMod n)) =
              if d = 0 ∨ d = a then c
              else if d = 2 * a then (if bit then c else 0)
              else 0 := by
            intro d hd
            have hval : (k + (d : ZMod n) - k).val = d := by
              rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hd]
            dsimp only [g]
            simp only [hval]
          have hgk : g k = c := by simpa using hg_at 0 (by omega)
          have hga : g (k + (a : ZMod n)) = c := by simpa using hg_at a (by omega)
          have hg2a : g (k + ((2 * a : ℕ) : ZMod n)) = if bit then c else 0 := by
            have := hg_at (2 * a) (by omega)
            have hne1 : 2 * a ≠ 0 := by omega
            have hne2 : 2 * a ≠ a := by omega
            simpa [hne1, hne2] using this
          have hmg1 : mark g k := by
            refine ⟨by rw [hgk]; exact hc, ?_, Or.inr (by rw [hga, hgk])⟩
            intro t
            have hrew : k + 1 + (t.val : ZMod n) = k + ((t.val + 1 : ℕ) : ZMod n) := by push_cast; ring
            rw [hrew, hg_at (t.val + 1) (by omega)]
            have h2 : t.val + 1 ≠ a := by omega
            have h3 : t.val + 1 ≠ 2 * a := by omega
            simp [h2, h3]
          have hmg2 : mark g (k + (a : ZMod n)) := by
            refine ⟨by rw [hga]; exact hc, ?_, ?_⟩
            · intro t
              have hrew : k + (a : ZMod n) + 1 + (t.val : ZMod n) = k + ((a + 1 + t.val : ℕ) : ZMod n) := by
                push_cast; ring
              rw [hrew, hg_at (a + 1 + t.val) (by omega)]
              have h2 : a + 1 + t.val ≠ a := by omega
              have h3 : a + 1 + t.val ≠ 2 * a := by omega
              simp [h2, h3]
            · have hrew : k + (a : ZMod n) + (a : ZMod n) = k + ((2 * a : ℕ) : ZMod n) := by push_cast; ring
              rw [hrew, hg2a, hga]
              cases bit <;> simp
          refine ⟨(g, k), ?_, ?_⟩
          · simp only [Pairs2, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨hmg1, hmg2⟩, trivial⟩
          · apply Prod.ext
            · exact Subtype.ext hgk
            · change decide (g (k + ((2 * a : ℕ) : ZMod n)) ≠ 0) = bit
              rw [hg2a]; cases bit <;> simp [hc]
      rw [hbij, Fintype.card_prod, card_ne_zero, hA_card, Fintype.card_bool]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hfib k), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    ring
  have hqa_ge : 1 ≤ q ^ a := Nat.one_le_pow a q (Nat.one_le_two_pow)
  have hmul_sub : 2 * n * (q - 1) * (q ^ a - 1) + 2 * n * (q - 1) = 2 * n * (q - 1) * q ^ a := by
    have h1 : q ^ a = (q ^ a - 1) + 1 := by omega
    conv_rhs => rw [h1, mul_add, mul_one]
  change 1 + GoodNZ.card = 1 + 2 * n * (q - 1) * (q ^ a - 1)
  omega


private lemma succeeds_imp_good {a m : ℕ} (ha : 2 ≤ a)
    (h : Fin (2 * a + 1) → (Fin m → ZMod 2))
    (U : Submodule (ZMod 2) (Fin (2 * a + 1) → ZMod 2))
    (hdimU : Module.finrank (ZMod 2) U = a)
    (hkill : ∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin (2 * a + 1),
      x i * y ⟨(i.val + 1) % (2 * a + 1), Nat.mod_lt _ (Nat.succ_pos (2 * a))⟩ =
      x ⟨(i.val + 1) % (2 * a + 1), Nat.mod_lt _ (Nat.succ_pos (2 * a))⟩ * y i) :
    let n := 2 * a + 1
    let idx : ZMod n → Fin n := fun z => ⟨z.val, ZMod.val_lt z⟩
    let g : ZMod n → (Fin m → ZMod 2) := fun t => h (idx ((2 : ZMod n) * t))
    (∃ k : ZMod n, ∀ t : Fin a, g (k + (t.val : ZMod n)) = 0) ∨
    (∃ k : ZMod n, (∀ t : Fin (a - 1), g (k + 1 + (t.val : ZMod n)) = 0) ∧
      g k = g (k + (a : ZMod n))) := by
  classical
  dsimp only
  let F := ZMod 2
  let n := 2 * a + 1
  let A := Fin m → F
  let W := Fin n → F
  let next : Fin n → Fin n := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.succ_pos (2 * a))⟩
  change ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (next i) = x (next i) * y i at hiso
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let idx : ZMod n → Fin n := fun z => ⟨z.val, ZMod.val_lt z⟩
  let toZ : Fin n → ZMod n := fun i => (i.val : ZMod n)
  have hidx_toZ : ∀ i : Fin n, idx (toZ i) = i := by
    intro i; apply Fin.ext
    dsimp only [idx, toZ]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  have htoZ_idx : ∀ z : ZMod n, toZ (idx z) = z := by
    intro z; dsimp only [idx, toZ]; exact ZMod.natCast_zmod_val z
  have hidx_inj : Function.Injective idx := fun z1 z2 h => by
    have := congrArg toZ h; rwa [htoZ_idx, htoZ_idx] at this
  have hnext_idx : ∀ z : ZMod n, next (idx z) = idx (z + 1) := by
    intro z; apply Fin.ext
    dsimp only [next, idx]
    have hcast : (z + 1).val = (z.val + 1) % n := by
      have h1 : (z + 1) = ((z.val + 1 : ℕ) : ZMod n) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [h1, ZMod.val_natCast]
    exact hcast.symm
  let step2 : (Fin n → A) → (ZMod n → A) := fun h t => h (idx ((2 : ZMod n) * t))
  let g : ZMod n → A := step2 h
  let S : Finset (ZMod n) := Finset.univ.filter (fun z => ∃ x ∈ U, x (idx z) ≠ 0)
  have hedge : ∀ z : ZMod n, z ∈ S → z + 1 ∈ S → ∀ x ∈ U, x (idx z) = x (idx (z + 1)) := by
    intro z hz1 hz2 x hx
    rcases (Finset.mem_filter.mp hz1).2 with ⟨y, hyU, hy0⟩
    rcases (Finset.mem_filter.mp hz2).2 with ⟨w, hwU, hw0⟩
    have hy1 : y (idx z) = 1 := zmod2_eq_one_of_ne_zero hy0
    have hw1 : w (idx (z + 1)) = 1 := zmod2_eq_one_of_ne_zero hw0
    have hwy := hiso y hyU w hwU (idx z)
    rw [hnext_idx, hy1, hw1, one_mul] at hwy
    have hy_next : y (idx (z + 1)) = 1 := by
      rcases (eq_or_ne (y (idx (z + 1))) 0) with h0 | hne
      · rw [h0, zero_mul] at hwy; exact absurd hwy (by decide)
      · exact zmod2_eq_one_of_ne_zero hne
    have hxy := hiso x hx y hyU (idx z)
    rw [hnext_idx, hy1, hy_next, mul_one, mul_one] at hxy
    exact hxy
  have hS_ne_univ : S ≠ Finset.univ := by
    intro huniv
    have hconst : ∀ x ∈ U, ∀ z : ZMod n, x (idx z) = x (idx 0) := by
      intro x hx z
      have hwalk : ∀ t : ℕ, x (idx (t : ZMod n)) = x (idx 0) := by
        intro t
        induction t with
        | zero => simp
        | succ t iht =>
          have h1 : (t : ZMod n) ∈ S := by rw [huniv]; exact Finset.mem_univ _
          have h2 : (t : ZMod n) + 1 ∈ S := by rw [huniv]; exact Finset.mem_univ _
          have he := hedge (t : ZMod n) h1 h2 x hx
          push_cast
          exact he.symm.trans iht
      have h := hwalk z.val
      rwa [ZMod.natCast_zmod_val] at h
    let ev0 : U →ₗ[F] F :=
      { toFun := fun x => x.1 (idx 0), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hev0_inj : Function.Injective ev0 := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply Subtype.ext
      funext i
      have h := hconst x.1 x.2 (toZ i)
      rw [hidx_toZ] at h
      exact h.trans hx
    have hrk_le := LinearMap.finrank_le_finrank_of_injective hev0_inj
    rw [hdimU, Module.finrank_self] at hrk_le
    omega
  have hex_out : ∃ z0 : ZMod n, z0 ∉ S := by
    by_contra hall
    push Not at hall
    apply hS_ne_univ
    ext z; simp [hall z]
  rcases hex_out with ⟨z0, hz0⟩
  let Starts : Finset (ZMod n) := S.filter (fun z => z - 1 ∉ S)
  let ρ : U →ₗ[F] (↥Starts → F) :=
    { toFun := fun x s => x.1 (idx s.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hρ_inj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx0 : ∀ z : ZMod n, x.1 (idx z) = 0 := by
      intro z
      have hwalk : ∀ t : ℕ, x.1 (idx (z0 + (t : ZMod n))) = 0 := by
        intro t
        induction t with
        | zero =>
          simp only [Nat.cast_zero, add_zero]
          by_contra hne
          exact hz0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1, x.2, hne⟩)
        | succ t iht =>
          have hrew : z0 + ((t + 1 : ℕ) : ZMod n) = (z0 + (t : ZMod n)) + 1 := by push_cast; ring
          rw [hrew]
          by_cases hzS : (z0 + (t : ZMod n)) + 1 ∈ S
          · by_cases hprevS : z0 + (t : ZMod n) ∈ S
            · rw [← hedge _ hprevS hzS x.1 x.2, iht]
            · have hst : (z0 + (t : ZMod n)) + 1 ∈ Starts := by
                rw [Finset.mem_filter]
                refine ⟨hzS, ?_⟩
                rwa [add_sub_cancel_right]
              exact congrFun hx ⟨_, hst⟩
          · by_contra hne
            exact hzS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1, x.2, hne⟩)
      have h := hwalk (z - z0).val
      have heq : z0 + (((z - z0).val : ℕ) : ZMod n) = z := by
        rw [ZMod.natCast_zmod_val]; ring
      rwa [heq] at h
    apply Subtype.ext
    funext i
    have := hx0 (toZ i)
    rwa [hidx_toZ] at this
  have hStarts_ge : a ≤ Starts.card := by
    have hle := LinearMap.finrank_le_finrank_of_injective hρ_inj
    rw [hdimU, Module.finrank_pi F, Fintype.card_coe] at hle
    exact hle
  have hStarts_le_S : Starts.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hStarts_le_comp : Starts.card ≤ (Finset.univ \ S).card := by
    apply Finset.card_le_card_of_injOn (fun z => z - 1)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
    · intro z1 _ z2 _ heq; exact sub_left_inj.mp heq
  have hcomp_sum : S.card + (Finset.univ \ S).card = n := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ S), Finset.card_univ, ZMod.card]
    have hle : S.card ≤ n := by
      calc S.card ≤ (Finset.univ : Finset (ZMod n)).card := Finset.card_le_univ S
        _ = n := ZMod.card n
    omega
  have hStarts_eq : Starts.card = a := by omega
  have hρ_bij : Function.Bijective ρ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hρ_inj, ?_⟩
    have h1 := Module.card_eq_pow_finrank (K := F) (V := U)
    have h2 := Module.card_eq_pow_finrank (K := F) (V := ↥Starts → F)
    rw [h1, h2, hdimU, Module.finrank_pi F, Fintype.card_coe, hStarts_eq]
  have hS_cases : S.card = a ∨ S.card = a + 1 := by omega
  rcases hS_cases with hSa | hSa1
  · left
    have hSeq : Starts = S :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hindS : ∀ z ∈ S, z + 1 ∉ S := by
      intro z hz hnext
      have hst : z + 1 ∈ Starts := hSeq.symm ▸ hnext
      have hnot := (Finset.mem_filter.mp hst).2
      rw [add_sub_cancel_right] at hnot
      exact hnot hz
    have hzeroS : ∀ z ∈ S, h (idx z) = 0 := by
      intro z hz
      have hzSt : z ∈ Starts := hSeq.symm ▸ hz
      obtain ⟨u, hu⟩ := hρ_bij.2 (fun s => if s.1 = z then 1 else 0)
      have hu_val : ∀ z' : ZMod n, u.1 (idx z') = if z' = z then 1 else 0 := by
        intro z'
        by_cases hz'S : z' ∈ S
        · have hz'St : z' ∈ Starts := hSeq.symm ▸ hz'S
          exact congrFun hu ⟨z', hz'St⟩
        · have hne : z' ≠ z := fun heq => hz'S (heq ▸ hz)
          simp only [hne, ↓reduceIte]
          by_contra h0
          exact hz'S (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.1, u.2, h0⟩)
      funext b
      have hkb := hkill u.1 u.2 b
      rw [Finset.sum_eq_single (idx z)] at hkb
      · have h1 := hu_val z
        simp only [↓reduceIte] at h1
        rw [h1, mul_one] at hkb
        exact hkb
      · intro i _ hne
        have h1 := hu_val (toZ i)
        rw [hidx_toZ] at h1
        have hne' : toZ i ≠ z := fun heq => hne (by rw [← hidx_toZ i, heq])
        simp only [hne', ↓reduceIte] at h1
        rw [h1, mul_zero]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    obtain ⟨w, hw⟩ := ind_set_alternating S hSa hindS
    let k : ZMod n := ((a + 1 : ℕ) : ZMod n) * w
    refine ⟨k, ?_⟩
    intro t
    have h2kt : (2 : ZMod n) * (k + (t.val : ZMod n)) = w + (2 * t.val : ℕ) := by
      dsimp only [k]
      calc (2 : ZMod n) * (((a + 1 : ℕ) : ZMod n) * w + (t.val : ZMod n))
          = ((2 : ZMod n) * ((a + 1 : ℕ) : ZMod n)) * w + (2 : ZMod n) * (t.val : ZMod n) := by ring
        _ = 1 * w + (2 : ZMod n) * (t.val : ZMod n) := by rw [zmod_two_mul_inv a]
        _ = w + ((2 * t.val : ℕ) : ZMod n) := by push_cast; ring
    change h (idx ((2 : ZMod n) * (k + (t.val : ZMod n)))) = 0
    rw [h2kt]
    exact hzeroS _ (hw t)
  · right
    have hdiff_card : (S \ Starts).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hSa1, hStarts_eq]
      omega
    rcases Finset.card_eq_one.mp hdiff_card with ⟨pR, hpR_eq⟩
    have hpR_mem : pR ∈ S \ Starts := hpR_eq ▸ Finset.mem_singleton_self pR
    have hpR_S : pR ∈ S := (Finset.mem_sdiff.mp hpR_mem).1
    have hpR_nSt : pR ∉ Starts := (Finset.mem_sdiff.mp hpR_mem).2
    have hpL_S : pR - 1 ∈ S := by
      by_contra hnot
      exact hpR_nSt (Finset.mem_filter.mpr ⟨hpR_S, hnot⟩)
    have huniq : ∀ z ∈ S, z ∉ Starts → z = pR := by
      intro z hz hn
      have hmem : z ∈ S \ Starts := Finset.mem_sdiff.mpr ⟨hz, hn⟩
      rw [hpR_eq, Finset.mem_singleton] at hmem
      exact hmem
    have hpL_ne_pR : pR - 1 ≠ pR := by
      intro heq
      have h1 : (1 : ZMod n) = 0 := by linear_combination -heq
      have : Fact (1 < n) := ⟨by omega⟩
      have hv := congrArg ZMod.val h1
      rw [ZMod.val_one, ZMod.val_zero] at hv
      exact Nat.one_ne_zero hv
    have hpL_St : pR - 1 ∈ Starts := by
      by_contra hn
      exact hpL_ne_pR (huniq (pR - 1) hpL_S hn)
    have hpL_prev_nS : pR - 2 ∉ S := by
      have h := (Finset.mem_filter.mp hpL_St).2
      have heq : pR - 1 - 1 = pR - 2 := by ring
      rwa [heq] at h
    have hpR_next_nS : pR + 1 ∉ S := by
      intro hnext
      have hnSt : pR + 1 ∉ Starts := by
        intro hst
        have hnot := (Finset.mem_filter.mp hst).2
        rw [add_sub_cancel_right] at hnot
        exact hnot hpR_S
      have heq := huniq (pR + 1) hnext hnSt
      have h1 : (1 : ZMod n) = 0 := by linear_combination heq
      have : Fact (1 < n) := ⟨by omega⟩
      have hv := congrArg ZMod.val h1
      rw [ZMod.val_one, ZMod.val_zero] at hv
      exact Nat.one_ne_zero hv
    have hpair_eq : h (idx (pR - 1)) = h (idx pR) := by
      obtain ⟨u, hu⟩ := hρ_bij.2 (fun s => if s.1 = pR - 1 then 1 else 0)
      have hu_val : ∀ z : ZMod n, u.1 (idx z) = if z = pR - 1 ∨ z = pR then 1 else 0 := by
        intro z
        by_cases hzS : z ∈ S
        · by_cases hzSt : z ∈ Starts
          · have h1 := congrFun hu ⟨z, hzSt⟩
            dsimp only [ρ, LinearMap.coe_mk, AddHom.coe_mk] at h1
            rw [h1]
            have hne : z ≠ pR := fun heq => hpR_nSt (heq ▸ hzSt)
            simp [hne]
          · have hzpR : z = pR := huniq z hzS hzSt
            rw [hzpR]
            have he := hedge (pR - 1) hpL_S (by rwa [sub_add_cancel]) u.1 u.2
            rw [sub_add_cancel] at he
            have h1 := congrFun hu ⟨pR - 1, hpL_St⟩
            dsimp only [ρ, LinearMap.coe_mk, AddHom.coe_mk] at h1
            simp only [↓reduceIte] at h1
            rw [← he, h1]
            simp
        · have hne1 : z ≠ pR - 1 := fun heq => hzS (heq ▸ hpL_S)
          have hne2 : z ≠ pR := fun heq => hzS (heq ▸ hpR_S)
          simp only [hne1, hne2, or_self, ↓reduceIte]
          by_contra h0
          exact hzS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.1, u.2, h0⟩)
      funext b
      have hkb := hkill u.1 u.2 b
      have hpair_sum : (∑ i : Fin n, h i b * u.1 i) = h (idx (pR - 1)) b + h (idx pR) b := by
        have hsub2 : ({idx (pR - 1), idx pR} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
        rw [← Finset.sum_subset hsub2]
        · rw [Finset.sum_pair (fun heq => hpL_ne_pR (hidx_inj heq))]
          have h1 := hu_val (pR - 1)
          have h2 := hu_val pR
          simp only [true_or, or_true, ↓reduceIte] at h1 h2
          rw [h1, h2, mul_one, mul_one]
        · intro i _ hni
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hni
          have h1 := hu_val (toZ i)
          rw [hidx_toZ] at h1
          have hne1 : toZ i ≠ pR - 1 := fun heq => hni.1 (by rw [← hidx_toZ i, heq])
          have hne2 : toZ i ≠ pR := fun heq => hni.2 (by rw [← hidx_toZ i, heq])
          simp only [hne1, hne2, or_self, ↓reduceIte] at h1
          rw [h1, mul_zero]
      rw [hpair_sum] at hkb
      have hadd := congrArg (fun x => x + h (idx pR) b) hkb
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
      exact hadd
    let S' : Finset (ZMod n) := Starts.erase (pR - 1)
    have hS'_card : S'.card = a - 1 := by
      rw [Finset.card_erase_of_mem hpL_St, hStarts_eq]
    have hS'_sub : ∀ z ∈ S', z ≠ pR - 1 ∧ z ≠ pR ∧ z ≠ pR + 1 ∧ z ≠ pR - 2 := by
      intro z hz
      have hzSt : z ∈ Starts := Finset.mem_of_mem_erase hz
      have hzS : z ∈ S := (Finset.mem_filter.mp hzSt).1
      exact ⟨Finset.ne_of_mem_erase hz, fun h => hpR_nSt (h ▸ hzSt),
        fun h => hpR_next_nS (h ▸ hzS), fun h => hpL_prev_nS (h ▸ hzS)⟩
    have hS'_ind : ∀ z ∈ S', z + 1 ∉ S' := by
      intro z hz hnext
      have hzS : z ∈ S := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hz)).1
      have hnot := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hnext)).2
      rw [add_sub_cancel_right] at hnot
      exact hnot hzS
    have hzeroS' : ∀ z ∈ S', h (idx z) = 0 := by
      intro z hz
      have hzSt : z ∈ Starts := Finset.mem_of_mem_erase hz
      have hz_ne_pL : z ≠ pR - 1 := Finset.ne_of_mem_erase hz
      have hz_ne_pR : z ≠ pR := fun h => hpR_nSt (h ▸ hzSt)
      obtain ⟨u, hu⟩ := hρ_bij.2 (fun s => if s.1 = z then 1 else 0)
      have hu_val : ∀ z' : ZMod n, u.1 (idx z') = if z' = z then 1 else 0 := by
        intro z'
        by_cases hz'S : z' ∈ S
        · by_cases hz'St : z' ∈ Starts
          · exact congrFun hu ⟨z', hz'St⟩
          · have hz'pR : z' = pR := huniq z' hz'S hz'St
            rw [hz'pR]
            have he := hedge (pR - 1) hpL_S (by rwa [sub_add_cancel]) u.1 u.2
            rw [sub_add_cancel] at he
            have h1 := congrFun hu ⟨pR - 1, hpL_St⟩
            dsimp only [ρ, LinearMap.coe_mk, AddHom.coe_mk] at h1
            simp only [hz_ne_pL.symm, ↓reduceIte] at h1
            rw [← he, h1]
            simp only [hz_ne_pR.symm, ↓reduceIte]
        · have hne : z' ≠ z := fun heq => hz'S (heq ▸ (Finset.mem_filter.mp hzSt).1)
          simp only [hne, ↓reduceIte]
          by_contra h0
          exact hz'S (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.1, u.2, h0⟩)
      funext b
      have hkb := hkill u.1 u.2 b
      rw [Finset.sum_eq_single (idx z)] at hkb
      · have h1 := hu_val z
        simp only [↓reduceIte] at h1
        rw [h1, mul_one] at hkb
        exact hkb
      · intro i _ hne
        have h1 := hu_val (toZ i)
        rw [hidx_toZ] at h1
        have hne' : toZ i ≠ z := fun heq => hne (by rw [← hidx_toZ i, heq])
        simp only [hne', ↓reduceIte] at h1
        rw [h1, mul_zero]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    have halt := ind_set_pair_alternating ha S' pR hS'_card hS'_sub hS'_ind
    let k : ZMod n := ((a + 1 : ℕ) : ZMod n) * pR
    have h2k : (2 : ZMod n) * k = pR := by
      dsimp only [k]
      calc (2 : ZMod n) * (((a + 1 : ℕ) : ZMod n) * pR)
          = ((2 : ZMod n) * ((a + 1 : ℕ) : ZMod n)) * pR := by ring
        _ = 1 * pR := by rw [zmod_two_mul_inv a]
        _ = pR := one_mul _
    refine ⟨k, ?_, ?_⟩
    · intro t
      have h2kt : (2 : ZMod n) * (k + 1 + (t.val : ZMod n)) = pR + ((2 + 2 * t.val : ℕ) : ZMod n) := by
        calc (2 : ZMod n) * (k + 1 + (t.val : ZMod n))
            = (2 : ZMod n) * k + (2 : ZMod n) + (2 : ZMod n) * (t.val : ZMod n) := by ring
          _ = pR + ((2 + 2 * t.val : ℕ) : ZMod n) := by rw [h2k]; push_cast; ring
      change h (idx ((2 : ZMod n) * (k + 1 + (t.val : ZMod n)))) = 0
      rw [h2kt]
      exact hzeroS' _ (halt t)
    · have h2ka : (2 : ZMod n) * (k + (a : ZMod n)) = pR - 1 := by
        have hn0 : ((2 * a + 1 : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
        calc (2 : ZMod n) * (k + (a : ZMod n))
            = (2 : ZMod n) * k + (2 : ZMod n) * (a : ZMod n) := by ring
          _ = pR + (2 : ZMod n) * (a : ZMod n) := by rw [h2k]
          _ = pR - 1 := by push_cast at hn0; linear_combination hn0
      change h (idx ((2 : ZMod n) * k)) = h (idx ((2 : ZMod n) * (k + (a : ZMod n))))
      rw [h2k, h2ka]
      exact hpair_eq.symm

end PEqualNP.Outside.L_lib_865_aux

open PEqualNP.Outside.L_lib_865_aux

theorem PEqualNP.Outside.L_lib_865 :
    (∀ (a m : ℕ), 2 ≤ a →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 2*a+1
  let A := Fin m → F
  let W := Fin n → F
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.succ_pos (2*a))⟩ : Fin n)
  let succeeds := fun h : Fin n → A =>
    ∃ U : Submodule F W, Module.finrank F U = a ∧
      (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let q := 2^m
  ((Finset.univ : Finset (Fin n → A)).filter succeeds).card =
    1 + 2*n*(q-1)*(q^a-1)) := by
  intro a m ha
  classical
  dsimp only
  let F := ZMod 2
  let n := 2 * a + 1
  let A := Fin m → F
  let W := Fin n → F
  let next : Fin n → Fin n := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.succ_pos (2 * a))⟩
  let succeeds : (Fin n → A) → Prop := fun h =>
    ∃ U : Submodule F W, Module.finrank F U = a ∧
      (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let q := 2 ^ m
  have : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let idx : ZMod n → Fin n := fun z => ⟨z.val, ZMod.val_lt z⟩
  let toZ : Fin n → ZMod n := fun i => (i.val : ZMod n)
  have hidx_toZ : ∀ i : Fin n, idx (toZ i) = i := by
    intro i; apply Fin.ext
    dsimp only [idx, toZ]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  have htoZ_idx : ∀ z : ZMod n, toZ (idx z) = z := by
    intro z; dsimp only [idx, toZ]; exact ZMod.natCast_zmod_val z
  have hidx_inj : Function.Injective idx := fun z1 z2 h => by
    have := congrArg toZ h; rwa [htoZ_idx, htoZ_idx] at this
  have hnext_idx : ∀ z : ZMod n, next (idx z) = idx (z + 1) := by
    intro z; apply Fin.ext
    dsimp only [next, idx]
    have hcast : (z + 1).val = (z.val + 1) % n := by
      have h1 : (z + 1) = ((z.val + 1 : ℕ) : ZMod n) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [h1, ZMod.val_natCast]
    exact hcast.symm
  let step2 : (Fin n → A) → (ZMod n → A) := fun h t => h (idx ((2 : ZMod n) * t))
  have hstep2_bij : Function.Bijective step2 := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · intro h1 h2 heq
      funext i
      let t : ZMod n := ((a + 1 : ℕ) : ZMod n) * toZ i
      have h2t : (2 : ZMod n) * t = toZ i := by
        dsimp only [t]
        calc (2 : ZMod n) * (((a + 1 : ℕ) : ZMod n) * toZ i)
            = ((2 : ZMod n) * ((a + 1 : ℕ) : ZMod n)) * toZ i := by ring
          _ = 1 * toZ i := by rw [zmod_two_mul_inv a]
          _ = toZ i := one_mul _
      have ht := congrFun heq t
      dsimp only [step2] at ht
      rw [h2t, hidx_toZ] at ht
      exact ht
    · simp [Fintype.card_pi, ZMod.card]
  let good : (ZMod n → A) → Prop := fun g =>
    (∃ k : ZMod n, ∀ t : Fin a, g (k + (t.val : ZMod n)) = 0) ∨
    (∃ k : ZMod n, (∀ t : Fin (a - 1), g (k + 1 + (t.val : ZMod n)) = 0) ∧ g k = g (k + (a : ZMod n)))
  have hsucceeds_iff : ∀ h : Fin n → A, succeeds h ↔ good (step2 h) := by
    intro h
    let g := step2 h
    constructor
    · rintro ⟨U, hdimU, hkill, hiso⟩
      exact succeeds_imp_good ha h U hdimU hkill hiso
    · rintro (⟨k, hk⟩ | ⟨k, hk0, hkeq⟩)
      · let p : Fin a → Fin n := fun t => idx ((2 : ZMod n) * (k + (t.val : ZMod n)))
        let v : Fin a → W := fun t i => if i = p t then 1 else 0
        let U : Submodule F W := Submodule.span F (Set.range v)
        have hp_inj : Function.Injective p := by
          intro t1 t2 heq
          have hz := zmod_two_mul_cancel (hidx_inj heq)
          exact Fin.ext ((zmod_add_natCast_eq_iff k (by omega : t1.val < n) (by omega : t2.val < n)).mp hz)
        have hli : LinearIndependent F v := by
          rw [Fintype.linearIndependent_iff]
          intro c hc t
          have hval : (∑ x : Fin a, c x * v x (p t)) = 0 := by
            have h0 := congrFun hc (p t)
            change (∑ x : Fin a, (c x • v x)) (p t) = 0 at h0
            rw [Finset.sum_apply] at h0
            exact h0
          rw [Finset.sum_eq_single t] at hval
          · simp only [v, ↓reduceIte, mul_one] at hval; exact hval
          · intro t' _ hne
            have hne' : p t ≠ p t' := fun heq => hne (hp_inj heq).symm
            simp only [v, hne', ↓reduceIte, mul_zero]
          · intro hnu; exact absurd (Finset.mem_univ _) hnu
        have hdimU : Module.finrank F U = a := by
          rw [finrank_span_eq_card hli, Fintype.card_fin]
        have hkill : ∀ x ∈ U, ∀ b : Fin m, (∑ i : Fin n, h i b * x i) = 0 := by
          intro x hx b
          let lin : W →ₗ[F] F :=
            { toFun := fun y => ∑ i : Fin n, h i b * y i
              map_add' := fun y1 y2 => by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                change h i b * (y1 i + y2 i) = h i b * y1 i + h i b * y2 i
                ring
              map_smul' := fun c y => by
                change (∑ i : Fin n, h i b * (c * y i)) = c * (∑ i : Fin n, h i b * y i)
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun i _ => by ring) }
          have hle : U ≤ LinearMap.ker lin := by
            rw [Submodule.span_le]
            rintro _ ⟨t, rfl⟩
            rw [SetLike.mem_coe, LinearMap.mem_ker]
            change ∑ i : Fin n, h i b * v t i = 0
            rw [Finset.sum_eq_single (p t)]
            · simp only [v, ↓reduceIte, mul_one]
              exact congrFun (hk t) b
            · intro i _ hne; simp [v, hne]
            · intro hnu; exact absurd (Finset.mem_univ _) hnu
          exact LinearMap.mem_ker.mp (hle hx)
        have hno_adj : ∀ t1 t2 : Fin a, next (p t1) ≠ p t2 := by
          intro t1 t2 heq
          dsimp only [p] at heq
          rw [hnext_idx] at heq
          have hz := (zmod_next_step2_iff (k + (t1.val : ZMod n)) (k + (t2.val : ZMod n))).mp (hidx_inj heq)
          have hrew : k + (t1.val : ZMod n) = k + ((t2.val + a : ℕ) : ZMod n) := by
            push_cast; linear_combination hz
          have hnat := (zmod_add_natCast_eq_iff k (by omega : t1.val < n) (by omega : t2.val + a < n)).mp hrew
          omega
        have hzero_out : ∀ x ∈ U, ∀ i : Fin n, (∀ t : Fin a, i ≠ p t) → x i = 0 := by
          intro x hx i hni
          let ev : W →ₗ[F] F :=
            { toFun := fun y => y i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
          have hle : U ≤ LinearMap.ker ev := by
            rw [Submodule.span_le]
            rintro _ ⟨t, rfl⟩
            rw [SetLike.mem_coe, LinearMap.mem_ker]
            change v t i = 0
            simp [v, hni t]
          exact LinearMap.mem_ker.mp (hle hx)
        refine ⟨U, hdimU, hkill, ?_⟩
        intro x hx y hy i
        by_cases hi : ∃ t : Fin a, i = p t
        · rcases hi with ⟨t, rfl⟩
          have hnext_out : ∀ t2 : Fin a, next (p t) ≠ p t2 := hno_adj t
          rw [hzero_out x hx (next (p t)) hnext_out, hzero_out y hy (next (p t)) hnext_out, mul_zero, zero_mul]
        · push Not at hi
          rw [hzero_out x hx i hi, hzero_out y hy i hi, zero_mul, mul_zero]
      · let pL : Fin n := idx ((2 : ZMod n) * (k + (a : ZMod n)))
        let pR : Fin n := idx ((2 : ZMod n) * k)
        have hnext_pL : next pL = pR := by
          dsimp only [pL, pR]
          rw [hnext_idx]
          congr 1
          exact (zmod_next_step2_iff (k + (a : ZMod n)) k).mpr rfl
        let qpt : Fin (a - 1) → Fin n := fun t => idx ((2 : ZMod n) * (k + 1 + (t.val : ZMod n)))
        let v : Option (Fin (a - 1)) → W := fun o i =>
          match o with
          | none => (if i = pL then 1 else 0) + (if i = pR then 1 else 0)
          | some t => if i = qpt t then 1 else 0
        let U : Submodule F W := Submodule.span F (Set.range v)
        have hpL_ne_pR : pL ≠ pR := by
          intro heq
          have hz := zmod_two_mul_cancel (hidx_inj heq)
          have hrew : k + (a : ZMod n) = k + ((0 : ℕ) : ZMod n) := by simpa using hz
          have hnat := (zmod_add_natCast_eq_iff k (by omega : a < n) (by omega : 0 < n)).mp hrew
          omega
        have hpR_ne_q : ∀ t : Fin (a - 1), pR ≠ qpt t := by
          intro t heq
          have hz := zmod_two_mul_cancel (hidx_inj heq)
          have hrew : k + ((0 : ℕ) : ZMod n) = k + ((t.val + 1 : ℕ) : ZMod n) := by
            push_cast; linear_combination hz
          have hnat := (zmod_add_natCast_eq_iff k (by omega : 0 < n) (by omega : t.val + 1 < n)).mp hrew
          omega
        have hpL_ne_q : ∀ t : Fin (a - 1), pL ≠ qpt t := by
          intro t heq
          have hz := zmod_two_mul_cancel (hidx_inj heq)
          have hrew : k + (a : ZMod n) = k + ((t.val + 1 : ℕ) : ZMod n) := by
            push_cast; linear_combination hz
          have hnat := (zmod_add_natCast_eq_iff k (by omega : a < n) (by omega : t.val + 1 < n)).mp hrew
          omega
        have hq_inj : Function.Injective qpt := by
          intro t1 t2 heq
          have hz := zmod_two_mul_cancel (hidx_inj heq)
          have hrew : k + ((t1.val + 1 : ℕ) : ZMod n) = k + ((t2.val + 1 : ℕ) : ZMod n) := by
            push_cast; linear_combination hz
          have hnat := (zmod_add_natCast_eq_iff k (by omega : t1.val + 1 < n) (by omega : t2.val + 1 < n)).mp hrew
          exact Fin.ext (by omega)
        have hli : LinearIndependent F v := by
          rw [Fintype.linearIndependent_iff]
          intro c hc o
          cases o with
          | none =>
            have hval : (∑ o : Option (Fin (a - 1)), c o * v o pR) = 0 := by
              have h0 := congrFun hc pR
              change (∑ o : Option (Fin (a - 1)), (c o • v o)) pR = 0 at h0
              rw [Finset.sum_apply] at h0
              exact h0
            rw [Fintype.sum_option] at hval
            have hsum0 : ∑ t : Fin (a - 1), c (some t) * v (some t) pR = 0 :=
              Finset.sum_eq_zero (fun t _ => by simp only [v, hpR_ne_q t, ↓reduceIte, mul_zero])
            rw [hsum0, add_zero] at hval
            simp only [v, hpL_ne_pR.symm, ↓reduceIte, zero_add, mul_one] at hval
            exact hval
          | some t =>
            have hval : (∑ o : Option (Fin (a - 1)), c o * v o (qpt t)) = 0 := by
              have h0 := congrFun hc (qpt t)
              change (∑ o : Option (Fin (a - 1)), (c o • v o)) (qpt t) = 0 at h0
              rw [Finset.sum_apply] at h0
              exact h0
            rw [Fintype.sum_option] at hval
            have hnone0 : c none * v none (qpt t) = 0 := by
              simp only [v, (hpL_ne_q t).symm, (hpR_ne_q t).symm, ↓reduceIte, add_zero, mul_zero]
            rw [hnone0, zero_add] at hval
            rw [Finset.sum_eq_single t] at hval
            · simp only [v, ↓reduceIte, mul_one] at hval; exact hval
            · intro t' _ hne
              have hne' : qpt t ≠ qpt t' := fun heq => hne (hq_inj heq).symm
              simp only [v, hne', ↓reduceIte, mul_zero]
            · intro hnu; exact absurd (Finset.mem_univ _) hnu
        have hdimU : Module.finrank F U = a := by
          rw [finrank_span_eq_card hli, Fintype.card_option, Fintype.card_fin]
          omega
        have hkill : ∀ x ∈ U, ∀ b : Fin m, (∑ i : Fin n, h i b * x i) = 0 := by
          intro x hx b
          let lin : W →ₗ[F] F :=
            { toFun := fun y => ∑ i : Fin n, h i b * y i
              map_add' := fun y1 y2 => by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                change h i b * (y1 i + y2 i) = h i b * y1 i + h i b * y2 i
                ring
              map_smul' := fun c y => by
                change (∑ i : Fin n, h i b * (c * y i)) = c * (∑ i : Fin n, h i b * y i)
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun i _ => by ring) }
          have hle : U ≤ LinearMap.ker lin := by
            rw [Submodule.span_le]
            rintro _ ⟨o, rfl⟩
            rw [SetLike.mem_coe, LinearMap.mem_ker]
            change ∑ i : Fin n, h i b * v o i = 0
            cases o with
            | none =>
              have hsub2 : ({pL, pR} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
              rw [← Finset.sum_subset hsub2]
              · rw [Finset.sum_pair hpL_ne_pR]
                simp only [v, ↓reduceIte, hpL_ne_pR, hpL_ne_pR.symm, add_zero, zero_add, mul_one]
                have hbg : g (k + (a : ZMod n)) b = g k b := (congrFun hkeq b).symm
                change g (k + (a : ZMod n)) b + g k b = 0
                rw [hbg, zmod2_add_self]
              · intro i _ hni
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hni
                simp [v, hni.1, hni.2]
            | some t =>
              rw [Finset.sum_eq_single (qpt t)]
              · simp only [v, ↓reduceIte, mul_one]
                exact congrFun (hk0 t) b
              · intro i _ hne; simp [v, hne]
              · intro hnu; exact absurd (Finset.mem_univ _) hnu
          exact LinearMap.mem_ker.mp (hle hx)
        have hpair_eq_U : ∀ x ∈ U, x pL = x pR := by
          intro x hx
          let diff : W →ₗ[F] F :=
            { toFun := fun y => y pL + y pR
              map_add' := fun y1 y2 => by
                change (y1 pL + y2 pL) + (y1 pR + y2 pR) = (y1 pL + y1 pR) + (y2 pL + y2 pR); ring
              map_smul' := fun c y => by
                change c * y pL + c * y pR = c * (y pL + y pR); ring }
          have hle : U ≤ LinearMap.ker diff := by
            rw [Submodule.span_le]
            rintro _ ⟨o, rfl⟩
            rw [SetLike.mem_coe, LinearMap.mem_ker]
            change v o pL + v o pR = 0
            cases o with
            | none =>
              simp only [v, ↓reduceIte, hpL_ne_pR, hpL_ne_pR.symm, add_zero, zero_add]
              exact zmod2_add_self 1
            | some t =>
              simp [v, hpL_ne_q t, hpR_ne_q t]
          have h0 : x pL + x pR = 0 := LinearMap.mem_ker.mp (hle hx)
          have h1 := congrArg (fun z => z + x pR) h0
          rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h1
          exact h1
        have hzero_out : ∀ x ∈ U, ∀ i : Fin n, i ≠ pL → i ≠ pR → (∀ t : Fin (a - 1), i ≠ qpt t) → x i = 0 := by
          intro x hx i h1 h2 h3
          let ev : W →ₗ[F] F :=
            { toFun := fun y => y i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
          have hle : U ≤ LinearMap.ker ev := by
            rw [Submodule.span_le]
            rintro _ ⟨o, rfl⟩
            rw [SetLike.mem_coe, LinearMap.mem_ker]
            change v o i = 0
            cases o with
            | none => simp [v, h1, h2]
            | some t => simp [v, h3 t]
          exact LinearMap.mem_ker.mp (hle hx)
        have hno_other_adj : ∀ z1 z2 : ℕ, z1 ≤ a → z2 ≤ a →
            next (idx ((2 : ZMod n) * (k + (z1 : ZMod n)))) = idx ((2 : ZMod n) * (k + (z2 : ZMod n))) →
            z1 = a ∧ z2 = 0 := by
          intro z1 z2 hz1 hz2 heq
          rw [hnext_idx] at heq
          have hz := (zmod_next_step2_iff (k + (z1 : ZMod n)) (k + (z2 : ZMod n))).mp (hidx_inj heq)
          have hrew : k + (z1 : ZMod n) = k + ((z2 + a : ℕ) : ZMod n) := by
            push_cast; linear_combination hz
          have hnat := (zmod_add_natCast_eq_iff k (by omega : z1 < n) (by omega : z2 + a < n)).mp hrew
          omega
        refine ⟨U, hdimU, hkill, ?_⟩
        intro x hx y hy i
        by_cases hipL : i = pL
        · subst hipL
          rw [hnext_pL, hpair_eq_U x hx, hpair_eq_U y hy]
        · by_cases hiS : ∃ z1 : ℕ, z1 ≤ a ∧ i = idx ((2 : ZMod n) * (k + (z1 : ZMod n)))
          · rcases hiS with ⟨z1, hz1, rfl⟩
            have hz1_ne : z1 ≠ a := fun h => hipL (by rw [h])
            have hnext_not_in : ∀ z2 : ℕ, z2 ≤ a → next (idx ((2 : ZMod n) * (k + (z1 : ZMod n)))) ≠
                idx ((2 : ZMod n) * (k + (z2 : ZMod n))) := by
              intro z2 hz2 heq
              exact hz1_ne (hno_other_adj z1 z2 hz1 hz2 heq).1
            have hn1 : next (idx ((2 : ZMod n) * (k + (z1 : ZMod n)))) ≠ pL := hnext_not_in a (le_refl a)
            have hn2 : next (idx ((2 : ZMod n) * (k + (z1 : ZMod n)))) ≠ pR := by
              simpa [pR] using hnext_not_in 0 (Nat.zero_le a)
            have hn3 : ∀ t : Fin (a - 1), next (idx ((2 : ZMod n) * (k + (z1 : ZMod n)))) ≠ qpt t := by
              intro t
              have h := hnext_not_in (t.val + 1) (by omega)
              have hrew : k + ((t.val + 1 : ℕ) : ZMod n) = k + 1 + (t.val : ZMod n) := by push_cast; ring
              dsimp only [qpt]
              rwa [← hrew]
            rw [hzero_out x hx _ hn1 hn2 hn3, hzero_out y hy _ hn1 hn2 hn3, mul_zero, zero_mul]
          · push Not at hiS
            have hi1 : i ≠ pL := hipL
            have hi2 : i ≠ pR := by simpa [pR] using hiS 0 (Nat.zero_le a)
            have hi3 : ∀ t : Fin (a - 1), i ≠ qpt t := by
              intro t
              have h := hiS (t.val + 1) (by omega)
              have hrew : k + ((t.val + 1 : ℕ) : ZMod n) = k + 1 + (t.val : ZMod n) := by push_cast; ring
              dsimp only [qpt]
              rwa [← hrew]
            rw [hzero_out x hx i hi1 hi2 hi3, hzero_out y hy i hi1 hi2 hi3, zero_mul, mul_zero]
  trans ((Finset.univ : Finset (ZMod n → A)).filter good).card
  · apply Finset.card_bij (fun h _ => step2 h)
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact (hsucceeds_iff h).mp hh
    · intro h1 _ h2 _ heq; exact hstep2_bij.1 heq
    · intro g hg
      obtain ⟨h, rfl⟩ := hstep2_bij.2 g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact ⟨h, (hsucceeds_iff h).mpr hg, rfl⟩
  · exact card_good_eq ha _

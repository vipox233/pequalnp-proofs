import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25713_aux

private def lossFn {n : ℕ} (G : Fin n → Fin n → Bool) (q : ℕ) (π : Equiv.Perm (Fin n))
    (rowFlip colFlip : Fin n → Bool) (R C : Fin q → Finset (Fin n))
    (out : Finset (Fin n) → (Fin q → Bool) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
    out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
      Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card

private lemma sq_le_four_pow : ∀ m : ℕ, m * m ≤ 4 ^ m
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | m + 3 => by
      have ih := sq_le_four_pow (m + 2)
      have h1 : (m + 3) * (m + 3) ≤ 4 * ((m + 2) * (m + 2)) := by nlinarith
      calc
        (m + 3) * (m + 3) ≤ 4 * ((m + 2) * (m + 2)) := h1
        _ ≤ 4 * 4 ^ (m + 2) := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (m + 3) := by rw [← pow_succ']

private lemma two_pow_two_mul_sub_one_le (m : ℕ) : 2 ^ (2 * m - 1) ≤ 4 ^ m := by
  have h1 : 2 ^ (2 * m - 1) ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ (2 * m) = 4 ^ m := by
    rw [pow_mul]
    norm_num
  omega

private lemma exists_mono_biclique {n : ℕ} (G : Fin n → Fin n → Bool) {m : ℕ} (hm : 1 ≤ m)
    {U V : Finset (Fin n)} (hU : m * 4 ^ m ≤ U.card) (hV : m * 4 ^ m ≤ V.card) :
    ∃ (A B : Finset (Fin n)) (c : Bool),
      A ⊆ U ∧ B ⊆ V ∧ A.card = m ∧ B.card = m ∧ ∀ a ∈ A, ∀ b ∈ B, G a b = c := by
  have h2m1_le : 2 * m - 1 ≤ V.card := by
    have h4m : 2 ≤ 4 ^ m := by
      calc
        2 ≤ 4 ^ 1 := by decide
        _ ≤ 4 ^ m := Nat.pow_le_pow_right (by omega) hm
    have hmul : m * 2 ≤ m * 4 ^ m := Nat.mul_le_mul_left m h4m
    omega
  rcases Finset.exists_subset_card_eq h2m1_le with ⟨B0, hB0_sub, hB0_card⟩
  let pat : Fin n → (B0 → Bool) := fun a b => G a b.1
  have hsum_fib :
      ∑ p : B0 → Bool, (U.filter (fun a => pat a = p)).card = U.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨pat a, ha, rfl⟩⟩
    · intro p₁ _ p₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hcard_pat : Fintype.card (B0 → Bool) = 2 ^ (2 * m - 1) := by
    simp [hB0_card]
  have hex_p : ∃ p : B0 → Bool, m ≤ (U.filter (fun a => pat a = p)).card := by
    by_contra hall
    push Not at hall
    have hle : ∑ p : B0 → Bool, (U.filter (fun a => pat a = p)).card ≤
        ∑ _p : B0 → Bool, (m - 1) :=
      Finset.sum_le_sum fun p _ => by have := hall p; omega
    simp only [Finset.sum_const, Finset.card_univ, hcard_pat, smul_eq_mul] at hle
    rw [hsum_fib] at hle
    have hpow := two_pow_two_mul_sub_one_le m
    have hlt : 2 ^ (2 * m - 1) * (m - 1) < m * 4 ^ m := by
      have hpos : 0 < 4 ^ m := Nat.pos_of_ne_zero (by positivity)
      have hstep : 2 ^ (2 * m - 1) * (m - 1) ≤ 4 ^ m * (m - 1) :=
        Nat.mul_le_mul_right (m - 1) hpow
      have hstep2 : 4 ^ m * (m - 1) < 4 ^ m * m :=
        Nat.mul_lt_mul_of_pos_left (by omega) hpos
      rw [mul_comm (4 ^ m) m] at hstep2
      omega
    omega
  rcases hex_p with ⟨p, hp⟩
  rcases Finset.exists_subset_card_eq hp with ⟨A, hA_sub_f, hA_card⟩
  have hA_sub : A ⊆ U := Finset.Subset.trans hA_sub_f (Finset.filter_subset _ _)
  let Bt := B0.attach.filter (fun b => p b = true)
  let Bf := B0.attach.filter (fun b => p b = false)
  have hBtf_disj : Disjoint Bt Bf := by
    rw [Finset.disjoint_left]
    intro b h1 h2
    simp only [Bt, Bf, Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  have hBtf_union : Bt ∪ Bf = B0.attach := by
    ext b
    simp only [Bt, Bf, Finset.mem_union, Finset.mem_filter, Finset.mem_attach, true_and, iff_true]
    cases p b <;> simp
  have hBtf_card : Bt.card + Bf.card = 2 * m - 1 := by
    rw [← Finset.card_union_of_disjoint hBtf_disj, hBtf_union, Finset.card_attach, hB0_card]
  by_cases hBt : m ≤ Bt.card
  · rcases Finset.exists_subset_card_eq hBt with ⟨Bsub, hBsub, hBsub_card⟩
    let B : Finset (Fin n) := Bsub.image Subtype.val
    have hB_card : B.card = m := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hBsub_card]
    have hB_sub : B ⊆ V := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨b', _, rfl⟩
      exact hB0_sub b'.2
    refine ⟨A, B, true, hA_sub, hB_sub, hA_card, hB_card, ?_⟩
    intro a ha b hb
    rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
    have ha' := (Finset.mem_filter.mp (hA_sub_f ha)).2
    have hb'' := (Finset.mem_filter.mp (hBsub hb')).2
    have := congr_fun ha' b'
    simpa only [pat, hb''] using this
  · have hBf : m ≤ Bf.card := by omega
    rcases Finset.exists_subset_card_eq hBf with ⟨Bsub, hBsub, hBsub_card⟩
    let B : Finset (Fin n) := Bsub.image Subtype.val
    have hB_card : B.card = m := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hBsub_card]
    have hB_sub : B ⊆ V := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨b', _, rfl⟩
      exact hB0_sub b'.2
    refine ⟨A, B, false, hA_sub, hB_sub, hA_card, hB_card, ?_⟩
    intro a ha b hb
    rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
    have ha' := (Finset.mem_filter.mp (hA_sub_f ha)).2
    have hb'' := (Finset.mem_filter.mp (hBsub hb')).2
    have := congr_fun ha' b'
    simpa only [pat, hb''] using this

private lemma pack_mono_groups {n : ℕ} (G : Fin n → Fin n → Bool) (m : ℕ) (hm : 1 ≤ m) :
    ∀ s : ℕ, ∀ U V : Finset (Fin n), U.card = s → V.card = s →
      ∃ (L : ℕ) (e : U ≃ V) (g : U → Fin L),
        m * L ≤ s + m * (m * 4 ^ m) ∧
        ∀ x y : U, g x = g y → G x.1 (e y).1 = G y.1 (e x).1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro U V hU hV
    by_cases hbig : m * 4 ^ m ≤ s
    · rcases exists_mono_biclique G hm (hU ▸ hbig) (hV ▸ hbig) with
        ⟨A, B, c, hA_sub, hB_sub, hA_card, hB_card, hmono⟩
      let U' := U \ A
      let V' := V \ B
      have hU'_card : U'.card = s - m := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hA_sub, hU, hA_card]
      have hV'_card : V'.card = s - m := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB_sub, hV, hB_card]
      have hlt : s - m < s := by
        have hpos : 0 < m * 4 ^ m := by
          have : 0 < 4 ^ m := Nat.pos_of_ne_zero (by positivity)
          nlinarith
        omega
      rcases ih (s - m) hlt U' V' hU'_card hV'_card with ⟨L', e', g', hL', hsym'⟩
      have hcardAB : Fintype.card A = Fintype.card B := by
        simp [Fintype.card_coe, hA_card, hB_card]
      let eAB : A ≃ B := Fintype.equivOfCardEq hcardAB
      let eFun : U → V := fun x =>
        if hx : x.1 ∈ A then ⟨(eAB ⟨x.1, hx⟩).1, hB_sub (eAB ⟨x.1, hx⟩).2⟩
        else ⟨(e' ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).1,
          (Finset.mem_sdiff.mp (e' ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).1⟩
      have heFun_inj : Function.Injective eFun := by
        intro x₁ x₂ hEq
        by_cases h1 : x₁.1 ∈ A <;> by_cases h2 : x₂.1 ∈ A
        · simp only [eFun, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at hEq
          have hsub : eAB ⟨x₁.1, h1⟩ = eAB ⟨x₂.1, h2⟩ := Subtype.ext hEq
          have hinj := eAB.injective hsub
          simp only [Subtype.mk.injEq] at hinj
          exact Subtype.ext hinj
        · simp only [eFun, h1, h2, ↓reduceDIte] at hEq
          have hm1 : (eAB ⟨x₁.1, h1⟩).1 ∈ B := (eAB ⟨x₁.1, h1⟩).2
          have hm2 : (e' ⟨x₂.1, Finset.mem_sdiff.mpr ⟨x₂.2, h2⟩⟩).1 ∉ B :=
            (Finset.mem_sdiff.mp (e' ⟨x₂.1, Finset.mem_sdiff.mpr ⟨x₂.2, h2⟩⟩).2).2
          rw [congr_arg Subtype.val hEq] at hm1
          exact absurd hm1 hm2
        · simp only [eFun, h1, h2, ↓reduceDIte] at hEq
          have hm1 : (e' ⟨x₁.1, Finset.mem_sdiff.mpr ⟨x₁.2, h1⟩⟩).1 ∉ B :=
            (Finset.mem_sdiff.mp (e' ⟨x₁.1, Finset.mem_sdiff.mpr ⟨x₁.2, h1⟩⟩).2).2
          have hm2 : (eAB ⟨x₂.1, h2⟩).1 ∈ B := (eAB ⟨x₂.1, h2⟩).2
          rw [← congr_arg Subtype.val hEq] at hm2
          exact absurd hm2 hm1
        · simp only [eFun, h1, h2, ↓reduceDIte, Subtype.mk.injEq] at hEq
          have hsub : e' ⟨x₁.1, Finset.mem_sdiff.mpr ⟨x₁.2, h1⟩⟩ =
              e' ⟨x₂.1, Finset.mem_sdiff.mpr ⟨x₂.2, h2⟩⟩ := Subtype.ext hEq
          have hinj := e'.injective hsub
          simp only [Subtype.mk.injEq] at hinj
          exact Subtype.ext hinj
      have hcardUV : Fintype.card U = Fintype.card V := by
        simp [Fintype.card_coe, hU, hV]
      have heFun_bij : Function.Bijective eFun :=
        (Fintype.bijective_iff_injective_and_card eFun).mpr ⟨heFun_inj, hcardUV⟩
      let e : U ≃ V := Equiv.ofBijective eFun heFun_bij
      let g : U → Fin (L' + 1) := fun x =>
        if hx : x.1 ∈ A then 0 else (g' ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).succ
      refine ⟨L' + 1, e, g, ?_, ?_⟩
      · have hms : m ≤ s := by
          have : 1 ≤ 4 ^ m := Nat.one_le_pow m 4 (by omega)
          nlinarith
        rw [mul_add, mul_one]
        omega
      · intro x y hgy
        by_cases hx : x.1 ∈ A <;> by_cases hy : y.1 ∈ A
        · have hex : (e x).1 ∈ B := by
            simp only [e, Equiv.ofBijective_apply, eFun, hx, ↓reduceDIte]
            exact (eAB ⟨x.1, hx⟩).2
          have hey : (e y).1 ∈ B := by
            simp only [e, Equiv.ofBijective_apply, eFun, hy, ↓reduceDIte]
            exact (eAB ⟨y.1, hy⟩).2
          rw [hmono x.1 hx (e y).1 hey, hmono y.1 hy (e x).1 hex]
        · simp only [g, hx, hy, ↓reduceDIte] at hgy
          exact absurd hgy.symm (Fin.succ_ne_zero _)
        · simp only [g, hx, hy, ↓reduceDIte] at hgy
          exact absurd hgy (Fin.succ_ne_zero _)
        · simp only [g, hx, hy, ↓reduceDIte] at hgy
          have hg'eq := Fin.succ_injective _ hgy
          have hsym := hsym' ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
            ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩ hg'eq
          simpa only [e, Equiv.ofBijective_apply, eFun, hx, hy, ↓reduceDIte] using hsym
    · have hcardUV : Fintype.card U = Fintype.card V := by
        simp [Fintype.card_coe, hU, hV]
      let e : U ≃ V := Fintype.equivOfCardEq hcardUV
      let g : U → Fin s := fun x => (U.equivFin x).cast hU
      have hg_inj : Function.Injective g := by
        intro x₁ x₂ hEq
        have hv : (g x₁).val = (g x₂).val := congr_arg Fin.val hEq
        have h1 : U.equivFin x₁ = U.equivFin x₂ := Fin.ext (by simpa [g] using hv)
        exact U.equivFin.injective h1
      refine ⟨s, e, g, ?_, ?_⟩
      · have : s ≤ m * 4 ^ m := by omega
        have h1 : m * s ≤ m * (m * 4 ^ m) := Nat.mul_le_mul_left m this
        omega
      · intro x y hgy
        have hxy := hg_inj hgy
        subst hxy
        rfl

private lemma tern_distinguish :
    ∀ u v : Fin 3, u ≠ v →
      decide (u = 0 ∨ v = 1) ≠ decide (v = 0 ∨ u = 1) := by
  decide

private lemma upper_bound_packing {k q : ℕ} (hk : 16 ≤ k) (hq : 16 * 2 ^ k ≤ k * 3 ^ q)
    (G : Fin (2 ^ k) → Fin (2 ^ k) → Bool) :
    ∃ (π : Equiv.Perm (Fin (2 ^ k))) (R C : Fin q → Finset (Fin (2 ^ k)))
      (out : Finset (Fin (2 ^ k)) → (Fin q → Bool) → Bool),
      lossFn G q π (fun _ => false) (fun _ => false) R C out = 0 := by
  classical
  let n := 2 ^ k
  let m := k / 4
  have hm4 : 4 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hpack := pack_mono_groups G m hm1 n Finset.univ Finset.univ
    (by simp [n]) (by simp [n])
  rcases hpack with ⟨L, e, g, hL_bound, hsym⟩
  have hm_sq : m * (m * 4 ^ m) ≤ n := by
    have h1 : m * m ≤ 4 ^ m := sq_le_four_pow m
    have h2 : m * (m * 4 ^ m) = (m * m) * 4 ^ m := by ring
    have h3 : 4 ^ m * 4 ^ m = 2 ^ (4 * m) := by
      calc
        4 ^ m * 4 ^ m = (4 * 4) ^ m := (mul_pow 4 4 m).symm
        _ = (2 ^ 4) ^ m := by norm_num
        _ = 2 ^ (4 * m) := (pow_mul 2 4 m).symm
    have h4 : 2 ^ (4 * m) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      m * (m * 4 ^ m) = (m * m) * 4 ^ m := h2
      _ ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul_right (4 ^ m) h1
      _ = 2 ^ (4 * m) := h3
      _ ≤ 2 ^ k := h4
  have hL_le : L ≤ 3 ^ q := by
    have h1 : m * L ≤ 2 * n := by omega
    have h2 : k ≤ 8 * m := by omega
    have h3 : k * L ≤ 8 * m * L := Nat.mul_le_mul_right L h2
    have h4 : 8 * m * L = 8 * (m * L) := by ring
    have h5 : k * L ≤ k * 3 ^ q := by omega
    exact Nat.le_of_mul_le_mul_left h5 (by omega)
  let π : Equiv.Perm (Fin n) :=
    { toFun := fun x => (e ⟨x, Finset.mem_univ x⟩).1
      invFun := fun y => (e.symm ⟨y, Finset.mem_univ y⟩).1
      left_inv := fun x => by
        have := e.symm_apply_apply ⟨x, Finset.mem_univ x⟩
        exact congr_arg Subtype.val this
      right_inv := fun y => by
        have := e.apply_symm_apply ⟨y, Finset.mem_univ y⟩
        exact congr_arg Subtype.val this }
  have hcard_tern : Fintype.card (Fin q → Fin 3) = 3 ^ q := by
    simp
  let eTern : Fin (3 ^ q) ≃ (Fin q → Fin 3) :=
    (finCongr hcard_tern.symm).trans (Fintype.equivFin (Fin q → Fin 3)).symm
  let addr : Fin n → (Fin q → Fin 3) := fun x =>
    eTern (Fin.castLE hL_le (g ⟨x, Finset.mem_univ x⟩))
  let R : Fin q → Finset (Fin n) := fun j => Finset.univ.filter (fun x => addr x j = 0)
  let C : Fin q → Finset (Fin n) := fun j => Finset.univ.filter (fun y => addr (π.symm y) j = 1)
  let sig : Fin n → Fin n → (Fin q → Bool) := fun x y j => decide (x ∈ R j ∨ π y ∈ C j)
  have hsig_eq : ∀ x y : Fin n, ∀ j : Fin q,
      sig x y j = decide (addr x j = 0 ∨ addr y j = 1) := by
    intro x y j
    simp only [sig, R, C, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  have hwell : ∀ x₁ y₁ x₂ y₂ : Fin n,
      ({x₁, y₁} : Finset (Fin n)) = ({x₂, y₂} : Finset (Fin n)) →
      sig x₁ y₁ = sig x₂ y₂ →
      G x₁ (π y₁) = G x₂ (π y₂) := by
    intro x₁ y₁ x₂ y₂ hset hsig
    have hmem1 : x₁ ∈ ({x₂, y₂} : Finset (Fin n)) := by rw [← hset]; simp
    have hmem2 : y₁ ∈ ({x₂, y₂} : Finset (Fin n)) := by rw [← hset]; simp
    have hmem3 : x₂ ∈ ({x₁, y₁} : Finset (Fin n)) := by rw [hset]; simp
    have hmem4 : y₂ ∈ ({x₁, y₁} : Finset (Fin n)) := by rw [hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2 hmem3 hmem4
    by_cases hsame : x₁ = x₂ ∧ y₁ = y₂
    · rw [hsame.1, hsame.2]
    · have hswap : x₁ = y₂ ∧ y₁ = x₂ := by
        rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2 <;>
          rcases hmem3 with h3 | h3 <;> rcases hmem4 with h4 | h4 <;>
          subst_vars <;> first | exact ⟨rfl, rfl⟩ | exact absurd ⟨rfl, rfl⟩ hsame
      rcases hswap with ⟨rfl, rfl⟩
      by_cases haddr : addr x₁ = addr y₁
      · have hg_eq : g ⟨x₁, Finset.mem_univ x₁⟩ = g ⟨y₁, Finset.mem_univ y₁⟩ := by
          have h1 := eTern.injective haddr
          exact Fin.ext (by simpa [Fin.val_castLE] using congr_arg Fin.val h1)
        exact hsym ⟨x₁, Finset.mem_univ x₁⟩ ⟨y₁, Finset.mem_univ y₁⟩ hg_eq
      · exfalso
        have hex : ∃ j : Fin q, addr x₁ j ≠ addr y₁ j := by
          by_contra hall
          push Not at hall
          exact haddr (funext hall)
        rcases hex with ⟨j, hj⟩
        have hsj := congr_fun hsig j
        rw [hsig_eq x₁ y₁ j, hsig_eq y₁ x₁ j] at hsj
        exact tern_distinguish (addr x₁ j) (addr y₁ j) hj hsj
  let out : Finset (Fin n) → (Fin q → Bool) → Bool := fun S s =>
    if h : ∃ z : Fin n × Fin n, ({z.1, z.2} : Finset (Fin n)) = S ∧ sig z.1 z.2 = s then
      G (Classical.choose h).1 (π (Classical.choose h).2)
    else false
  refine ⟨π, R, C, out, ?_⟩
  simp only [lossFn, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_implies, not_not, Bool.xor_false]
  intro z
  have hex : ∃ z' : Fin n × Fin n, ({z'.1, z'.2} : Finset (Fin n)) = {z.1, z.2} ∧
      sig z'.1 z'.2 = sig z.1 z.2 := ⟨z, rfl, rfl⟩
  have hsp := Classical.choose_spec hex
  have hout : out {z.1, z.2} (sig z.1 z.2) =
      G (Classical.choose hex).1 (π (Classical.choose hex).2) := by
    simp only [out, hex, ↓reduceDIte]
  change out {z.1, z.2} (sig z.1 z.2) = G z.1 (π z.2)
  rw [hout]
  exact hwell (Classical.choose hex).1 (Classical.choose hex).2 z.1 z.2 hsp.1 hsp.2

private def toTern (r c : Bool) : Fin 3 :=
  match r, c with
  | true,  false => 0
  | false, true  => 1
  | _,     _     => 2

private lemma same_tern_same_or :
    ∀ r1 c1 r2 c2 : Bool,
      toTern r1 c1 = toTern r2 c2 →
      (r1 || c2) = (r2 || c1) := by
  decide

private lemma binom_tail_fourth_bound (B e : ℕ) :
    (∑ j ∈ Finset.range (e + 1), B.choose j) ^ 4 ≤ 2 ^ (12 * e + B) := by
  let S := ∑ j ∈ Finset.range (e + 1), B.choose j
  have h1 : S * 8 ^ B ≤ 8 ^ e * 9 ^ B := by
    have hmul : S * 8 ^ B = ∑ j ∈ Finset.range (e + 1), B.choose j * 8 ^ B := Finset.sum_mul ..
    rw [hmul]
    have hle1 :
        ∑ j ∈ Finset.range (e + 1), B.choose j * 8 ^ B ≤
        ∑ j ∈ Finset.range (e + 1), 8 ^ e * (B.choose j * 8 ^ (B - j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      by_cases hjB : j ≤ B
      · have hpow : 8 ^ B = 8 ^ j * 8 ^ (B - j) := by
          rw [← pow_add, Nat.add_sub_of_le hjB]
        have h8 : 8 ^ j ≤ 8 ^ e := Nat.pow_le_pow_right (by omega) hje
        calc
          B.choose j * 8 ^ B = B.choose j * (8 ^ j * 8 ^ (B - j)) := by rw [hpow]
          _ = 8 ^ j * (B.choose j * 8 ^ (B - j)) := by ring
          _ ≤ 8 ^ e * (B.choose j * 8 ^ (B - j)) := Nat.mul_le_mul_right _ h8
      · have h0 : B.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [h0]
    have hle2 :
        ∑ j ∈ Finset.range (e + 1), B.choose j * 8 ^ (B - j) ≤
        ∑ j ∈ Finset.range (B + 1), B.choose j * 8 ^ (B - j) := by
      by_cases heB : e ≤ B
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.succ_le_succ heB)) (fun _ _ _ => Nat.zero_le _)
      · have hsub : Finset.range (B + 1) ⊆ Finset.range (e + 1) :=
          Finset.range_mono (by omega)
        have heq :
            ∑ j ∈ Finset.range (e + 1), B.choose j * 8 ^ (B - j) =
            ∑ j ∈ Finset.range (B + 1), B.choose j * 8 ^ (B - j) := by
          symm
          refine Finset.sum_subset hsub ?_
          intro j _ hjB
          have hgt : B < j := by
            simp only [Finset.mem_range] at hjB
            omega
          simp [Nat.choose_eq_zero_of_lt hgt]
        exact le_of_eq heq
    have hbinom : ∑ j ∈ Finset.range (B + 1), B.choose j * 8 ^ (B - j) = 9 ^ B := by
      have hp := add_pow (1 : ℕ) 8 B
      have h9 : (1 + 8 : ℕ) = 9 := rfl
      rw [h9] at hp
      rw [hp]
      refine Finset.sum_congr rfl fun j _ => by simp [mul_comm]
    calc
      ∑ j ∈ Finset.range (e + 1), B.choose j * 8 ^ B
          ≤ ∑ j ∈ Finset.range (e + 1), 8 ^ e * (B.choose j * 8 ^ (B - j)) := hle1
      _ = 8 ^ e * ∑ j ∈ Finset.range (e + 1), B.choose j * 8 ^ (B - j) :=
            (Finset.mul_sum ..).symm
      _ ≤ 8 ^ e * ∑ j ∈ Finset.range (B + 1), B.choose j * 8 ^ (B - j) :=
            Nat.mul_le_mul_left _ hle2
      _ = 8 ^ e * 9 ^ B := by rw [hbinom]
  have hpow4 : (S * 8 ^ B) ^ 4 ≤ (8 ^ e * 9 ^ B) ^ 4 := Nat.pow_le_pow_left h1 4
  have h94 : 9 ^ 4 ≤ 2 * 8 ^ 4 := by decide
  have h9B : (9 ^ 4) ^ B ≤ (2 * 8 ^ 4) ^ B := Nat.pow_le_pow_left h94 B
  have h84_pos : 0 < (8 ^ 4) ^ B := Nat.pos_of_ne_zero (by positivity)
  have hkey : S ^ 4 * (8 ^ 4) ^ B ≤ 2 ^ (12 * e + B) * (8 ^ 4) ^ B := by
    calc
      S ^ 4 * (8 ^ 4) ^ B = S ^ 4 * (8 ^ B) ^ 4 := by rw [← pow_mul, mul_comm 4 B, pow_mul]
      _ = (S * 8 ^ B) ^ 4 := (mul_pow S (8 ^ B) 4).symm
      _ ≤ (8 ^ e * 9 ^ B) ^ 4 := hpow4
      _ = (8 ^ e) ^ 4 * (9 ^ B) ^ 4 := mul_pow (8 ^ e) (9 ^ B) 4
      _ = 2 ^ (12 * e) * (9 ^ 4) ^ B := by
            have h8e : (8 ^ e) ^ 4 = 2 ^ (12 * e) := by
              calc
                (8 ^ e) ^ 4 = (2 ^ 3) ^ (e * 4) := by rw [← pow_mul]; norm_num
                _ = 2 ^ (3 * (e * 4)) := (pow_mul 2 3 (e * 4)).symm
                _ = 2 ^ (12 * e) := by ring_nf
            have h9e : (9 ^ B) ^ 4 = (9 ^ 4) ^ B := by
              rw [← pow_mul, mul_comm B 4, pow_mul]
            rw [h8e, h9e]
      _ ≤ 2 ^ (12 * e) * (2 * 8 ^ 4) ^ B := Nat.mul_le_mul_left _ h9B
      _ = 2 ^ (12 * e) * (2 ^ B * (8 ^ 4) ^ B) := by rw [mul_pow]
      _ = 2 ^ (12 * e + B) * (8 ^ 4) ^ B := by rw [← mul_assoc, ← pow_add]
  exact Nat.le_of_mul_le_mul_right hkey h84_pos

private lemma colliding_pairs_lower {n C : ℕ} (_hC : 0 < C) (bucket : Fin n → Fin C) :
    n * n ≤ C * (2 * ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => z.1 < z.2 ∧ bucket z.1 = bucket z.2)).card + n) := by
  let Coll := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun z => z.1 < z.2 ∧ bucket z.1 = bucket z.2)
  let EqPairs := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun z => bucket z.1 = bucket z.2)
  have hEq_card : EqPairs.card = 2 * Coll.card + n := by
    let Lt := EqPairs.filter (fun z => z.1 < z.2)
    let Gt := EqPairs.filter (fun z => z.2 < z.1)
    let Diag := EqPairs.filter (fun z => z.1 = z.2)
    have hLt_eq : Lt = Coll := by
      ext z
      simp only [Lt, EqPairs, Coll, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hGt_card : Gt.card = Coll.card := by
      rw [← hLt_eq]
      refine Finset.card_bij (fun z _ => (z.2, z.1)) ?_ ?_ ?_
      · intro z hz
        simp only [Gt, Lt, EqPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact ⟨hz.1.symm, hz.2⟩
      · intro z₁ _ z₂ _ h
        exact Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)
      · intro z hz
        simp only [Lt, EqPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        refine ⟨(z.2, z.1), ?_, rfl⟩
        simp only [Gt, EqPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hz.1.symm, hz.2⟩
    have hDiag_card : Diag.card = n := by
      have hbij : Diag.card = (Finset.univ : Finset (Fin n)).card := by
        refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro z₁ hz₁ z₂ hz₂ h
          simp only [Diag, Finset.mem_filter] at hz₁ hz₂
          exact Prod.ext h (hz₁.2.symm.trans (h.trans hz₂.2))
        · intro x _
          refine ⟨(x, x), ?_, rfl⟩
          simp [Diag, EqPairs]
      simpa using hbij
    have hd1 : Disjoint Lt Gt := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      simp only [Lt, Gt, Finset.mem_filter] at h1 h2
      exact lt_asymm h1.2 h2.2
    have hd2 : Disjoint (Lt ∪ Gt) Diag := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      simp only [Lt, Gt, Diag, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with h | h
      · exact ne_of_lt h.2 h2.2
      · exact ne_of_gt h.2 h2.2
    have hunion : (Lt ∪ Gt) ∪ Diag = EqPairs := by
      ext z
      simp only [Lt, Gt, Diag, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h
        rcases h with (h | h) | h <;> exact h.1
      · intro h
        rcases lt_trichotomy z.1 z.2 with hlt | heq | hgt
        · exact Or.inl (Or.inl ⟨h, hlt⟩)
        · exact Or.inr ⟨h, heq⟩
        · exact Or.inl (Or.inr ⟨h, hgt⟩)
    rw [← hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      hLt_eq, hGt_card, hDiag_card]
    omega
  have hsum_m : ∑ t : Fin C, ((Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)).card = n := by
    rw [← Finset.card_biUnion]
    · have huniv : Finset.univ.biUnion (fun t : Fin C =>
          (Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)) = Finset.univ := by
        ext x
        simp
      rw [huniv]
      simp
    · intro t₁ _ t₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hsum_sq :
      ∑ t : Fin C, ((Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)).card ^ 2 =
      EqPairs.card := by
    have h1 : ∀ t : Fin C,
        ((Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)).card ^ 2 =
        (EqPairs.filter (fun z => bucket z.1 = t)).card := by
      intro t
      let Ft := (Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)
      have hprod : Ft ×ˢ Ft = EqPairs.filter (fun z => bucket z.1 = t) := by
        ext z
        simp only [Ft, EqPairs, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨h1, h2⟩
          exact ⟨h1.trans h2.symm, h1⟩
        · intro ⟨h1, h2⟩
          exact ⟨h2, h1.symm.trans h2⟩
      rw [← hprod, Finset.card_product, sq]
    simp_rw [h1]
    rw [← Finset.card_biUnion]
    · congr 1
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun ⟨_, hz, _⟩ => hz, fun hz => ⟨bucket z.1, hz, rfl⟩⟩
    · intro t₁ _ t₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro z h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hcs_int :
      ((∑ t : Fin C, ((Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)).card : ℕ) : ℤ) ^ 2 ≤
      (C : ℤ) * ((∑ t : Fin C, ((Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)).card ^ 2 : ℕ) : ℤ) := by
    let f : Fin C → ℤ := fun t => (((Finset.univ : Finset (Fin n)).filter (fun x => bucket x = t)).card : ℤ)
    have hnn : (0 : ℤ) ≤ ∑ t₁ : Fin C, ∑ t₂ : Fin C, (f t₁ - f t₂) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp :
        ∑ t₁ : Fin C, ∑ t₂ : Fin C, (f t₁ - f t₂) ^ 2 =
        2 * ((C : ℤ) * (∑ t : Fin C, f t ^ 2) - (∑ t : Fin C, f t) ^ 2) := by
      have hterm : ∀ t₁ t₂ : Fin C, (f t₁ - f t₂) ^ 2 = f t₁ ^ 2 + f t₂ ^ 2 - 2 * (f t₁ * f t₂) :=
        fun t₁ t₂ => by ring
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hle : (∑ t : Fin C, f t) ^ 2 ≤ (C : ℤ) * ∑ t : Fin C, f t ^ 2 := by linarith
    simpa [f] using hle
  rw [hsum_m, hsum_sq, hEq_card] at hcs_int
  have hnat : n ^ 2 ≤ C * (2 * Coll.card + n) := by exact_mod_cast hcs_int
  simpa only [sq] using hnat

private lemma bad_tables_for_candidate {n C : ℕ}
    (π : Equiv.Perm (Fin n)) (rowFlip colFlip : Fin n → Bool) (bucket : Fin n → Fin C) (e : ℕ) :
    let Coll := (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => z.1 < z.2 ∧ bucket z.1 = bucket z.2)
    let target : Fin n × Fin n → Bool := fun z =>
      Bool.xor (Bool.xor (rowFlip z.1) (colFlip (π z.2)))
        (Bool.xor (rowFlip z.2) (colFlip (π z.1)))
    ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
      (Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z)).card ≤ e)).card ≤
    2 ^ (n * n - Coll.card) * ∑ j ∈ Finset.range (e + 1), Coll.card.choose j := by
  classical
  intro Coll target
  let GoodSet := (Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
    (Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z)).card ≤ e)
  let Subsets := Coll.powerset.filter (fun S => S.card ≤ e)
  let LeftCells : Finset (Fin n × Fin n) := Coll.image (fun z => (z.1, π z.2))
  have hLeft_card : LeftCells.card = Coll.card := by
    refine Finset.card_image_of_injective Coll ?_
    intro z₁ z₂ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (π.injective h.2)
  have hRight_not_Left : ∀ z ∈ Coll, (z.2, π z.1) ∉ LeftCells := by
    intro z hz hmem
    rcases Finset.mem_image.mp hmem with ⟨w, hw, hEq⟩
    have hz_lt : z.1 < z.2 := (Finset.mem_filter.mp hz).2.1
    have hw_lt : w.1 < w.2 := (Finset.mem_filter.mp hw).2.1
    have h1 : w.1 = z.2 := congr_arg Prod.fst hEq
    have h2 : w.2 = z.1 := π.injective (congr_arg Prod.snd hEq)
    rw [h1, h2] at hw_lt
    exact lt_asymm hz_lt hw_lt
  have hfiber_le : ∀ S ∈ Subsets,
      ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
        Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z) = S)).card ≤
      2 ^ (n * n - Coll.card) := by
    intro S _
    let Fib := (Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
      Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z) = S)
    let restr : (Fin n → Fin n → Bool) → ((LeftCellsᶜ : Finset (Fin n × Fin n)) → Bool) :=
      fun G c => G c.1.1 c.1.2
    have hinj : Set.InjOn restr Fib := by
      intro G₁ hG₁ G₂ hG₂ hEq
      have hS₁ := (Finset.mem_filter.mp hG₁).2
      have hS₂ := (Finset.mem_filter.mp hG₂).2
      ext x y
      by_cases hxy : (x, y) ∈ LeftCells
      · rcases Finset.mem_image.mp hxy with ⟨z, hz, hzEq⟩
        have hx : z.1 = x := congr_arg Prod.fst hzEq
        have hy : π z.2 = y := congr_arg Prod.snd hzEq
        rw [← hx, ← hy]
        have hr_mem : (z.2, π z.1) ∈ (LeftCellsᶜ : Finset (Fin n × Fin n)) :=
          Finset.mem_compl.mpr (hRight_not_Left z hz)
        have hG_right : G₁ z.2 (π z.1) = G₂ z.2 (π z.1) :=
          congr_fun hEq ⟨(z.2, π z.1), hr_mem⟩
        have hmem_iff :
            (Bool.xor (G₁ z.1 (π z.2)) (G₁ z.2 (π z.1)) ≠ target z) ↔
            (Bool.xor (G₂ z.1 (π z.2)) (G₂ z.2 (π z.1)) ≠ target z) := by
          have h1 : z ∈ Coll.filter (fun w => Bool.xor (G₁ w.1 (π w.2)) (G₁ w.2 (π w.1)) ≠ target w) ↔
              z ∈ S := by rw [hS₁]
          have h2 : z ∈ Coll.filter (fun w => Bool.xor (G₂ w.1 (π w.2)) (G₂ w.2 (π w.1)) ≠ target w) ↔
              z ∈ S := by rw [hS₂]
          have h12 := h1.trans h2.symm
          simp only [Finset.mem_filter, hz, true_and] at h12
          exact h12
        rw [hG_right] at hmem_iff
        cases a1 : G₁ z.1 (π z.2) <;> cases a2 : G₂ z.1 (π z.2) <;>
          cases b : G₂ z.2 (π z.1) <;> cases t : target z <;> simp_all
      · exact congr_fun hEq ⟨(x, y), Finset.mem_compl.mpr hxy⟩
    have hcard_le : Fib.card ≤ (Finset.univ : Finset ((LeftCellsᶜ : Finset (Fin n × Fin n)) → Bool)).card :=
      Finset.card_le_card_of_injOn restr (fun _ _ => Finset.mem_univ _) hinj
    have hcard_rhs :
        (Finset.univ : Finset ((LeftCellsᶜ : Finset (Fin n × Fin n)) → Bool)).card =
        2 ^ (n * n - Coll.card) := by
      simp [hLeft_card]
    rwa [hcard_rhs] at hcard_le
  have hSub_card : Subsets.card = ∑ j ∈ Finset.range (e + 1), Coll.card.choose j := by
    have hunion :
        (Finset.range (e + 1)).biUnion (fun j => Coll.powersetCard j) = Subsets := by
      ext S
      simp only [Subsets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
        Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨j, hj, hsub, hcard⟩
        exact ⟨hsub, by omega⟩
      · rintro ⟨hsub, hle⟩
        exact ⟨S.card, by omega, hsub, rfl⟩
    rw [← hunion, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun j _ => Finset.card_powersetCard j Coll
    · intro j₁ _ j₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro S h1 h2
      simp only [Finset.mem_powersetCard] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hcover : GoodSet ⊆ Subsets.biUnion (fun S =>
      (Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
        Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z) = S)) := by
    intro G hG
    simp only [GoodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hG
    refine Finset.mem_biUnion.mpr ⟨Coll.filter (fun z =>
      Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z), ?_, ?_⟩
    · simp only [Subsets, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.filter_subset _ _, hG⟩
    · simp
  calc
    GoodSet.card ≤
        (Subsets.biUnion (fun S =>
          (Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
            Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z) = S))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ S ∈ Subsets,
          ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
            Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z) = S)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ Subsets, 2 ^ (n * n - Coll.card) := Finset.sum_le_sum hfiber_le
    _ = Subsets.card * 2 ^ (n * n - Coll.card) := by simp
    _ = 2 ^ (n * n - Coll.card) * ∑ j ∈ Finset.range (e + 1), Coll.card.choose j := by
      rw [hSub_card, mul_comm]

private lemma loss_ge_bad_pairs {n q : ℕ} (G : Fin n → Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (rowFlip colFlip : Fin n → Bool)
    (R C : Fin q → Finset (Fin n)) (out : Finset (Fin n) → (Fin q → Bool) → Bool) :
    let bucket : Fin n → (Fin q → Fin 3) := fun x j =>
      toTern (decide (x ∈ R j)) (decide (π x ∈ C j))
    let Coll := (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => z.1 < z.2 ∧ bucket z.1 = bucket z.2)
    let target : Fin n × Fin n → Bool := fun z =>
      Bool.xor (Bool.xor (rowFlip z.1) (colFlip (π z.2)))
        (Bool.xor (rowFlip z.2) (colFlip (π z.1)))
    (Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z)).card ≤
    lossFn G q π rowFlip colFlip R C out := by
  intro bucket Coll target
  let Bad := Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z)
  let Err := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
    out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
      Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))
  have hex_err : ∀ z ∈ Bad, z ∈ Err ∨ (z.2, z.1) ∈ Err := by
    intro z hz
    simp only [Bad, Coll, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hsig_eq :
        (fun j : Fin q => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) =
        (fun j : Fin q => decide (z.2 ∈ R j ∨ π z.1 ∈ C j)) := by
      funext j
      have hbj := congr_fun hz.1.2 j
      have hor := same_tern_same_or _ _ _ _ hbj
      by_cases h1 : z.1 ∈ R j <;> by_cases h2 : π z.2 ∈ C j <;>
        by_cases h3 : z.2 ∈ R j <;> by_cases h4 : π z.1 ∈ C j <;>
        simp_all
    have hset_eq : ({z.1, z.2} : Finset (Fin n)) = ({z.2, z.1} : Finset (Fin n)) :=
      Finset.pair_comm z.1 z.2
    have hout_eq :
        out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) =
        out {z.2, z.1} (fun j => decide (z.2 ∈ R j ∨ π z.1 ∈ C j)) := by
      rw [hset_eq, hsig_eq]
    by_contra hneither
    push Not at hneither
    simp only [Err, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hneither
    rw [hout_eq] at hneither
    have hT : Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))) =
        Bool.xor (G z.2 (π z.1)) (Bool.xor (rowFlip z.2) (colFlip (π z.1))) :=
      hneither.1.symm.trans hneither.2
    have hbad := hz.2
    simp only [target] at hbad
    cases a1 : G z.1 (π z.2) <;> cases a2 : G z.2 (π z.1) <;>
      cases r1 : rowFlip z.1 <;> cases c1 : colFlip (π z.2) <;>
      cases r2 : rowFlip z.2 <;> cases c2 : colFlip (π z.1) <;> simp_all
  let pick : Fin n × Fin n → Fin n × Fin n := fun z => if z ∈ Err then z else (z.2, z.1)
  refine Finset.card_le_card_of_injOn pick ?_ ?_
  · intro z hz
    simp only [pick]
    split_ifs with h1
    · exact h1
    · exact (hex_err z hz).resolve_left h1
  · intro z₁ hz₁ z₂ hz₂ hEq
    have hlt1 : z₁.1 < z₁.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz₁).1).2.1
    have hlt2 : z₂.1 < z₂.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz₂).1).2.1
    simp only [pick] at hEq
    split_ifs at hEq with h1 h2
    · exact hEq
    · have ha : z₁.1 = z₂.2 := congr_arg Prod.fst hEq
      have hb : z₁.2 = z₂.1 := congr_arg Prod.snd hEq
      omega
    · have ha : z₁.2 = z₂.1 := congr_arg Prod.fst hEq
      have hb : z₁.1 = z₂.2 := congr_arg Prod.snd hEq
      omega
    · exact Prod.ext (congr_arg Prod.snd hEq) (congr_arg Prod.fst hEq)

private lemma pad_loss_eq {n q q0 : ℕ} (hq : q ≤ q0)
    (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)) (rowFlip colFlip : Fin n → Bool)
    (R C : Fin q → Finset (Fin n)) (out : Finset (Fin n) → (Fin q → Bool) → Bool) :
    ∃ (R' C' : Fin q0 → Finset (Fin n)) (out' : Finset (Fin n) → (Fin q0 → Bool) → Bool),
      lossFn G q0 π rowFlip colFlip R' C' out' = lossFn G q π rowFlip colFlip R C out := by
  let R' : Fin q0 → Finset (Fin n) := fun j => if hj : j.val < q then R ⟨j.val, hj⟩ else ∅
  let C' : Fin q0 → Finset (Fin n) := fun j => if hj : j.val < q then C ⟨j.val, hj⟩ else ∅
  let out' : Finset (Fin n) → (Fin q0 → Bool) → Bool :=
    fun S s => out S (fun j => s (Fin.castLE hq j))
  refine ⟨R', C', out', ?_⟩
  simp only [lossFn]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hsig :
      (fun j : Fin q => decide (z.1 ∈ R' (Fin.castLE hq j) ∨ π z.2 ∈ C' (Fin.castLE hq j))) =
      (fun j : Fin q => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) := by
    funext j
    simp only [R', C', Fin.val_castLE, j.isLt, ↓reduceDIte]
  simp only [out', hsig]

private lemma eight_mul_le_two_pow : ∀ k : ℕ, 16 ≤ k → 8 * k ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h16 : k < 16
    · have : k = 15 := by omega
      subst this
      decide
    · have hih := ih (by omega)
      have hk16 : 16 ≤ k := by omega
      rw [pow_succ]
      omega

private lemma lower_bound_counting {k : ℕ} (hk : 16 ≤ k) :
    let n := 2 ^ k
    ∃ G : Fin n → Fin n → Bool, ∀ q : ℕ, 8 * k * 3 ^ q ≤ n →
      ∀ (π : Equiv.Perm (Fin n)) (rowFlip colFlip : Fin n → Bool)
        (R C : Fin q → Finset (Fin n)) (out : Finset (Fin n) → (Fin q → Bool) → Bool),
        k * n < 4 * lossFn G q π rowFlip colFlip R C out := by
  classical
  intro n
  have h0_adm : 8 * k * 3 ^ 0 ≤ n := by
    simpa [n] using eight_mul_le_two_pow k hk
  have hbound_q : ∀ q : ℕ, 8 * k * 3 ^ q ≤ n → q ≤ n := by
    intro q hq
    have hlt : q < 3 ^ q := Nat.lt_pow_self (by omega)
    have h8k : 1 ≤ 8 * k := by omega
    have : 3 ^ q ≤ 8 * k * 3 ^ q := Nat.le_mul_of_pos_left (3 ^ q) h8k
    omega
  let admQ : Finset ℕ := (Finset.range (n + 1)).filter (fun q => 8 * k * 3 ^ q ≤ n)
  have hadmQ_ne : admQ.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by positivity), h0_adm⟩⟩
  let q0 : ℕ := admQ.max' hadmQ_ne
  have hq0_adm : 8 * k * 3 ^ q0 ≤ n := (Finset.mem_filter.mp (Finset.max'_mem admQ hadmQ_ne)).2
  have hq_le_q0 : ∀ q : ℕ, 8 * k * 3 ^ q ≤ n → q ≤ q0 := by
    intro q hq
    exact Finset.le_max' admQ q
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound_q q hq)), hq⟩)
  let Ccnt := 3 ^ q0
  have hCpos : 0 < Ccnt := Nat.pos_of_ne_zero (by positivity)
  let e := k * n / 4
  let Cand := Equiv.Perm (Fin n) × (Fin n → Bool) × (Fin n → Bool) × (Fin n → Fin Ccnt)
  let badOf : Cand → Finset (Fin n → Fin n → Bool) := fun c =>
    let π := c.1
    let rf := c.2.1
    let cf := c.2.2.1
    let bkt := c.2.2.2
    let Coll := (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => z.1 < z.2 ∧ bkt z.1 = bkt z.2)
    let target : Fin n × Fin n → Bool := fun z =>
      Bool.xor (Bool.xor (rf z.1) (cf (π z.2))) (Bool.xor (rf z.2) (cf (π z.1)))
    (Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
      (Coll.filter (fun z => Bool.xor (G z.1 (π z.2)) (G z.2 (π z.1)) ≠ target z)).card ≤ e)
  have hcand_card : Fintype.card Cand ≤ 2 ^ ((2 * k + 1) * n) := by
    have hperm : Fintype.card (Equiv.Perm (Fin n)) ≤ 2 ^ (k * n) := by
      have h1 : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
        simp [Fintype.card_perm]
      have h2 : Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
      have h3 : n ^ n = 2 ^ (k * n) := by
        simp only [n, ← pow_mul]
      rw [h1, ← h3]
      exact h2
    have hbkt : Fintype.card (Fin n → Fin Ccnt) ≤ 2 ^ ((k - 1) * n) := by
      have h1 : Fintype.card (Fin n → Fin Ccnt) = Ccnt ^ n := by simp
      have hC_le : Ccnt ≤ 2 ^ (k - 1) := by
        have h2k : 2 * 2 ^ (k - 1) = 2 ^ k := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
        have hq0' : 8 * k * Ccnt ≤ 2 ^ k := hq0_adm
        have h2le : 2 * Ccnt ≤ 8 * k * Ccnt := Nat.mul_le_mul_right Ccnt (by omega)
        omega
      rw [h1]
      calc
        Ccnt ^ n ≤ (2 ^ (k - 1)) ^ n := Nat.pow_le_pow_left hC_le n
        _ = 2 ^ ((k - 1) * n) := (pow_mul 2 (k - 1) n).symm
    have htot :
        Fintype.card Cand =
        Fintype.card (Equiv.Perm (Fin n)) * (2 ^ n * (2 ^ n * Fintype.card (Fin n → Fin Ccnt))) := by
      simp [Cand, Fintype.card_prod]
    rw [htot]
    calc
      Fintype.card (Equiv.Perm (Fin n)) * (2 ^ n * (2 ^ n * Fintype.card (Fin n → Fin Ccnt)))
          ≤ 2 ^ (k * n) * (2 ^ n * (2 ^ n * 2 ^ ((k - 1) * n))) := by
            refine Nat.mul_le_mul hperm ?_
            refine Nat.mul_le_mul_left _ ?_
            exact Nat.mul_le_mul_left _ hbkt
      _ = 2 ^ (k * n + n + n + (k - 1) * n) := by
            simp only [← pow_add, add_assoc]
      _ = 2 ^ ((2 * k + 1) * n) := by
            congr 1
            have hkn : (k - 1) * n + n = k * n := by
              rw [← add_one_mul, Nat.sub_add_cancel (by omega)]
            linarith
  have hsingle_bound : ∀ c : Cand, (badOf c).card ^ 4 * (2 ^ ((2 * k + 1) * n)) ^ 4 <
      (2 ^ (n * n)) ^ 4 := by
    intro c
    let π := c.1
    let rf := c.2.1
    let cf := c.2.2.1
    let bkt := c.2.2.2
    let Coll := (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => z.1 < z.2 ∧ bkt z.1 = bkt z.2)
    let B := Coll.card
    have hB_le : B ≤ n * n := by
      calc
        B ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
        _ = n * n := by simp
    have h2B : (8 * k - 1) * n ≤ 2 * B := by
      have hcs := colliding_pairs_lower hCpos bkt
      have h8kn : 8 * k * Ccnt * n ≤ n * n := Nat.mul_le_mul_right n hq0_adm
      have hC_ge : Ccnt * (8 * k * n) ≤ Ccnt * (2 * B + n) := by
        calc
          Ccnt * (8 * k * n) = 8 * k * Ccnt * n := by ring
          _ ≤ n * n := h8kn
          _ ≤ Ccnt * (2 * B + n) := hcs
      have hge := Nat.le_of_mul_le_mul_left hC_ge hCpos
      have h8k : (8 * k - 1) * n + n = 8 * k * n := by
        rw [← add_one_mul, Nat.sub_add_cancel (by omega)]
      omega
    have hbad_le := bad_tables_for_candidate π rf cf bkt e
    have hS4 := binom_tail_fourth_bound B e
    have hexp_lt : 4 * ((2 * k + 1) * n) + (12 * e + B) < 4 * B := by
      have h4e : 4 * e ≤ k * n := Nat.mul_div_le (k * n) 4
      have h12e : 12 * e ≤ 3 * k * n := by nlinarith
      have hn_pos : 0 < n := by positivity
      have h2_lt : 2 * (4 * ((2 * k + 1) * n) + 12 * e) < 2 * (3 * B) := by
        have h1 : 2 * (4 * ((2 * k + 1) * n) + 12 * e) ≤ (22 * k + 8) * n := by linarith
        have h2 : (24 * k - 3) * n ≤ 3 * (2 * B) := by
          have hsub : 3 * (8 * k - 1) = 24 * k - 3 := by omega
          calc
            (24 * k - 3) * n = 3 * ((8 * k - 1) * n) := by rw [← mul_assoc, hsub]
            _ ≤ 3 * (2 * B) := Nat.mul_le_mul_left 3 h2B
        have h3 : 22 * k + 8 < 24 * k - 3 := by omega
        have h4 : (22 * k + 8) * n < (24 * k - 3) * n := Nat.mul_lt_mul_of_pos_right h3 hn_pos
        omega
      omega
    have hpow_lt :
        2 ^ (4 * (n * n - B) + (12 * e + B) + 4 * ((2 * k + 1) * n)) <
        2 ^ (4 * (n * n)) := by
      refine Nat.pow_lt_pow_right (by omega) ?_
      omega
    have hbad4 : (badOf c).card ^ 4 ≤ 2 ^ (4 * (n * n - B) + (12 * e + B)) := by
      calc
        (badOf c).card ^ 4
            ≤ (2 ^ (n * n - B) * ∑ j ∈ Finset.range (e + 1), B.choose j) ^ 4 :=
              Nat.pow_le_pow_left hbad_le 4
        _ = (2 ^ (n * n - B)) ^ 4 * (∑ j ∈ Finset.range (e + 1), B.choose j) ^ 4 :=
              mul_pow _ _ 4
        _ ≤ (2 ^ (n * n - B)) ^ 4 * 2 ^ (12 * e + B) := Nat.mul_le_mul_left _ hS4
        _ = 2 ^ (4 * (n * n - B) + (12 * e + B)) := by
              rw [← pow_mul, mul_comm (n * n - B) 4, ← pow_add]
    calc
      (badOf c).card ^ 4 * (2 ^ ((2 * k + 1) * n)) ^ 4
          ≤ 2 ^ (4 * (n * n - B) + (12 * e + B)) * (2 ^ ((2 * k + 1) * n)) ^ 4 :=
            Nat.mul_le_mul_right _ hbad4
      _ = 2 ^ (4 * (n * n - B) + (12 * e + B) + 4 * ((2 * k + 1) * n)) := by
            rw [← pow_mul, mul_comm ((2 * k + 1) * n) 4, ← pow_add]
      _ < 2 ^ (4 * (n * n)) := hpow_lt
      _ = (2 ^ (n * n)) ^ 4 := by rw [mul_comm 4 (n * n), pow_mul]
  have hsingle_lt : ∀ c : Cand, (badOf c).card * 2 ^ ((2 * k + 1) * n) < 2 ^ (n * n) := by
    intro c
    by_contra hge
    push Not at hge
    have h4 := Nat.pow_le_pow_left hge 4
    rw [mul_pow] at h4
    exact not_le_of_gt (hsingle_bound c) h4
  have hall_lt :
      ((Finset.univ : Finset Cand).biUnion badOf).card <
      (Finset.univ : Finset (Fin n → Fin n → Bool)).card := by
    have huniv_card : (Finset.univ : Finset (Fin n → Fin n → Bool)).card = 2 ^ (n * n) := by
      simp [← pow_mul]
    rw [huniv_card]
    by_cases hCne : (Finset.univ : Finset Cand).Nonempty
    · have hsum_lt :
          ∑ c : Cand, (badOf c).card * 2 ^ ((2 * k + 1) * n) <
          ∑ _c : Cand, 2 ^ (n * n) :=
        Finset.sum_lt_sum_of_nonempty hCne (fun c _ => hsingle_lt c)
      rw [← Finset.sum_mul] at hsum_lt
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum_lt
      have hle1 : ((Finset.univ : Finset Cand).biUnion badOf).card * 2 ^ ((2 * k + 1) * n) ≤
          (∑ c : Cand, (badOf c).card) * 2 ^ ((2 * k + 1) * n) :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
      have hle2 : Fintype.card Cand * 2 ^ (n * n) ≤ 2 ^ ((2 * k + 1) * n) * 2 ^ (n * n) :=
        Nat.mul_le_mul_right _ hcand_card
      have hmul_lt :
          ((Finset.univ : Finset Cand).biUnion badOf).card * 2 ^ ((2 * k + 1) * n) <
          2 ^ (n * n) * 2 ^ ((2 * k + 1) * n) := by
        rw [mul_comm (2 ^ (n * n)) (2 ^ ((2 * k + 1) * n))]
        omega
      exact Nat.lt_of_mul_lt_mul_right hmul_lt
    · have hemp : (Finset.univ : Finset Cand) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCne
      rw [hemp]
      simp
  have hexG : ∃ G : Fin n → Fin n → Bool, G ∉ (Finset.univ : Finset Cand).biUnion badOf := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin n → Fin n → Bool)) ⊆
        (Finset.univ : Finset Cand).biUnion badOf := fun G _ => hall G
    exact not_le_of_gt hall_lt (Finset.card_le_card hsub)
  rcases hexG with ⟨G, hG_good⟩
  refine ⟨G, ?_⟩
  intro q hq π rowFlip colFlip R C out
  rcases pad_loss_eq (hq_le_q0 q hq) G π rowFlip colFlip R C out with ⟨R', C', out', hpad⟩
  rw [← hpad]
  have hcard_tern : Fintype.card (Fin q0 → Fin 3) = Ccnt := by simp [Ccnt]
  let eTern : (Fin q0 → Fin 3) ≃ Fin Ccnt :=
    (Fintype.equivFin (Fin q0 → Fin 3)).trans (finCongr hcard_tern)
  let bkt0 : Fin n → (Fin q0 → Fin 3) := fun x j => toTern (decide (x ∈ R' j)) (decide (π x ∈ C' j))
  let bkt : Fin n → Fin Ccnt := fun x => eTern (bkt0 x)
  have hnot_bad : G ∉ badOf (π, rowFlip, colFlip, bkt) := by
    intro hmem
    exact hG_good (Finset.mem_biUnion.mpr ⟨(π, rowFlip, colFlip, bkt), Finset.mem_univ _, hmem⟩)
  simp only [badOf, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot_bad
  have hcoll_eq :
      (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 < z.2 ∧ bkt z.1 = bkt z.2) =
      (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 < z.2 ∧ bkt0 z.1 = bkt0 z.2) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bkt, EmbeddingLike.apply_eq_iff_eq]
  rw [hcoll_eq] at hnot_bad
  have hge := loss_ge_bad_pairs G π rowFlip colFlip R' C' out'
  have hlt_loss : e < lossFn G q0 π rowFlip colFlip R' C' out' := lt_of_lt_of_le hnot_bad hge
  omega

end PEqualNP.Outside.L_meta_25713_aux

open PEqualNP.Outside.L_meta_25713_aux in
theorem PEqualNP.Outside.L_meta_25713 : (∀ k : ℕ, 16 ≤ k →
  let n := 2^k
  let I := Fin n
  let Table := I → I → Bool
  let loss := fun (G : Table) (q : ℕ) (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
      (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card
  (∀ (G : Table) (q : ℕ), 16*n ≤ k*3^q →
    ∃ (π : Equiv.Perm I) (R C : Fin q → Finset I)
      (out : Finset I → (Fin q → Bool) → Bool),
      loss G q π (fun _row => false) (fun _col => false) R C out = 0) ∧
  (∃ G : Table, ∀ q : ℕ, 8*k*3^q ≤ n →
    ∀ (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
      (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool),
      k*n < 4*loss G q π rowFlip colFlip R C out)) := by
  intro k hk n I Table loss
  exact ⟨fun G q hq => upper_bound_packing hk hq G, lower_bound_counting hk⟩

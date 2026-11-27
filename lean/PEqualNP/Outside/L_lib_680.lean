import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_680_aux

open Classical

abbrev B := ZMod 2
abbrev UType (h : ℕ) := Fin h → B
abbrev VType (m : ℕ) := Fin m → B

lemma z2_cases (r : B) : r = 0 ∨ r = 1 := by
  fin_cases r
  · left; rfl
  · right; rfl

lemma z2_add_self (r : B) : r + r = 0 := by
  fin_cases r <;> decide

lemma z2_val_lt (r : B) : r.val < 2 := ZMod.val_lt r

lemma z2_val_cast (n : ℕ) : ((n % 2 : ℕ) : B).val = n % 2 := by
  rw [ZMod.val_natCast, Nat.mod_mod]

lemma lin_eval_zero_right {h m : ℕ} (L : (UType h × VType m) →ₗ[B] B) (u : UType h) (x : VType m) :
    L (u, x) = L (u, 0) + L (0, x) := by
  have hsplit : (u, x) = (u, (0 : VType m)) + ((0 : UType h), x) := by
    ext <;> simp
  rw [hsplit, map_add]

lemma extract_greedy_basis {h q : ℕ} (α : Fin q → (UType h →ₗ[B] B)) :
    ∃ J : Finset (Fin q),
      Function.Surjective (fun u : UType h => fun j : ↥J => α j.1 u) ∧
      (∀ r : Fin q, ∀ w : UType h, (∀ j ∈ J, α j w = 0) → α r w = 0) := by
  have hstep : ∀ k : ℕ, k ≤ q →
      ∃ J : Finset (Fin q),
        Function.Surjective (fun u : UType h => fun j : ↥J => α j.1 u) ∧
        (∀ r : Fin q, r.val < k → ∀ w : UType h, (∀ j ∈ J, α j w = 0) → α r w = 0) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, ?_, ?_⟩
      · intro y
        refine ⟨0, ?_⟩
        funext j
        exact absurd j.2 (Finset.notMem_empty _)
      · intro r hr; omega
    | succ k ih =>
      intro hk
      obtain ⟨J, hJsurj, hJspan⟩ := ih (by omega)
      let r0 : Fin q := ⟨k, hk⟩
      by_cases hex : ∃ w : UType h, (∀ j ∈ J, α j w = 0) ∧ α r0 w ≠ 0
      · obtain ⟨w0, hw0J, hw0r⟩ := hex
        have hw0_one : α r0 w0 = 1 := by
          rcases z2_cases (α r0 w0) with h0 | h1
          · exact absurd h0 hw0r
          · exact h1
        have hr0_not : r0 ∉ J := by
          intro hmem
          exact hw0r (hw0J r0 hmem)
        refine ⟨insert r0 J, ?_, ?_⟩
        · intro y
          obtain ⟨u1, hu1⟩ := hJsurj (fun j : ↥J => y ⟨j.1, Finset.mem_insert_of_mem j.2⟩)
          let c : B := y ⟨r0, Finset.mem_insert_self r0 J⟩ + α r0 u1
          refine ⟨u1 + c • w0, ?_⟩
          funext j
          rcases Finset.mem_insert.mp j.2 with hjEq | hjJ
          · have hjSub : j = ⟨r0, Finset.mem_insert_self r0 J⟩ := Subtype.ext hjEq
            rw [hjSub]
            dsimp only
            rw [map_add, map_smul, smul_eq_mul, hw0_one, mul_one]
            simp only [c]
            have hadd : α r0 u1 + (y ⟨r0, Finset.mem_insert_self r0 J⟩ + α r0 u1) =
                y ⟨r0, Finset.mem_insert_self r0 J⟩ + (α r0 u1 + α r0 u1) := by ring
            rw [hadd, z2_add_self, add_zero]
          · have h1 := congrFun hu1 ⟨j.1, hjJ⟩
            dsimp only at h1 ⊢
            rw [map_add, map_smul, smul_eq_mul, hw0J j.1 hjJ, mul_zero, add_zero]
            exact h1
        · intro r hr w hw
          by_cases hlt : r.val < k
          · exact hJspan r hlt w (fun j hj => hw j (Finset.mem_insert_of_mem hj))
          · have hrEq : r = r0 := Fin.ext (by dsimp only [r0]; omega)
            rw [hrEq]
            exact hw r0 (Finset.mem_insert_self r0 J)
      · push Not at hex
        refine ⟨J, hJsurj, ?_⟩
        intro r hr w hw
        by_cases hlt : r.val < k
        · exact hJspan r hlt w hw
        · have hrEq : r = r0 := Fin.ext (by dsimp only [r0]; omega)
          rw [hrEq]
          exact hex w hw
  obtain ⟨J, hJsurj, hJspan⟩ := hstep q (le_refl q)
  exact ⟨J, hJsurj, fun r => hJspan r r.isLt⟩

lemma kernel_card_of_surj {h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : UType h →ₗ[B] (ι → B)) (hsurj : Function.Surjective f) :
    Fintype.card ι ≤ h ∧
    (Finset.univ.filter (fun u : UType h => f u = 0)).card = 2 ^ (h - Fintype.card ι) := by
  let K := Finset.univ.filter (fun u : UType h => f u = 0)
  have hfiber : ∀ y : ι → B, (Finset.univ.filter (fun u : UType h => f u = y)).card = K.card := by
    intro y
    obtain ⟨u0, hu0⟩ := hsurj y
    symm
    refine Finset.card_bij (fun w _ => w + u0) ?_ ?_ ?_
    · intro w hw
      have hw0 : f w = 0 := (Finset.mem_filter.mp hw).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [map_add, hw0, hu0, zero_add]
    · intro w1 _ w2 _ hEq
      exact add_right_cancel hEq
    · intro u hu
      have huy : f u = y := (Finset.mem_filter.mp hu).2
      refine ⟨u + u0, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, huy, hu0]
        funext i
        exact z2_add_self (y i)
      · funext i
        simp only [Pi.add_apply]
        rw [add_assoc, z2_add_self, add_zero]
  have hpart : Fintype.card (UType h) = Fintype.card (ι → B) * K.card := by
    have h1 : (Finset.univ : Finset (UType h)).card =
        ∑ y : ι → B, (Finset.univ.filter (fun u : UType h => f u = y)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext u; simp
      · intro y1 _ y2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [Finset.card_univ] at h1
    rw [h1, Finset.sum_congr rfl (fun y _ => hfiber y), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hUcard : Fintype.card (UType h) = 2 ^ h := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hYcard : Fintype.card (ι → B) = 2 ^ (Fintype.card ι) := by
    rw [Fintype.card_fun, ZMod.card]
  rw [hUcard, hYcard] at hpart
  have hKpos : 0 < K.card := by
    apply Finset.card_pos.mpr
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, map_zero f⟩⟩
  have hpow_le : 2 ^ (Fintype.card ι) ≤ 2 ^ h := by
    calc
      2 ^ (Fintype.card ι) = 2 ^ (Fintype.card ι) * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ (Fintype.card ι) * K.card := Nat.mul_le_mul_left _ hKpos
      _ = 2 ^ h := hpart.symm
  have hle : Fintype.card ι ≤ h := by
    by_contra hgt
    have hlt : h < Fintype.card ι := by omega
    have hltp : 2 ^ h < 2 ^ (Fintype.card ι) := Nat.pow_lt_pow_right (by omega) hlt
    omega
  refine ⟨hle, ?_⟩
  have hpow_eq : 2 ^ (Fintype.card ι) * 2 ^ (h - Fintype.card ι) = 2 ^ h := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hle]
  have hpos : 0 < 2 ^ (Fintype.card ι) := Nat.pow_pos (by omega)
  exact Nat.eq_of_mul_eq_mul_left hpos (hpart.symm.trans hpow_eq.symm)

lemma answers_eq_iff_path {h m q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → B) → ((UType h × VType m) →ₗ[B] B))
    (answers : UType h → VType m → Fin q → B)
    (hrec : ∀ (u : UType h) (x : VType m) (j : Fin q),
      answers u x j = ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x))
    (u : UType h) (x : VType m) (p : Fin q → B) :
    answers u x = p ↔ ∀ j : Fin q, ask j (fun i => p ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x) = p j := by
  constructor
  · rintro rfl j
    exact (hrec u x j).symm
  · intro hall
    funext j
    have hstrong : ∀ k : ℕ, (hk : k < q) → answers u x ⟨k, hk⟩ = p ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk
        rw [hrec u x ⟨k, hk⟩]
        have hpref : (fun i : Fin k => answers u x ⟨i.val, Nat.lt_trans i.isLt hk⟩) =
            (fun i : Fin k => p ⟨i.val, Nat.lt_trans i.isLt hk⟩) := by
          funext i
          exact ih i.val i.isLt (Nat.lt_trans i.isLt hk)
        rw [hpref]
        exact hall ⟨k, hk⟩
    exact hstrong j.val j.isLt

lemma alpha_decomp_lemma {h q : ℕ}
    (α : Fin q → (UType h →ₗ[B] B))
    (J : Finset (Fin q))
    (hJspan : ∀ (r : Fin q) (w : UType h), (∀ j ∈ J, α j w = 0) → α r w = 0)
    (uBasis : ↥J → UType h)
    (huBasis : ∀ (j j' : ↥J), α j'.1 (uBasis j) = if j' = j then 1 else 0)
    (r : Fin q) (u : UType h) :
    α r u = ∑ j : ↥J, α r (uBasis j) * α j.1 u := by
  let w : UType h := u + ∑ j : ↥J, (α j.1 u) • uBasis j
  have hwJ : ∀ j ∈ J, α j w = 0 := by
    intro j hj
    have h1 : α j w = α j u + ∑ j' : ↥J, α j'.1 u * α j (uBasis j') := by
      dsimp only [w]
      rw [map_add, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j' _
      rw [map_smul, smul_eq_mul]
    rw [h1]
    have h2 : ∑ j' : ↥J, α j'.1 u * α j (uBasis j') = α j u := by
      have hterm : ∀ j' : ↥J, α j'.1 u * α j (uBasis j') =
          if j' = ⟨j, hj⟩ then α j'.1 u else 0 := by
        intro j'
        have hv := huBasis j' ⟨j, hj⟩
        by_cases heq : j' = ⟨j, hj⟩
        · subst heq; simp at hv; simp [hv]
        · have hne : (⟨j, hj⟩ : ↥J) ≠ j' := Ne.symm heq
          simp [hne] at hv
          simp [heq, hv]
      rw [Finset.sum_congr rfl (fun j' _ => hterm j')]
      rw [Finset.sum_ite_eq' Finset.univ ⟨j, hj⟩ (fun j' : ↥J => α j'.1 u)]
      simp
    rw [h2]
    exact z2_add_self (α j u)
  have hwr : α r w = 0 := hJspan r w hwJ
  have hexp : α r w = α r u + ∑ j : ↥J, α r (uBasis j) * α j.1 u := by
    dsimp only [w]
    rw [map_add, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hexp] at hwr
  have hadd := congrArg (· + α r u) hwr
  rw [zero_add] at hadd
  have hcancel : α r u + (∑ j : ↥J, α r (uBasis j) * α j.1 u) + α r u =
      ∑ j : ↥J, α r (uBasis j) * α j.1 u := by
    calc
      α r u + (∑ j : ↥J, α r (uBasis j) * α j.1 u) + α r u
        = (α r u + α r u) + ∑ j : ↥J, α r (uBasis j) * α j.1 u := by ring
      _ = ∑ j : ↥J, α r (uBasis j) * α j.1 u := by rw [z2_add_self, zero_add]
  rw [hcancel] at hadd
  exact hadd.symm

lemma part1_forward {m h q : ℕ} (label : UType h → VType m → Bool)
    (hfeas : ∃ (ask : (j : Fin q) → (Fin j.val → B) → ((UType h × VType m) →ₗ[B] B))
      (answers : UType h → VType m → Fin q → B) (leaf : (Fin q → B) → Bool),
      (∀ (u : UType h) (x : VType m) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) ∧
      ∀ (u : UType h) (x : VType m), label u x = leaf (answers u x))
    (hzero : ∀ witness : UType h, label witness 0 = false) :
    ∃ (n : ℕ) (depth : Fin n → ℕ)
      (maps : (i : Fin n) → VType m →ₗ[B] (Fin (q - depth i) → B)),
      ((∀ i, depth i ≤ min h q) ∧ (∑ i : Fin n, 2 ^ (h - depth i)) = 2 ^ h) ∧
      ∀ x : VType m,
        (∑ i : Fin n, if maps i x = 0 then 2 ^ (h - depth i) else 0) ≤
          ((Finset.univ : Finset (UType h)).filter (fun witness => label witness x = false)).card := by
  obtain ⟨ask, answers, leaf, hrec, hlabel⟩ := hfeas
  let Reach : Finset (Fin q → B) := Finset.univ.image (fun u : UType h => answers u 0)
  let n : ℕ := Reach.card
  let enumR : Fin n ≃ ↥Reach := (Fintype.equivFinOfCardEq (by simp [n])).symm
  let pathOf : Fin n → (Fin q → B) := fun i => (enumR i).1
  have hpath_mem : ∀ i : Fin n, pathOf i ∈ Reach := fun i => (enumR i).2
  have hpath_inj : Function.Injective pathOf := by
    intro i1 i2 hEq
    exact enumR.injective (Subtype.ext hEq)
  let alpha : Fin n → Fin q → (UType h →ₗ[B] B) := fun i j =>
    { toFun := fun u => ask j (fun r => pathOf i ⟨r.val, Nat.lt_trans r.isLt j.isLt⟩) (u, 0)
      map_add' := fun u1 u2 => by
        have h1 : (u1 + u2, (0 : VType m)) = (u1, 0) + (u2, 0) := by ext <;> simp
        rw [h1, map_add]
      map_smul' := fun c u => by
        have h1 : (c • u, (0 : VType m)) = c • (u, 0) := by ext <;> simp
        rw [h1, map_smul]
        rfl }
  let beta : Fin n → Fin q → (VType m →ₗ[B] B) := fun i j =>
    { toFun := fun x => ask j (fun r => pathOf i ⟨r.val, Nat.lt_trans r.isLt j.isLt⟩) (0, x)
      map_add' := fun x1 x2 => by
        have h1 : ((0 : UType h), x1 + x2) = (0, x1) + (0, x2) := by ext <;> simp
        rw [h1, map_add]
      map_smul' := fun c x => by
        have h1 : ((0 : UType h), c • x) = c • (0, x) := by ext <;> simp
        rw [h1, map_smul]
        rfl }
  have hJex : ∀ i : Fin n, ∃ J : Finset (Fin q),
      Function.Surjective (fun u : UType h => fun j : ↥J => alpha i j.1 u) ∧
      (∀ r : Fin q, ∀ w : UType h, (∀ j ∈ J, alpha i j w = 0) → alpha i r w = 0) :=
    fun i => extract_greedy_basis (alpha i)
  let Jof : Fin n → Finset (Fin q) := fun i => Classical.choose (hJex i)
  have hJsurj : ∀ i : Fin n,
      Function.Surjective (fun u : UType h => fun j : ↥(Jof i) => alpha i j.1 u) :=
    fun i => (Classical.choose_spec (hJex i)).1
  have hJspan : ∀ (i : Fin n) (r : Fin q) (w : UType h),
      (∀ j ∈ Jof i, alpha i j w = 0) → alpha i r w = 0 :=
    fun i => (Classical.choose_spec (hJex i)).2
  let depth : Fin n → ℕ := fun i => (Jof i).card
  let evJ : (i : Fin n) → UType h →ₗ[B] (↥(Jof i) → B) := fun i =>
    { toFun := fun u j => alpha i j.1 u
      map_add' := fun u1 u2 => by funext j; exact map_add (alpha i j.1) u1 u2
      map_smul' := fun c u => by funext j; exact map_smul (alpha i j.1) c u }
  have hker_props : ∀ i : Fin n,
      depth i ≤ h ∧
      (Finset.univ.filter (fun u : UType h => evJ i u = 0)).card = 2 ^ (h - depth i) := by
    intro i
    have hk := kernel_card_of_surj (evJ i) (hJsurj i)
    have hcard : Fintype.card ↥(Jof i) = depth i := Fintype.card_coe (Jof i)
    rw [hcard] at hk
    exact hk
  have hdepth_le : ∀ i : Fin n, depth i ≤ min h q := by
    intro i
    refine Nat.le_min.mpr ⟨(hker_props i).1, ?_⟩
    calc
      (Jof i).card ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = q := by simp
  have huBasis_ex : ∀ (i : Fin n) (j : ↥(Jof i)), ∃ u : UType h, evJ i u = Pi.single j (1 : B) :=
    fun i j => hJsurj i (Pi.single j (1 : B))
  let uBasis : (i : Fin n) → ↥(Jof i) → UType h := fun i j => Classical.choose (huBasis_ex i j)
  have huBasis_spec : ∀ (i : Fin n) (j : ↥(Jof i)), evJ i (uBasis i j) = Pi.single j (1 : B) :=
    fun i j => Classical.choose_spec (huBasis_ex i j)
  have halpha_decomp : ∀ (i : Fin n) (r : Fin q) (u : UType h),
      alpha i r u = ∑ j : ↥(Jof i), alpha i r (uBasis i j) * alpha i j.1 u := by
    intro i r u
    refine alpha_decomp_lemma (alpha i) (Jof i) (hJspan i) (uBasis i) ?_ r u
    intro j j'
    have hv := congrFun (huBasis_spec i j) j'
    simpa [evJ, Pi.single_apply] using hv
  have hcompl_card : ∀ i : Fin n, Fintype.card ↥((Jof i)ᶜ) = q - depth i := by
    intro i
    rw [Fintype.card_coe]
    have hsum : ((Jof i)ᶜ).card + (Jof i).card = q := by
      have hd : Disjoint ((Jof i)ᶜ) (Jof i) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact (Finset.mem_compl.mp h1) h2
      have hu : (Jof i)ᶜ ∪ Jof i = Finset.univ := by
        ext x; by_cases hx : x ∈ Jof i <;> simp
      have hc := Finset.card_union_of_disjoint hd
      rw [hu, Finset.card_univ, Fintype.card_fin] at hc
      exact hc.symm
    dsimp only [depth]
    omega
  let enumC : (i : Fin n) → Fin (q - depth i) ≃ ↥((Jof i)ᶜ) := fun i =>
    (Fintype.equivFinOfCardEq (hcompl_card i)).symm
  let maps : (i : Fin n) → VType m →ₗ[B] (Fin (q - depth i) → B) := fun i =>
    { toFun := fun x idx =>
        let r : Fin q := (enumC i idx).1
        beta i r x + ∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x
      map_add' := fun x1 x2 => by
        funext idx
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        funext idx
        simp only [Pi.smul_apply, smul_eq_mul, map_smul, RingHom.id_apply]
        have h1 : ∑ j : ↥(Jof i), alpha i (enumC i idx).1 (uBasis i j) * (c * beta i j.1 x) =
            ∑ j : ↥(Jof i), c * (alpha i (enumC i idx).1 (uBasis i j) * beta i j.1 x) := by
          apply Finset.sum_congr rfl
          intro j _; ring
        rw [h1, ← Finset.mul_sum, mul_add] }
  have hfiber0 : ∀ i : Fin n,
      (Finset.univ.filter (fun u : UType h => answers u 0 = pathOf i)).card = 2 ^ (h - depth i) := by
    intro i
    rcases Finset.mem_image.mp (hpath_mem i) with ⟨u0, _, hu0⟩
    have hu0_eq : ∀ j : Fin q, alpha i j u0 = pathOf i j := by
      have h1 := (answers_eq_iff_path ask answers hrec u0 0 (pathOf i)).mp hu0
      exact h1
    have hfilt_eq : Finset.univ.filter (fun u : UType h => answers u 0 = pathOf i) =
        (Finset.univ.filter (fun w : UType h => evJ i w = 0)).image (fun w => w + u0) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hu
        have hu_all : ∀ j : Fin q, alpha i j u = pathOf i j := (answers_eq_iff_path ask answers hrec u 0 (pathOf i)).mp hu
        refine ⟨u + u0, ?_, ?_⟩
        · funext j
          dsimp only [evJ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
          rw [map_add, hu_all j.1, hu0_eq j.1, z2_add_self]
        · funext k; simp only [Pi.add_apply]; rw [add_assoc, z2_add_self, add_zero]
      · rintro ⟨w, hw0, rfl⟩
        apply (answers_eq_iff_path ask answers hrec (w + u0) 0 (pathOf i)).mpr
        intro r
        have hwr : alpha i r w = 0 := hJspan i r w (fun j hj => congrFun hw0 ⟨j, hj⟩)
        change alpha i r (w + u0) = pathOf i r
        rw [map_add, hwr, zero_add, hu0_eq r]
    rw [hfilt_eq, Finset.card_image_of_injective _ (fun _ _ hEq => add_right_cancel hEq)]
    exact (hker_props i).2
  have hshape_sum : ∑ i : Fin n, 2 ^ (h - depth i) = 2 ^ h := by
    have h1 : (Finset.univ : Finset (UType h)).card =
        ∑ i : Fin n, (Finset.univ.filter (fun u : UType h => answers u 0 = pathOf i)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext u
        simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
        have hmem : answers u 0 ∈ Reach := Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
        refine ⟨enumR.symm ⟨answers u 0, hmem⟩, ?_⟩
        simp [pathOf]
      · intro i1 _ i2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact hne (hpath_inj ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
    rw [Finset.sum_congr rfl (fun i _ => hfiber0 i)] at h1
    exact h1.symm
  refine ⟨n, depth, maps, ⟨hdepth_le, hshape_sum⟩, ?_⟩
  intro x
  let Active : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => maps i x = 0)
  have hfiberx : ∀ i ∈ Active,
      (Finset.univ.filter (fun u : UType h => answers u x = pathOf i)).card = 2 ^ (h - depth i) := by
    intro i hi
    have hmap0 : maps i x = 0 := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_image.mp (hpath_mem i) with ⟨u0, _, hu0⟩
    have hu0_eq : ∀ j : Fin q, alpha i j u0 = pathOf i j :=
      (answers_eq_iff_path ask answers hrec u0 0 (pathOf i)).mp hu0
    obtain ⟨v0, hv0⟩ := hJsurj i (fun j : ↥(Jof i) => beta i j.1 x)
    have hv0_all : ∀ r : Fin q, alpha i r v0 = beta i r x := by
      intro r
      by_cases hr : r ∈ Jof i
      · exact congrFun hv0 ⟨r, hr⟩
      · have hrc : r ∈ (Jof i)ᶜ := Finset.mem_compl.mpr hr
        let idx : Fin (q - depth i) := (enumC i).symm ⟨r, hrc⟩
        have hidx : (enumC i idx).1 = r := by
          have h1 := (enumC i).apply_symm_apply ⟨r, hrc⟩
          exact congrArg Subtype.val h1
        have h0 := congrFun hmap0 idx
        dsimp only [maps, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
        rw [hidx] at h0
        rw [halpha_decomp i r v0]
        have hv0_j : ∀ j : ↥(Jof i), alpha i j.1 v0 = beta i j.1 x :=
          fun j => congrFun hv0 j
        have hsub : ∑ j : ↥(Jof i), alpha i r (uBasis i j) * alpha i j.1 v0 =
            ∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hv0_j j]
        rw [hsub]
        have hadd := congrArg (· + beta i r x) h0
        rw [zero_add] at hadd
        have hcancel : beta i r x + (∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x) + beta i r x =
            ∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x := by
          calc
            beta i r x + (∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x) + beta i r x
              = (beta i r x + beta i r x) + ∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x := by ring
            _ = ∑ j : ↥(Jof i), alpha i r (uBasis i j) * beta i j.1 x := by rw [z2_add_self, zero_add]
        rw [hcancel] at hadd
        exact hadd
    let u1 : UType h := u0 + v0
    have hfilt_eq : Finset.univ.filter (fun u : UType h => answers u x = pathOf i) =
        (Finset.univ.filter (fun w : UType h => evJ i w = 0)).image (fun w => w + u1) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hu
        have hu_all := (answers_eq_iff_path ask answers hrec u x (pathOf i)).mp hu
        refine ⟨u + u1, ?_, ?_⟩
        · funext j
          dsimp only [evJ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
          have hux := hu_all j.1
          rw [lin_eval_zero_right] at hux
          change alpha i j.1 u + beta i j.1 x = pathOf i j.1 at hux
          rw [map_add, map_add, hu0_eq j.1, hv0_all j.1]
          have hre : alpha i j.1 u + (pathOf i j.1 + beta i j.1 x) =
              (alpha i j.1 u + beta i j.1 x) + pathOf i j.1 := by ring
          rw [hre, hux, z2_add_self]
        · funext k; simp only [Pi.add_apply]; rw [add_assoc, z2_add_self, add_zero]
      · rintro ⟨w, hw0, rfl⟩
        apply (answers_eq_iff_path ask answers hrec (w + u1) x (pathOf i)).mpr
        intro r
        rw [lin_eval_zero_right]
        change alpha i r (w + u1) + beta i r x = pathOf i r
        have hwr : alpha i r w = 0 := hJspan i r w (fun j hj => congrFun hw0 ⟨j, hj⟩)
        rw [map_add, map_add, hwr, zero_add, hu0_eq r, hv0_all r]
        rw [add_assoc, z2_add_self, add_zero]
    rw [hfilt_eq, Finset.card_image_of_injective _ (fun _ _ hEq => add_right_cancel hEq)]
    exact (hker_props i).2
  have hsum_active : (∑ i : Fin n, if maps i x = 0 then 2 ^ (h - depth i) else 0) =
      (Active.biUnion (fun i => Finset.univ.filter (fun u : UType h => answers u x = pathOf i))).card := by
    rw [← Finset.sum_filter]
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun i hi => (hfiberx i hi).symm)
    · intro i1 _ i2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro u h1 h2
      exact hne (hpath_inj ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
  rw [hsum_active]
  apply Finset.card_le_card
  intro u hu
  rcases Finset.mem_biUnion.mp hu with ⟨i, _, hui⟩
  have hux : answers u x = pathOf i := (Finset.mem_filter.mp hui).2
  rcases Finset.mem_image.mp (hpath_mem i) with ⟨u0, _, hu0⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ u, ?_⟩
  rw [hlabel u x, hux, ← hu0, ← hlabel u0 0]
  exact hzero u0

lemma exists_sorted_perm :
    ∀ (n : ℕ) (f : Fin n → ℕ),
      ∃ σ : Equiv.Perm (Fin n), ∀ a b : Fin n, a ≤ b → f (σ a) ≤ f (σ b) := by
  intro n
  induction n with
  | zero =>
    intro f
    exact ⟨Equiv.refl (Fin 0), fun a => Fin.elim0 a⟩
  | succ n ih =>
    intro f
    obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1))) f
      ⟨0, Finset.mem_univ 0⟩
    let sw : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 imin
    obtain ⟨τ, hτ⟩ := ih (fun j : Fin n => f (sw j.succ))
    let extFun : Fin (n + 1) → Fin (n + 1) := Fin.cases 0 (fun j => (τ j).succ)
    let invFun : Fin (n + 1) → Fin (n + 1) := Fin.cases 0 (fun j => (τ.symm j).succ)
    have hext_inv : Function.LeftInverse invFun extFun := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp [extFun, invFun]
      · intro j; simp [extFun, invFun]
    have hext_inv2 : Function.RightInverse invFun extFun := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp [extFun, invFun]
      · intro j; simp [extFun, invFun]
    let τ' : Equiv.Perm (Fin (n + 1)) :=
      { toFun := extFun
        invFun := invFun
        left_inv := hext_inv
        right_inv := hext_inv2 }
    refine ⟨τ'.trans sw, ?_⟩
    intro a b
    refine Fin.cases ?_ ?_ a
    · intro _
      simp only [Equiv.trans_apply, τ', extFun, Equiv.coe_fn_mk, Fin.cases_zero, sw,
        Equiv.swap_apply_left]
      exact hmin _ (Finset.mem_univ _)
    · intro a'
      refine Fin.cases ?_ ?_ b
      · intro hle
        exact absurd hle (by simp)
      · intro b' hle
        have hle' : a' ≤ b' := Fin.succ_le_succ_iff.mp hle
        simpa [Equiv.trans_apply, τ', extFun] using hτ a' b' hle'

def binNum {h : ℕ} (u : UType h) : ℕ :=
  ∑ r : Fin h, (u r).val * 2 ^ (h - 1 - r.val)

lemma binNum_lt {h : ℕ} (u : UType h) : binNum u < 2 ^ h := by
  induction h with
  | zero => simp [binNum]
  | succ h ih =>
    let u' : UType h := fun r => u r.succ
    have hsplit : binNum u = (u 0).val * 2 ^ h + binNum u' := by
      simp only [binNum, Fin.sum_univ_succ]
      have h0 : h + 1 - 1 - (0 : Fin (h + 1)).val = h := by simp
      rw [h0]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      have hr : h + 1 - 1 - r.succ.val = h - 1 - r.val := by
        simp only [Fin.val_succ]
        omega
      rw [hr]
    have hlt1 : (u 0).val ≤ 1 := by
      have := z2_val_lt (u 0); omega
    have hlt2 : binNum u' < 2 ^ h := ih u'
    rw [hsplit, Nat.pow_succ]
    nlinarith

lemma binNum_div_pow_mod_two {h : ℕ} (u : UType h) (r : Fin h) :
    (binNum u / 2 ^ (h - 1 - r.val)) % 2 = (u r).val := by
  let hi := ∑ j ∈ Finset.univ.filter (fun j : Fin h => j.val < r.val), (u j).val * 2 ^ (h - 1 - j.val)
  let lo := ∑ j ∈ Finset.univ.filter (fun j : Fin h => r.val < j.val), (u j).val * 2 ^ (h - 1 - j.val)
  have hpart : binNum u = hi + (u r).val * 2 ^ (h - 1 - r.val) + lo := by
    have h1 : (Finset.univ : Finset (Fin h)) =
        Finset.univ.filter (fun j : Fin h => j.val < r.val) ∪
        ({r} ∪ Finset.univ.filter (fun j : Fin h => r.val < j.val)) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and,
        Finset.mem_singleton, true_iff]
      rcases lt_trichotomy j.val r.val with hlt | heq | hgt
      · exact Or.inl hlt
      · exact Or.inr (Or.inl (Fin.ext heq))
      · exact Or.inr (Or.inr hgt)
    have hd1 : Disjoint (Finset.univ.filter (fun j : Fin h => j.val < r.val))
        ({r} ∪ Finset.univ.filter (fun j : Fin h => r.val < j.val)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have hlt : j.val < r.val := (Finset.mem_filter.mp hj1).2
      rcases Finset.mem_union.mp hj2 with hEq | hgt
      · rw [Finset.mem_singleton.mp hEq] at hlt; omega
      · have := (Finset.mem_filter.mp hgt).2; omega
    have hd2 : Disjoint ({r} : Finset (Fin h))
        (Finset.univ.filter (fun j : Fin h => r.val < j.val)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      rw [Finset.mem_singleton.mp hj1] at hj2
      have := (Finset.mem_filter.mp hj2).2; omega
    dsimp only [binNum, hi, lo]
    conv_lhs => rw [h1]
    rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
    ring
  have hlo_lt : lo < 2 ^ (h - 1 - r.val) := by
    have hle : lo ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin h => r.val < j.val), 2 ^ (h - 1 - j.val) := by
      apply Finset.sum_le_sum
      intro j _
      have hv : (u j).val ≤ 1 := by have := z2_val_lt (u j); omega
      calc
        (u j).val * 2 ^ (h - 1 - j.val) ≤ 1 * 2 ^ (h - 1 - j.val) := Nat.mul_le_mul_right _ hv
        _ = 2 ^ (h - 1 - j.val) := Nat.one_mul _
    have hsum_pow : ∑ j ∈ Finset.univ.filter (fun j : Fin h => r.val < j.val), 2 ^ (h - 1 - j.val) =
        ∑ t ∈ Finset.range (h - 1 - r.val), 2 ^ t := by
      refine Finset.sum_bij (fun j _ => h - 1 - j.val) ?_ ?_ ?_ ?_
      · intro j hj
        have hgt : r.val < j.val := (Finset.mem_filter.mp hj).2
        have hlt : j.val < h := j.isLt
        exact Finset.mem_range.mpr (by omega)
      · intro j1 h1 j2 h2 hEq
        have hlt1 : j1.val < h := j1.isLt
        have hlt2 : j2.val < h := j2.isLt
        exact Fin.ext (by omega)
      · intro t ht
        have htr : t < h - 1 - r.val := Finset.mem_range.mp ht
        refine ⟨⟨h - 1 - t, by omega⟩, ?_, by dsimp only; omega⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only
        omega
      · intro j _; rfl
    have hgeom : ∀ k : ℕ, (∑ t ∈ Finset.range k, 2 ^ t) + 1 = 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, Nat.pow_succ]
        omega
    have hg := hgeom (h - 1 - r.val)
    omega
  have hhi_dvd : 2 * 2 ^ (h - 1 - r.val) ∣ hi := by
    apply Finset.dvd_sum
    intro j hj
    have hlt : j.val < r.val := (Finset.mem_filter.mp hj).2
    have hpow : 2 * 2 ^ (h - 1 - r.val) ∣ 2 ^ (h - 1 - j.val) := by
      have hexp : h - 1 - r.val + 1 ≤ h - 1 - j.val := by omega
      rw [mul_comm, ← Nat.pow_succ]
      exact Nat.pow_dvd_pow 2 hexp
    exact dvd_mul_of_dvd_right hpow (u j).val
  obtain ⟨qhi, hqhi⟩ := hhi_dvd
  have hdiv : binNum u / 2 ^ (h - 1 - r.val) = 2 * qhi + (u r).val := by
    have hpos : 0 < 2 ^ (h - 1 - r.val) := Nat.pow_pos (by omega)
    have hrew : binNum u = lo + (2 * qhi + (u r).val) * 2 ^ (h - 1 - r.val) := by
      rw [hpart, hqhi]
      ring
    rw [hrew, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo_lt, zero_add]
  rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (z2_val_lt (u r))]

lemma top_bits_eq_iff_div_eq {h d : ℕ} (hd : d ≤ h) (a b : ℕ) (ha : a < 2 ^ h) (hb : b < 2 ^ h) :
    (∀ r : Fin d, (b / 2 ^ (h - 1 - r.val)) % 2 = (a / 2 ^ (h - 1 - r.val)) % 2) ↔
      b / 2 ^ (h - d) = a / 2 ^ (h - d) := by
  have hstep : ∀ k : ℕ, k ≤ h →
      ((∀ r : Fin k, (b / 2 ^ (h - 1 - r.val)) % 2 = (a / 2 ^ (h - 1 - r.val)) % 2) ↔
        b / 2 ^ (h - k) = a / 2 ^ (h - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, iff_true]
      intro r; exact Fin.elim0 r
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hpow_step : 2 ^ (h - k) = 2 ^ (h - (k + 1)) * 2 := by
        have h1 : h - k = h - (k + 1) + 1 := by omega
        rw [h1, Nat.pow_succ]
      have hdiv_step : ∀ x : ℕ, x / 2 ^ (h - k) = (x / 2 ^ (h - (k + 1))) / 2 := by
        intro x
        rw [hpow_step, Nat.div_div_eq_div_mul]
      have hlast : h - 1 - k = h - (k + 1) := by omega
      constructor
      · intro hall
        have hprev : b / 2 ^ (h - k) = a / 2 ^ (h - k) :=
          ih'.mp (fun r => hall ⟨r.val, by omega⟩)
        have hmod : (b / 2 ^ (h - (k + 1))) % 2 = (a / 2 ^ (h - (k + 1))) % 2 := by
          have h1 := hall ⟨k, by omega⟩
          simpa only [hlast] using h1
        rw [hdiv_step b, hdiv_step a] at hprev
        have hb' := Nat.div_add_mod (b / 2 ^ (h - (k + 1))) 2
        have ha' := Nat.div_add_mod (a / 2 ^ (h - (k + 1))) 2
        omega
      · intro hEq r
        by_cases hr : r.val < k
        · have hprev : b / 2 ^ (h - k) = a / 2 ^ (h - k) := by
            rw [hdiv_step b, hdiv_step a, hEq]
          exact ih'.mpr hprev ⟨r.val, hr⟩
        · have hrk : r.val = k := by omega
          rw [hrk, hlast, hEq]
  exact hstep d hd

lemma exists_prefix_code {h n : ℕ} (depth : Fin n → ℕ)
    (hdepth : ∀ i : Fin n, depth i ≤ h)
    (hsum : ∑ i : Fin n, 2 ^ (h - depth i) = 2 ^ h) :
    ∃ pref : (i : Fin n) → (Fin (depth i) → B),
      (∀ u : UType h, ∃! i : Fin n,
        ∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩ = pref i r) ∧
      (∀ i : Fin n,
        (Finset.univ.filter (fun u : UType h =>
          ∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩ = pref i r)).card =
          2 ^ (h - depth i)) := by
  obtain ⟨σ, hσ⟩ := exists_sorted_perm n depth
  let sz : Fin n → ℕ := fun k => 2 ^ (h - depth (σ k))
  let start : Fin n → ℕ := fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), sz j
  have hsum_sz : ∑ k : Fin n, sz k = 2 ^ h := by
    dsimp only [sz]
    rw [Equiv.sum_comp σ (fun i => 2 ^ (h - depth i))]
    exact hsum
  have hstart_dvd : ∀ k : Fin n, sz k ∣ start k := by
    intro k
    apply Finset.dvd_sum
    intro j hj
    have hlt : j < k := (Finset.mem_filter.mp hj).2
    have hdle : depth (σ j) ≤ depth (σ k) := hσ j k (le_of_lt hlt)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hstart_le : ∀ k : Fin n, start k + sz k ≤ 2 ^ h := by
    intro k
    have hsub : insert k (Finset.univ.filter (fun j : Fin n => j < k)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hnot : k ∉ Finset.univ.filter (fun j : Fin n => j < k) := by simp
    have hle := Finset.sum_le_sum_of_subset (f := sz) hsub
    rw [Finset.sum_insert hnot, hsum_sz] at hle
    dsimp only [start]
    omega
  have hstart_lt : ∀ k : Fin n, start k < 2 ^ h := by
    intro k
    have hpos : 0 < sz k := Nat.pow_pos (by omega)
    have := hstart_le k
    omega
  have hmono_end : ∀ k1 k2 : Fin n, k1 < k2 → start k1 + sz k1 ≤ start k2 := by
    intro k1 k2 hlt
    have hsub : insert k1 (Finset.univ.filter (fun j : Fin n => j < k1)) ⊆
        Finset.univ.filter (fun j : Fin n => j < k2) := by
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | h1
      · exact hlt
      · exact lt_trans (Finset.mem_filter.mp h1).2 hlt
    have hnot : k1 ∉ Finset.univ.filter (fun j : Fin n => j < k1) := by simp
    have hle := Finset.sum_le_sum_of_subset (f := sz) hsub
    rw [Finset.sum_insert hnot] at hle
    dsimp only [start]
    omega
  have hcover_num : ∀ x : ℕ, x < 2 ^ h → ∃ k : Fin n, start k ≤ x ∧ x < start k + sz k := by
    intro x hx
    have hne : (Finset.univ.filter (fun k : Fin n => start k ≤ x)).Nonempty := by
      have hn_pos : 0 < n := by
        by_contra h0
        have hn0 : n = 0 := by omega
        subst hn0
        simp at hsum
        have hpos : 0 < 2 ^ h := Nat.pow_pos (by omega)
        omega
      refine ⟨⟨0, hn_pos⟩, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hemp : Finset.univ.filter (fun j : Fin n => j < ⟨0, hn_pos⟩) = ∅ := by
        ext j; simp [Fin.lt_def]
      simp [start, hemp]
    obtain ⟨kmax, hkmax_mem, hkmax_ge⟩ :=
      Finset.exists_max_image (Finset.univ.filter (fun k : Fin n => start k ≤ x)) id hne
    have hle_x : start kmax ≤ x := (Finset.mem_filter.mp hkmax_mem).2
    refine ⟨kmax, hle_x, ?_⟩
    by_contra hge
    push Not at hge
    by_cases hlast : kmax.val + 1 < n
    · let knext : Fin n := ⟨kmax.val + 1, hlast⟩
      have hstart_next : start knext = start kmax + sz kmax := by
        have hfilt : Finset.univ.filter (fun j : Fin n => j < knext) =
            insert kmax (Finset.univ.filter (fun j : Fin n => j < kmax)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
            Fin.ext_iff, knext]
          omega
        have hnot : kmax ∉ Finset.univ.filter (fun j : Fin n => j < kmax) := by simp
        dsimp only [start]
        rw [hfilt, Finset.sum_insert hnot]
        omega
      have hnext_mem : knext ∈ Finset.univ.filter (fun k : Fin n => start k ≤ x) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hstart_next]
        exact hge
      have hle_max := hkmax_ge knext hnext_mem
      have : knext.val ≤ kmax.val := hle_max
      dsimp only [knext] at this
      omega
    · have hall : Finset.univ = insert kmax (Finset.univ.filter (fun j : Fin n => j < kmax)) := by
        ext j
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff,
          Fin.lt_def, Fin.ext_iff]
        have := j.isLt
        omega
      have hnot : kmax ∉ Finset.univ.filter (fun j : Fin n => j < kmax) := by simp
      have htot : start kmax + sz kmax = 2 ^ h := by
        rw [← hsum_sz, hall, Finset.sum_insert hnot]
        dsimp only [start]
        omega
      omega
  let pref : (i : Fin n) → (Fin (depth i) → B) := fun i r =>
    (((start (σ.symm i) / 2 ^ (h - 1 - r.val)) % 2 : ℕ) : B)
  have hmatch_iff : ∀ (u : UType h) (i : Fin n),
      (∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩ = pref i r) ↔
        (start (σ.symm i) ≤ binNum u ∧ binNum u < start (σ.symm i) + sz (σ.symm i)) := by
    intro u i
    let k := σ.symm i
    have hσk : σ k = i := σ.apply_symm_apply i
    have hszk : sz k = 2 ^ (h - depth i) := by simp [sz, hσk]
    have hbit : (∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩ = pref i r) ↔
        ∀ r : Fin (depth i),
          (binNum u / 2 ^ (h - 1 - r.val)) % 2 = (start k / 2 ^ (h - 1 - r.val)) % 2 := by
      constructor
      · intro h1 r
        rw [binNum_div_pow_mod_two u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩]
        have hr := congrArg ZMod.val (h1 r)
        simpa [pref, k, z2_val_cast] using hr
      · intro h1 r
        apply ZMod.val_injective
        rw [← binNum_div_pow_mod_two u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩, h1 r]
        simp [pref, k]
    rw [hbit, top_bits_eq_iff_div_eq (hdepth i) (start k) (binNum u) (hstart_lt k) (binNum_lt u), hszk]
    obtain ⟨q0, hq0⟩ := hstart_dvd k
    rw [hszk] at hq0
    have hpos : 0 < 2 ^ (h - depth i) := Nat.pow_pos (by omega)
    have hdiv_start : start k / 2 ^ (h - depth i) = q0 := by
      rw [hq0, Nat.mul_div_cancel_left q0 hpos]
    rw [hdiv_start, hq0]
    constructor
    · intro hdiv
      have hdm := Nat.div_add_mod (binNum u) (2 ^ (h - depth i))
      have hmlt := Nat.mod_lt (binNum u) hpos
      rw [hdiv] at hdm
      constructor
      · omega
      · have h1 : 2 ^ (h - depth i) * q0 + 2 ^ (h - depth i) = 2 ^ (h - depth i) * q0 + 2 ^ (h - depth i) := rfl
        omega
    · rintro ⟨h1, h2⟩
      have hdm := Nat.div_add_mod (binNum u) (2 ^ (h - depth i))
      have hmlt := Nat.mod_lt (binNum u) hpos
      have hle1 : q0 ≤ binNum u / 2 ^ (h - depth i) := by
        by_contra hlt
        have : binNum u / 2 ^ (h - depth i) + 1 ≤ q0 := by omega
        have : 2 ^ (h - depth i) * (binNum u / 2 ^ (h - depth i) + 1) ≤ 2 ^ (h - depth i) * q0 :=
          Nat.mul_le_mul_left _ this
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      have hle2 : binNum u / 2 ^ (h - depth i) ≤ q0 := by
        by_contra hgt
        have : q0 + 1 ≤ binNum u / 2 ^ (h - depth i) := by omega
        have : 2 ^ (h - depth i) * (q0 + 1) ≤ 2 ^ (h - depth i) * (binNum u / 2 ^ (h - depth i)) :=
          Nat.mul_le_mul_left _ this
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      omega
  refine ⟨pref, ?_, ?_⟩
  · intro u
    obtain ⟨k, hk1, hk2⟩ := hcover_num (binNum u) (binNum_lt u)
    refine ⟨σ k, (hmatch_iff u (σ k)).mpr (by simpa using ⟨hk1, hk2⟩), ?_⟩
    intro i hi
    have h1 := (hmatch_iff u i).mp hi
    by_contra hne
    have hkne : σ.symm i ≠ k := fun hEq => hne (by rw [← hEq, σ.apply_symm_apply])
    rcases lt_or_gt_of_ne hkne with hlt | hgt
    · have := hmono_end (σ.symm i) k hlt
      omega
    · have := hmono_end k (σ.symm i) hgt
      omega
  · intro i
    have hbij : (Finset.univ.filter (fun u : UType h =>
        ∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth i)⟩ = pref i r)).card =
        Fintype.card (Fin (h - depth i) → B) := by
      refine Finset.card_bij
        (fun u _ => fun r : Fin (h - depth i) => u ⟨depth i + r.val, by have := r.isLt; have := hdepth i; omega⟩)
        ?_ ?_ ?_
      · intro u _; exact Finset.mem_univ _
      · intro u1 h1 u2 h2 hEq
        have hm1 := (Finset.mem_filter.mp h1).2
        have hm2 := (Finset.mem_filter.mp h2).2
        funext r
        by_cases hr : r.val < depth i
        · have e1 := hm1 ⟨r.val, hr⟩
          have e2 := hm2 ⟨r.val, hr⟩
          exact e1.trans e2.symm
        · have hv := congrFun hEq ⟨r.val - depth i, by have := r.isLt; omega⟩
          have hidx : (⟨depth i + (r.val - depth i), by have := r.isLt; have := hdepth i; omega⟩ : Fin h) = r :=
            Fin.ext (by dsimp only; omega)
          simpa [hidx] using hv
      · intro tail _
        let u : UType h := fun r =>
          if hr : r.val < depth i then pref i ⟨r.val, hr⟩
          else tail ⟨r.val - depth i, by have := r.isLt; omega⟩
        refine ⟨u, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ u, ?_⟩
          intro r
          simp [u, r.isLt]
        · funext r
          have hnot : ¬ (depth i + r.val < depth i) := by omega
          have hsub : depth i + r.val - depth i = r.val := by omega
          simp [u, hnot, hsub]
    rw [hbij, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma part2_backward {m h q n : ℕ} (depth : Fin n → ℕ)
    (maps : (i : Fin n) → VType m →ₗ[B] (Fin (q - depth i) → B))
    (hshape : (∀ i, depth i ≤ min h q) ∧ (∑ i : Fin n, 2 ^ (h - depth i)) = 2 ^ h) :
    ∃ label : UType h → VType m → Bool,
      (∃ (ask : (j : Fin q) → (Fin j.val → B) → ((UType h × VType m) →ₗ[B] B))
        (answers : UType h → VType m → Fin q → B) (leaf : (Fin q → B) → Bool),
        (∀ (u : UType h) (x : VType m) (j : Fin q), answers u x j =
          ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) ∧
        ∀ (u : UType h) (x : VType m), label u x = leaf (answers u x)) ∧
      ∀ x : VType m,
        ((Finset.univ : Finset (UType h)).filter (fun witness => label witness x = false)).card =
          ∑ i : Fin n, if maps i x = 0 then 2 ^ (h - depth i) else 0 := by
  have hdepth_h : ∀ i : Fin n, depth i ≤ h := fun i => le_trans (hshape.1 i) (Nat.min_le_left h q)
  have hdepth_q : ∀ i : Fin n, depth i ≤ q := fun i => le_trans (hshape.1 i) (Nat.min_le_right h q)
  obtain ⟨pref, huniq, hcard_pref⟩ := exists_prefix_code depth hdepth_h hshape.2
  have hpref_disj : ∀ (i1 i2 : Fin n) (k : ℕ) (w : Fin k → B),
      (h1 : depth i1 ≤ k) → (h2 : depth i2 ≤ k) →
      (∀ r : Fin (depth i1), w ⟨r.val, lt_of_lt_of_le r.isLt h1⟩ = pref i1 r) →
      (∀ r : Fin (depth i2), w ⟨r.val, lt_of_lt_of_le r.isLt h2⟩ = pref i2 r) →
      i1 = i2 := by
    intro i1 i2 k w h1 h2 hm1 hm2
    let u : UType h := fun r => if hr : r.val < k then w ⟨r.val, hr⟩ else 0
    have hu1 : ∀ r : Fin (depth i1), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_h i1)⟩ = pref i1 r := by
      intro r
      have hrk : r.val < k := lt_of_lt_of_le r.isLt h1
      simp only [u, hrk, ↓reduceDIte]
      exact hm1 r
    have hu2 : ∀ r : Fin (depth i2), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_h i2)⟩ = pref i2 r := by
      intro r
      have hrk : r.val < k := lt_of_lt_of_le r.isLt h2
      simp only [u, hrk, ↓reduceDIte]
      exact hm2 r
    exact (huniq u).unique hu1 hu2
  let owner : UType h → Fin n := fun u => Classical.choose (huniq u)
  have howner_match : ∀ u : UType h,
      ∀ r : Fin (depth (owner u)),
        u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_h (owner u))⟩ = pref (owner u) r :=
    fun u => (Classical.choose_spec (huniq u)).1
  have howner_uniq : ∀ (u : UType h) (i : Fin n),
      (∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_h i)⟩ = pref i r) →
      i = owner u :=
    fun u i hi => (Classical.choose_spec (huniq u)).2 i hi
  let ask : (j : Fin q) → (Fin j.val → B) → ((UType h × VType m) →ₗ[B] B) := fun j hist =>
    if hex : ∃ i : Fin n, ∃ hle : depth i ≤ j.val,
        ∀ r : Fin (depth i), hist ⟨r.val, lt_of_lt_of_le r.isLt hle⟩ = pref i r then
      let i := Classical.choose hex
      let hle : depth i ≤ j.val := Classical.choose (Classical.choose_spec hex)
      { toFun := fun p => maps i p.2 ⟨j.val - depth i, by have := j.isLt; omega⟩
        map_add' := fun p1 p2 => by
          change maps i (p1.2 + p2.2) _ = maps i p1.2 _ + maps i p2.2 _
          rw [map_add]; rfl
        map_smul' := fun c p => by
          change maps i (c • p.2) _ = c * maps i p.2 _
          rw [map_smul]; rfl }
    else
      if hjh : j.val < h then
        { toFun := fun p => p.1 ⟨j.val, hjh⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      else 0
  let answers : UType h → VType m → Fin q → B := fun u x j =>
    let i := owner u
    if hj : j.val < depth i then
      u ⟨j.val, lt_of_lt_of_le hj (hdepth_h i)⟩
    else
      maps i x ⟨j.val - depth i, by have := j.isLt; omega⟩
  let leaf : (Fin q → B) → Bool := fun ans =>
    if hex : ∃ i : Fin n, ∀ r : Fin (depth i),
        ans ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_q i)⟩ = pref i r then
      let i := Classical.choose hex
      decide (∃ r : Fin (q - depth i),
        ans ⟨depth i + r.val, by have := r.isLt; have := hdepth_q i; omega⟩ ≠ 0)
    else true
  let label : UType h → VType m → Bool := fun u x => leaf (answers u x)
  have hrec : ∀ (u : UType h) (x : VType m) (j : Fin q),
      answers u x j =
        ask j (fun r => answers u x ⟨r.val, Nat.lt_trans r.isLt j.isLt⟩) (u, x) := by
    intro u x j
    let i0 := owner u
    let hist : Fin j.val → B := fun r => answers u x ⟨r.val, Nat.lt_trans r.isLt j.isLt⟩
    change answers u x j = ask j hist (u, x)
    by_cases hj : j.val < depth i0
    · have hno : ¬ ∃ i : Fin n, ∃ hle : depth i ≤ j.val,
          ∀ r : Fin (depth i), hist ⟨r.val, lt_of_lt_of_le r.isLt hle⟩ = pref i r := by
        rintro ⟨i, hle, hm⟩
        have hmatch_u : ∀ r : Fin (depth i),
            u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_h i)⟩ = pref i r := by
          intro r
          have hlt0 : r.val < depth i0 := lt_trans (lt_of_lt_of_le r.isLt hle) hj
          have h1 := hm r
          simpa [hist, answers, i0, hlt0] using h1
        have hiEq : i = i0 := howner_uniq u i hmatch_u
        subst hiEq
        omega
      have hjh : j.val < h := lt_of_lt_of_le hj (hdepth_h i0)
      have hask : ask j hist (u, x) = u ⟨j.val, hjh⟩ := by
        dsimp only [ask]
        rw [dif_neg hno, dif_pos hjh]
        rfl
      rw [hask]
      simp only [answers, i0, hj, ↓reduceDIte]
    · have hle0 : depth i0 ≤ j.val := by omega
      have hex : ∃ i : Fin n, ∃ hle : depth i ≤ j.val,
          ∀ r : Fin (depth i), hist ⟨r.val, lt_of_lt_of_le r.isLt hle⟩ = pref i r := by
        refine ⟨i0, hle0, ?_⟩
        intro r
        have hlt0 : r.val < depth i0 := r.isLt
        simpa [hist, answers, i0, hlt0] using howner_match u r
      have hask : ask j hist (u, x) = maps i0 x ⟨j.val - depth i0, by have := j.isLt; omega⟩ := by
        dsimp only [ask]
        rw [dif_pos hex]
        dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        have hch_eq : Classical.choose hex = i0 := by
          have hspec := Classical.choose_spec hex
          have hle' := Classical.choose hspec
          have hm' := Classical.choose_spec hspec
          exact hpref_disj (Classical.choose hex) i0 j.val hist hle' hle0 hm'
            (fun r => by
              have hlt0 : r.val < depth i0 := r.isLt
              simpa [hist, answers, i0, hlt0] using howner_match u r)
        have hcongr : ∀ (i1 i2 : Fin n) (h1 : j.val - depth i1 < q - depth i1)
            (h2 : j.val - depth i2 < q - depth i2), i1 = i2 →
            maps i1 x ⟨j.val - depth i1, h1⟩ = maps i2 x ⟨j.val - depth i2, h2⟩ := by
          rintro i1 _ h1 h2 rfl; rfl
        exact hcongr _ _ _ _ hch_eq
      rw [hask]
      simp only [answers, i0, hj, ↓reduceDIte]
  have hleaf_eq : ∀ (ans : Fin q → B) (i0 : Fin n),
      (∀ r : Fin (depth i0), ans ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_q i0)⟩ = pref i0 r) →
      leaf ans = decide (∃ r : Fin (q - depth i0),
        ans ⟨depth i0 + r.val, by have := r.isLt; have := hdepth_q i0; omega⟩ ≠ 0) := by
    intro ans i0 hm
    dsimp only [leaf]
    by_cases hex : ∃ i : Fin n, ∀ r : Fin (depth i),
        ans ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_q i)⟩ = pref i r
    · rw [dif_pos hex]
      have hch : Classical.choose hex = i0 :=
        hpref_disj (Classical.choose hex) i0 q ans (hdepth_q _) (hdepth_q i0)
          (Classical.choose_spec hex) hm
      have hcongr : ∀ (i1 i2 : Fin n), i1 = i2 →
          decide (∃ r : Fin (q - depth i1), ans ⟨depth i1 + r.val, by have := r.isLt; have := hdepth_q i1; omega⟩ ≠ 0) =
          decide (∃ r : Fin (q - depth i2), ans ⟨depth i2 + r.val, by have := r.isLt; have := hdepth_q i2; omega⟩ ≠ 0) := by
        rintro i1 _ rfl; rfl
      exact hcongr _ _ hch
    · exact absurd ⟨i0, hm⟩ hex
  have hlabel_iff : ∀ (u : UType h) (x : VType m),
      label u x = false ↔ maps (owner u) x = 0 := by
    intro u x
    let i0 := owner u
    have hlab : label u x = decide (∃ r : Fin (q - depth i0),
        answers u x ⟨depth i0 + r.val, by have := r.isLt; have := hdepth_q i0; omega⟩ ≠ 0) :=
      hleaf_eq (answers u x) i0 (fun r => by simpa [answers, i0, r.isLt] using howner_match u r)
    rw [hlab]
    have hans_tail : ∀ r : Fin (q - depth i0),
        answers u x ⟨depth i0 + r.val, by have := r.isLt; have := hdepth_q i0; omega⟩ =
          maps i0 x r := by
      intro r
      have hnot : ¬ (depth i0 + r.val < depth i0) := by omega
      have hsub : depth i0 + r.val - depth i0 = r.val := by omega
      simp only [answers, i0, hnot, ↓reduceDIte]
      exact congrArg (maps i0 x) (Fin.ext hsub)
    simp_rw [hans_tail]
    constructor
    · intro hdec
      have hno : ¬ ∃ r : Fin (q - depth i0), maps i0 x r ≠ 0 := by
        intro h1
        have ht : decide (∃ r : Fin (q - depth i0), maps i0 x r ≠ 0) = true := decide_eq_true h1
        rw [ht] at hdec
        cases hdec
      push Not at hno
      funext r
      exact hno r
    · intro h0
      have hno : ¬ ∃ r : Fin (q - depth i0), maps i0 x r ≠ 0 := by
        rintro ⟨r, hr⟩
        exact hr (congrFun h0 r)
      exact decide_eq_false hno
  refine ⟨label, ⟨ask, answers, leaf, hrec, fun _ _ => rfl⟩, ?_⟩
  intro x
  have hpart : (Finset.univ.filter (fun u : UType h => label u x = false)) =
      (Finset.univ.filter (fun i : Fin n => maps i x = 0)).biUnion
        (fun i => Finset.univ.filter (fun u : UType h =>
          ∀ r : Fin (depth i), u ⟨r.val, lt_of_lt_of_le r.isLt (hdepth_h i)⟩ = pref i r)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hlabel_iff]
    constructor
    · intro h0
      exact ⟨owner u, h0, howner_match u⟩
    · rintro ⟨i, h0, hm⟩
      have hiEq : i = owner u := howner_uniq u i hm
      rwa [← hiEq]
  rw [hpart, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun i _ => hcard_pref i), Finset.sum_filter]
  · intro i1 _ i2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u h1 h2
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := (Finset.mem_filter.mp h2).2
    exact hne ((howner_uniq u i1 hm1).trans (howner_uniq u i2 hm2).symm)

end PEqualNP.Outside.L_lib_680_aux

theorem PEqualNP.Outside.L_lib_680 :
∀ (m h q : Nat),
  let U := Fin h → ZMod 2
  let V := Fin m → ZMod 2
  let feasible := fun (label : U → V → Bool) =>
    ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
      (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
      (∀ (u : U) (x : V) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u,x)) ∧
      ∀ (u : U) (x : V), label u x = leaf (answers u x)
  let rejected := fun (label : U → V → Bool) (x : V) =>
    ((Finset.univ : Finset U).filter (fun witness => label witness x = false)).card
  let shape := fun (n : Nat) (depth : Fin n → Nat) =>
    (∀ i, depth i ≤ min h q) ∧ (∑ i : Fin n, 2^(h-depth i)) = 2^h
  let mass := fun (n : Nat) (depth : Fin n → Nat)
    (maps : (i : Fin n) → V →ₗ[ZMod 2] (Fin (q-depth i) → ZMod 2)) (x : V) =>
      ∑ i : Fin n, if maps i x = 0 then 2^(h-depth i) else 0
  (∀ label : U → V → Bool, feasible label → (∀ witness, label witness 0 = false) →
    ∃ (n : Nat) (depth : Fin n → Nat)
      (maps : (i : Fin n) → V →ₗ[ZMod 2] (Fin (q-depth i) → ZMod 2)),
      shape n depth ∧ ∀ x : V, mass n depth maps x ≤ rejected label x) ∧
  (∀ (n : Nat) (depth : Fin n → Nat)
    (maps : (i : Fin n) → V →ₗ[ZMod 2] (Fin (q-depth i) → ZMod 2)),
    shape n depth → ∃ label : U → V → Bool, feasible label ∧
      ∀ x : V, rejected label x = mass n depth maps x) := by
  intro m h q
  dsimp only
  exact ⟨fun label hfeas hzero => PEqualNP.Outside.L_lib_680_aux.part1_forward label hfeas hzero,
         fun n depth maps hshape => PEqualNP.Outside.L_lib_680_aux.part2_backward depth maps hshape⟩

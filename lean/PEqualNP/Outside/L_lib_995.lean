import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_995_aux

private lemma det2_ne_zero_iff (a00 a01 a10 a11 : Bool) :
    ((if a00 then (-1 : ℤ) else 1) * (if a11 then -1 else 1) -
     (if a01 then -1 else 1) * (if a10 then -1 else 1) ≠ 0) ↔
    (xor a00 a10 ≠ xor a01 a11) := by
  revert a00 a01 a10 a11
  decide

private lemma det_ne_zero_iff (k : ℕ)
    (π : Equiv.Perm (Fin k × Fin 2))
    (s : (Fin k × Fin 2) × (Fin k × Fin 2) → Bool) :
    Matrix.det (fun i j : Fin k × Fin 2 =>
      if s (i, j) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
      else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0 ↔
    ∀ b : Fin k,
      xor (s ((b, 0), π.symm (b, 0))) (s ((b, 1), π.symm (b, 0))) ≠
      xor (s ((b, 0), π.symm (b, 1))) (s ((b, 1), π.symm (b, 1))) := by
  let I := Fin k × Fin 2
  let M : Matrix I I ℤ := fun i j =>
    if s (i, j) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
    else (if i.1 = (π j).1 then (1 : ℤ) else 0)
  let A : Matrix I I ℤ := fun i j => M i (π.symm j)
  have hMA : M = A.submatrix id π := by
    ext i j
    change M i j = A i (π j)
    dsimp only [A]
    rw [Equiv.symm_apply_apply]
  have hdetM : M.det = (Equiv.Perm.sign π : ℤ) * A.det := by
    rw [hMA, ← Matrix.det_transpose]
    have htr : (A.submatrix id π).transpose = A.transpose.submatrix π id := rfl
    rw [htr, Matrix.det_permute, Matrix.det_transpose]
    simp
  have hsign_ne : (Equiv.Perm.sign π : ℤ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hM_iff_A : M.det ≠ 0 ↔ A.det ≠ 0 := by
    rw [hdetM, mul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨hsign_ne, h⟩⟩
  let B : Fin k → Matrix (Fin 2) (Fin 2) ℤ := fun b r c =>
    if s ((b, r), π.symm (b, c)) then -1 else 1
  have hAB : A = (Matrix.blockDiagonal B).submatrix
      (Equiv.prodComm (Fin k) (Fin 2)) (Equiv.prodComm (Fin k) (Fin 2)) := by
    ext ⟨b, r⟩ ⟨b', c⟩
    rw [Matrix.submatrix_apply, Equiv.prodComm_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Prod.swap_prod_mk, Matrix.blockDiagonal_apply]
    dsimp only [A, M, B]
    rw [Equiv.apply_symm_apply]
    by_cases h : b = b'
    · subst h
      by_cases hs : s ((b, r), π.symm (b, c)) = true <;> simp [hs]
    · by_cases hs : s ((b, r), π.symm (b', c)) = true <;> simp [h, hs]
  have hdetA : A.det = ∏ b : Fin k, (B b).det := by
    rw [hAB, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  rw [hM_iff_A, hdetA, Finset.prod_ne_zero_iff]
  constructor
  · intro h b
    have hb := h b (Finset.mem_univ b)
    rw [Matrix.det_fin_two] at hb
    exact (det2_ne_zero_iff _ _ _ _).mp hb
  · intro h b _
    rw [Matrix.det_fin_two]
    exact (det2_ne_zero_iff _ _ _ _).mpr (h b)

private lemma two_mul_le_sq_half {a b k : ℕ} (h : a + b = 2 * k) :
    2 * a * b ≤ 2 * k ^ 2 := by
  zify at h ⊢
  nlinarith [sq_nonneg ((a : ℤ) - b)]

private lemma card_good_equiv_le : ∀ (k : ℕ) (α : Type*) [Fintype α] [DecidableEq α],
    Fintype.card α = 2 * k →
    ∀ (c : Fin k → α → Bool),
    ((Finset.univ : Finset ((Fin k × Fin 2) ≃ α)).filter
      (fun f => ∀ b : Fin k, c b (f (b, 0)) ≠ c b (f (b, 1)))).card ≤
    2 ^ k * k.factorial ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro α _ _ hcard c
    have hle : ((Finset.univ : Finset ((Fin 0 × Fin 2) ≃ α)).filter
        (fun f => ∀ b : Fin 0, c b (f (b, 0)) ≠ c b (f (b, 1)))).card ≤
        Fintype.card ((Fin 0 × Fin 2) ≃ α) := by
      simp [Finset.card_filter_le]
    have hce : Fintype.card ((Fin 0 × Fin 2) ≃ α) = 1 := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [hcard]))]
      simp
    simp only [pow_zero, Nat.factorial_zero, one_pow, mul_one]
    exact hle.trans (le_of_eq hce)
  | succ k ih =>
    intro α _ _ hcard c
    let G : Finset ((Fin (k + 1) × Fin 2) ≃ α) :=
      Finset.univ.filter (fun f => ∀ b : Fin (k + 1), c b (f (b, 0)) ≠ c b (f (b, 1)))
    let pair : ((Fin (k + 1) × Fin 2) ≃ α) → α × α :=
      fun f => (f (Fin.last k, 0), f (Fin.last k, 1))
    let P : Finset (α × α) :=
      Finset.univ.filter (fun p => c (Fin.last k) p.1 ≠ c (Fin.last k) p.2)
    have hmaps : ∀ f ∈ G, pair f ∈ P := by
      intro f hf
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, pair]
      exact hf (Fin.last k)
    have hPcard : P.card ≤ 2 * (k + 1) ^ 2 := by
      let A := Finset.univ.filter (fun x : α => c (Fin.last k) x = false)
      let B := Finset.univ.filter (fun x : α => c (Fin.last k) x = true)
      have hAB_sum : A.card + B.card = 2 * (k + 1) := by
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_filter]
          intro x _ h1 h2
          rw [h1] at h2
          exact Bool.noConfusion h2
        have hunion : A ∪ B = Finset.univ := by
          ext x
          simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases c (Fin.last k) x <;> simp
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, hcard]
      have hPeq : P = (A ×ˢ B) ∪ (B ×ˢ A) := by
        ext ⟨u, v⟩
        simp only [P, A, B, Finset.mem_union, Finset.mem_product, Finset.mem_filter,
          Finset.mem_univ, true_and]
        cases c (Fin.last k) u <;> cases c (Fin.last k) v <;> decide
      have hPdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
        rw [Finset.disjoint_left]
        intro ⟨u, v⟩ h1 h2
        simp only [A, B, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        rw [h1.1] at h2
        exact Bool.noConfusion h2.1
      rw [hPeq, Finset.card_union_of_disjoint hPdisj, Finset.card_product, Finset.card_product]
      have hmul : A.card * B.card + B.card * A.card = 2 * A.card * B.card := by ring
      rw [hmul]
      exact two_mul_le_sq_half hAB_sum
    have hfiber : ∀ p ∈ P, (G.filter (fun f => pair f = p)).card ≤ 2 ^ k * k.factorial ^ 2 := by
      intro p hp
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have huv : p.1 ≠ p.2 := fun h => hp (congrArg (c (Fin.last k)) h)
      let α' := {x : α // x ≠ p.1 ∧ x ≠ p.2}
      have hcard' : Fintype.card α' = 2 * k := by
        have h1 : Fintype.card α' = (Finset.univ.filter (fun x : α => x ≠ p.1 ∧ x ≠ p.2)).card :=
          Fintype.card_subtype _
        have h2 : Finset.univ.filter (fun x : α => x ≠ p.1 ∧ x ≠ p.2) =
            (Finset.univ : Finset α) \ {p.1, p.2} := by
          ext x
          simp
        rw [h1, h2, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard,
          Finset.card_pair huv]
        omega
      let c' : Fin k → α' → Bool := fun b x => c b.castSucc x.1
      let G' : Finset ((Fin k × Fin 2) ≃ α') :=
        Finset.univ.filter (fun f => ∀ b : Fin k, c' b (f (b, 0)) ≠ c' b (f (b, 1)))
      have hih := ih α' hcard' c'
      have hcard_le : (G.filter (fun f => pair f = p)).card ≤ G'.card := by
        have hsub : ∀ f ∈ G.filter (fun f => pair f = p),
            ∀ i : Fin k × Fin 2, f (i.1.castSucc, i.2) ≠ p.1 ∧ f (i.1.castSucc, i.2) ≠ p.2 := by
          intro f hf i
          have hpair : pair f = p := (Finset.mem_filter.mp hf).2
          have h1 : f (Fin.last k, 0) = p.1 := congrArg Prod.fst hpair
          have h2 : f (Fin.last k, 1) = p.2 := congrArg Prod.snd hpair
          constructor
          · intro heq
            have := f.injective (heq.trans h1.symm)
            have := congrArg Prod.fst this
            exact Fin.castSucc_ne_last i.1 this
          · intro heq
            have := f.injective (heq.trans h2.symm)
            have := congrArg Prod.fst this
            exact Fin.castSucc_ne_last i.1 this
        let toG' : {f // f ∈ G.filter (fun f => pair f = p)} → {f' // f' ∈ G'} := fun ⟨f, hf⟩ =>
          let fn : Fin k × Fin 2 → α' := fun i => ⟨f (i.1.castSucc, i.2), hsub f hf i⟩
          have hfn_inj : Function.Injective fn := by
            intro i j hij
            have h1 : f (i.1.castSucc, i.2) = f (j.1.castSucc, j.2) := congrArg Subtype.val hij
            have h2 := f.injective h1
            have hf1 : i.1.castSucc = j.1.castSucc := (Prod.mk.inj h2).1
            have hf2 : i.2 = j.2 := (Prod.mk.inj h2).2
            exact Prod.ext (Fin.castSucc_inj.mp hf1) hf2
          have hcard_eq : Fintype.card (Fin k × Fin 2) = Fintype.card α' := by
            simp [hcard']; omega
          let e : (Fin k × Fin 2) ≃ α' :=
            Equiv.ofBijective fn ((Fintype.bijective_iff_injective_and_card fn).mpr ⟨hfn_inj, hcard_eq⟩)
          ⟨e, by
            simp only [G', Finset.mem_filter, Finset.mem_univ, true_and]
            intro b
            have hfG := (Finset.mem_filter.mp hf).1
            simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hfG
            exact hfG b.castSucc⟩
        have htoG'_inj : Function.Injective toG' := by
          intro ⟨f1, hf1⟩ ⟨f2, hf2⟩ h
          apply Subtype.ext
          apply Equiv.ext
          intro ⟨b, r⟩
          refine Fin.lastCases ?_ ?_ b
          · have h1 : pair f1 = p := (Finset.mem_filter.mp hf1).2
            have h2 : pair f2 = p := (Finset.mem_filter.mp hf2).2
            fin_cases r
            · exact (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
            · exact (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm
          · intro b'
            have hval := congrArg (fun x => (x.1 (b', r)).1) h
            exact hval
        rw [← Fintype.card_coe (G.filter (fun f => pair f = p)), ← Fintype.card_coe G']
        exact Fintype.card_le_of_injective toG' htoG'_inj
      exact hcard_le.trans hih
    calc G.card = ∑ p ∈ P, (G.filter (fun f => pair f = p)).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _p ∈ P, (2 ^ k * k.factorial ^ 2) := Finset.sum_le_sum hfiber
      _ = P.card * (2 ^ k * k.factorial ^ 2) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (2 * (k + 1) ^ 2) * (2 ^ k * k.factorial ^ 2) := Nat.mul_le_mul_right _ hPcard
      _ = 2 ^ (k + 1) * (k + 1).factorial ^ 2 := by
          rw [pow_succ, Nat.factorial_succ]
          ring

private lemma part1 (k : ℕ) (s : (Fin k × Fin 2) × (Fin k × Fin 2) → Bool) :
    ((Finset.univ : Finset (Equiv.Perm (Fin k × Fin 2))).filter
      (fun π => Matrix.det (fun i j : Fin k × Fin 2 =>
        if s (i, j) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
        else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0)).card ≤
    2 ^ k * k.factorial ^ 2 := by
  let I := Fin k × Fin 2
  let c : Fin k → I → Bool := fun b j => xor (s ((b, 0), j)) (s ((b, 1), j))
  have hfilter_eq : (Finset.univ : Finset (Equiv.Perm I)).filter
      (fun π => Matrix.det (fun i j : I =>
        if s (i, j) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
        else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0) =
      (Finset.univ : Finset (Equiv.Perm I)).filter
      (fun π => ∀ b : Fin k, c b (π.symm (b, 0)) ≠ c b (π.symm (b, 1))) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact det_ne_zero_iff k π s
  rw [hfilter_eq]
  have hsymm : ((Finset.univ : Finset (Equiv.Perm I)).filter
      (fun π => ∀ b : Fin k, c b (π.symm (b, 0)) ≠ c b (π.symm (b, 1)))).card =
      ((Finset.univ : Finset (Equiv.Perm I)).filter
      (fun f => ∀ b : Fin k, c b (f (b, 0)) ≠ c b (f (b, 1)))).card := by
    refine Finset.card_bij (fun π _ => π.symm) ?_ ?_ ?_
    · intro π hπ
      simpa using hπ
    · intro π1 _ π2 _ h
      exact Equiv.symm_bijective.injective h
    · intro f hf
      refine ⟨f.symm, ?_, f.symm_symm⟩
      simpa using hf
  rw [hsymm]
  exact card_good_equiv_le k I (by simp [I]; omega) c

private lemma cut_xor_iff (k : ℕ) (U : Finset (Fin k × Fin 2))
    (π : Equiv.Perm (Fin k × Fin 2)) :
    (∀ b : Fin k,
      xor (decide ((0 : Fin 2).val = 1 ∧ π.symm (b, 0) ∈ U))
          (decide ((1 : Fin 2).val = 1 ∧ π.symm (b, 0) ∈ U)) ≠
      xor (decide ((0 : Fin 2).val = 1 ∧ π.symm (b, 1) ∈ U))
          (decide ((1 : Fin 2).val = 1 ∧ π.symm (b, 1) ∈ U))) ↔
    (∀ b : Fin k, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)) := by
  simp

private lemma part2 (k : ℕ) (U : Finset (Fin k × Fin 2)) (hU : U.card = k) :
    ((Finset.univ : Finset (Equiv.Perm (Fin k × Fin 2))).filter
      (fun π => Matrix.det (fun i j : Fin k × Fin 2 =>
        if decide (i.2.val = 1 ∧ j ∈ U) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
        else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0)).card =
    2 ^ k * k.factorial ^ 2 := by
  let I := Fin k × Fin 2
  have hfilter_eq : (Finset.univ : Finset (Equiv.Perm I)).filter
      (fun π => Matrix.det (fun i j : I =>
        if decide (i.2.val = 1 ∧ j ∈ U) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
        else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0) =
      (Finset.univ : Finset (Equiv.Perm I)).filter
      (fun π => ∀ b : Fin k, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [det_ne_zero_iff k π (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U))]
    exact cut_xor_iff k U π
  rw [hfilter_eq]
  have hsymm : ((Finset.univ : Finset (Equiv.Perm I)).filter
      (fun π => ∀ b : Fin k, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U))).card =
      ((Finset.univ : Finset (Equiv.Perm I)).filter
      (fun f => ∀ b : Fin k, decide (f (b, 0) ∈ U) ≠ decide (f (b, 1) ∈ U))).card := by
    refine Finset.card_bij (fun π _ => π.symm) ?_ ?_ ?_
    · intro π hπ; simpa using hπ
    · intro π1 _ π2 _ h; exact Equiv.symm_bijective.injective h
    · intro f hf; refine ⟨f.symm, ?_, f.symm_symm⟩; simpa using hf
  rw [hsymm]
  let TU := {x : I // x ∈ U}
  let TC := {x : I // x ∉ U}
  have hcardTU : Fintype.card TU = k := by
    rw [Fintype.card_coe, hU]
  have hcardTC : Fintype.card TC = k := by
    have h1 : Fintype.card TC = (Finset.univ \ U).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext x
      simp
    rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hU]
    simp [I]
    omega
  let Good := {f : Equiv.Perm I // ∀ b : Fin k, decide (f (b, 0) ∈ U) ≠ decide (f (b, 1) ∈ U)}
  have hmemU : ∀ (f : Good) (b : Fin k),
      f.1 (b, if decide (f.1 (b, 0) ∈ U) then 0 else 1) ∈ U := by
    intro f b
    by_cases h : f.1 (b, 0) ∈ U
    · simp [h]
    · have h1 := f.2 b
      simp [h] at h1
      simp [h, h1]
  have hmemC : ∀ (f : Good) (b : Fin k),
      f.1 (b, if decide (f.1 (b, 0) ∈ U) then 1 else 0) ∉ U := by
    intro f b
    by_cases h : f.1 (b, 0) ∈ U
    · have h1 := f.2 b
      simp [h] at h1
      simp [h, h1]
    · simp [h]
  let toProd : Good → (Fin k → Bool) × (Fin k ≃ TU) × (Fin k ≃ TC) := fun f =>
    let ε : Fin k → Bool := fun b => decide (f.1 (b, 0) ∈ U)
    let fnU : Fin k → TU := fun b => ⟨f.1 (b, if ε b then 0 else 1), hmemU f b⟩
    let fnC : Fin k → TC := fun b => ⟨f.1 (b, if ε b then 1 else 0), hmemC f b⟩
    have hinjU : Function.Injective fnU := by
      intro b1 b2 h
      exact congrArg Prod.fst (f.1.injective (congrArg Subtype.val h))
    have hinjC : Function.Injective fnC := by
      intro b1 b2 h
      exact congrArg Prod.fst (f.1.injective (congrArg Subtype.val h))
    let eU : Fin k ≃ TU :=
      Equiv.ofBijective fnU ((Fintype.bijective_iff_injective_and_card fnU).mpr
        ⟨hinjU, by simp [hcardTU]⟩)
    let eC : Fin k ≃ TC :=
      Equiv.ofBijective fnC ((Fintype.bijective_iff_injective_and_card fnC).mpr
        ⟨hinjC, by simp [hcardTC]⟩)
    (ε, eU, eC)
  let ofProd : (Fin k → Bool) × (Fin k ≃ TU) × (Fin k ≃ TC) → Good := fun ⟨ε, eU, eC⟩ =>
    let fn : I → I := fun ⟨b, r⟩ =>
      if (decide (r = 0) == ε b) then (eU b).1 else (eC b).1
    have hinj : Function.Injective fn := by
      intro ⟨b1, r1⟩ ⟨b2, r2⟩ h
      dsimp only [fn] at h
      split_ifs at h with h1 h2 h2
      · have hb : b1 = b2 := eU.injective (Subtype.ext h)
        subst hb
        fin_cases r1 <;> fin_cases r2 <;> simp_all
      · exfalso
        exact (eC b2).2 (h ▸ (eU b1).2)
      · exfalso
        exact (eC b1).2 (h.symm ▸ (eU b2).2)
      · have hb : b1 = b2 := eC.injective (Subtype.ext h)
        subst hb
        fin_cases r1 <;> fin_cases r2 <;> simp_all
    let f : Equiv.Perm I :=
      Equiv.ofBijective fn ((Fintype.bijective_iff_injective_and_card fn).mpr ⟨hinj, rfl⟩)
    ⟨f, by
      intro b
      change decide (fn (b, 0) ∈ U) ≠ decide (fn (b, 1) ∈ U)
      dsimp only [fn]
      by_cases hε : ε b = true <;> simp [hε, (eU b).2, (eC b).2]⟩
  let eqv : Good ≃ (Fin k → Bool) × (Fin k ≃ TU) × (Fin k ≃ TC) :=
    { toFun := toProd
      invFun := ofProd
      left_inv := fun f => by
        apply Subtype.ext
        apply Equiv.ext
        intro ⟨b, r⟩
        change (if (decide (r = 0) == decide (f.1 (b, 0) ∈ U)) then
            f.1 (b, if decide (f.1 (b, 0) ∈ U) then 0 else 1)
          else f.1 (b, if decide (f.1 (b, 0) ∈ U) then 1 else 0)) = f.1 (b, r)
        fin_cases r <;> by_cases h : f.1 (b, 0) ∈ U <;> simp [h]
      right_inv := fun ⟨ε, eU, eC⟩ => by
        have hε_eq : (fun b => decide ((ofProd (ε, eU, eC)).1 (b, 0) ∈ U)) = ε := by
          ext b
          change decide ((if (decide ((0 : Fin 2) = 0) == ε b) then (eU b).1 else (eC b).1) ∈ U) = ε b
          by_cases hε : ε b = true <;> simp [hε, (eU b).2, (eC b).2]
        refine Prod.ext hε_eq (Prod.ext ?_ ?_)
        · apply Equiv.ext
          intro b
          apply Subtype.ext
          change (if (decide ((if decide ((ofProd (ε, eU, eC)).1 (b, 0) ∈ U) then (0 : Fin 2) else 1) = 0) == ε b)
            then (eU b).1 else (eC b).1) = (eU b).1
          have hb : decide ((ofProd (ε, eU, eC)).1 (b, 0) ∈ U) = ε b := congrFun hε_eq b
          rw [hb]
          by_cases hε : ε b = true <;> simp [hε]
        · apply Equiv.ext
          intro b
          apply Subtype.ext
          change (if (decide ((if decide ((ofProd (ε, eU, eC)).1 (b, 0) ∈ U) then (1 : Fin 2) else 0) = 0) == ε b)
            then (eU b).1 else (eC b).1) = (eC b).1
          have hb : decide ((ofProd (ε, eU, eC)).1 (b, 0) ∈ U) = ε b := congrFun hε_eq b
          rw [hb]
          by_cases hε : ε b = true <;> simp [hε] }
  have hcardGood : ((Finset.univ : Finset (Equiv.Perm I)).filter
      (fun f => ∀ b : Fin k, decide (f (b, 0) ∈ U) ≠ decide (f (b, 1) ∈ U))).card =
      Fintype.card Good := (Fintype.card_subtype _).symm
  rw [hcardGood, Fintype.card_congr eqv, Fintype.card_prod, Fintype.card_prod]
  have heU : Fintype.card (Fin k ≃ TU) = k.factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [hcardTU]))]
    simp
  have heC : Fintype.card (Fin k ≃ TC) = k.factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [hcardTC]))]
    simp
  rw [heU, heC]
  simp [sq]

private lemma part3 (k : ℕ) (π : Equiv.Perm (Fin k × Fin 2)) :
    ((Finset.univ : Finset (Finset (Fin k × Fin 2))).filter
      (fun U => U.card = k ∧ Matrix.det (fun i j : Fin k × Fin 2 =>
        if decide (i.2.val = 1 ∧ j ∈ U) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
        else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0)).card = 2 ^ k := by
  let I := Fin k × Fin 2
  have hfilter_eq : (Finset.univ : Finset (Finset I)).filter
      (fun U => U.card = k ∧ Matrix.det (fun i j : I =>
        if decide (i.2.val = 1 ∧ j ∈ U) then -(if i.1 = (π j).1 then (1 : ℤ) else 0)
        else (if i.1 = (π j).1 then (1 : ℤ) else 0)) ≠ 0) =
      (Finset.univ : Finset (Finset I)).filter
      (fun U => U.card = k ∧ ∀ b : Fin k, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)) := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [det_ne_zero_iff k π (fun z => decide (z.1.2.val = 1 ∧ z.2 ∈ U)), cut_xor_iff]
  rw [hfilter_eq]
  let GoodU := {U : Finset I // U.card = k ∧ ∀ b : Fin k, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U)}
  let eqv : (Fin k → Bool) ≃ GoodU :=
    { toFun := fun ε =>
        let U := Finset.univ.image (fun b : Fin k => π.symm (b, if ε b then 0 else 1))
        ⟨U, by
          have hinj : Function.Injective (fun b : Fin k => π.symm (b, if ε b then 0 else 1)) := by
            intro b1 b2 h
            exact congrArg Prod.fst (π.symm.injective h)
          constructor
          · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
          · intro b
            have h0 : π.symm (b, 0) ∈ U ↔ ε b = true := by
              simp only [U, Finset.mem_image, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨b', hb'⟩
                have h1 := π.symm.injective hb'
                have hb : b' = b := congrArg Prod.fst h1
                subst hb
                have hr : (if ε b' then (0 : Fin 2) else 1) = 0 := congrArg Prod.snd h1
                cases hε : ε b' <;> simp [hε] at hr ⊢
              · intro hε
                exact ⟨b, by simp [hε]⟩
            have h1 : π.symm (b, 1) ∈ U ↔ ε b = false := by
              simp only [U, Finset.mem_image, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨b', hb'⟩
                have h2 := π.symm.injective hb'
                have hb : b' = b := congrArg Prod.fst h2
                subst hb
                have hr : (if ε b' then (0 : Fin 2) else 1) = 1 := congrArg Prod.snd h2
                cases hε : ε b' <;> simp [hε] at hr ⊢
              · intro hε
                exact ⟨b, by simp [hε]⟩
            cases hε : ε b <;> simp [h0, h1, hε]⟩
      invFun := fun U b => decide (π.symm (b, 0) ∈ U.1)
      left_inv := fun ε => by
        ext b
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        cases hε : ε b
        · simp only [decide_eq_false_iff_not]
          rintro ⟨b', hb'⟩
          have h1 := π.symm.injective hb'
          have hb : b' = b := congrArg Prod.fst h1
          subst hb
          have hr : (if ε b' then (0 : Fin 2) else 1) = 0 := congrArg Prod.snd h1
          simp [hε] at hr
        · simp only [decide_eq_true_eq]
          exact ⟨b, by simp [hε]⟩
      right_inv := fun U => by
        apply Subtype.ext
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        have hx : x = π.symm (π x) := (π.symm_apply_apply x).symm
        rcases hpx : π x with ⟨b, r⟩
        rw [hpx] at hx
        rw [hx]
        constructor
        · rintro ⟨b', hb'⟩
          have h1 := π.symm.injective hb'
          have hb : b' = b := congrArg Prod.fst h1
          subst hb
          have hr : (if decide (π.symm (b', 0) ∈ U.1) then (0 : Fin 2) else 1) = r := congrArg Prod.snd h1
          rw [← hr]
          by_cases h0 : π.symm (b', 0) ∈ U.1
          · simp [h0]
          · have hne := U.2.2 b'
            simp [h0] at hne
            simp [h0, hne]
        · intro hmem
          refine ⟨b, ?_⟩
          congr 1
          apply Prod.ext
          · rfl
          · have hne := U.2.2 b
            fin_cases r
            · change (if decide (π.symm (b, 0) ∈ U.1) then (0 : Fin 2) else 1) = 0
              simp [show π.symm (b, 0) ∈ U.1 from hmem]
            · change (if decide (π.symm (b, 0) ∈ U.1) then (0 : Fin 2) else 1) = 1
              by_cases h0 : π.symm (b, 0) ∈ U.1
              · simp [h0] at hne
                exact absurd (show π.symm (b, 1) ∈ U.1 from hmem) hne
              · simp [h0] }
  have hcardGoodU : ((Finset.univ : Finset (Finset I)).filter
      (fun U => U.card = k ∧ ∀ b : Fin k, decide (π.symm (b, 0) ∈ U) ≠ decide (π.symm (b, 1) ∈ U))).card =
      Fintype.card GoodU := (Fintype.card_subtype _).symm
  rw [hcardGoodU, ← Fintype.card_congr eqv]
  simp

end PEqualNP.Outside.L_lib_995_aux

theorem PEqualNP.Outside.L_lib_995 : (∀ blocks : ℕ,
  let I := Fin blocks × Fin 2
  let S := I × I → Bool
  let board := fun (π : Equiv.Perm I) (i j : I) => if i.1 = (π j).1 then (1 : ℤ) else 0
  let det := fun (π : Equiv.Perm I) (s : S) =>
    Matrix.det (fun i j => if s (i,j) then -board π i j else board π i j : Matrix I I ℤ)
  let hits := fun s : S => ((Finset.univ : Finset (Equiv.Perm I)).filter (fun π => det π s ≠ 0)).card
  let cut := fun (U : Finset I) (z : I × I) => decide (z.1.2.val = 1 ∧ z.2 ∈ U)
  (∀ s : S, hits s ≤ 2^blocks * blocks.factorial^2) ∧
  (∀ U : Finset I, U.card = blocks → hits (cut U) = 2^blocks * blocks.factorial^2) ∧
  (∀ π : Equiv.Perm I,
    ((Finset.univ : Finset (Finset I)).filter (fun U => U.card = blocks ∧ det π (cut U) ≠ 0)).card = 2^blocks)) := by
  intro blocks
  exact ⟨PEqualNP.Outside.L_lib_995_aux.part1 blocks,
    PEqualNP.Outside.L_lib_995_aux.part2 blocks,
    PEqualNP.Outside.L_lib_995_aux.part3 blocks⟩

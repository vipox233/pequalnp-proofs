import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PEqualNP.Outside.L_lib_1030_aux

open scoped BigOperators

lemma det_eq_sign_mul_prod (b : ℕ) (s : (Fin b × Fin 2) × (Fin b × Fin 2) → Bool)
    (π : Equiv.Perm (Fin b × Fin 2)) :
    let I := Fin b × Fin 2
    let M : Matrix I I ℤ :=
      fun i j => if i.1 = (π j).1 then (if s (i, j) then -1 else 1) else 0
    let B : Fin b → Matrix (Fin 2) (Fin 2) ℤ :=
      fun k r c => if s ((k, r), π.symm (k, c)) then -1 else 1
    M.det = (Equiv.Perm.sign π : ℤ) * ∏ k : Fin b, (B k).det := by
  intro I M B
  let e : Fin b × Fin 2 ≃ Fin 2 × Fin b := Equiv.prodComm (Fin b) (Fin 2)
  have hsub : M.submatrix id π.symm =
      (Matrix.blockDiagonal B).submatrix e e := by
    ext ⟨k1, r1⟩ ⟨k2, r2⟩
    change M (k1, r1) (π.symm (k2, r2)) = Matrix.blockDiagonal B (r1, k1) (r2, k2)
    rw [Matrix.blockDiagonal_apply]
    dsimp [M, B]
    simp only [Equiv.apply_symm_apply]
    by_cases h : k1 = k2
    · subst h; simp
    · simp [h]
  have hdet1 : (M.submatrix id π.symm).det = (Equiv.Perm.sign π.symm : ℤ) * M.det := by
    simpa [Matrix.submatrix_id_id] using Matrix.det_permute' π.symm M
  have hdet2 : ((Matrix.blockDiagonal B).submatrix e e).det =
      (Matrix.blockDiagonal B).det :=
    Matrix.det_submatrix_equiv_self e (Matrix.blockDiagonal B)
  rw [hsub, hdet2, Matrix.det_blockDiagonal] at hdet1
  have hsign : (Equiv.Perm.sign π.symm : ℤ) = (Equiv.Perm.sign π : ℤ) := by
    simp
  rw [hsign] at hdet1
  have hsq : ((Equiv.Perm.sign π : ℤ)) * ((Equiv.Perm.sign π : ℤ)) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  calc
    M.det = ((Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ)) * M.det := by rw [hsq, one_mul]
    _ = (Equiv.Perm.sign π : ℤ) * ((Equiv.Perm.sign π : ℤ) * M.det) := by ring
    _ = (Equiv.Perm.sign π : ℤ) * ∏ k : Fin b, (B k).det := by rw [hdet1]

lemma det_trichotomy (b : ℕ) (s : (Fin b × Fin 2) × (Fin b × Fin 2) → Bool)
    (π : Equiv.Perm (Fin b × Fin 2)) :
    let I := Fin b × Fin 2
    let D : ℤ := Matrix.det (fun i j =>
      if i.1 = (π j).1 then (if s (i, j) then -1 else 1) else 0 : Matrix I I ℤ)
    (D = 0 ∨ D = (2 : ℤ) ^ b ∨ D = -((2 : ℤ) ^ b)) ∧
    (D ≠ 0 ↔ ∀ k : Fin b,
      xor (s ((k, 0), π.symm (k, 0))) (s ((k, 1), π.symm (k, 0))) ≠
      xor (s ((k, 0), π.symm (k, 1))) (s ((k, 1), π.symm (k, 1)))) := by
  intro I D
  let B : Fin b → Matrix (Fin 2) (Fin 2) ℤ :=
    fun k r c => if s ((k, r), π.symm (k, c)) then -1 else 1
  have hD : D = (Equiv.Perm.sign π : ℤ) * ∏ k : Fin b, (B k).det := det_eq_sign_mul_prod b s π
  have hBdet : ∀ k : Fin b,
      ((B k).det = 0 ∨ (B k).det = 2 ∨ (B k).det = -2) ∧
      ((B k).det ≠ 0 ↔
        xor (s ((k, 0), π.symm (k, 0))) (s ((k, 1), π.symm (k, 0))) ≠
        xor (s ((k, 0), π.symm (k, 1))) (s ((k, 1), π.symm (k, 1)))) := by
    intro k
    rw [Matrix.det_fin_two]
    dsimp [B]
    cases s ((k, 0), π.symm (k, 0)) <;> cases s ((k, 0), π.symm (k, 1)) <;>
      cases s ((k, 1), π.symm (k, 0)) <;> cases s ((k, 1), π.symm (k, 1)) <;>
      decide
  have hprod : ∀ t : Finset (Fin b),
      (∏ k ∈ t, (B k).det) = 0 ∨
      (∏ k ∈ t, (B k).det) = (2 : ℤ) ^ t.card ∨
      (∏ k ∈ t, (B k).det) = -((2 : ℤ) ^ t.card) := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      rcases (hBdet a).1 with ha0 | ha2 | ham2 <;> rcases ih with ht0 | ht2 | htm2
      · left; simp [ha0]
      · left; simp [ha0]
      · left; simp [ha0]
      · left; simp [ht0]
      · right; left; rw [ha2, ht2]; ring
      · right; right; rw [ha2, htm2]; ring
      · left; simp [ht0]
      · right; right; rw [ham2, ht2]; ring
      · right; left; rw [ham2, htm2]; ring
  constructor
  · rw [hD]
    have hp := hprod Finset.univ
    simp only [Finset.card_univ, Fintype.card_fin] at hp
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> rw [hs]
    · simpa using hp
    · rcases hp with h0 | h2 | hm2
      · left; simp [h0]
      · right; right; simp [h2]
      · right; left; simp [hm2]
  · rw [hD]
    have hsn : (Equiv.Perm.sign π : ℤ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]
    rw [mul_ne_zero_iff, and_iff_right hsn, Finset.prod_ne_zero_iff]
    constructor
    · intro h k
      exact (hBdet k).2.mp (h k (Finset.mem_univ k))
    · intro h k _
      exact (hBdet k).2.mpr (h k)

lemma card_good_equiv : ∀ (b : ℕ) {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2 * b) (p : Fin b → α → Bool),
    (Finset.univ.filter (fun σ : (Fin b × Fin 2) ≃ α =>
      ∀ k : Fin b, p k (σ (k, 0)) ≠ p k (σ (k, 1)))).card ≤
    2 ^ b * (b.factorial) ^ 2 := by
  intro b
  induction b with
  | zero =>
    intro α _ _ hcard p
    have hle : (Finset.univ.filter (fun σ : (Fin 0 × Fin 2) ≃ α =>
        ∀ k : Fin 0, p k (σ (k, 0)) ≠ p k (σ (k, 1)))).card ≤
        Fintype.card ((Fin 0 × Fin 2) ≃ α) := Finset.card_le_univ _
    have hc : Fintype.card ((Fin 0 × Fin 2) ≃ α) = 1 := by
      haveI : Subsingleton ((Fin 0 × Fin 2) ≃ α) :=
        ⟨fun e1 e2 => Equiv.ext fun x => Fin.elim0 x.1⟩
      haveI : Unique ((Fin 0 × Fin 2) ≃ α) :=
        uniqueOfSubsingleton (Fintype.equivOfCardEq (by simp [hcard]))
      exact Fintype.card_unique
    rw [hc] at hle
    simpa using hle
  | succ b ih =>
    intro α _ _ hcard p
    let good : Finset ((Fin (b + 1) × Fin 2) ≃ α) :=
      Finset.univ.filter (fun σ => ∀ k : Fin (b + 1), p k (σ (k, 0)) ≠ p k (σ (k, 1)))
    let pairs : Finset (α × α) :=
      Finset.univ.filter (fun q : α × α => p (Fin.last b) q.1 ≠ p (Fin.last b) q.2)
    have hpairs_le : pairs.card ≤ 2 * (b + 1) ^ 2 := by
      let A := Finset.univ.filter (fun a : α => p (Fin.last b) a = false)
      let B := Finset.univ.filter (fun a : α => p (Fin.last b) a = true)
      have hAB : A.card + B.card = 2 * (b + 1) := by
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_filter]
          intro a _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
        have hun : A ∪ B = Finset.univ := by
          ext a
          simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          cases p (Fin.last b) a <;> simp
        rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ, hcard]
      have hpeq : pairs = (A ×ˢ B) ∪ (B ×ˢ A) := by
        ext ⟨x, y⟩
        simp only [pairs, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Finset.mem_product]
        cases p (Fin.last b) x <;> cases p (Fin.last b) y <;> simp
      have hdisj_p : Disjoint (A ×ˢ B) (B ×ˢ A) := by
        rw [Finset.disjoint_left]
        rintro ⟨x, y⟩ h1 h2
        simp only [A, B, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        rw [h1.1] at h2
        exact Bool.noConfusion h2.1
      rw [hpeq, Finset.card_union_of_disjoint hdisj_p, Finset.card_product, Finset.card_product,
        mul_comm B.card A.card]
      have hmul : A.card * B.card ≤ (b + 1) ^ 2 := by
        nlinarith [sq_nonneg ((A.card : ℤ) - (b + 1))]
      omega
    have hfiber : ∀ q ∈ pairs,
        (good.filter (fun σ => (σ (Fin.last b, 0), σ (Fin.last b, 1)) = q)).card ≤
        2 ^ b * (b.factorial) ^ 2 := by
      intro q hq
      have hqne : q.1 ≠ q.2 := by
        intro heq
        have hne := (Finset.mem_filter.mp hq).2
        rw [heq] at hne
        exact hne rfl
      let β := {a : α // a ≠ q.1 ∧ a ≠ q.2}
      have hβcard : Fintype.card β = 2 * b := by
        have h1 : Fintype.card β = (Finset.univ.filter (fun a : α => a ≠ q.1 ∧ a ≠ q.2)).card :=
          Fintype.card_subtype _
        have h2 : Finset.univ.filter (fun a : α => a ≠ q.1 ∧ a ≠ q.2) =
            (Finset.univ.erase q.1).erase q.2 := by
          ext a
          simp [and_comm]
        rw [h1, h2, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hqne.symm, Finset.mem_univ q.2⟩),
          Finset.card_erase_of_mem (Finset.mem_univ q.1), Finset.card_univ, hcard]
        omega
      let p' : Fin b → β → Bool := fun k x => p k.castSucc x.1
      let fib := good.filter (fun σ => (σ (Fin.last b, 0), σ (Fin.last b, 1)) = q)
      let tgt := Finset.univ.filter (fun τ : (Fin b × Fin 2) ≃ β =>
        ∀ k : Fin b, p' k (τ (k, 0)) ≠ p' k (τ (k, 1)))
      have hinj : fib.card ≤ tgt.card := by
        refine Finset.card_le_card_of_injOn
          (fun σ =>
            if hσ : σ ∈ fib then
              have hq1 : σ (Fin.last b, 0) = q.1 := congrArg Prod.fst (Finset.mem_filter.mp hσ).2
              have hq2 : σ (Fin.last b, 1) = q.2 := congrArg Prod.snd (Finset.mem_filter.mp hσ).2
              let f : Fin b × Fin 2 → β := fun ⟨k, c⟩ =>
                ⟨σ (k.castSucc, c), by
                  constructor
                  · intro h
                    have h' := σ.injective (h.trans hq1.symm)
                    have hk : k.castSucc = Fin.last b := congrArg Prod.fst h'
                    exact Fin.castSucc_ne_last k hk
                  · intro h
                    have h' := σ.injective (h.trans hq2.symm)
                    have hk : k.castSucc = Fin.last b := congrArg Prod.fst h'
                    exact Fin.castSucc_ne_last k hk⟩
              have hfinj : Function.Injective f := by
                intro x y hxy
                have hxy' : σ (x.1.castSucc, x.2) = σ (y.1.castSucc, y.2) := congrArg Subtype.val hxy
                have h2 : (x.1.castSucc, x.2) = (y.1.castSucc, y.2) := σ.injective hxy'
                have hfst : x.1 = y.1 := Fin.castSucc_injective b (Prod.mk.inj h2).1
                have hsnd : x.2 = y.2 := (Prod.mk.inj h2).2
                exact Prod.ext hfst hsnd
              have hfbij : Function.Bijective f :=
                (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by simp [hβcard, mul_comm]⟩
              Equiv.ofBijective f hfbij
            else
              (Fintype.equivOfCardEq (by simp [hβcard, mul_comm])))
          ?_ ?_
        · intro σ hσ
          simp only [Finset.mem_coe] at hσ ⊢
          simp only [hσ, ↓reduceDIte, tgt, Finset.mem_filter, Finset.mem_univ, true_and]
          intro k
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2 k.castSucc
        · intro σ1 hσ1 σ2 hσ2 heq
          simp only [Finset.mem_coe] at hσ1 hσ2
          simp only [hσ1, hσ2, ↓reduceDIte] at heq
          apply Equiv.ext
          rintro ⟨k, c⟩
          refine Fin.lastCases ?_ ?_ k
          · have h1 := (Finset.mem_filter.mp hσ1).2
            have h2 := (Finset.mem_filter.mp hσ2).2
            fin_cases c
            · exact (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
            · exact (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm
          · intro k0
            have hval := congrArg (fun (e : (Fin b × Fin 2) ≃ β) => (e (k0, c)).1) heq
            simpa using hval
      exact hinj.trans (ih hβcard p')
    have hsum : good.card =
        ∑ q ∈ pairs, (good.filter (fun σ => (σ (Fin.last b, 0), σ (Fin.last b, 1)) = q)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext σ
        simp only [Finset.mem_biUnion, Finset.mem_filter, pairs, Finset.mem_univ, true_and]
        constructor
        · intro hσ
          exact ⟨(σ (Fin.last b, 0), σ (Fin.last b, 1)), (Finset.mem_filter.mp hσ).2 (Fin.last b), hσ, rfl⟩
        · rintro ⟨_, _, hσ, _⟩
          exact hσ
      · intro q1 _ q2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro σ h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hle1 : good.card ≤ ∑ _q ∈ pairs, (2 ^ b * (b.factorial) ^ 2) := by
      rw [hsum]
      exact Finset.sum_le_sum hfiber
    rw [Finset.sum_const, smul_eq_mul] at hle1
    have hle2 : pairs.card * (2 ^ b * (b.factorial) ^ 2) ≤
        (2 * (b + 1) ^ 2) * (2 ^ b * (b.factorial) ^ 2) :=
      Nat.mul_le_mul_right _ hpairs_le
    calc
      good.card ≤ (2 * (b + 1) ^ 2) * (2 ^ b * (b.factorial) ^ 2) := hle1.trans hle2
      _ = 2 ^ (b + 1) * ((b + 1).factorial) ^ 2 := by
        rw [pow_succ, Nat.factorial_succ]
        ring

lemma card_nonzero_perm_le (b : ℕ) (s : (Fin b × Fin 2) × (Fin b × Fin 2) → Bool) :
    let I := Fin b × Fin 2
    (Finset.univ.filter (fun π : Equiv.Perm I =>
      Matrix.det (fun i j => if i.1 = (π j).1 then (if s (i, j) then -1 else 1) else 0 : Matrix I I ℤ) ≠ 0)).card ≤
    2 ^ b * (b.factorial) ^ 2 := by
  intro I
  let p : Fin b → I → Bool := fun k u => xor (s ((k, 0), u)) (s ((k, 1), u))
  have hbij : (Finset.univ.filter (fun π : Equiv.Perm I =>
      Matrix.det (fun i j => if i.1 = (π j).1 then (if s (i, j) then -1 else 1) else 0 : Matrix I I ℤ) ≠ 0)).card =
      (Finset.univ.filter (fun σ : (Fin b × Fin 2) ≃ I =>
        ∀ k : Fin b, p k (σ (k, 0)) ≠ p k (σ (k, 1)))).card := by
    refine Finset.card_bij (fun π _ => π.symm) ?_ ?_ ?_
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      exact (det_trichotomy b s π).2.mp hπ
    · intro π1 _ π2 _ h
      exact Equiv.symm_bijective.injective h
    · intro σ hσ
      refine ⟨σ.symm, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      exact (det_trichotomy b s σ.symm).2.mpr (by simpa using hσ)
  rw [hbij]
  exact card_good_equiv b (by simp [I, mul_comm]) p

lemma card_pair_fiber_le (b : ℕ) (π0 : Equiv.Perm (Fin b × Fin 2)) :
    let I := Fin b × Fin 2
    let pair := fun (π : Equiv.Perm I) (j k : I) => decide ((π j).1 = (π k).1)
    (Finset.univ.filter (fun π : Equiv.Perm I => pair π = pair π0)).card ≤
    2 ^ b * b.factorial := by
  intro I pair
  let fib := Finset.univ.filter (fun π : Equiv.Perm I => pair π = pair π0)
  let Φ : Equiv.Perm I → (Fin b → Fin b) × (Fin b → Fin 2) :=
    fun π => (fun k => (π (π0.symm (k, 0))).1, fun k => (π (π0.symm (k, 0))).2)
  have hmem : ∀ π ∈ fib, Function.Injective (Φ π).1 := by
    intro π hπ k1 k2 hk
    have hpeq := (Finset.mem_filter.mp hπ).2
    have h1 := congrFun (congrFun hpeq (π0.symm (k1, 0))) (π0.symm (k2, 0))
    simp only [pair, Equiv.apply_symm_apply, decide_eq_decide] at h1
    exact h1.mp hk
  have hinj : Set.InjOn (fun π =>
      if h : Function.Injective (Φ π).1 then
        (Equiv.ofBijective (Φ π).1 (Finite.injective_iff_bijective.mp h), (Φ π).2)
      else (Equiv.refl (Fin b), fun _ => 0)) (fib : Set (Equiv.Perm I)) := by
    intro π1 h1 π2 h2 heq
    simp only [Finset.mem_coe] at h1 h2
    have hi1 := hmem π1 h1
    have hi2 := hmem π2 h2
    simp only [hi1, hi2, ↓reduceDIte, Prod.mk.injEq] at heq
    have hfst : ∀ k : Fin b, (π1 (π0.symm (k, 0))).1 = (π2 (π0.symm (k, 0))).1 :=
      fun k => congrArg (fun (e : Equiv.Perm (Fin b)) => e k) heq.1
    have hsnd : ∀ k : Fin b, (π1 (π0.symm (k, 0))).2 = (π2 (π0.symm (k, 0))).2 :=
      fun k => congrFun heq.2 k
    have h0 : ∀ k : Fin b, π1 (π0.symm (k, 0)) = π2 (π0.symm (k, 0)) :=
      fun k => Prod.ext (hfst k) (hsnd k)
    have hpeq1 := (Finset.mem_filter.mp h1).2
    have hpeq2 := (Finset.mem_filter.mp h2).2
    have h1eq : ∀ k : Fin b, π1 (π0.symm (k, 1)) = π2 (π0.symm (k, 1)) := by
      intro k
      have hp1 : (π1 (π0.symm (k, 1))).1 = (π1 (π0.symm (k, 0))).1 := by
        have h := congrFun (congrFun hpeq1 (π0.symm (k, 1))) (π0.symm (k, 0))
        simpa [pair] using h
      have hp2 : (π2 (π0.symm (k, 1))).1 = (π2 (π0.symm (k, 0))).1 := by
        have h := congrFun (congrFun hpeq2 (π0.symm (k, 1))) (π0.symm (k, 0))
        simpa [pair] using h
      have hne1 : (π1 (π0.symm (k, 1))).2 ≠ (π1 (π0.symm (k, 0))).2 := by
        intro hc
        have hfull : π1 (π0.symm (k, 1)) = π1 (π0.symm (k, 0)) := Prod.ext hp1 hc
        have hcontra := π0.symm.injective (π1.injective hfull)
        have h10 : (1 : Fin 2) = 0 := congrArg Prod.snd hcontra
        exact absurd h10 (by decide)
      have hne2 : (π2 (π0.symm (k, 1))).2 ≠ (π2 (π0.symm (k, 0))).2 := by
        intro hc
        have hfull : π2 (π0.symm (k, 1)) = π2 (π0.symm (k, 0)) := Prod.ext hp2 hc
        have hcontra := π0.symm.injective (π2.injective hfull)
        have h10 : (1 : Fin 2) = 0 := congrArg Prod.snd hcontra
        exact absurd h10 (by decide)
      apply Prod.ext
      · rw [hp1, hp2, hfst k]
      · rw [← hsnd k] at hne2
        generalize (π1 (π0.symm (k, 0))).2 = c0 at hne1 hne2
        generalize (π1 (π0.symm (k, 1))).2 = c1 at hne1
        generalize (π2 (π0.symm (k, 1))).2 = c2 at hne2
        fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> simp_all
    apply Equiv.ext
    intro x
    have hx : x = π0.symm (π0 x) := (π0.symm_apply_apply x).symm
    rw [hx]
    rcases π0 x with ⟨k, c⟩
    fin_cases c
    · exact h0 k
    · exact h1eq k
  have hle := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_fin, mul_comm] using hle

lemma neg_log_one_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  rw [← Real.log_inv]
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x)
    linarith
  have hle : (1 - x)⁻¹ ≤ Real.exp (2 * x) := hinv.trans hexp
  have hlog := Real.log_le_log (inv_pos.mpr hpos) hle
  rwa [Real.log_exp] at hlog

lemma pow_two_le_central_binom (b : ℕ) : 2 ^ b ≤ Nat.choose (2 * b) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have heq : 2 * (b + 1) = (2 * b + 1) + 1 := by omega
    rw [heq, Nat.choose_succ_succ]
    have hsymm : Nat.choose (2 * b + 1) (b + 1) = Nat.choose (2 * b + 1) b := by
      have h1 : 2 * b + 1 = b + (b + 1) := by omega
      rw [h1, Nat.choose_symm_add]
    have hmono : Nat.choose (2 * b) b ≤ Nat.choose (2 * b + 1) b := by
      cases b with
      | zero => simp
      | succ k =>
        rw [Nat.choose_succ_succ]
        exact Nat.le_add_left _ _
    rw [hsymm, pow_succ]
    omega

lemma alpha_le_one (b : ℕ) : (2 : ℝ) ^ b / (Nat.choose (2 * b) b : ℝ) ≤ 1 := by
  have hpos : (0 : ℝ) < (Nat.choose (2 * b) b : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : b ≤ 2 * b)
  rw [div_le_one hpos]
  exact_mod_cast pow_two_le_central_binom b

lemma kl_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (p w : ι → ℝ) (wt : ι → ℕ)
    (t : ℕ) (α N : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hN : 0 < N)
    (hp_pos : ∀ c ∈ C, 0 < p c)
    (hp_sum : ∑ c ∈ C, p c = 1)
    (hp_le : ∀ c ∈ C, p c ≤ 3 / (2 * N))
    (hw_pos : ∀ c ∈ C, 0 < w c)
    (hw_sum : ∑ c ∈ C, w c ≤ 1)
    (hlog_w : ∀ c ∈ C, -Real.log (w c) ≤ (t : ℝ) * α + (wt c : ℝ) * Real.log (4 / α))
    (havg : ∑ c ∈ C, p c * (wt c : ℝ) ≤ (3 / 2 : ℝ) * (t : ℝ) * α) :
    2 * Real.log (2 * N / 3) ≤ 3 * (t : ℝ) * α * (1 + Real.log (4 / α)) := by
  have hKL : ∑ c ∈ C, p c * Real.log (w c / p c) ≤ 0 := by
    have h1 : ∑ c ∈ C, p c * Real.log (w c / p c) ≤ ∑ c ∈ C, p c * (w c / p c - 1) := by
      refine Finset.sum_le_sum fun c hc => ?_
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (hw_pos c hc) (hp_pos c hc))) (hp_pos c hc).le
    have h2 : ∑ c ∈ C, p c * (w c / p c - 1) = (∑ c ∈ C, w c) - 1 := by
      have hterm : ∀ c ∈ C, p c * (w c / p c - 1) = w c - p c := fun c hc => by
        have hpne := (hp_pos c hc).ne'
        field_simp [hpne]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hp_sum]
    linarith
  have hsplit : ∑ c ∈ C, p c * Real.log (w c / p c) =
      (∑ c ∈ C, p c * Real.log (w c)) - (∑ c ∈ C, p c * Real.log (p c)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Real.log_div (hw_pos c hc).ne' (hp_pos c hc).ne']
    ring
  have hneg_p : ∑ c ∈ C, p c * (-Real.log (p c)) ≤ ∑ c ∈ C, p c * (-Real.log (w c)) := by
    have hA : ∑ c ∈ C, p c * (-Real.log (p c)) = -(∑ c ∈ C, p c * Real.log (p c)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hB : ∑ c ∈ C, p c * (-Real.log (w c)) = -(∑ c ∈ C, p c * Real.log (w c)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hA, hB]
    linarith
  have hlow : Real.log (2 * N / 3) ≤ ∑ c ∈ C, p c * (-Real.log (p c)) := by
    have h1 : Real.log (2 * N / 3) = ∑ c ∈ C, p c * Real.log (2 * N / 3) := by
      rw [← Finset.sum_mul, hp_sum, one_mul]
    rw [h1]
    refine Finset.sum_le_sum fun c hc => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hp_pos c hc).le
    rw [← Real.log_inv]
    refine Real.log_le_log (by positivity) ?_
    have hpc := hp_le c hc
    have hp0 := hp_pos c hc
    rw [le_inv_comm₀ (by positivity) hp0]
    have : (2 * N / 3)⁻¹ = 3 / (2 * N) := by field_simp
    rwa [this]
  have hup : ∑ c ∈ C, p c * (-Real.log (w c)) ≤
      (t : ℝ) * α + ((3 / 2 : ℝ) * (t : ℝ) * α) * Real.log (4 / α) := by
    have h1 : ∑ c ∈ C, p c * (-Real.log (w c)) ≤
        ∑ c ∈ C, p c * ((t : ℝ) * α + (wt c : ℝ) * Real.log (4 / α)) :=
      Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hlog_w c hc) (hp_pos c hc).le
    have h2 : ∑ c ∈ C, p c * ((t : ℝ) * α + (wt c : ℝ) * Real.log (4 / α)) =
        (t : ℝ) * α + (∑ c ∈ C, p c * (wt c : ℝ)) * Real.log (4 / α) := by
      have hexp : ∀ c ∈ C, p c * ((t : ℝ) * α + (wt c : ℝ) * Real.log (4 / α)) =
          p c * ((t : ℝ) * α) + (p c * (wt c : ℝ)) * Real.log (4 / α) := fun _ _ => by ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hp_sum, one_mul]
    have hlog4 : 0 ≤ Real.log (4 / α) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hα0]
      linarith
    have h3 : (∑ c ∈ C, p c * (wt c : ℝ)) * Real.log (4 / α) ≤
        ((3 / 2 : ℝ) * (t : ℝ) * α) * Real.log (4 / α) :=
      mul_le_mul_of_nonneg_right havg hlog4
    linarith
  have hta : 0 ≤ (t : ℝ) * α := by positivity
  linarith

theorem main :
    ∀ b : ℕ, 0 < b →
      let I := Fin b × Fin 2
      let S := I × I → Bool
      let P := I → I → Bool
      let pair := fun (π : Equiv.Perm I) (j k : I) => decide ((π j).1 = (π k).1)
      let D := fun (s : S) (π : Equiv.Perm I) =>
        Matrix.det (fun i j => if i.1 = (π j).1 then (if s (i,j) then -1 else 1) else 0 : Matrix I I ℤ)
      let α := (2 : ℝ)^b / (Nat.choose (2*b) b : ℝ)
      let N := ((2*b).factorial : ℝ) / ((2 : ℝ)^b * (b.factorial : ℝ))
      ∀ (R t : ℕ) (list : Fin R → Fin t → S) (read : Fin R → (Fin t → ℤ) → P),
        0 < R →
        (∀ π : Equiv.Perm I, 2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter (fun u =>
          read u (fun h => D (list u h) π) = pair π)).card) →
        2 * Real.log (2*N/3) ≤ 3*(t : ℝ)*α*(1 + Real.log (4/α)) := by
  dsimp only
  intro b hb R t list read hR hrec
  let I := Fin b × Fin 2
  let pair : Equiv.Perm I → I → I → Bool := fun π j k => decide ((π j).1 = (π k).1)
  let D : (I × I → Bool) → Equiv.Perm I → ℤ := fun s π =>
    Matrix.det (fun i j => if i.1 = (π j).1 then (if s (i, j) then -1 else 1) else 0 : Matrix I I ℤ)
  let α : ℝ := (2 : ℝ) ^ b / (Nat.choose (2 * b) b : ℝ)
  let N : ℝ := ((2 * b).factorial : ℝ) / ((2 : ℝ) ^ b * (b.factorial : ℝ))
  have hch_pos : (0 : ℝ) < (Nat.choose (2 * b) b : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : b ≤ 2 * b)
  have hα_pos : 0 < α := div_pos (by positivity) hch_pos
  have hα_le1 : α ≤ 1 := alpha_le_one b
  have hN_pos : 0 < N := by
    dsimp [N]
    have h1 : (0 : ℝ) < ((2 * b).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h2 : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hcardI : Fintype.card I = 2 * b := by simp [I, mul_comm]
  have hcardPerm : Fintype.card (Equiv.Perm I) = (2 * b).factorial := by
    rw [Fintype.card_perm, hcardI]
  have hdouble :
      ∑ u : Fin R, (Finset.univ.filter (fun π : Equiv.Perm I =>
        read u (fun h => D (list u h) π) = pair π)).card =
      ∑ π : Equiv.Perm I, (Finset.univ.filter (fun u : Fin R =>
        read u (fun h => D (list u h) π) = pair π)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have htot : 2 * R * (2 * b).factorial ≤
      3 * ∑ u : Fin R, (Finset.univ.filter (fun π : Equiv.Perm I =>
        read u (fun h => D (list u h) π) = pair π)).card := by
    rw [hdouble, Finset.mul_sum]
    have hsum_le : ∑ _π : Equiv.Perm I, (2 * R) ≤
        ∑ π : Equiv.Perm I, 3 * (Finset.univ.filter (fun u : Fin R =>
          read u (fun h => D (list u h) π) = pair π)).card :=
      Finset.sum_le_sum fun π _ => hrec π
    simpa [Finset.sum_const, smul_eq_mul, hcardPerm, mul_comm, mul_left_comm, mul_assoc] using hsum_le
  have hex_u : ∃ u0 : Fin R,
      2 * (2 * b).factorial ≤
      3 * (Finset.univ.filter (fun π : Equiv.Perm I =>
        read u0 (fun h => D (list u0 h) π) = pair π)).card := by
    by_contra hall
    push Not at hall
    have hlt : ∑ u : Fin R, 3 * (Finset.univ.filter (fun π : Equiv.Perm I =>
        read u (fun h => D (list u h) π) = pair π)).card <
        ∑ _u : Fin R, (2 * (2 * b).factorial) := by
      refine Finset.sum_lt_sum_of_nonempty ?_ fun u _ => hall u
      have : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
      exact Finset.univ_nonempty
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have heq : R * (2 * (2 * b).factorial) = 2 * R * (2 * b).factorial := by ring
    omega
  rcases hex_u with ⟨u0, hu0⟩
  let G : Finset (Equiv.Perm I) :=
    Finset.univ.filter (fun π : Equiv.Perm I => read u0 (fun h => D (list u0 h) π) = pair π)
  have hG_nat : 2 * (2 * b).factorial ≤ 3 * G.card := hu0
  have hG_pos : (0 : ℝ) < (G.card : ℝ) := by
    have hfac : 0 < (2 * b).factorial := Nat.factorial_pos _
    have hpos : 0 < G.card := by omega
    exact_mod_cast hpos
  let code : Equiv.Perm I → (Fin t → Fin 3) := fun π h =>
    if D (list u0 h) π = 0 then 0 else if D (list u0 h) π = (2 : ℤ) ^ b then 1 else 2
  have hcode_eq : ∀ π1 π2 : Equiv.Perm I, code π1 = code π2 →
      (fun h => D (list u0 h) π1) = (fun h => D (list u0 h) π2) := by
    intro π1 π2 hc
    funext h
    have hch := congrFun hc h
    have h1 : D (list u0 h) π1 = 0 ∨ D (list u0 h) π1 = (2 : ℤ) ^ b ∨
        D (list u0 h) π1 = -((2 : ℤ) ^ b) := (det_trichotomy b (list u0 h) π1).1
    have h2 : D (list u0 h) π2 = 0 ∨ D (list u0 h) π2 = (2 : ℤ) ^ b ∨
        D (list u0 h) π2 = -((2 : ℤ) ^ b) := (det_trichotomy b (list u0 h) π2).1
    have h2pos : (0 : ℤ) < (2 : ℤ) ^ b := by positivity
    have h2ne0 : (2 : ℤ) ^ b ≠ 0 := h2pos.ne'
    have hm2ne0 : -((2 : ℤ) ^ b) ≠ 0 := by omega
    have hm2ne2 : -((2 : ℤ) ^ b) ≠ (2 : ℤ) ^ b := by omega
    dsimp [code] at hch
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · rw [h1, h2]
    · simp only [h1, h2, h2ne0, ↓reduceIte] at hch; exact absurd hch (by decide)
    · simp only [h1, h2, hm2ne0, hm2ne2, ↓reduceIte] at hch; exact absurd hch (by decide)
    · simp only [h1, h2, h2ne0, ↓reduceIte] at hch; exact absurd hch (by decide)
    · rw [h1, h2]
    · simp only [h1, h2, h2ne0, hm2ne0, hm2ne2, ↓reduceIte] at hch; exact absurd hch (by decide)
    · simp only [h1, h2, hm2ne0, hm2ne2, ↓reduceIte] at hch; exact absurd hch (by decide)
    · simp only [h1, h2, h2ne0, hm2ne0, hm2ne2, ↓reduceIte] at hch; exact absurd hch (by decide)
    · rw [h1, h2]
  let F : (Fin t → Fin 3) → Finset (Equiv.Perm I) := fun c => G.filter (fun π => code π = c)
  have hF_le : ∀ c : Fin t → Fin 3, (F c).card ≤ 2 ^ b * b.factorial := by
    intro c
    rcases (F c).eq_empty_or_nonempty with hem | ⟨π0, hπ0⟩
    · simp [hem]
    · have hsub : F c ⊆ Finset.univ.filter (fun π : Equiv.Perm I => pair π = pair π0) := by
        intro π hπ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hc_eq : code π = code π0 :=
          (Finset.mem_filter.mp hπ).2.trans (Finset.mem_filter.mp hπ0).2.symm
        have hd_eq := hcode_eq π π0 hc_eq
        have hr1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hπ).1).2
        have hr0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hπ0).1).2
        rw [← hr1, ← hr0, hd_eq]
      exact (Finset.card_le_card hsub).trans (card_pair_fiber_le b π0)
  let qf : Fin 3 → ℝ := fun z => if z = 0 then 1 - α / 2 else α / 4
  have hqf_pos : ∀ z : Fin 3, 0 < qf z := by
    intro z; fin_cases z <;> dsimp [qf] <;> linarith
  have hqf_sum : ∑ z : Fin 3, qf z = 1 := by
    rw [Fin.sum_univ_three]; dsimp [qf]; ring
  let w : (Fin t → Fin 3) → ℝ := fun c => ∏ h : Fin t, qf (c h)
  have hw_pos : ∀ c, 0 < w c := fun c => Finset.prod_pos fun h _ => hqf_pos (c h)
  have hw_sum : ∑ c : Fin t → Fin 3, w c = 1 := by
    have h := Fintype.prod_sum (fun (_ : Fin t) (z : Fin 3) => qf z)
    simp only [hqf_sum, Finset.prod_const_one] at h
    exact h.symm
  let C := Finset.univ.filter (fun c : Fin t → Fin 3 => 0 < (F c).card)
  let p : (Fin t → Fin 3) → ℝ := fun c => ((F c).card : ℝ) / (G.card : ℝ)
  let wt : (Fin t → Fin 3) → ℕ := fun c => (Finset.univ.filter (fun h : Fin t => c h ≠ 0)).card
  have hG_part : ∑ c ∈ C, ((F c).card : ℝ) = (G.card : ℝ) := by
    have hnat : ∑ c ∈ C, (F c).card = G.card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext π
        simp only [Finset.mem_biUnion, C, F, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, _, hπ, _⟩; exact hπ
        · intro hπ
          exact ⟨code π, Finset.card_pos.mpr ⟨π, Finset.mem_filter.mpr ⟨hπ, rfl⟩⟩, hπ, rfl⟩
      · intro c1 _ c2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro π h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    exact_mod_cast hnat
  have hp_sum : ∑ c ∈ C, p c = 1 := by
    dsimp [p]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hG_part]
    exact mul_inv_cancel₀ hG_pos.ne'
  have hp_pos : ∀ c ∈ C, 0 < p c := fun c hc => by
    have hFc : (0 : ℝ) < ((F c).card : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hc).2
    exact div_pos hFc hG_pos
  have hp_le : ∀ c ∈ C, p c ≤ 3 / (2 * N) := fun c _ => by
    dsimp [p, N]
    have hFc_le_r : ((F c).card : ℝ) ≤ (2 : ℝ) ^ b * (b.factorial : ℝ) := by exact_mod_cast hF_le c
    have hG_ge : (2 : ℝ) * ((2 * b).factorial : ℝ) ≤ 3 * (G.card : ℝ) := by exact_mod_cast hG_nat
    have h2bf : (0 : ℝ) < ((2 * b).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hbf : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hden : 0 < (2 : ℝ) ^ b * (b.factorial : ℝ) := by positivity
    rw [div_le_div_iff₀ hG_pos (by positivity)]
    have hrhs : 3 * (G.card : ℝ) ≥ 2 * ((2 * b).factorial : ℝ) := hG_ge
    have h1 : ((F c).card : ℝ) * (2 * (((2 * b).factorial : ℝ) / ((2 : ℝ) ^ b * (b.factorial : ℝ)))) ≤
        ((2 : ℝ) ^ b * (b.factorial : ℝ)) * (2 * (((2 * b).factorial : ℝ) / ((2 : ℝ) ^ b * (b.factorial : ℝ)))) :=
      mul_le_mul_of_nonneg_right hFc_le_r (by positivity)
    have h2 : ((2 : ℝ) ^ b * (b.factorial : ℝ)) * (2 * (((2 * b).factorial : ℝ) / ((2 : ℝ) ^ b * (b.factorial : ℝ)))) =
        2 * ((2 * b).factorial : ℝ) := by field_simp [hden.ne']
    linarith
  have hw_sumC : ∑ c ∈ C, w c ≤ 1 := by
    rw [← hw_sum]
    exact Finset.sum_le_univ_sum_of_nonneg fun c => (hw_pos c).le
  have hlog_w : ∀ c ∈ C, -Real.log (w c) ≤ (t : ℝ) * α + (wt c : ℝ) * Real.log (4 / α) := by
    intro c _
    have hprod_log : Real.log (w c) = ∑ h : Fin t, Real.log (qf (c h)) := by
      dsimp [w]
      exact Real.log_prod fun h _ => (hqf_pos (c h)).ne'
    rw [hprod_log, ← Finset.sum_neg_distrib]
    have hterm : ∀ h : Fin t, -Real.log (qf (c h)) ≤ (if c h = 0 then α else Real.log (4 / α)) := by
      intro h
      by_cases h0 : c h = 0
      · simp only [h0, qf, ↓reduceIte]
        have := neg_log_one_sub_le (α / 2) (by linarith) (by linarith)
        linarith
      · simp only [h0, qf, ↓reduceIte]
        rw [← Real.log_inv]
        have : (α / 4)⁻¹ = 4 / α := by field_simp
        rw [this]
    have hsum_le := Finset.sum_le_sum fun h (_ : h ∈ Finset.univ) => hterm h
    have hrhs : ∑ h : Fin t, (if c h = 0 then α else Real.log (4 / α)) =
        ((Finset.univ.filter (fun h : Fin t => c h = 0)).card : ℝ) * α +
        (wt c : ℝ) * Real.log (4 / α) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    rw [hrhs] at hsum_le
    have hzero_le : ((Finset.univ.filter (fun h : Fin t => c h = 0)).card : ℝ) ≤ (t : ℝ) := by
      have : (Finset.univ.filter (fun h : Fin t => c h = 0)).card ≤ t := by
        simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin t)) (fun h => c h = 0))
      exact_mod_cast this
    have hmul := mul_le_mul_of_nonneg_right hzero_le hα_pos.le
    linarith
  have havg : ∑ c ∈ C, p c * (wt c : ℝ) ≤ (3 / 2 : ℝ) * (t : ℝ) * α := by
    have hsum_wt : ∑ c ∈ C, ((F c).card : ℝ) * (wt c : ℝ) = ∑ π ∈ G, (wt (code π) : ℝ) := by
      have hnat : ∑ c ∈ C, (F c).card * wt c = ∑ π ∈ G, wt (code π) := by
        have hstep : ∀ c ∈ C, (F c).card * wt c = ∑ π ∈ F c, wt (code π) := by
          intro c _
          have : ∀ π ∈ F c, wt (code π) = wt c := fun π hπ => by rw [(Finset.mem_filter.mp hπ).2]
          rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_biUnion]
        · congr 1
          ext π
          simp only [Finset.mem_biUnion, C, F, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨_, _, hπ, _⟩; exact hπ
          · intro hπ
            exact ⟨code π, Finset.card_pos.mpr ⟨π, Finset.mem_filter.mpr ⟨hπ, rfl⟩⟩, hπ, rfl⟩
        · intro c1 _ c2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro π h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      exact_mod_cast hnat
    have hG_wt_le : ∑ π ∈ G, wt (code π) ≤ t * (2 ^ b * (b.factorial) ^ 2) := by
      have hswap : ∑ π ∈ G, wt (code π) =
          ∑ h : Fin t, (G.filter (fun π => code π h ≠ 0)).card := by
        simp only [wt, Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap]
      have hle_each : ∀ h : Fin t, (G.filter (fun π => code π h ≠ 0)).card ≤
          2 ^ b * (b.factorial) ^ 2 := by
        intro h
        have hsub : G.filter (fun π => code π h ≠ 0) ⊆
            Finset.univ.filter (fun π : Equiv.Perm I => D (list u0 h) π ≠ 0) := by
          intro π hπ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hne0 := (Finset.mem_filter.mp hπ).2
          intro hd0
          apply hne0
          simp [code, hd0]
        exact (Finset.card_le_card hsub).trans (card_nonzero_perm_le b (list u0 h))
      calc
        ∑ h : Fin t, (G.filter (fun π => code π h ≠ 0)).card ≤
            ∑ _h : Fin t, (2 ^ b * (b.factorial) ^ 2) := Finset.sum_le_sum fun h _ => hle_each h
        _ = t * (2 ^ b * (b.factorial) ^ 2) := by simp
    have hα_fac : α * ((2 * b).factorial : ℝ) = (2 : ℝ) ^ b * (b.factorial : ℝ) ^ 2 := by
      dsimp [α]
      have hch := Nat.choose_mul_factorial_mul_factorial (by omega : b ≤ 2 * b)
      have h2b : 2 * b - b = b := by omega
      rw [h2b] at hch
      have hch_r : (Nat.choose (2 * b) b : ℝ) * (b.factorial : ℝ) * (b.factorial : ℝ) =
          ((2 * b).factorial : ℝ) := by exact_mod_cast hch
      field_simp [hch_pos.ne']
      nlinarith
    have hG_ge : (2 : ℝ) * ((2 * b).factorial : ℝ) ≤ 3 * (G.card : ℝ) := by exact_mod_cast hG_nat
    have hsum_r : ∑ c ∈ C, p c * (wt c : ℝ) = (∑ π ∈ G, (wt (code π) : ℝ)) / (G.card : ℝ) := by
      rw [← hsum_wt]
      dsimp [p]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hsum_r, div_le_iff₀ hG_pos]
    have hle_r : ∑ π ∈ G, (wt (code π) : ℝ) ≤ (t : ℝ) * ((2 : ℝ) ^ b * (b.factorial : ℝ) ^ 2) := by
      exact_mod_cast hG_wt_le
    rw [← hα_fac] at hle_r
    have ht_nn : (0 : ℝ) ≤ (t : ℝ) * α := by positivity
    nlinarith
  exact kl_step C p w wt t α N hα_pos hα_le1 hN_pos hp_pos hp_sum hp_le (fun c _ => hw_pos c)
    hw_sumC hlog_w havg

end PEqualNP.Outside.L_lib_1030_aux

theorem PEqualNP.Outside.L_lib_1030 : ∀ b : ℕ, 0 < b →
  let I := Fin b × Fin 2
  let S := I × I → Bool
  let P := I → I → Bool
  let pair := fun (π : Equiv.Perm I) (j k : I) => decide ((π j).1 = (π k).1)
  let D := fun (s : S) (π : Equiv.Perm I) =>
    Matrix.det (fun i j => if i.1 = (π j).1 then (if s (i,j) then -1 else 1) else 0 : Matrix I I ℤ)
  let α := (2 : ℝ)^b / (Nat.choose (2*b) b : ℝ)
  let N := ((2*b).factorial : ℝ) / ((2 : ℝ)^b * (b.factorial : ℝ))
  ∀ (R t : ℕ) (list : Fin R → Fin t → S) (read : Fin R → (Fin t → ℤ) → P),
    0 < R →
    (∀ π : Equiv.Perm I, 2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter (fun u =>
      read u (fun h => D (list u h) π) = pair π)).card) →
    2 * Real.log (2*N/3) ≤ 3*(t : ℝ)*α*(1 + Real.log (4/α)) :=
  PEqualNP.Outside.L_lib_1030_aux.main

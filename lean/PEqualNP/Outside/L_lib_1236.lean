import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_lib_1236_aux

private lemma part1 (m N : ℕ) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool)
    (hsym : ∀ u v, v ∈ H u ↔ u ∈ H v) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∃ A B : (Fin m → Bool) →
      ↥(((Finset.univ : Finset (Fin N)).filter (fun v => side v = false)).powerset.image
        (fun S => S.biUnion (fun v => (H v).filter (fun w => side w = true)))) → ℕ,
      ∀ f g,
        ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
          (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
          ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card = ∑ U, A f U * B g U := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let lhs := (Finset.univ : Finset (Fin N)).filter (fun v => side v = false)
  let rhs := (Finset.univ : Finset (Fin N)).filter (fun v => side v = true)
  let forb : Finset (Fin N) → Finset (Fin N) := fun S =>
    S.biUnion (fun v => (H v).filter (fun w => side w = true))
  let unions := lhs.powerset.image forb
  let validL : (Fin m → Bool) → Finset (Fin N) → Prop := fun f S =>
    S ⊆ lhs ∧ (∀ v ∈ S, left f v = true) ∧ (∀ u ∈ S, ∀ v ∈ H u, v ∉ S)
  let validR : (Fin m → Bool) → Finset (Fin N) → Finset (Fin N) → Prop := fun g U T =>
    T ⊆ rhs ∧ (∀ v ∈ T, right g v = true) ∧ (∀ u ∈ T, ∀ v ∈ H u, v ∉ T) ∧ Disjoint T U
  let A : (Fin m → Bool) → ↥unions → ℕ := fun f U =>
    (lhs.powerset.filter (fun S => validL f S ∧ forb S = U.1)).card
  let B : (Fin m → Bool) → ↥unions → ℕ := fun g U =>
    (rhs.powerset.filter (fun T => validR g U.1 T)).card
  refine ⟨A, B, fun f g => ?_⟩
  let GoodI : Finset (Finset (Fin N)) := (Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
    (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
    ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)
  have hmaps : ∀ I ∈ GoodI, forb (I ∩ lhs) ∈ unions := fun I _ =>
    Finset.mem_image.mpr ⟨I ∩ lhs, Finset.mem_powerset.mpr Finset.inter_subset_right, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, ← Finset.sum_attach unions]
  congr 1; ext U
  have hdisjLR : Disjoint lhs rhs := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
  have hprod : (GoodI.filter (fun I => forb (I ∩ lhs) = U.1)).card =
      ((lhs.powerset.filter (fun S => validL f S ∧ forb S = U.1)) ×ˢ
       (rhs.powerset.filter (fun T => validR g U.1 T))).card := by
    refine Finset.card_bij (fun I _ => (I ∩ lhs, I ∩ rhs)) ?_ ?_ ?_
    · intro I hI
      have hIG := (Finset.mem_filter.mp hI).1
      have hIU := (Finset.mem_filter.mp hI).2
      have hIprop := (Finset.mem_filter.mp hIG).2
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ⟨?_, ?_, ?_⟩, hIU⟩
        · exact Finset.inter_subset_right
        · intro v hv
          have hvI := (Finset.mem_inter.mp hv).1
          have hvL := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
          have h := hIprop.1 v hvI
          simpa [hvL] using h
        · intro u hu v hv hvS
          exact hIprop.2 u (Finset.mem_inter.mp hu).1 v hv (Finset.mem_inter.mp hvS).1
      · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_, ?_, ?_, ?_⟩
        · exact Finset.inter_subset_right
        · intro v hv
          have hvI := (Finset.mem_inter.mp hv).1
          have hvR := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
          have h := hIprop.1 v hvI
          simpa [hvR] using h
        · intro u hu v hv hvT
          exact hIprop.2 u (Finset.mem_inter.mp hu).1 v hv (Finset.mem_inter.mp hvT).1
        · rw [← hIU]
          refine Finset.disjoint_left.mpr fun w hwT hwF => ?_
          rcases Finset.mem_biUnion.mp hwF with ⟨u, huS, hwu⟩
          have hwH : w ∈ H u := (Finset.mem_filter.mp hwu).1
          exact hIprop.2 u (Finset.mem_inter.mp huS).1 w hwH (Finset.mem_inter.mp hwT).1
    · intro I1 _ I2 _ heq
      have h1 : I1 ∩ lhs = I2 ∩ lhs := (Prod.mk.inj heq).1
      have h2 : I1 ∩ rhs = I2 ∩ rhs := (Prod.mk.inj heq).2
      ext v
      have hsplit : ∀ I : Finset (Fin N), v ∈ I ↔ v ∈ I ∩ lhs ∨ v ∈ I ∩ rhs := fun I => by
        simp only [Finset.mem_inter, lhs, rhs, Finset.mem_filter, Finset.mem_univ, true_and]
        cases side v <;> simp
      rw [hsplit I1, hsplit I2, h1, h2]
    · intro ⟨S, T⟩ hST
      rcases Finset.mem_product.mp hST with ⟨hSmem, hTmem⟩
      rcases (Finset.mem_filter.mp hSmem).2 with ⟨hS, hSU⟩
      have hT := (Finset.mem_filter.mp hTmem).2
      have hST_L : (S ∪ T) ∩ lhs = S := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hvS | hvT, hvL⟩
          · exact hvS
          · exact absurd (hT.1 hvT) (Finset.disjoint_left.mp hdisjLR hvL)
        · intro hvS; exact ⟨Or.inl hvS, hS.1 hvS⟩
      have hST_R : (S ∪ T) ∩ rhs = T := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hvS | hvT, hvR⟩
          · exact absurd hvR (Finset.disjoint_left.mp hdisjLR (hS.1 hvS))
          · exact hvT
        · intro hvT; exact ⟨Or.inr hvT, hT.1 hvT⟩
      refine ⟨S ∪ T, ?_, Prod.ext hST_L hST_R⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, by rw [hST_L, hSU]⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with hvS | hvT
        · have hvL : side v = false := (Finset.mem_filter.mp (hS.1 hvS)).2
          simpa [hvL] using hS.2.1 v hvS
        · have hvR : side v = true := (Finset.mem_filter.mp (hT.1 hvT)).2
          simpa [hvR] using hT.2.1 v hvT
      · intro u hu v hv hvU
        rcases Finset.mem_union.mp hu with huS | huT
        · rcases Finset.mem_union.mp hvU with hvS | hvT
          · exact hS.2.2 u huS v hv hvS
          · have hvR : side v = true := (Finset.mem_filter.mp (hT.1 hvT)).2
            have hvF : v ∈ U.1 := hSU ▸ Finset.mem_biUnion.mpr ⟨u, huS, Finset.mem_filter.mpr ⟨hv, hvR⟩⟩
            exact Finset.disjoint_left.mp hT.2.2.2 hvT hvF
        · rcases Finset.mem_union.mp hvU with hvS | hvT
          · have huR : side u = true := (Finset.mem_filter.mp (hT.1 huT)).2
            have huH : u ∈ H v := (hsym u v).mp hv
            have huF : u ∈ U.1 := hSU ▸ Finset.mem_biUnion.mpr ⟨v, hvS, Finset.mem_filter.mpr ⟨huH, huR⟩⟩
            exact Finset.disjoint_left.mp hT.2.2.2 huT huF
          · exact hT.2.2.1 u huT v hv hvT
  rw [hprod, Finset.card_product]

private lemma card_monomials (q d : ℕ) :
    ((Finset.univ : Finset (Fin q → Fin (d + 1))).filter
      (fun α => (∑ j : Fin q, (α j).val) ≤ d)).card = Nat.choose (q + d) d := by
  induction q generalizing d with
  | zero =>
    have h1 : (Finset.univ : Finset (Fin 0 → Fin (d + 1))).filter
        (fun α => (∑ j : Fin 0, (α j).val) ≤ d) = Finset.univ := by
      ext α; simp
    rw [h1, Finset.card_univ]
    simp
  | succ q ih =>
    induction d with
    | zero =>
      have h1 : (Finset.univ : Finset (Fin (q + 1) → Fin 1)).filter
          (fun α => (∑ j : Fin (q + 1), (α j).val) ≤ 0) = Finset.univ := by
        ext α; simp
      rw [h1, Finset.card_univ]
      simp
    | succ d ihd =>
      let S := (Finset.univ : Finset (Fin (q + 1) → Fin (d + 2))).filter
        (fun α => (∑ j : Fin (q + 1), (α j).val) ≤ d + 1)
      let S0 := S.filter (fun α => (α 0).val = 0)
      let S1 := S.filter (fun α => (α 0).val ≠ 0)
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_filter]
        intro α _ h1 h2; exact h2 h1
      have hunion : S0 ∪ S1 = S := by
        ext α
        simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        tauto
      have hS0 : S0.card = Nat.choose (q + (d + 1)) (d + 1) := by
        rw [← ih (d + 1)]
        refine Finset.card_bij (fun α _ i => α i.succ) ?_ ?_ ?_
        · intro α hα
          simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
          have hsum := Fin.sum_univ_succ (fun i : Fin (q + 1) => (α i).val)
          rw [hα.2, zero_add] at hsum
          omega
        · intro α1 hα1 α2 hα2 heq
          simp only [S0, Finset.mem_filter] at hα1 hα2
          funext i
          refine Fin.cases ?_ (fun i' => congrFun heq i') i
          exact Fin.ext (hα1.2.trans hα2.2.symm)
        · intro β hβ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
          refine ⟨Fin.cons 0 β, ?_, by funext i; simp⟩
          simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero, Fin.val_zero]
          refine ⟨?_, trivial⟩
          rw [Fin.sum_univ_succ]
          simpa using hβ
      have hS1 : S1.card = Nat.choose (q + 1 + d) d := by
        rw [← ihd]
        refine Finset.card_bij
          (fun α hα => fun i : Fin (q + 1) =>
            if hi : i = 0 then ⟨(α 0).val - 1, by
              have hmem := (Finset.mem_filter.mp (Finset.mem_filter.mp hα).1).2
              have hle : (α 0).val ≤ ∑ j : Fin (q + 1), (α j).val :=
                Finset.single_le_sum (f := fun j : Fin (q + 1) => (α j).val)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
              have hne := (Finset.mem_filter.mp hα).2
              omega⟩
            else ⟨(α i).val, by
              have hmem := (Finset.mem_filter.mp (Finset.mem_filter.mp hα).1).2
              have hne := (Finset.mem_filter.mp hα).2
              have hsum := Fin.sum_univ_succ (fun j : Fin (q + 1) => (α j).val)
              obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero hi
              have hle : (α i'.succ).val ≤ ∑ j : Fin q, (α j.succ).val :=
                Finset.single_le_sum (f := fun j : Fin q => (α j.succ).val)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ i')
              omega⟩) ?_ ?_ ?_
        · intro α hα
          simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
          rw [Fin.sum_univ_succ]
          have hsum := Fin.sum_univ_succ (fun j : Fin (q + 1) => (α j).val)
          simp only [↓reduceDIte, Fin.succ_ne_zero]
          omega
        · intro α1 hα1 α2 hα2 heq
          simp only [S1, Finset.mem_filter] at hα1 hα2
          funext i
          refine Fin.cases ?_ (fun i' => ?_) i
          · have h0 := congrArg Fin.val (congrFun heq 0)
            simp only [↓reduceDIte] at h0
            exact Fin.ext (by omega)
          · have hi := congrArg Fin.val (congrFun heq i'.succ)
            simp only [Fin.succ_ne_zero, ↓reduceDIte] at hi
            exact Fin.ext hi
        · intro β hβ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
          let α : Fin (q + 1) → Fin (d + 2) := fun i =>
            if i = 0 then ⟨(β 0).val + 1, by omega⟩ else ⟨(β i).val, by omega⟩
          refine ⟨α, ?_, ?_⟩
          · simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, by simp [α]⟩
            rw [Fin.sum_univ_succ]
            have hsum := Fin.sum_univ_succ (fun j : Fin (q + 1) => (β j).val)
            simp only [α, ↓reduceIte, Fin.succ_ne_zero]
            omega
          · funext i
            refine Fin.cases ?_ (fun i' => ?_) i
            · apply Fin.ext; simp [α]
            · apply Fin.ext; simp [α]
      change S.card = Nat.choose (q + 1 + (d + 1)) (d + 1)
      rw [← hunion, Finset.card_union_of_disjoint hdisj, hS0, hS1]
      have h1 : q + 1 + (d + 1) = (q + d + 1) + 1 := by omega
      have h2 : q + (d + 1) = q + d + 1 := by omega
      have h3 : q + 1 + d = q + d + 1 := by omega
      rw [h1, h2, h3, add_comm, ← Nat.choose_succ_succ]

private lemma walsh_mul_transpose (m : ℕ) (e : (Fin m → Bool) ≃ (Fin m → Bool)) :
    let W := Fin m → Bool
    let M : Matrix W W ℚ := fun f g =>
      1 - 2 * (if ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card % 2 = 1
        then (1 : ℚ) else 0)
    M * M.transpose = ((2 : ℚ) ^ m) • (1 : Matrix W W ℚ) := by
  intro W M
  have hM : ∀ f g : W, M f g = ∏ i : Fin m, if (e f i && g i) = true then (-1 : ℚ) else 1 := by
    intro f g
    have hprod : (∏ i : Fin m, if (e f i && g i) = true then (-1 : ℚ) else 1) =
        (-1 : ℚ) ^ ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [hprod]
    dsimp only [M]
    rcases Nat.mod_two_eq_zero_or_one ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card with h | h
    · rw [h]; simp only [zero_ne_one, ↓reduceIte, mul_zero, sub_zero]
      have hev : Even ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card :=
        Nat.even_iff.mpr h
      exact hev.neg_one_pow.symm
    · rw [h]; simp only [↓reduceIte, mul_one]
      have hodd : Odd ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card :=
        Nat.odd_iff.mpr h
      rw [hodd.neg_one_pow]; norm_num
  ext f1 f2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [hM]
  have hcomb : ∀ g : W,
      (∏ i : Fin m, if (e f1 i && g i) = true then (-1 : ℚ) else 1) *
      (∏ i : Fin m, if (e f2 i && g i) = true then (-1 : ℚ) else 1) =
      ∏ i : Fin m, if (xor (e f1 i) (e f2 i) && g i) = true then (-1 : ℚ) else 1 := by
    intro g
    rw [← Finset.prod_mul_distrib]
    congr 1; ext i
    cases e f1 i <;> cases e f2 i <;> cases g i <;> norm_num
  simp_rw [hcomb]
  have hps := (Fintype.prod_sum (fun (i : Fin m) (b : Bool) =>
    if (xor (e f1 i) (e f2 i) && b) = true then (-1 : ℚ) else 1)).symm
  rw [hps]
  by_cases hf : f1 = f2
  · subst hf
    simp only [↓reduceIte, mul_one]
    have h1 : ∀ i : Fin m, (∑ b : Bool, if (xor (e f1 i) (e f1 i) && b) = true then (-1 : ℚ) else 1) = 2 := by
      intro i; cases e f1 i <;> norm_num
    simp [h1]
  · simp only [hf, ↓reduceIte, mul_zero]
    have hne : e f1 ≠ e f2 := fun h => hf (e.injective h)
    have hex : ∃ i : Fin m, e f1 i ≠ e f2 i := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    rcases hex with ⟨i0, hi0⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    cases h1 : e f1 i0 <;> cases h2 : e f2 i0 <;> simp_all <;> norm_num

private lemma deg_bound_from_choose (m q d : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m)
    (hch : 2 ^ m ≤ Nat.choose (q + d) d) : m < 4 * d := by
  by_contra hle
  push Not at hle
  have hm : 1 ≤ m := le_trans hq hqm
  have h1 : 2 ^ m ≤ Nat.choose (m + d) d :=
    hch.trans (Nat.choose_le_choose d (by omega))
  have hbinom : Nat.choose (m + d) d * 4 ^ m ≤ 5 ^ (m + d) := by
    have hsum := add_pow 1 4 (m + d)
    have h5 : (1 + 4 : ℕ) ^ (m + d) = 5 ^ (m + d) := by norm_num
    rw [h5] at hsum
    have hmem : d ∈ Finset.range (m + d + 1) := Finset.mem_range.mpr (by omega)
    have hle_sum := Finset.single_le_sum (f := fun k => 1 ^ k * 4 ^ (m + d - k) * Nat.choose (m + d) k)
      (fun _ _ => Nat.zero_le _) hmem
    have hsub : m + d - d = m := by omega
    rw [one_pow, one_mul, hsub, mul_comm] at hle_sum
    exact hle_sum.trans (le_of_eq hsum.symm)
  have h2 : 2 ^ m * 4 ^ m ≤ 5 ^ (m + d) :=
    (Nat.mul_le_mul_right (4 ^ m) h1).trans hbinom
  have h3 : (2 ^ m * 4 ^ m) ^ 4 ≤ (5 ^ (m + d)) ^ 4 := Nat.pow_le_pow_left h2 4
  have hLHS : (2 ^ m * 4 ^ m) ^ 4 = 4096 ^ m := by
    calc (2 ^ m * 4 ^ m) ^ 4 = ((2 * 4) ^ m) ^ 4 := by rw [← mul_pow]
      _ = (8 ^ 4) ^ m := by rw [← pow_mul, mul_comm m 4, pow_mul]
      _ = 4096 ^ m := by norm_num
  have hRHS : (5 ^ (m + d)) ^ 4 ≤ 3125 ^ m := by
    calc (5 ^ (m + d)) ^ 4 = 5 ^ (4 * m + 4 * d) := by rw [← pow_mul]; ring_nf
      _ ≤ 5 ^ (5 * m) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (5 ^ 5) ^ m := by rw [pow_mul]
      _ = 3125 ^ m := by norm_num
  have hbad : 4096 ^ m ≤ 3125 ^ m := by omega
  have hlt : 3125 ^ m < 4096 ^ m := Nat.pow_lt_pow_left (by decide) (by omega)
  omega

private lemma eval_eq_sum_range_of_le (Q : Polynomial ℚ) (d : ℕ) (hd : Q.natDegree ≤ d) (x : ℚ) :
    Q.eval x = ∑ k ∈ Finset.range (d + 1), Q.coeff k * x ^ k := by
  rw [Polynomial.eval_eq_sum]
  refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr ?_) (fun k _ hk => ?_)
  · have hle : k ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    omega
  · simp [Polynomial.notMem_support_iff.mp hk]

private lemma part2 (m q : ℕ) (hq : 1 ≤ q)
    (A B : (Fin m → Bool) → Fin q → ℕ)
    (P : Polynomial ℚ) (e : (Fin m → Bool) ≃ (Fin m → Bool))
    (hP : ∀ f g, P.eval ((∑ U : Fin q, A f U * B g U : ℕ) : ℚ) =
      (if ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card % 2 = 1
       then (1 : ℚ) else 0)) :
    2 ^ m ≤ Nat.choose (q + P.natDegree) P.natDegree ∧
    (q ≤ m → m < 4 * P.natDegree) := by
  let W := Fin m → Bool
  let d := P.natDegree
  let K := (Finset.univ : Finset (Fin q → Fin (d + 1))).filter
    (fun α => (∑ j : Fin q, (α j).val) ≤ d)
  let M : Matrix W W ℚ := fun f g =>
    1 - 2 * (if ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card % 2 = 1
      then (1 : ℚ) else 0)
  let Q : Polynomial ℚ := 1 - 2 * P
  have hQdeg : Q.natDegree ≤ d := by
    have h2 : (2 : Polynomial ℚ).natDegree = 0 := by
      have : (2 : Polynomial ℚ) = Polynomial.C 2 := rfl
      rw [this, Polynomial.natDegree_C]
    have h1 : (2 * P).natDegree ≤ d := (Polynomial.natDegree_mul_le).trans (by simp [h2, d])
    exact (Polynomial.natDegree_sub_le 1 (2 * P)).trans (by simp [h1])
  have hMeval : ∀ f g : W, M f g = ∑ k ∈ Finset.range (d + 1),
      Q.coeff k * (∑ j : Fin q, (A f j : ℚ) * (B g j : ℚ)) ^ k := by
    intro f g
    have hsum_cast : ((∑ U : Fin q, A f U * B g U : ℕ) : ℚ) =
        ∑ j : Fin q, (A f j : ℚ) * (B g j : ℚ) := by
      push_cast; rfl
    have h1 : M f g = Q.eval (∑ j : Fin q, (A f j : ℚ) * (B g j : ℚ)) := by
      dsimp only [M, Q]
      rw [← hsum_cast, ← hP f g]
      simp [Polynomial.eval_sub, Polynomial.eval_mul]
    rw [h1, eval_eq_sum_range_of_le Q d hQdeg]
  have hex_c : ∀ k : Fin (d + 1), ∃ c : ↥K → ℚ, ∀ (a b : Fin q → ℚ),
      (∑ j : Fin q, a j * b j) ^ k.val =
      ∑ α : ↥K, c α * (∏ j : Fin q, a j ^ (α.1 j).val) * (∏ j : Fin q, b j ^ (α.1 j).val) := by
    intro k
    let count : (Fin k.val → Fin q) → (Fin q → Fin (d + 1)) := fun w j =>
      ⟨((Finset.univ : Finset (Fin k.val)).filter (fun t => w t = j)).card, by
        have hle : ((Finset.univ : Finset (Fin k.val)).filter (fun t => w t = j)).card ≤ k.val := by
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k.val)) (fun t => w t = j)
        omega⟩
    have hcount_mem : ∀ w : Fin k.val → Fin q, count w ∈ K := fun w => by
      have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k.val)))
        (t := (Finset.univ : Finset (Fin q))) (f := w) (fun _ _ => Finset.mem_univ _)
      have hsum : (∑ j : Fin q, (count w j).val) = k.val := by simpa [count] using h.symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    let c : ↥K → ℚ := fun α =>
      (((Finset.univ : Finset (Fin k.val → Fin q)).filter (fun w => count w = α.1)).card : ℚ)
    refine ⟨c, fun a b => ?_⟩
    have hpow : (∑ j : Fin q, a j * b j) ^ k.val =
        ∑ w : Fin k.val → Fin q, ∏ t : Fin k.val, (a (w t) * b (w t)) := by
      have h := Fintype.prod_sum (fun (_ : Fin k.val) (j : Fin q) => a j * b j)
      simpa using h
    rw [hpow]
    have hterm : ∀ w : Fin k.val → Fin q,
        ∏ t : Fin k.val, (a (w t) * b (w t)) =
        (∏ j : Fin q, a j ^ (count w j).val) * (∏ j : Fin q, b j ^ (count w j).val) := by
      intro w
      rw [Finset.prod_mul_distrib]
      congr 1
      · rw [← Finset.prod_fiberwise_of_maps_to (g := w) (t := (Finset.univ : Finset (Fin q)))
          (fun _ _ => Finset.mem_univ _)]
        congr 1; ext j
        have h1 : ∀ t ∈ (Finset.univ : Finset (Fin k.val)).filter (fun t => w t = j), a (w t) = a j := by
          intro t ht; rw [(Finset.mem_filter.mp ht).2]
        rw [Finset.prod_congr rfl h1, Finset.prod_const]
      · rw [← Finset.prod_fiberwise_of_maps_to (g := w) (t := (Finset.univ : Finset (Fin q)))
          (fun _ _ => Finset.mem_univ _)]
        congr 1; ext j
        have h1 : ∀ t ∈ (Finset.univ : Finset (Fin k.val)).filter (fun t => w t = j), b (w t) = b j := by
          intro t ht; rw [(Finset.mem_filter.mp ht).2]
        rw [Finset.prod_congr rfl h1, Finset.prod_const]
    simp_rw [hterm]
    rw [← Finset.sum_fiberwise_of_maps_to (g := count) (t := K) (fun w _ => hcount_mem w)]
    rw [← Finset.sum_attach K]
    congr 1; ext α
    have hcongr : ∀ w ∈ (Finset.univ : Finset (Fin k.val → Fin q)).filter (fun w => count w = α.1),
        (∏ j : Fin q, a j ^ (count w j).val) * (∏ j : Fin q, b j ^ (count w j).val) =
        (∏ j : Fin q, a j ^ (α.1 j).val) * (∏ j : Fin q, b j ^ (α.1 j).val) := by
      intro w hw; rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
    dsimp only [c]; ring
  let ck : Fin (d + 1) → ↥K → ℚ := fun k => Classical.choose (hex_c k)
  have hck : ∀ (k : Fin (d + 1)) (a b : Fin q → ℚ),
      (∑ j : Fin q, a j * b j) ^ k.val =
      ∑ α : ↥K, ck k α * (∏ j : Fin q, a j ^ (α.1 j).val) * (∏ j : Fin q, b j ^ (α.1 j).val) :=
    fun k => Classical.choose_spec (hex_c k)
  let U : Matrix W ↥K ℚ := fun f α =>
    (∑ k : Fin (d + 1), Q.coeff k.val * ck k α) * (∏ j : Fin q, (A f j : ℚ) ^ (α.1 j).val)
  let V : Matrix ↥K W ℚ := fun α g =>
    ∏ j : Fin q, (B g j : ℚ) ^ (α.1 j).val
  have hMUV : M = U * V := by
    ext f g
    rw [hMeval f g, ← Fin.sum_univ_eq_sum_range]
    simp_rw [hck _ (fun j => (A f j : ℚ)) (fun j => (B g j : ℚ))]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Matrix.mul_apply]
    congr 1; ext α
    dsimp only [U, V]
    rw [Finset.sum_mul, Finset.sum_mul]
    congr 1; ext k
    ring
  have hsurj : Function.Surjective U.mulVecLin := by
    intro y
    have hMMT := walsh_mul_transpose m e
    let inv2 : ℚ := ((2 : ℚ) ^ m)⁻¹
    refine ⟨V.mulVec (inv2 • M.transpose.mulVec y), ?_⟩
    change U.mulVec (V.mulVec (inv2 • M.transpose.mulVec y)) = y
    rw [Matrix.mulVec_mulVec, ← hMUV, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMMT,
      Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
    have hne : (2 : ℚ) ^ m ≠ 0 := by positivity
    rw [inv_mul_cancel₀ hne, one_smul]
  have hfr : Module.finrank ℚ (W → ℚ) ≤ Module.finrank ℚ (↥K → ℚ) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  have hfrW : Module.finrank ℚ (W → ℚ) = 2 ^ m := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [W]
  have hfrK : Module.finrank ℚ (↥K → ℚ) = Nat.choose (q + d) d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    exact card_monomials q d
  rw [hfrW, hfrK] at hfr
  exact ⟨hfr, fun hqm => deg_bound_from_choose m q d hq hqm hfr⟩

end PEqualNP.Outside.L_lib_1236_aux

theorem PEqualNP.Outside.L_lib_1236 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m N : Nat) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
  (left right : (Fin m → Bool) → Fin N → Bool),
  (∀ u, u ∉ H u) → (∀ u v, v ∈ H u ↔ u ∈ H v) →
  let lhs := (Finset.univ : Finset (Fin N)).filter (fun v => side v = false)
  let unions := lhs.powerset.image (fun S => S.biUnion
    (fun v => (H v).filter (fun w => side w = true)))
  let q := unions.card
  let total := fun (f g : Fin m → Bool) =>
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
      ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
  (∃ A B : (Fin m → Bool) → ↥unions → Nat,
    ∀ f g, total f g = ∑ U, A f U * B g U) ∧
  ∀ (P : Polynomial ℚ) (e : (Fin m → Bool) ≃ (Fin m → Bool)),
    (∀ f g, P.eval (total f g : ℚ) =
      (if ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card % 2 = 1
       then (1 : ℚ) else 0)) →
    2^m ≤ Nat.choose (q + P.natDegree) P.natDegree ∧
    (q ≤ m → m < 4*P.natDegree)) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro m N H side left right _ hsym
  have hp1 := PEqualNP.Outside.L_lib_1236_aux.part1 m N H side left right hsym
  refine ⟨hp1, ?_⟩
  rcases hp1 with ⟨A, B, hAB⟩
  intro P e hP
  let lhs := (Finset.univ : Finset (Fin N)).filter (fun v => side v = false)
  let unions := lhs.powerset.image (fun S => S.biUnion
    (fun v => (H v).filter (fun w => side w = true)))
  have hq_pos : 1 ≤ unions.card := by
    have hne : unions.Nonempty := ⟨∅, Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset _, by simp⟩⟩
    exact Finset.one_le_card.mpr hne
  let eu : Fin unions.card ≃ ↥unions := (Fintype.equivOfCardEq (by simp)).symm
  let A' : (Fin m → Bool) → Fin unions.card → ℕ := fun f j => A f (eu j)
  let B' : (Fin m → Bool) → Fin unions.card → ℕ := fun g j => B g (eu j)
  refine PEqualNP.Outside.L_lib_1236_aux.part2 m unions.card hq_pos A' B' P e ?_
  intro f g
  have hsum : ∑ j : Fin unions.card, A' f j * B' g j = ∑ U : ↥unions, A f U * B g U :=
    Fintype.sum_equiv eu _ _ (fun _ => rfl)
  rw [hsum, ← hAB f g]
  convert hP f g

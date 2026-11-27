import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_781_aux

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma totalDegree_C_mul_le {σ : Type*} (c : ZMod 2) (p : MvPolynomial σ (ZMod 2)) :
    (MvPolynomial.C c * p).totalDegree ≤ p.totalDegree := by
  have h := MvPolynomial.totalDegree_mul (MvPolynomial.C c) p
  rw [MvPolynomial.totalDegree_C, zero_add] at h
  exact h

private lemma totalDegree_prod_le {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add_left ih _)

private lemma totalDegree_sum_le {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2))
    (d : ℕ) (h : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (h a (Finset.mem_insert_self a t))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

private lemma totalDegree_pow_le {σ : Type*} (p : MvPolynomial σ (ZMod 2)) (k : ℕ) :
    (p ^ k).totalDegree ≤ k * p.totalDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.add_mul, one_mul]
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add_right ih _)

private lemma totalDegree_eval₂_linear {σ τ : Type*}
    (g : σ → MvPolynomial τ (ZMod 2))
    (hg : ∀ i : σ, (g i).totalDegree ≤ 1)
    (P : MvPolynomial σ (ZMod 2)) :
    (MvPolynomial.eval₂ MvPolynomial.C g P).totalDegree ≤ P.totalDegree := by
  classical
  have hdef : MvPolynomial.eval₂ MvPolynomial.C g P =
      ∑ m ∈ P.support, MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g i) ^ (m i) := by
    rw [MvPolynomial.eval₂_eq]
  rw [hdef]
  refine totalDegree_sum_le _ _ _ fun m hm => ?_
  have h1 : (MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g i) ^ (m i)).totalDegree ≤
      (∏ i ∈ m.support, (g i) ^ (m i)).totalDegree := totalDegree_C_mul_le _ _
  have h2 : (∏ i ∈ m.support, (g i) ^ (m i)).totalDegree ≤
      ∑ i ∈ m.support, ((g i) ^ (m i)).totalDegree := totalDegree_prod_le _ _
  have h3 : ∑ i ∈ m.support, ((g i) ^ (m i)).totalDegree ≤ m.sum (fun _ e => e) := by
    rw [Finsupp.sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hp := totalDegree_pow_le (g i) (m i)
    have hgi := hg i
    nlinarith
  have h4 : m.sum (fun _ e => e) ≤ P.totalDegree :=
    Finset.le_sup (f := fun t : σ →₀ ℕ => t.sum fun _ e => e) hm
  omega

private lemma eval_sub_zero_one_sum_deg {s : ℕ} (P : MvPolynomial (Fin (s + 1)) (ZMod 2)) :
    let g0 : Fin (s + 1) → MvPolynomial (Fin s) (ZMod 2) :=
      fun i => if hi : i.val = 0 then 0 else MvPolynomial.X ⟨i.val - 1, by omega⟩
    let g1 : Fin (s + 1) → MvPolynomial (Fin s) (ZMod 2) :=
      fun i => if hi : i.val = 0 then 1 else MvPolynomial.X ⟨i.val - 1, by omega⟩
    (MvPolynomial.eval₂ MvPolynomial.C g0 P + MvPolynomial.eval₂ MvPolynomial.C g1 P).totalDegree ≤
      P.totalDegree - 1 := by
  classical
  intro g0 g1
  have hrew : MvPolynomial.eval₂ MvPolynomial.C g0 P + MvPolynomial.eval₂ MvPolynomial.C g1 P =
      ∑ m ∈ P.support,
        (MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g0 i) ^ (m i) +
         MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g1 i) ^ (m i)) := by
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, ← Finset.sum_add_distrib]
  rw [hrew]
  refine totalDegree_sum_le _ _ _ fun m hm => ?_
  by_cases hm0 : m 0 = 0
  · have hprod_eq : ∏ i ∈ m.support, (g0 i) ^ (m i) = ∏ i ∈ m.support, (g1 i) ^ (m i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hine : i ≠ 0 := by
        intro h0
        subst h0
        exact (Finsupp.mem_support_iff.1 hi) hm0
      simp [g0, g1, hine]
    have hzero : MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g0 i) ^ (m i) +
        MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g1 i) ^ (m i) = 0 := by
      rw [hprod_eq, ← add_mul, ← map_add, zmod2_add_self, map_zero, zero_mul]
    rw [hzero]
    simp
  · have h0mem : (0 : Fin (s + 1)) ∈ m.support := Finsupp.mem_support_iff.2 hm0
    have hp0 : ∏ i ∈ m.support, (g0 i) ^ (m i) = 0 := by
      rw [← Finset.mul_prod_erase _ _ h0mem]
      have hg00 : g0 0 = 0 := by simp [g0]
      rw [hg00, zero_pow hm0, zero_mul]
    rw [hp0, mul_zero, zero_add]
    have h1 : (MvPolynomial.C (P.coeff m) * ∏ i ∈ m.support, (g1 i) ^ (m i)).totalDegree ≤
        (∏ i ∈ m.support, (g1 i) ^ (m i)).totalDegree := totalDegree_C_mul_le _ _
    have h2 : (∏ i ∈ m.support, (g1 i) ^ (m i)).totalDegree ≤
        ∑ i ∈ m.support, ((g1 i) ^ (m i)).totalDegree := totalDegree_prod_le _ _
    have hg10 : ((g1 0) ^ (m 0)).totalDegree = 0 := by
      have : g1 0 = 1 := by simp [g1]
      rw [this, one_pow, MvPolynomial.totalDegree_one]
    have h3 : ∑ i ∈ m.support, ((g1 i) ^ (m i)).totalDegree ≤ m.sum (fun _ e => e) - m 0 := by
      rw [← Finset.add_sum_erase _ _ h0mem, hg10, zero_add]
      have hsum_er : m.sum (fun _ e => e) = m 0 + ∑ i ∈ m.support.erase 0, m i := by
        rw [Finsupp.sum, ← Finset.add_sum_erase _ _ h0mem]
      have hle_er : ∑ i ∈ m.support.erase 0, ((g1 i) ^ (m i)).totalDegree ≤
          ∑ i ∈ m.support.erase 0, m i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hgi : (g1 i).totalDegree ≤ 1 := by
          dsimp only [g1]
          split_ifs
          · simp
          · simp [MvPolynomial.totalDegree_X]
        have hp := totalDegree_pow_le (g1 i) (m i)
        nlinarith
      omega
    have h4 : m.sum (fun _ e => e) ≤ P.totalDegree :=
      Finset.le_sup (f := fun t : Fin (s + 1) →₀ ℕ => t.sum fun _ e => e) hm
    have hm0pos : 1 ≤ m 0 := Nat.pos_of_ne_zero hm0
    omega

private lemma rm_weight_bound :
    ∀ (s d : ℕ) (P : MvPolynomial (Fin s) (ZMod 2)),
      P.totalDegree ≤ d →
      (∃ y : Fin s → ZMod 2, MvPolynomial.eval y P ≠ 0) →
      2 ^ (s - d) ≤ (Finset.univ.filter (fun y : Fin s → ZMod 2 => MvPolynomial.eval y P ≠ 0)).card := by
  intro s
  induction s with
  | zero =>
    intro d P _ ⟨y, hy⟩
    simp only [Nat.zero_sub, pow_zero]
    exact Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩⟩
  | succ s ih =>
    intro d P hdeg ⟨y0, hy0⟩
    by_cases hd0 : d = 0
    · subst hd0
      have hconst : P = MvPolynomial.C (P.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hdeg)
      have hcne : P.coeff 0 ≠ 0 := by
        rw [hconst, MvPolynomial.eval_C] at hy0
        exact hy0
      have hall : Finset.univ.filter (fun y : Fin (s + 1) → ZMod 2 => MvPolynomial.eval y P ≠ 0) =
          Finset.univ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hconst, MvPolynomial.eval_C]
        exact ⟨fun _ => trivial, fun _ => hcne⟩
      rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.sub_zero]
    · let g0 : Fin (s + 1) → MvPolynomial (Fin s) (ZMod 2) :=
        fun i => if hi : i.val = 0 then 0 else MvPolynomial.X ⟨i.val - 1, by omega⟩
      let g1 : Fin (s + 1) → MvPolynomial (Fin s) (ZMod 2) :=
        fun i => if hi : i.val = 0 then 1 else MvPolynomial.X ⟨i.val - 1, by omega⟩
      let P0 : MvPolynomial (Fin s) (ZMod 2) := MvPolynomial.eval₂ MvPolynomial.C g0 P
      let P1 : MvPolynomial (Fin s) (ZMod 2) := MvPolynomial.eval₂ MvPolynomial.C g1 P
      have hg0_deg : ∀ i, (g0 i).totalDegree ≤ 1 := fun i => by
        dsimp only [g0]; split_ifs <;> simp [MvPolynomial.totalDegree_X]
      have hg1_deg : ∀ i, (g1 i).totalDegree ≤ 1 := fun i => by
        dsimp only [g1]; split_ifs <;> simp [MvPolynomial.totalDegree_X]
      have hP0_deg : P0.totalDegree ≤ d :=
        le_trans (totalDegree_eval₂_linear g0 hg0_deg P) hdeg
      have hP1_deg : P1.totalDegree ≤ d :=
        le_trans (totalDegree_eval₂_linear g1 hg1_deg P) hdeg
      have hPsum_deg : (P0 + P1).totalDegree ≤ d - 1 :=
        le_trans (eval_sub_zero_one_sum_deg P) (Nat.sub_le_sub_right hdeg 1)
      let consV : ZMod 2 → (Fin s → ZMod 2) → (Fin (s + 1) → ZMod 2) :=
        fun b tail i => if hi : i.val = 0 then b else tail ⟨i.val - 1, by omega⟩
      have heval0 : ∀ tail : Fin s → ZMod 2,
          MvPolynomial.eval tail P0 = MvPolynomial.eval (consV 0 tail) P := by
        intro tail
        dsimp only [P0]
        rw [MvPolynomial.eval_eval₂]
        have hcomp : (MvPolynomial.eval tail).comp MvPolynomial.C = RingHom.id (ZMod 2) := by
          ext; simp
        have hfn : (fun i => MvPolynomial.eval tail (g0 i)) = consV 0 tail := by
          funext i
          dsimp only [g0, consV]
          split_ifs <;> simp
        rw [hcomp, hfn]
        rfl
      have heval1 : ∀ tail : Fin s → ZMod 2,
          MvPolynomial.eval tail P1 = MvPolynomial.eval (consV 1 tail) P := by
        intro tail
        dsimp only [P1]
        rw [MvPolynomial.eval_eval₂]
        have hcomp : (MvPolynomial.eval tail).comp MvPolynomial.C = RingHom.id (ZMod 2) := by
          ext; simp
        have hfn : (fun i => MvPolynomial.eval tail (g1 i)) = consV 1 tail := by
          funext i
          dsimp only [g1, consV]
          split_ifs <;> simp
        rw [hcomp, hfn]
        rfl
      have hsplit_card :
          (Finset.univ.filter (fun y : Fin (s + 1) → ZMod 2 => MvPolynomial.eval y P ≠ 0)).card =
          (Finset.univ.filter (fun tail : Fin s → ZMod 2 => MvPolynomial.eval tail P0 ≠ 0)).card +
          (Finset.univ.filter (fun tail : Fin s → ZMod 2 => MvPolynomial.eval tail P1 ≠ 0)).card := by
        let S := Finset.univ.filter (fun y : Fin (s + 1) → ZMod 2 => MvPolynomial.eval y P ≠ 0)
        have hpart := Finset.card_filter_add_card_filter_not (s := S) (p := fun y => y 0 = 0)
        have hS0 : (S.filter (fun y => y 0 = 0)).card =
            (Finset.univ.filter (fun tail : Fin s → ZMod 2 => MvPolynomial.eval tail P0 ≠ 0)).card := by
          refine Finset.card_bij (fun y _ => fun j : Fin s => y j.succ) ?_ ?_ ?_
          · intro y hy
            rw [Finset.mem_filter] at hy
            obtain ⟨hyS, hy0'⟩ := hy
            rw [Finset.mem_filter] at hyS ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [heval0]
            have hcons : consV 0 (fun j : Fin s => y j.succ) = y := by
              funext i
              cases i using Fin.cases with
              | zero => simp [consV, hy0']
              | succ j => simp [consV]
            rw [hcons]
            exact hyS.2
          · intro y1 h1 y2 h2 hEq
            have h10 : y1 0 = 0 := (Finset.mem_filter.1 h1).2
            have h20 : y2 0 = 0 := (Finset.mem_filter.1 h2).2
            funext i
            cases i using Fin.cases with
            | zero => rw [h10, h20]
            | succ j => exact congrFun hEq j
          · intro tail ht
            rw [Finset.mem_filter] at ht
            refine ⟨consV 0 tail, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp [consV]⟩
              rw [← heval0 tail]
              exact ht.2
            · funext j
              simp [consV]
        have hS1 : (S.filter (fun y => ¬ y 0 = 0)).card =
            (Finset.univ.filter (fun tail : Fin s → ZMod 2 => MvPolynomial.eval tail P1 ≠ 0)).card := by
          refine Finset.card_bij (fun y _ => fun j : Fin s => y j.succ) ?_ ?_ ?_
          · intro y hy
            rw [Finset.mem_filter] at hy
            obtain ⟨hyS, hy1'⟩ := hy
            have hy1eq : y 0 = 1 := by
              rcases zmod2_eq_zero_or_one (y 0) with h0 | h1
              · exact absurd h0 hy1'
              · exact h1
            rw [Finset.mem_filter] at hyS ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [heval1]
            have hcons : consV 1 (fun j : Fin s => y j.succ) = y := by
              funext i
              cases i using Fin.cases with
              | zero => simp [consV, hy1eq]
              | succ j => simp [consV]
            rw [hcons]
            exact hyS.2
          · intro y1 h1 y2 h2 hEq
            have h11 : y1 0 = 1 := by
              rcases zmod2_eq_zero_or_one (y1 0) with h0 | h1
              · exact absurd h0 (Finset.mem_filter.1 h1).2
              · exact h1
            have h21 : y2 0 = 1 := by
              rcases zmod2_eq_zero_or_one (y2 0) with h0 | h1
              · exact absurd h0 (Finset.mem_filter.1 h2).2
              · exact h1
            funext i
            cases i using Fin.cases with
            | zero => rw [h11, h21]
            | succ j => exact congrFun hEq j
          · intro tail ht
            rw [Finset.mem_filter] at ht
            refine ⟨consV 1 tail, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp [consV]⟩
              rw [← heval1 tail]
              exact ht.2
            · funext j
              simp [consV]
        rw [← hpart, hS0, hS1]
      rw [hsplit_card]
      by_cases h0 : ∃ t : Fin s → ZMod 2, MvPolynomial.eval t P0 ≠ 0
      · by_cases h1 : ∃ t : Fin s → ZMod 2, MvPolynomial.eval t P1 ≠ 0
        · have hb0 := ih d P0 hP0_deg h0
          have hb1 := ih d P1 hP1_deg h1
          have hpow : 2 ^ (s + 1 - d) ≤ 2 ^ (s - d) + 2 ^ (s - d) := by
            by_cases hsd : d ≤ s
            · have heq : s + 1 - d = (s - d) + 1 := by omega
              rw [heq, pow_succ]
              omega
            · have h1' : s + 1 - d ≤ 1 := by omega
              have h2' : 2 ^ (s + 1 - d) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) h1'
              have hpos : 1 ≤ 2 ^ (s - d) := Nat.one_le_two_pow
              omega
          omega
        · push Not at h1
          have heq_sum : ∀ t, MvPolynomial.eval t (P0 + P1) = MvPolynomial.eval t P0 := by
            intro t
            rw [map_add, h1 t, add_zero]
          have hsum_ne : ∃ t, MvPolynomial.eval t (P0 + P1) ≠ 0 := by
            obtain ⟨t, ht⟩ := h0
            exact ⟨t, by rw [heq_sum t]; exact ht⟩
          have hb := ih (d - 1) (P0 + P1) hPsum_deg hsum_ne
          have hcard_eq : (Finset.univ.filter (fun t : Fin s → ZMod 2 => MvPolynomial.eval t (P0 + P1) ≠ 0)).card =
              (Finset.univ.filter (fun t : Fin s → ZMod 2 => MvPolynomial.eval t P0 ≠ 0)).card := by
            congr 1
            ext t
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [heq_sum t]
          have hsub : s - (d - 1) = s + 1 - d := by omega
          rw [hcard_eq, hsub] at hb
          omega
      · push Not at h0
        have h1 : ∃ t : Fin s → ZMod 2, MvPolynomial.eval t P1 ≠ 0 := by
          let tail0 : Fin s → ZMod 2 := fun j => y0 j.succ
          rcases zmod2_eq_zero_or_one (y0 0) with hy00 | hy01
          · exfalso
            have hcons : consV 0 tail0 = y0 := by
              funext i
              cases i using Fin.cases with
              | zero => simp [consV, hy00]
              | succ j => simp [consV, tail0]
            have := h0 tail0
            rw [heval0, hcons] at this
            exact hy0 this
          · refine ⟨tail0, ?_⟩
            have hcons : consV 1 tail0 = y0 := by
              funext i
              cases i using Fin.cases with
              | zero => simp [consV, hy01]
              | succ j => simp [consV, tail0]
            rw [heval1, hcons]
            exact hy0
        have heq_sum : ∀ t, MvPolynomial.eval t (P0 + P1) = MvPolynomial.eval t P1 := by
          intro t
          rw [map_add, h0 t, zero_add]
        have hsum_ne : ∃ t, MvPolynomial.eval t (P0 + P1) ≠ 0 := by
          obtain ⟨t, ht⟩ := h1
          exact ⟨t, by rw [heq_sum t]; exact ht⟩
        have hb := ih (d - 1) (P0 + P1) hPsum_deg hsum_ne
        have hcard_eq : (Finset.univ.filter (fun t : Fin s → ZMod 2 => MvPolynomial.eval t (P0 + P1) ≠ 0)).card =
            (Finset.univ.filter (fun t : Fin s → ZMod 2 => MvPolynomial.eval t P1 ≠ 0)).card := by
          congr 1
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [heq_sum t]
        have hsub : s - (d - 1) = s + 1 - d := by omega
        rw [hcard_eq, hsub] at hb
        omega

private lemma subspace_poly_support_ge {n s d : ℕ}
    (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    [DecidablePred (fun x : Fin n → ZMod 2 => x ∈ W)]
    (hs : s ≤ Module.finrank (ZMod 2) ↥W)
    (Q : MvPolynomial (Fin n) (ZMod 2))
    (hdeg : Q.totalDegree ≤ d)
    (hQ0 : MvPolynomial.eval (0 : Fin n → ZMod 2) Q ≠ 0) :
    2 ^ (s - d) ≤ (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ W ∧ MvPolynomial.eval x Q ≠ 0)).card := by
  let b := Module.finBasis (ZMod 2) ↥W
  let v : Fin s → (Fin n → ZMod 2) := fun k => (b ⟨k.val, Nat.lt_of_lt_of_le k.isLt hs⟩).1
  have hv_mem : ∀ y : Fin s → ZMod 2, (∑ k : Fin s, y k • v k) ∈ W := by
    intro y
    refine Submodule.sum_mem W fun k _ => Submodule.smul_mem W (y k) (b ⟨k.val, Nat.lt_of_lt_of_le k.isLt hs⟩).2
  have hv_inj : Function.Injective (fun y : Fin s → ZMod 2 => ∑ k : Fin s, y k • v k) := by
    intro y1 y2 hEq
    have hli : LinearIndependent (ZMod 2) v := by
      have h1 : LinearIndependent (ZMod 2) (fun k : Fin s => b ⟨k.val, Nat.lt_of_lt_of_le k.isLt hs⟩) :=
        b.linearIndependent.comp (fun k : Fin s => (⟨k.val, Nat.lt_of_lt_of_le k.isLt hs⟩ : Fin (Module.finrank (ZMod 2) ↥W)))
          (fun _ _ h => Fin.ext (Fin.mk.inj h))
      rw [Fintype.linearIndependent_iff] at h1 ⊢
      intro c hc
      apply h1 c
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa [v] using hc
    have hdiff : ∑ k : Fin s, (y1 k - y2 k) • v k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hEq, sub_self]
    have h0 := Fintype.linearIndependent_iff.1 hli (fun k => y1 k - y2 k) hdiff
    funext k
    exact sub_eq_zero.1 (h0 k)
  let g : Fin n → MvPolynomial (Fin s) (ZMod 2) :=
    fun i => ∑ k : Fin s, MvPolynomial.C (v k i) * MvPolynomial.X k
  have hg_deg : ∀ i : Fin n, (g i).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_sum_le _ _ 1 fun k _ => ?_
    exact le_trans (totalDegree_C_mul_le _ _) (by simp [MvPolynomial.totalDegree_X])
  let P : MvPolynomial (Fin s) (ZMod 2) := MvPolynomial.eval₂ MvPolynomial.C g Q
  have hP_deg : P.totalDegree ≤ d :=
    le_trans (totalDegree_eval₂_linear g hg_deg Q) hdeg
  have hP_eval : ∀ y : Fin s → ZMod 2,
      MvPolynomial.eval y P = MvPolynomial.eval (∑ k : Fin s, y k • v k) Q := by
    intro y
    dsimp only [P]
    rw [MvPolynomial.eval_eval₂]
    have hcomp : (MvPolynomial.eval y).comp MvPolynomial.C = RingHom.id (ZMod 2) := by
      ext; simp
    have hfn : (fun i => MvPolynomial.eval y (g i)) = ∑ k : Fin s, y k • v k := by
      funext i
      simp only [g, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hcomp, hfn]
    rfl
  have hP0 : MvPolynomial.eval (0 : Fin s → ZMod 2) P ≠ 0 := by
    rw [hP_eval]
    simpa using hQ0
  have hrm := rm_weight_bound s d P hP_deg ⟨0, hP0⟩
  have hcard_le :
      (Finset.univ.filter (fun y : Fin s → ZMod 2 => MvPolynomial.eval y P ≠ 0)).card ≤
      (Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ W ∧ MvPolynomial.eval x Q ≠ 0)).card := by
    refine Finset.card_le_card_of_injOn (fun y => ∑ k : Fin s, y k • v k) ?_ ?_
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
      refine ⟨Finset.mem_univ _, hv_mem y, ?_⟩
      rw [← hP_eval y]
      exact hy.2
    · intro y1 _ y2 _ hEq
      exact hv_inj hEq
  exact le_trans hrm hcard_le

private lemma forward_dir (n q d budget : Nat) (_hq : 0 < q) (hqn : q < n) (hd : 0 < d)
    (poly : MvPolynomial (Fin n) (ZMod 2)) (extra : Finset (Fin n → ZMod 2))
    (hdeg : poly.totalDegree ≤ d) (h0extra : (0 : Fin n → ZMod 2) ∉ extra)
    (hbud : extra.card ≤ budget)
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2))
    (ans : ((ZMod 2) × (Fin n → ZMod 2)) → Fin q → ZMod 2)
    (decode : (Fin q → ZMod 2) → Bool)
    (hrec : ∀ p j, ans p j = ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p)
    (hzero : ∀ b : ZMod 2, decode (ans (b, 0)) = false)
    (hsucc : ∀ x : Fin n → ZMod 2, x ≠ 0 → ∃ b : ZMod 2,
      (b = MvPolynomial.eval x poly ∨ x ∈ extra) ∧ decode (ans (b, x)) = true) :
    2 * (n + 1 - q) ≤ n ∧ 2 ^ (n + 1 - q - d) ≤ budget + 1 := by
  classical
  let s := n + 1 - q
  have hs_ge2 : 2 ≤ s := by omega
  let t0 : Fin q → ZMod 2 := ans (0, 0)
  let t1 : Fin q → ZMod 2 := ans (1, 0)
  let T0 : ((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] (Fin q → ZMod 2) :=
    LinearMap.pi fun j => ask j (fun e => t0 ⟨e.val, Nat.lt_trans e.isLt j.isLt⟩)
  let T1 : ((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] (Fin q → ZMod 2) :=
    LinearMap.pi fun j => ask j (fun e => t1 ⟨e.val, Nat.lt_trans e.isLt j.isLt⟩)
  have hT0_zero : T0 (0, 0) = t0 := by
    funext j
    exact (hrec (0, 0) j).symm
  have hT1_zero : T1 (1, 0) = t1 := by
    funext j
    exact (hrec (1, 0) j).symm
  have hker0_ans : ∀ p : (ZMod 2) × (Fin n → ZMod 2), p ∈ LinearMap.ker T0 → ans p = t0 := by
    intro p hp
    have hTp : T0 p = t0 := by
      have h0 : T0 p = 0 := LinearMap.mem_ker.1 hp
      have h00 : t0 = 0 := by rw [← hT0_zero]; exact map_zero T0
      rw [h0, h00]
    have haux : ∀ k (hk : k < q), ans p ⟨k, hk⟩ = t0 ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk
        rw [hrec p ⟨k, hk⟩]
        have hpref : (fun earlier : Fin k => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt hk⟩) =
            (fun earlier : Fin k => t0 ⟨earlier.val, Nat.lt_trans earlier.isLt hk⟩) := by
          funext e
          exact ih e.val e.isLt (Nat.lt_trans e.isLt hk)
        rw [hpref]
        exact congrFun hTp ⟨k, hk⟩
    funext j
    exact haux j.val j.isLt
  have hker1_ans : ∀ p : (ZMod 2) × (Fin n → ZMod 2), p ∈ LinearMap.ker T1 →
      ans (p.1 + 1, p.2) = t1 := by
    intro p hp
    have hTp : T1 (p.1 + 1, p.2) = t1 := by
      have hpair : (p.1 + 1, p.2) = p + (1, 0) := by ext <;> simp
      rw [hpair, map_add, LinearMap.mem_ker.1 hp, zero_add, hT1_zero]
    have haux : ∀ k (hk : k < q), ans (p.1 + 1, p.2) ⟨k, hk⟩ = t1 ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk
        rw [hrec (p.1 + 1, p.2) ⟨k, hk⟩]
        have hpref : (fun earlier : Fin k => ans (p.1 + 1, p.2) ⟨earlier.val, Nat.lt_trans earlier.isLt hk⟩) =
            (fun earlier : Fin k => t1 ⟨earlier.val, Nat.lt_trans earlier.isLt hk⟩) := by
          funext e
          exact ih e.val e.isLt (Nat.lt_trans e.isLt hk)
        rw [hpref]
        exact congrFun hTp ⟨k, hk⟩
    funext j
    exact haux j.val j.isLt
  let K0 : Submodule (ZMod 2) ((ZMod 2) × (Fin n → ZMod 2)) := LinearMap.ker T0
  let K1 : Submodule (ZMod 2) ((ZMod 2) × (Fin n → ZMod 2)) := LinearMap.ker T1
  have hK0_dim : s ≤ Module.finrank (ZMod 2) ↥K0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker T0
    have hdom : Module.finrank (ZMod 2) ((ZMod 2) × (Fin n → ZMod 2)) = n + 1 := by
      rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
      omega
    have hrng : Module.finrank (ZMod 2) ↥(LinearMap.range T0) ≤ q := by
      have := Submodule.finrank_le (LinearMap.range T0)
      rw [Module.finrank_fin_fun] at this
      exact this
    dsimp only [K0, s]
    omega
  have hK1_dim : s ≤ Module.finrank (ZMod 2) ↥K1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker T1
    have hdom : Module.finrank (ZMod 2) ((ZMod 2) × (Fin n → ZMod 2)) = n + 1 := by
      rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
      omega
    have hrng : Module.finrank (ZMod 2) ↥(LinearMap.range T1) ≤ q := by
      have := Submodule.finrank_le (LinearMap.range T1)
      rw [Module.finrank_fin_fun] at this
      exact this
    dsimp only [K1, s]
    omega
  let π : ((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearMap.snd (ZMod 2) (ZMod 2) (Fin n → ZMod 2)
  have h10_not_K0 : ((1 : ZMod 2), (0 : Fin n → ZMod 2)) ∉ K0 := by
    intro hmem
    have hproj_dim : 1 ≤ Module.finrank (ZMod 2) ↥(K0.map π) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (π.domRestrict K0)
      have hker_le : Module.finrank (ZMod 2) ↥(LinearMap.ker (π.domRestrict K0)) ≤ 1 := by
        let f : ↥(LinearMap.ker (π.domRestrict K0)) →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun z => z.1.1.1
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hfinj : Function.Injective f := by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact hab
          · have ha : a.1.1.2 = 0 := LinearMap.mem_ker.1 a.2
            have hb : b.1.1.2 = 0 := LinearMap.mem_ker.1 b.2
            rw [ha, hb]
        have hle := LinearMap.finrank_le_finrank_of_injective hfinj
        rw [Module.finrank_self] at hle
        exact hle
      have hrng_eq : LinearMap.range (π.domRestrict K0) = K0.map π := by
        ext x
        simp [Submodule.mem_map]
      rw [hrng_eq] at hrn
      omega
    have hne_bot : K0.map π ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hproj_dim
      omega
    obtain ⟨x, hx_mem, hx_ne⟩ := (Submodule.ne_bot_iff _).1 hne_bot
    obtain ⟨⟨b0, x'⟩, hbx_K0, hEq⟩ := Submodule.mem_map.1 hx_mem
    change x' = x at hEq
    rw [hEq] at hbx_K0
    have hb1_K0 : (b0 + 1, x) ∈ K0 := by
      have hsum : (b0 + 1, x) = (b0, x) + (1, 0) := by ext <;> simp
      rw [hsum]
      exact K0.add_mem hbx_K0 hmem
    have hdec0 : decode (ans (b0, x)) = false := by
      rw [hker0_ans (b0, x) hbx_K0]; exact hzero 0
    have hdec1 : decode (ans (b0 + 1, x)) = false := by
      rw [hker0_ans (b0 + 1, x) hb1_K0]; exact hzero 0
    obtain ⟨b, _, hb_true⟩ := hsucc x hx_ne
    have hcases : b = b0 ∨ b = b0 + 1 := by
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one b0 with rfl | rfl <;> decide
    rcases hcases with rfl | rfl
    · rw [hdec0] at hb_true; exact Bool.noConfusion hb_true
    · rw [hdec1] at hb_true; exact Bool.noConfusion hb_true
  have h10_not_K1 : ((1 : ZMod 2), (0 : Fin n → ZMod 2)) ∉ K1 := by
    intro hmem
    have hproj_dim : 1 ≤ Module.finrank (ZMod 2) ↥(K1.map π) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (π.domRestrict K1)
      have hker_le : Module.finrank (ZMod 2) ↥(LinearMap.ker (π.domRestrict K1)) ≤ 1 := by
        let f : ↥(LinearMap.ker (π.domRestrict K1)) →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun z => z.1.1.1
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hfinj : Function.Injective f := by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact hab
          · have ha : a.1.1.2 = 0 := LinearMap.mem_ker.1 a.2
            have hb : b.1.1.2 = 0 := LinearMap.mem_ker.1 b.2
            rw [ha, hb]
        have hle := LinearMap.finrank_le_finrank_of_injective hfinj
        rw [Module.finrank_self] at hle
        exact hle
      have hrng_eq : LinearMap.range (π.domRestrict K1) = K1.map π := by
        ext x
        simp [Submodule.mem_map]
      rw [hrng_eq] at hrn
      omega
    have hne_bot : K1.map π ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hproj_dim
      omega
    obtain ⟨x, hx_mem, hx_ne⟩ := (Submodule.ne_bot_iff _).1 hne_bot
    obtain ⟨⟨b0, x'⟩, hbx_K1, hEq⟩ := Submodule.mem_map.1 hx_mem
    change x' = x at hEq
    rw [hEq] at hbx_K1
    have hb1_K1 : (b0 + 1, x) ∈ K1 := by
      have hsum : (b0 + 1, x) = (b0, x) + (1, 0) := by ext <;> simp
      rw [hsum]
      exact K1.add_mem hbx_K1 hmem
    have hdec0 : decode (ans (b0 + 1, x)) = false := by
      rw [hker1_ans (b0, x) hbx_K1]; exact hzero 1
    have hdec1 : decode (ans (b0, x)) = false := by
      have h := hker1_ans (b0 + 1, x) hb1_K1
      simp only [add_assoc, zmod2_add_self, add_zero] at h
      rw [h]; exact hzero 1
    obtain ⟨b, _, hb_true⟩ := hsucc x hx_ne
    have hcases : b = b0 ∨ b = b0 + 1 := by
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one b0 with rfl | rfl <;> decide
    rcases hcases with rfl | rfl
    · rw [hdec1] at hb_true; exact Bool.noConfusion hb_true
    · rw [hdec0] at hb_true; exact Bool.noConfusion hb_true
  have ht0_ne_t1 : t0 ≠ t1 := by
    intro hEq
    have hT01 : T0 = T1 := by
      refine LinearMap.ext fun p => ?_
      funext j
      simp [T0, T1, hEq]
    have h10 : T0 (1, 0) = 0 := by
      rw [hT01, hT1_zero, ← hEq, ← hT0_zero]
      exact map_zero T0
    exact h10_not_K0 (LinearMap.mem_ker.2 h10)
  have hex_diff : ∃ k : ℕ, ∃ hk : k < q, t0 ⟨k, hk⟩ ≠ t1 ⟨k, hk⟩ := by
    by_contra hall
    push Not at hall
    apply ht0_ne_t1
    funext j
    exact hall j.val j.isLt
  let j0_nat := Nat.find hex_diff
  obtain ⟨hj0_lt, hj0_ne⟩ := Nat.find_spec hex_diff
  let j0 : Fin q := ⟨j0_nat, hj0_lt⟩
  have hj0_pref : (fun e : Fin j0.val => t0 ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩) =
      (fun e : Fin j0.val => t1 ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩) := by
    funext e
    by_contra hne
    exact Nat.find_min hex_diff e.isLt ⟨Nat.lt_trans e.isLt j0.isLt, hne⟩
  let L0 : ((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2 :=
    ask j0 (fun e => t0 ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩)
  let φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    L0.comp (LinearMap.inr (ZMod 2) (ZMod 2) (Fin n → ZMod 2))
  have hL0_10 : L0 (1, 0) = 1 := by
    have h0 : L0 (0, 0) = 0 := map_zero L0
    have h0' : t0 j0 = 0 := by
      have := congrFun hT0_zero j0
      change L0 (0, 0) = t0 j0 at this
      rw [h0] at this
      exact this.symm
    have h1' : t1 j0 = L0 (1, 0) := by
      have := congrFun hT1_zero j0
      change ask j0 (fun e => t1 ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩) (1, 0) = t1 j0 at this
      rw [← hj0_pref] at this
      exact this.symm
    rcases zmod2_eq_zero_or_one (L0 (1, 0)) with h | h
    · exfalso
      apply hj0_ne
      change t0 j0 = t1 j0
      rw [h0', h1', h]
    · exact h
  have hL0_eval : ∀ (b : ZMod 2) (x : Fin n → ZMod 2), L0 (b, x) = b + φ x := by
    intro b x
    have hpair : (b, x) = b • ((1 : ZMod 2), (0 : Fin n → ZMod 2)) +
        LinearMap.inr (ZMod 2) (ZMod 2) (Fin n → ZMod 2) x := by
      ext <;> simp
    conv_lhs => rw [hpair]
    rw [map_add, map_smul, hL0_10, smul_eq_mul, mul_one]
    rfl
  let W0 : Submodule (ZMod 2) (Fin n → ZMod 2) := K0.map π
  let W1 : Submodule (ZMod 2) (Fin n → ZMod 2) := K1.map π
  have hW0_forbid : ∀ x ∈ W0, decode (ans (φ x, x)) = false := by
    intro x hx
    obtain ⟨⟨b, x'⟩, hbx_K0, hEq⟩ := Submodule.mem_map.1 hx
    change x' = x at hEq
    rw [hEq] at hbx_K0
    have hL0z : L0 (b, x) = 0 := by
      have := congrFun (LinearMap.mem_ker.1 hbx_K0) j0
      exact this
    rw [hL0_eval] at hL0z
    have hb_eq : b = φ x := by
      have hadd := congrArg (fun z => z + φ x) hL0z
      simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at hadd
      exact hadd
    subst hb_eq
    rw [hker0_ans (φ x, x) hbx_K0]
    exact hzero 0
  have hW1_forbid : ∀ x ∈ W1, decode (ans (φ x + 1, x)) = false := by
    intro x hx
    obtain ⟨⟨b, x'⟩, hbx_K1, hEq⟩ := Submodule.mem_map.1 hx
    change x' = x at hEq
    rw [hEq] at hbx_K1
    have hL0z : L0 (b, x) = 0 := by
      have := congrFun (LinearMap.mem_ker.1 hbx_K1) j0
      change ask j0 (fun e => t1 ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩) (b, x) = 0 at this
      rw [← hj0_pref] at this
      exact this
    rw [hL0_eval] at hL0z
    have hb_eq : b = φ x := by
      have hadd := congrArg (fun z => z + φ x) hL0z
      simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at hadd
      exact hadd
    subst hb_eq
    rw [hker1_ans (φ x, x) hbx_K1]
    exact hzero 1
  have hW0_dim : s ≤ Module.finrank (ZMod 2) ↥W0 := by
    have hinj : Function.Injective (π.domRestrict K0) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      apply Subtype.ext
      apply Prod.ext
      · rcases zmod2_eq_zero_or_one z.1.1 with h0 | h1
        · exact h0
        · exfalso
          have hz2 : z.1.2 = 0 := LinearMap.mem_ker.1 hz
          have hz_eq : z.1 = (1, 0) := Prod.ext h1 hz2
          exact h10_not_K0 (hz_eq ▸ z.2)
      · exact LinearMap.mem_ker.1 hz
    have hrng : LinearMap.range (π.domRestrict K0) = W0 := by
      ext x; simp [W0, Submodule.mem_map]
    have hle := LinearMap.finrank_range_of_inj hinj
    rw [hrng] at hle
    omega
  have hW1_dim : s ≤ Module.finrank (ZMod 2) ↥W1 := by
    have hinj : Function.Injective (π.domRestrict K1) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      apply Subtype.ext
      apply Prod.ext
      · rcases zmod2_eq_zero_or_one z.1.1 with h0 | h1
        · exact h0
        · exfalso
          have hz2 : z.1.2 = 0 := LinearMap.mem_ker.1 hz
          have hz_eq : z.1 = (1, 0) := Prod.ext h1 hz2
          exact h10_not_K1 (hz_eq ▸ z.2)
      · exact LinearMap.mem_ker.1 hz
    have hrng : LinearMap.range (π.domRestrict K1) = W1 := by
      ext x; simp [W1, Submodule.mem_map]
    have hle := LinearMap.finrank_range_of_inj hinj
    rw [hrng] at hle
    omega
  have hdisj : W0 ⊓ W1 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hx0, hx1⟩ := Submodule.mem_inf.1 hx
    by_contra hxne
    obtain ⟨b, _, hb_true⟩ := hsucc x hxne
    have hcases : b = φ x ∨ b = φ x + 1 := by
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one (φ x) with h | h <;> rw [h] <;> decide
    rcases hcases with rfl | rfl
    · rw [hW0_forbid x hx0] at hb_true; exact Bool.noConfusion hb_true
    · rw [hW1_forbid x hx1] at hb_true; exact Bool.noConfusion hb_true
  have h2s_le_n : 2 * s ≤ n := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq W0 W1
    rw [hdisj, finrank_bot, add_zero] at hsup
    have hle := Submodule.finrank_le (W0 ⊔ W1)
    rw [Module.finrank_fin_fun] at hle
    omega
  let φPoly : MvPolynomial (Fin n) (ZMod 2) :=
    ∑ i : Fin n, MvPolynomial.C (φ (Pi.single i 1)) * MvPolynomial.X i
  have hφPoly_eval : ∀ x : Fin n → ZMod 2, MvPolynomial.eval x φPoly = φ x := by
    intro x
    have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    rw [map_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_smul, smul_eq_mul, mul_comm]
  have hφPoly_deg : φPoly.totalDegree ≤ 1 := by
    refine totalDegree_sum_le _ _ 1 fun i _ => ?_
    exact le_trans (totalDegree_C_mul_le _ _) (by simp [MvPolynomial.totalDegree_X])
  have hbud_bound : 2 ^ (s - d) ≤ budget + 1 := by
    rcases zmod2_eq_zero_or_one (MvPolynomial.eval (0 : Fin n → ZMod 2) poly) with h0 | h1
    · let Q : MvPolynomial (Fin n) (ZMod 2) := 1 + poly + φPoly
      have hQ_deg : Q.totalDegree ≤ d := by
        dsimp only [Q]
        have h1' := MvPolynomial.totalDegree_add (1 + poly) φPoly
        have h2' := MvPolynomial.totalDegree_add (1 : MvPolynomial (Fin n) (ZMod 2)) poly
        rw [MvPolynomial.totalDegree_one] at h2'
        omega
      have hQ0 : MvPolynomial.eval (0 : Fin n → ZMod 2) Q ≠ 0 := by
        simp only [Q, map_add, map_one, h0, hφPoly_eval, map_zero, add_zero]
        decide
      have hsupp := subspace_poly_support_ge W0 hW0_dim Q hQ_deg hQ0
      have hsub : Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ W0 ∧ MvPolynomial.eval x Q ≠ 0) ⊆
          insert 0 extra := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨_, hxW0, hxQ⟩ := hx
        by_cases hx0 : x = 0
        · rw [hx0]; exact Finset.mem_insert_self 0 extra
        · apply Finset.mem_insert_of_mem
          obtain ⟨b, hb_or, hb_true⟩ := hsucc x hx0
          rcases hb_or with rfl | hx_ex
          · exfalso
            have hevalQ : MvPolynomial.eval x Q = 1 + MvPolynomial.eval x poly + φ x := by
              simp [Q, hφPoly_eval]
            rw [hevalQ] at hxQ
            have hpeq : MvPolynomial.eval x poly = φ x := by
              rcases zmod2_eq_zero_or_one (MvPolynomial.eval x poly) with ha | ha <;>
              rcases zmod2_eq_zero_or_one (φ x) with hb | hb <;>
              rw [ha, hb] at hxQ ⊢ <;>
              first | rfl | exact absurd (by decide) hxQ
            rw [hpeq, hW0_forbid x hxW0] at hb_true
            exact Bool.noConfusion hb_true
          · exact hx_ex
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem h0extra] at hcard
      omega
    · let Q : MvPolynomial (Fin n) (ZMod 2) := poly + φPoly
      have hQ_deg : Q.totalDegree ≤ d := by
        dsimp only [Q]
        have h1' := MvPolynomial.totalDegree_add poly φPoly
        omega
      have hQ0 : MvPolynomial.eval (0 : Fin n → ZMod 2) Q ≠ 0 := by
        simp only [Q, map_add, h1, hφPoly_eval, map_zero, add_zero]
        decide
      have hsupp := subspace_poly_support_ge W1 hW1_dim Q hQ_deg hQ0
      have hsub : Finset.univ.filter (fun x : Fin n → ZMod 2 => x ∈ W1 ∧ MvPolynomial.eval x Q ≠ 0) ⊆
          insert 0 extra := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨_, hxW1, hxQ⟩ := hx
        by_cases hx0 : x = 0
        · rw [hx0]; exact Finset.mem_insert_self 0 extra
        · apply Finset.mem_insert_of_mem
          obtain ⟨b, hb_or, hb_true⟩ := hsucc x hx0
          rcases hb_or with rfl | hx_ex
          · exfalso
            have hevalQ : MvPolynomial.eval x Q = MvPolynomial.eval x poly + φ x := by
              simp [Q, hφPoly_eval]
            rw [hevalQ] at hxQ
            have hpeq : MvPolynomial.eval x poly = φ x + 1 := by
              rcases zmod2_eq_zero_or_one (MvPolynomial.eval x poly) with ha | ha <;>
              rcases zmod2_eq_zero_or_one (φ x) with hb | hb <;>
              rw [ha, hb] at hxQ ⊢ <;>
              first | decide | exact absurd (by decide) hxQ
            rw [hpeq, hW1_forbid x hxW1] at hb_true
            exact Bool.noConfusion hb_true
          · exact hx_ex
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem h0extra] at hcard
      omega
  exact ⟨h2s_le_n, hbud_bound⟩

private def coordP {n : Nat} (i : Fin n) : ((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun p => p.2 i
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private def fstP {n : Nat} : ((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun p => p.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private lemma totalDegree_one_add_X_le {n : ℕ} (i : Fin n) :
    ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X i).totalDegree ≤ 1 := by
  have h := MvPolynomial.totalDegree_add (1 : MvPolynomial (Fin n) (ZMod 2)) (MvPolynomial.X i)
  rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X] at h
  exact le_trans h (by decide)

private lemma backward_dir (n q d budget : Nat) (hq : 0 < q) (hqn : q < n) (_hd : 0 < d)
    (h2s : 2 * (n + 1 - q) ≤ n) (hbud : 2 ^ (n + 1 - q - d) ≤ budget + 1) :
    ∃ (poly : MvPolynomial (Fin n) (ZMod 2)) (extra : Finset (Fin n → ZMod 2)),
      poly.totalDegree ≤ d ∧ (0 : Fin n → ZMod 2) ∉ extra ∧ extra.card ≤ budget ∧
      ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2))
        (ans : ((ZMod 2) × (Fin n → ZMod 2)) → Fin q → ZMod 2) (decode : (Fin q → ZMod 2) → Bool),
        (∀ p j, ans p j = ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p) ∧
        (∀ b : ZMod 2, decode (ans (b, 0)) = false) ∧
        (∀ x : Fin n → ZMod 2, x ≠ 0 → ∃ b : ZMod 2,
          (b = MvPolynomial.eval x poly ∨ x ∈ extra) ∧ decode (ans (b, x)) = true) := by
  classical
  let s := n + 1 - q
  let k := min d s
  have hks : k ≤ s := Nat.min_le_right d s
  have hkd : k ≤ d := Nat.min_le_left d s
  have hsn : s ≤ n := by omega
  have hkn : k ≤ n := le_trans hks hsn
  let idxK : Fin k → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩
  let poly : MvPolynomial (Fin n) (ZMod 2) :=
    ∏ i : Fin k, ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (idxK i))
  have hpoly_deg : poly.totalDegree ≤ d := by
    have h1 : poly.totalDegree ≤
        ∑ i : Fin k, ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (idxK i)).totalDegree :=
      totalDegree_prod_le (Finset.univ : Finset (Fin k))
        (fun i : Fin k => (1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (idxK i))
    have h2 : ∑ i : Fin k, ((1 : MvPolynomial (Fin n) (ZMod 2)) + MvPolynomial.X (idxK i)).totalDegree ≤
        ∑ _i : Fin k, (1 : ℕ) :=
      Finset.sum_le_sum fun i _ => totalDegree_one_add_X_le (idxK i)
    have h3 : ∑ _i : Fin k, (1 : ℕ) = k := by simp
    omega
  have hpoly_eval : ∀ x : Fin n → ZMod 2,
      (MvPolynomial.eval x poly = 1 ↔ ∀ i : Fin k, x (idxK i) = 0) := by
    intro x
    simp only [poly, map_prod, map_add, map_one, MvPolynomial.eval_X]
    constructor
    · intro h1 i
      by_contra hne
      have hxi : x (idxK i) = 1 := by
        rcases zmod2_eq_zero_or_one (x (idxK i)) with h0 | h1'
        · exact absurd h0 hne
        · exact h1'
      have hprod0 : ∏ j : Fin k, (1 + x (idxK j)) = 0 := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hxi]
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h11, zero_mul]
      rw [hprod0] at h1
      exact absurd h1 (by decide)
    · intro hall
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hall i, add_zero]
  let extra : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      x ≠ 0 ∧ ∀ i : Fin n, (i.val < k ∨ s ≤ i.val) → x i = 0)
  have h0extra : (0 : Fin n → ZMod 2) ∉ extra := by
    simp [extra]
  have hextra_card : extra.card ≤ budget := by
    let S0 : Finset (Fin n → ZMod 2) :=
      Finset.univ.filter (fun x : Fin n → ZMod 2 => ∀ i : Fin n, (i.val < k ∨ s ≤ i.val) → x i = 0)
    have h0S0 : (0 : Fin n → ZMod 2) ∈ S0 := by simp [S0]
    have hex_eq : extra = S0.erase 0 := by
      ext x
      simp only [extra, S0, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    have hS0_card : S0.card = 2 ^ (s - k) := by
      have hbij : S0.card = (Finset.univ : Finset (Fin (s - k) → ZMod 2)).card := by
        refine Finset.card_bij (fun x _ j => x ⟨k + j.val, by omega⟩) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x1 h1 x2 h2 hEq
          have hx1 := (Finset.mem_filter.1 h1).2
          have hx2 := (Finset.mem_filter.1 h2).2
          funext i
          by_cases hlt : i.val < k
          · rw [hx1 i (Or.inl hlt), hx2 i (Or.inl hlt)]
          · by_cases hge : s ≤ i.val
            · rw [hx1 i (Or.inr hge), hx2 i (Or.inr hge)]
            · have hj := congrFun hEq ⟨i.val - k, by omega⟩
              have hidx : (⟨k + (i.val - k), by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
              rwa [hidx] at hj
        · intro f _
          let x : Fin n → ZMod 2 := fun i =>
            if h1 : i.val < k then 0
            else if h2 : i.val < s then f ⟨i.val - k, by omega⟩
            else 0
          refine ⟨x, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun i hi => ?_⟩
            rcases hi with h1 | h2
            · simp [x, h1]
            · have hnot : ¬ (i.val < s) := by omega
              dsimp only [x]
              split_ifs <;> rfl
          · funext j
            have h1 : ¬ (k + j.val < k) := by omega
            have h2 : k + j.val < s := by omega
            simp [x, h1, h2]
      rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have hsk : s - k = n + 1 - q - d := by omega
    rw [hex_eq, Finset.card_erase_of_mem h0S0, hS0_card, hsk]
    omega
  let idx0 : Fin q → Fin n := fun j =>
    if j.val - 1 < s then ⟨j.val - 1, by omega⟩ else ⟨j.val - 1 + s, by omega⟩
  let idx1 : Fin q → Fin n := fun j => ⟨s + (j.val - 1), by omega⟩
  let ask : (j : Fin q) → (Fin j.val → ZMod 2) → (((ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2) :=
    fun j pref =>
      if hj : j.val = 0 then fstP
      else if pref ⟨0, Nat.pos_of_ne_zero hj⟩ = 0 then coordP (idx0 j)
      else coordP (idx1 j)
  let ans : ((ZMod 2) × (Fin n → ZMod 2)) → Fin q → ZMod 2 := fun p j =>
    if j.val = 0 then p.1
    else if p.1 = 0 then p.2 (idx0 j)
    else p.2 (idx1 j)
  let decode : (Fin q → ZMod 2) → Bool := fun t =>
    decide (∃ j : Fin q, j.val ≠ 0 ∧ t j ≠ 0)
  have hrec : ∀ p j, ans p j =
      ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p := by
    intro p j
    by_cases hj : j.val = 0
    · simp [ans, ask, hj, fstP]
    · simp only [ans, ask, hj, ↓reduceIte, ↓reduceDIte]
      by_cases hp1 : p.1 = 0 <;> simp [hp1, coordP]
  have hzero : ∀ b : ZMod 2, decode (ans (b, 0)) = false := by
    intro b
    simp only [decode, decide_eq_false_iff_not]
    rintro ⟨j, hj, hne⟩
    simp only [ans, hj, ↓reduceIte] at hne
    split_ifs at hne <;> exact hne rfl
  have hdec0_true : ∀ x : Fin n → ZMod 2,
      (∃ i : Fin n, (i.val < s ∨ 2 * s ≤ i.val) ∧ x i ≠ 0) →
      decode (ans (0, x)) = true := by
    rintro x ⟨i, hi, hxi⟩
    simp only [decode, decide_eq_true_eq]
    rcases hi with hlt | hge
    · refine ⟨⟨i.val + 1, by omega⟩, by dsimp; omega, ?_⟩
      have hne0 : i.val + 1 ≠ 0 := by omega
      have hlt' : i.val + 1 - 1 < s := by omega
      have hidx : idx0 ⟨i.val + 1, by omega⟩ = i := by
        apply Fin.ext
        simp only [idx0, hlt', ↓reduceIte]
        omega
      simp only [ans, hne0, ↓reduceIte, hidx]
      exact hxi
    · refine ⟨⟨i.val - s + 1, by omega⟩, by dsimp; omega, ?_⟩
      have hne0 : i.val - s + 1 ≠ 0 := by omega
      have hnot : ¬ (i.val - s + 1 - 1 < s) := by omega
      have hidx : idx0 ⟨i.val - s + 1, by omega⟩ = i := by
        apply Fin.ext
        simp only [idx0, hnot, ↓reduceIte]
        omega
      simp only [ans, hne0, ↓reduceIte, hidx]
      exact hxi
  have hdec1_true : ∀ x : Fin n → ZMod 2,
      (∃ i : Fin n, s ≤ i.val ∧ x i ≠ 0) →
      decode (ans (1, x)) = true := by
    rintro x ⟨i, hi, hxi⟩
    simp only [decode, decide_eq_true_eq]
    refine ⟨⟨i.val - s + 1, by omega⟩, by dsimp; omega, ?_⟩
    have hne0 : i.val - s + 1 ≠ 0 := by omega
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have hidx : idx1 ⟨i.val - s + 1, by omega⟩ = i := by
      apply Fin.ext
      simp only [idx1]
      omega
    simp only [ans, hne0, h10, ↓reduceIte, hidx]
    exact hxi
  refine ⟨poly, extra, hpoly_deg, h0extra, hextra_card, ask, ans, decode, hrec, hzero, ?_⟩
  intro x hxne
  by_cases hge : ∃ i : Fin n, s ≤ i.val ∧ x i ≠ 0
  · by_cases hlt_k : ∃ i : Fin k, x (idxK i) ≠ 0
    · obtain ⟨i0, hi0⟩ := hlt_k
      have hpe : MvPolynomial.eval x poly = 0 := by
        rcases zmod2_eq_zero_or_one (MvPolynomial.eval x poly) with h0 | h1
        · exact h0
        · exact absurd ((hpoly_eval x).1 h1 i0) hi0
      refine ⟨0, Or.inl hpe.symm, hdec0_true x ⟨idxK i0, Or.inl (Nat.lt_of_lt_of_le i0.isLt hks), hi0⟩⟩
    · push Not at hlt_k
      have hpe : MvPolynomial.eval x poly = 1 := (hpoly_eval x).2 hlt_k
      exact ⟨1, Or.inl hpe.symm, hdec1_true x hge⟩
  · push Not at hge
    by_cases hlt_k : ∃ i : Fin k, x (idxK i) ≠ 0
    · obtain ⟨i0, hi0⟩ := hlt_k
      have hpe : MvPolynomial.eval x poly = 0 := by
        rcases zmod2_eq_zero_or_one (MvPolynomial.eval x poly) with h0 | h1
        · exact h0
        · exact absurd ((hpoly_eval x).1 h1 i0) hi0
      refine ⟨0, Or.inl hpe.symm, hdec0_true x ⟨idxK i0, Or.inl (Nat.lt_of_lt_of_le i0.isLt hks), hi0⟩⟩
    · push Not at hlt_k
      have hx_ex : x ∈ extra := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hxne, fun i hi => ?_⟩
        rcases hi with h1 | h2
        · exact hlt_k ⟨i.val, h1⟩
        · exact hge i h2
      have hex_nz : ∃ i : Fin n, i.val < s ∧ x i ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hxne
        funext i
        by_cases hi : i.val < s
        · exact hall i hi
        · exact hge i (by omega)
      obtain ⟨i0, hi0_lt, hi0_ne⟩ := hex_nz
      exact ⟨0, Or.inr hx_ex, hdec0_true x ⟨i0, Or.inl hi0_lt, hi0_ne⟩⟩

end PEqualNP.Outside.L_lib_781_aux

theorem PEqualNP.Outside.L_lib_781 :
  ∀ (n q d budget : Nat), 0 < q → q < n → 0 < d →
    let F := ZMod 2
    let V := Fin n → F
    let P := F × V
    let dim := n+1-q
    let success := fun (poly : MvPolynomial (Fin n) F) (extra : Finset V) =>
      ∃ (ask : (j : Fin q) → (Fin j.val → F) → (P →ₗ[F] F))
          (ans : P → Fin q → F) (decode : (Fin q → F) → Bool),
        (∀ (p : P) (j : Fin q), ans p j =
          ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p) ∧
        (∀ b : F, decode (ans (b,0)) = false) ∧
        (∀ x : V, x ≠ 0 → ∃ b : F,
          (b = MvPolynomial.eval x poly ∨ x ∈ extra) ∧ decode (ans (b,x)) = true)
    Iff
      (∃ (poly : MvPolynomial (Fin n) F) (extra : Finset V),
        poly.totalDegree ≤ d ∧ (0 : V) ∉ extra ∧ extra.card ≤ budget ∧ success poly extra)
      (2*dim ≤ n ∧ 2^(dim-d) ≤ budget+1) := by
  intro n q d budget hq hqn hd F V P dim success
  constructor
  · rintro ⟨poly, extra, hdeg, h0extra, hbud, ask, ans, decode, hrec, hzero, hsucc⟩
    exact PEqualNP.Outside.L_lib_781_aux.forward_dir n q d budget hq hqn hd poly extra hdeg
      h0extra hbud ask ans decode hrec hzero hsucc
  · rintro ⟨h2s, hbud⟩
    exact PEqualNP.Outside.L_lib_781_aux.backward_dir n q d budget hq hqn hd h2s hbud

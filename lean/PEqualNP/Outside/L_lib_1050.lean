import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1050

open scoped Matrix

private lemma prod_pm_one {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, f x = 1 ∨ f x = -1) :
    (∏ x ∈ s, f x) = 1 ∨ (∏ x ∈ s, f x) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha1 := hf a (Finset.mem_insert_self a s)
    have ih1 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    rcases ha1 with h1 | h1 <;> rcases ih1 with h2 | h2
    · left; rw [h1, h2]; norm_num
    · right; rw [h1, h2]; norm_num
    · right; rw [h1, h2]; norm_num
    · left; rw [h1, h2]; norm_num

private lemma exists_separating_fin {ι : Type*} [Nonempty ι] {W : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (φ : ι → (W →ₗ[ℝ] ℝ))
    (hsep : ∀ w : W, (∀ i : ι, φ i w = 0) → w = 0) :
    ∀ (k : ℕ) (S : Submodule ℝ W), Module.finrank ℝ S ≤ k →
      ∃ idx : Fin k → ι, ∀ w ∈ S, (∀ h : Fin k, φ (idx h) w = 0) → w = 0 := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨Fin.elim0, fun w hw _ => ?_⟩
    have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
    rw [hbot, Submodule.mem_bot] at hw
    exact hw
  | succ k ih =>
    intro S hS
    by_cases hbot : S = ⊥
    · refine ⟨fun _ => Classical.arbitrary ι, fun w hw _ => ?_⟩
      rw [hbot, Submodule.mem_bot] at hw
      exact hw
    · rcases Submodule.exists_mem_ne_zero_of_ne_bot hbot with ⟨w0, hw0S, hw0_ne⟩
      have hex_i : ∃ i0 : ι, φ i0 w0 ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hw0_ne (hsep w0 hall)
      rcases hex_i with ⟨i0, hi0⟩
      let f0 : S →ₗ[ℝ] ℝ := (φ i0).domRestrict S
      have hker_le : Module.finrank ℝ (LinearMap.ker f0) ≤ k := by
        have hkn := LinearMap.finrank_range_add_finrank_ker f0
        have hrg_pos : 0 < Module.finrank ℝ (LinearMap.range f0) := by
          have hne : LinearMap.range f0 ≠ ⊥ := by
            intro hb
            have hm : f0 ⟨w0, hw0S⟩ ∈ (⊥ : Submodule ℝ ℝ) := hb ▸ ⟨⟨w0, hw0S⟩, rfl⟩
            rw [Submodule.mem_bot] at hm
            exact hi0 hm
          by_contra h0
          exact hne (Submodule.finrank_eq_zero.mp (by omega))
        omega
      let S' : Submodule ℝ W := (LinearMap.ker f0).map S.subtype
      have hS'_rk : Module.finrank ℝ S' ≤ k :=
        (Submodule.finrank_map_le S.subtype (LinearMap.ker f0)).trans hker_le
      rcases ih S' hS'_rk with ⟨idx', hidx'⟩
      refine ⟨Fin.cons i0 idx', fun w hwS hvan => ?_⟩
      have hw0 : φ i0 w = 0 := by
        have h := hvan 0
        simpa using h
      have hwS' : w ∈ S' := ⟨⟨w, hwS⟩, hw0, rfl⟩
      exact hidx' w hwS' fun h => by
        have hv := hvan h.succ
        simpa using hv

private lemma main_1050 (n : ℕ) (H : Fin n → Fin n → Bool) (s : (Fin n × Fin n) → Bool)
    (halign : |Matrix.det (fun i j => if s (i, j) then -(if H i j then (1 : ℝ) else 0)
      else (if H i j then (1 : ℝ) else 0) : Matrix (Fin n) (Fin n) ℝ)| =
      Matrix.permanent (fun i j => if H i j then (1 : ℝ) else 0 : Matrix (Fin n) (Fin n) ℝ)) :
    let V := Submodule.span ℝ {v : (Fin n × Fin n) → ℝ |
      ∃ π : Equiv.Perm (Fin n), (∀ j, H (π j) j = true) ∧
        v = fun e => if π e.2 = e.1 then (1 : ℝ) else 0}
    let d := Module.finrank ℝ V
    ∃ (queries : Fin d → (Fin n × Fin n) → Bool)
      (read : (Fin d → ℝ) → Equiv.Perm (Fin n) → ℝ),
      (∀ h, ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => queries h e ≠ s e)).card ≤ 1) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ A i j) → (∀ i j, H i j = false → A i j = 0) →
        ∀ π : Equiv.Perm (Fin n),
          read (fun h => Matrix.det (fun i j => if queries h (i, j) then -A i j else A i j :
            Matrix (Fin n) (Fin n) ℝ)) π = ∏ j : Fin n, A (π j) j := by
  classical
  intro V d
  let vec : Equiv.Perm (Fin n) → (Fin n × Fin n) → ℝ :=
    fun π e => if π e.2 = e.1 then 1 else 0
  let D : ((Fin n × Fin n) → Bool) → Matrix (Fin n) (Fin n) ℝ → ℝ :=
    fun s' M => Matrix.det (fun i j => if s' (i, j) then -M i j else M i j : Matrix (Fin n) (Fin n) ℝ)
  let unit : Matrix (Fin n) (Fin n) ℝ := fun i j => if H i j then 1 else 0
  let GoodPerm : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π => ∀ j : Fin n, H (π j) j = true)
  by_cases hn0 : n = 0
  · subst hn0
    have hVbot : V = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v _
      funext e
      exact Fin.elim0 e.1
    have hd0 : d = 0 := by
      dsimp only [d]
      rw [hVbot, finrank_bot]
    refine ⟨fun h => False.elim (by have := h.isLt; omega), fun _ _ => 1, ?_, ?_⟩
    · intro h
      exact False.elim (by have := h.isLt; omega)
    · intro A _ _ π
      simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hEmpty : GoodPerm = ∅
    · have hVbot : V = ⊥ := by
        have hset : {v : (Fin n × Fin n) → ℝ |
            ∃ π : Equiv.Perm (Fin n), (∀ j, H (π j) j = true) ∧
              v = fun e => if π e.2 = e.1 then (1 : ℝ) else 0} = ∅ := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
          intro π hπ
          have hmem : π ∈ GoodPerm := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ.1⟩
          rw [hEmpty] at hmem
          exact Finset.notMem_empty _ hmem
        dsimp only [V]
        rw [hset, Submodule.span_empty]
      have hd0 : d = 0 := by
        dsimp only [d]
        rw [hVbot, finrank_bot]
      refine ⟨fun h => False.elim (by have := h.isLt; omega), fun _ _ => 0, ?_, ?_⟩
      · intro h
        exact False.elim (by have := h.isLt; omega)
      · intro A _ hAsupp π
        have hnot : ¬ ∀ j : Fin n, H (π j) j = true := by
          intro hall
          have hmem : π ∈ GoodPerm := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩
          rw [hEmpty] at hmem
          exact Finset.notMem_empty _ hmem
        push_neg at hnot
        rcases hnot with ⟨j0, hj0⟩
        have hfalse : H (π j0) j0 = false := Bool.eq_false_iff.mpr hj0
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ j0) (hAsupp (π j0) j0 hfalse)
    · have hNonempty : GoodPerm.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let sgn : ((Fin n × Fin n) → Bool) → Equiv.Perm (Fin n) → ℝ := fun s' π =>
        ((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ j : Fin n, (if s' (π j, j) then (-1 : ℝ) else 1)
      have hsgn_pm : ∀ s' π, sgn s' π = 1 ∨ sgn s' π = -1 := by
        intro s' π
        have hprod := prod_pm_one (Finset.univ : Finset (Fin n))
          (fun j => if s' (π j, j) then (-1 : ℝ) else 1)
          (fun j _ => by split_ifs <;> [right; left] <;> rfl)
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs1 | hs1 <;> rcases hprod with hp | hp
        · left; dsimp only [sgn]; rw [hs1, hp]; norm_num
        · right; dsimp only [sgn]; rw [hs1, hp]; norm_num
        · right; dsimp only [sgn]; rw [hs1, hp]; norm_num
        · left; dsimp only [sgn]; rw [hs1, hp]; norm_num
      have hD_formula : ∀ (s' : (Fin n × Fin n) → Bool) (M : Matrix (Fin n) (Fin n) ℝ),
          (∀ i j, H i j = false → M i j = 0) →
          D s' M = ∑ π ∈ GoodPerm, sgn s' π * ∏ j : Fin n, M (π j) j := by
        intro s' M hMsupp
        let Ms : Matrix (Fin n) (Fin n) ℝ := fun i j => if s' (i, j) then -M i j else M i j
        change Ms.det = _
        rw [Matrix.det_apply]
        have hsmul : ∀ π : Equiv.Perm (Fin n),
            Equiv.Perm.sign π • ∏ j : Fin n, Ms (π j) j =
            sgn s' π * ∏ j : Fin n, M (π j) j := by
          intro π
          have hfact : ∏ j : Fin n, Ms (π j) j =
              (∏ j : Fin n, (if s' (π j, j) then (-1 : ℝ) else 1)) * ∏ j : Fin n, M (π j) j := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun j _ => ?_
            dsimp only [Ms]
            split_ifs <;> ring
          rw [hfact]
          dsimp only [sgn]
          rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1
          · rw [h1, one_smul]; norm_num
          · rw [h1, Units.neg_smul, one_smul]; norm_num
        simp_rw [hsmul]
        rw [← Finset.sum_sdiff (Finset.subset_univ GoodPerm)]
        have hzero : ∑ π ∈ Finset.univ \ GoodPerm, sgn s' π * ∏ j : Fin n, M (π j) j = 0 := by
          refine Finset.sum_eq_zero fun π hπ => ?_
          have hnot : ¬ ∀ j : Fin n, H (π j) j = true := by
            have := (Finset.mem_sdiff.mp hπ).2
            simpa [GoodPerm] using this
          push_neg at hnot
          rcases hnot with ⟨j0, hj0⟩
          have hM0 : M (π j0) j0 = 0 := hMsupp (π j0) j0 (Bool.eq_false_iff.mpr hj0)
          rw [Finset.prod_eq_zero (f := fun j => M (π j) j) (Finset.mem_univ j0) hM0, mul_zero]
        rw [hzero, zero_add]
      have hunit_supp : ∀ i j, H i j = false → unit i j = 0 := fun i j h => by simp [unit, h]
      have hD_unit : D s unit = ∑ π ∈ GoodPerm, sgn s π := by
        rw [hD_formula s unit hunit_supp]
        refine Finset.sum_congr rfl fun π hπ => ?_
        have h1 : ∏ j : Fin n, unit (π j) j = 1 :=
          Finset.prod_eq_one fun j _ => by simp [unit, (Finset.mem_filter.mp hπ).2 j]
        rw [h1, mul_one]
      have hperm_unit : Matrix.permanent unit = (GoodPerm.card : ℝ) := by
        rw [Matrix.permanent]
        rw [← Finset.sum_sdiff (Finset.subset_univ GoodPerm)]
        have hzero : ∑ π ∈ Finset.univ \ GoodPerm, ∏ j : Fin n, unit (π j) j = 0 := by
          refine Finset.sum_eq_zero fun π hπ => ?_
          have hnot : ¬ ∀ j : Fin n, H (π j) j = true := by
            have := (Finset.mem_sdiff.mp hπ).2
            simpa [GoodPerm] using this
          push_neg at hnot
          rcases hnot with ⟨j0, hj0⟩
          exact Finset.prod_eq_zero (Finset.mem_univ j0) (hunit_supp _ _ (Bool.eq_false_iff.mpr hj0))
        have hones : ∑ π ∈ GoodPerm, ∏ j : Fin n, unit (π j) j = (GoodPerm.card : ℝ) := by
          have h1 : ∀ π ∈ GoodPerm, ∏ j : Fin n, unit (π j) j = 1 := fun π hπ =>
            Finset.prod_eq_one fun j _ => by simp [unit, (Finset.mem_filter.mp hπ).2 j]
          rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hzero, zero_add, hones]
      have hex_eps : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ π ∈ GoodPerm, sgn s π = ε := by
        have habs : |∑ π ∈ GoodPerm, sgn s π| = (GoodPerm.card : ℝ) := by
          rw [← hD_unit, ← hperm_unit]
          exact halign
        have hcases := (abs_eq (Nat.cast_nonneg GoodPerm.card)).mp habs
        rcases hcases with hpos | hneg
        · refine ⟨1, Or.inl rfl, fun π hπ => ?_⟩
          have hsum0 : ∑ σ ∈ GoodPerm, (1 - sgn s σ) = 0 := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hpos, sub_self]
          have hnn : ∀ σ ∈ GoodPerm, 0 ≤ 1 - sgn s σ := fun σ _ => by
            rcases hsgn_pm s σ with h1 | h1 <;> linarith
          have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 π hπ
          linarith
        · refine ⟨-1, Or.inr rfl, fun π hπ => ?_⟩
          have hsum0 : ∑ σ ∈ GoodPerm, (sgn s σ + 1) = 0 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hneg]
            ring
          have hnn : ∀ σ ∈ GoodPerm, 0 ≤ sgn s σ + 1 := fun σ _ => by
            rcases hsgn_pm s σ with h1 | h1 <;> linarith
          have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 π hπ
          linarith
      rcases hex_eps with ⟨ε, hε_pm, hε_eq⟩
      have hε_ne : ε ≠ 0 := by rcases hε_pm with rfl | rfl <;> norm_num
      let flip : (Fin n × Fin n) → (Fin n × Fin n) → Bool := fun e0 e =>
        if e = e0 then !s e else s e
      have hflip_diff : ∀ e0 : Fin n × Fin n,
          ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => flip e0 e ≠ s e)).card ≤ 1 := by
        intro e0
        have hsub : (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => flip e0 e ≠ s e) ⊆ {e0} := by
          intro e he
          have hne := (Finset.mem_filter.mp he).2
          rw [Finset.mem_singleton]
          by_contra he_ne
          exact hne (by simp [flip, he_ne])
        exact (Finset.card_le_card hsub).trans (by simp)
      have hsgn_flip : ∀ (e0 : Fin n × Fin n) (π : Equiv.Perm (Fin n)),
          π ∈ GoodPerm → sgn (flip e0) π = ε * (1 - 2 * vec π e0) := by
        intro e0 π hπ
        have hbase := hε_eq π hπ
        have hprod_rel : ∏ j : Fin n, (if flip e0 (π j, j) then (-1 : ℝ) else 1) =
            (1 - 2 * vec π e0) * ∏ j : Fin n, (if s (π j, j) then (-1 : ℝ) else 1) := by
          rw [← Finset.mul_prod_erase Finset.univ (fun j => if flip e0 (π j, j) then (-1 : ℝ) else 1)
            (Finset.mem_univ e0.2)]
          rw [← Finset.mul_prod_erase Finset.univ (fun j => if s (π j, j) then (-1 : ℝ) else 1)
            (Finset.mem_univ e0.2)]
          have hrest : ∏ j ∈ Finset.univ.erase e0.2, (if flip e0 (π j, j) then (-1 : ℝ) else 1) =
              ∏ j ∈ Finset.univ.erase e0.2, (if s (π j, j) then (-1 : ℝ) else 1) := by
            refine Finset.prod_congr rfl fun j hj => ?_
            have hj_ne : j ≠ e0.2 := (Finset.mem_erase.mp hj).1
            have hp_ne : (π j, j) ≠ e0 := fun h => hj_ne (congrArg Prod.snd h)
            simp [flip, hp_ne]
          rw [hrest, ← mul_assoc]
          congr 1
          by_cases hhit : π e0.2 = e0.1
          · have hpair : (π e0.2, e0.2) = e0 := Prod.ext hhit rfl
            simp only [flip, hpair, ↓reduceIte, vec, hhit]
            cases s e0 <;> norm_num
          · have hpair : (π e0.2, e0.2) ≠ e0 := fun h => hhit (congrArg Prod.fst h)
            simp only [flip, hpair, ↓reduceIte, vec, hhit]
            ring
        dsimp only [sgn] at hbase ⊢
        rw [hprod_rel]
        calc ((Equiv.Perm.sign π : ℤ) : ℝ) *
              ((1 - 2 * vec π e0) * ∏ j : Fin n, if s (π j, j) then (-1 : ℝ) else 1)
            = (((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ j : Fin n, if s (π j, j) then (-1 : ℝ) else 1) *
              (1 - 2 * vec π e0) := by ring
          _ = ε * (1 - 2 * vec π e0) := by rw [hbase]
      let j0 : Fin n := ⟨0, hn_pos⟩
      let mVec : Matrix (Fin n) (Fin n) ℝ → (Fin n × Fin n) → ℝ := fun A =>
        ∑ π ∈ GoodPerm, (∏ j : Fin n, A (π j) j) • vec π
      have hmVec_mem : ∀ A : Matrix (Fin n) (Fin n) ℝ, mVec A ∈ V := fun A =>
        Submodule.sum_mem V fun π hπ =>
          Submodule.smul_mem V _ (Submodule.subset_span ⟨π, (Finset.mem_filter.mp hπ).2, rfl⟩)
      have hvec_col_sum : ∀ π : Equiv.Perm (Fin n), ∑ i : Fin n, vec π (i, j0) = 1 := by
        intro π
        rw [Finset.sum_eq_single (π j0)]
        · simp [vec]
        · intro i _ hne; simp [vec, hne.symm]
        · intro h; exact (h (Finset.mem_univ _)).elim
      have hmVec_col_sum : ∀ A : Matrix (Fin n) (Fin n) ℝ,
          ∑ i : Fin n, mVec A (i, j0) = ∑ π ∈ GoodPerm, ∏ j : Fin n, A (π j) j := by
        intro A
        dsimp only [mVec]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [← Finset.mul_sum, hvec_col_sum π, mul_one]
      let φBase : V →ₗ[ℝ] ℝ :=
        { toFun := fun v => ε * ∑ i : Fin n, v.1 (i, j0)
          map_add' := fun v1 v2 => by
            simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
          map_smul' := fun r v => by
            simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
            ring }
      let φFlip : (Fin n × Fin n) → (V →ₗ[ℝ] ℝ) := fun e0 =>
        { toFun := fun v => ε * ((∑ i : Fin n, v.1 (i, j0)) - 2 * v.1 e0)
          map_add' := fun v1 v2 => by
            simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib]
            ring
          map_smul' := fun r v => by
            simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
            ring }
      let candS : Option (Fin n × Fin n) → (Fin n × Fin n) → Bool := fun o =>
        o.elim s flip
      let candΦ : Option (Fin n × Fin n) → (V →ₗ[ℝ] ℝ) := fun o =>
        o.elim φBase φFlip
      have hcand_diff : ∀ o : Option (Fin n × Fin n),
          ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => candS o e ≠ s e)).card ≤ 1 := by
        intro o
        cases o with
        | none => simp [candS]
        | some e0 => exact hflip_diff e0
      have hcand_eval : ∀ (o : Option (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) ℝ),
          (∀ i j, H i j = false → A i j = 0) →
          candΦ o ⟨mVec A, hmVec_mem A⟩ = D (candS o) A := by
        intro o A hAsupp
        cases o with
        | none =>
          dsimp only [candΦ, candS, Option.elim, φBase, LinearMap.coe_mk, AddHom.coe_mk]
          rw [hmVec_col_sum A, Finset.mul_sum, hD_formula s A hAsupp]
          refine Finset.sum_congr rfl fun π hπ => ?_
          rw [hε_eq π hπ]
        | some e0 =>
          dsimp only [candΦ, candS, Option.elim, φFlip, LinearMap.coe_mk, AddHom.coe_mk]
          rw [hmVec_col_sum A, hD_formula (flip e0) A hAsupp]
          have hm_e0 : mVec A e0 = ∑ π ∈ GoodPerm, (∏ j : Fin n, A (π j) j) * vec π e0 := by
            simp [mVec]
          rw [hm_e0, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun π hπ => ?_
          rw [hsgn_flip e0 π hπ]
          ring
      have hsep : ∀ v : V, (∀ o : Option (Fin n × Fin n), candΦ o v = 0) → v = 0 := by
        intro v hv
        have hb : ε * ∑ i : Fin n, v.1 (i, j0) = 0 := hv none
        have hS0 : ∑ i : Fin n, v.1 (i, j0) = 0 := (mul_eq_zero.mp hb).resolve_left hε_ne
        apply Subtype.ext
        funext e0
        have hf : ε * ((∑ i : Fin n, v.1 (i, j0)) - 2 * v.1 e0) = 0 := hv (some e0)
        rw [hS0, zero_sub] at hf
        have h2 : -(2 * v.1 e0) = 0 := (mul_eq_zero.mp hf).resolve_left hε_ne
        change v.1 e0 = 0
        linarith
      have htop_rk : Module.finrank ℝ (⊤ : Submodule ℝ V) ≤ d := by
        rw [finrank_top]
      rcases exists_separating_fin candΦ hsep d ⊤ htop_rk with ⟨idx, hidx⟩
      have hidx_inj : ∀ v1 v2 : V,
          (∀ h : Fin d, candΦ (idx h) v1 = candΦ (idx h) v2) → v1 = v2 := by
        intro v1 v2 heq
        have hdiff0 : v1 - v2 = 0 := hidx (v1 - v2) Submodule.mem_top fun h => by
          rw [map_sub, heq h, sub_self]
        exact sub_eq_zero.mp hdiff0
      have hunique_w : ∀ A B : Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, 0 ≤ A i j) → (∀ i j, H i j = false → A i j = 0) →
          (∀ i j, 0 ≤ B i j) → (∀ i j, H i j = false → B i j = 0) →
          mVec A = mVec B →
          ∀ π : Equiv.Perm (Fin n), ∏ j : Fin n, A (π j) j = ∏ j : Fin n, B (π j) j := by
        intro A B hAnn hAsupp hBnn hBsupp hmEq
        let wM : Matrix (Fin n) (Fin n) ℝ → Equiv.Perm (Fin n) → ℝ :=
          fun M π => ∏ j : Fin n, M (π j) j
        have hw_nn : ∀ M : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ M i j) →
            ∀ π, 0 ≤ wM M π := fun M hM π => Finset.prod_nonneg fun j _ => hM (π j) j
        have hw_pos_iff : ∀ M : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ M i j) →
            ∀ π ∈ GoodPerm, 0 < wM M π ↔ ∀ j : Fin n, 0 < mVec M (π j, j) := by
          intro M hM π hπ
          constructor
          · intro hw j
            have hm_ge : wM M π ≤ mVec M (π j, j) := by
              have hterm : (wM M π • vec π) (π j, j) = wM M π := by simp [vec]
              rw [← hterm]
              dsimp only [mVec]
              rw [Finset.sum_apply]
              exact Finset.single_le_sum (f := fun σ => (wM M σ • vec σ) (π j, j))
                (fun σ _ => by
                  simp only [Pi.smul_apply, smul_eq_mul]
                  refine mul_nonneg (hw_nn M hM σ) ?_
                  dsimp only [vec]; split_ifs <;> norm_num)
                hπ
            linarith
          · intro hall
            refine Finset.prod_pos fun j _ => ?_
            have hpos_j := hall j
            by_contra hle
            have hM0 : M (π j) j = 0 := le_antisymm (not_lt.mp hle) (hM (π j) j)
            have hm0 : mVec M (π j, j) = 0 := by
              dsimp only [mVec]
              rw [Finset.sum_apply]
              refine Finset.sum_eq_zero fun σ _ => ?_
              simp only [Pi.smul_apply, smul_eq_mul, vec]
              by_cases hhit : σ j = π j
              · rw [if_pos hhit, mul_one]
                exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hhit, hM0])
              · rw [if_neg hhit, mul_zero]
            linarith
        let Supp := GoodPerm.filter (fun π => 0 < wM A π)
        have hSupp_B : ∀ π ∈ GoodPerm, π ∈ Supp ↔ 0 < wM B π := by
          intro π hπ
          simp only [Supp, Finset.mem_filter, hπ, true_and]
          rw [hw_pos_iff A hAnn π hπ, hw_pos_iff B hBnn π hπ, hmEq]
        have hlog_w : ∀ (M : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ M i j) →
            ∀ π ∈ GoodPerm, 0 < wM M π →
            Real.log (wM M π) = ∑ e : Fin n × Fin n, vec π e * Real.log (M e.1 e.2) := by
          intro M hM π _ hpos
          have hne_j : ∀ j : Fin n, M (π j) j ≠ 0 := by
            intro j h0
            have := Finset.prod_eq_zero (f := fun k => M (π k) k) (Finset.mem_univ j) h0
            change wM M π = 0 at this
            linarith
          have hlogp : Real.log (wM M π) = ∑ j : Fin n, Real.log (M (π j) j) :=
            Real.log_prod fun j _ => hne_j j
          rw [hlogp, Fintype.sum_prod_type_right]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single (π j)]
          · simp [vec]
          · intro i _ hne; simp [vec, hne.symm]
          · intro h; exact (h (Finset.mem_univ _)).elim
        have hsum_zero : ∑ π ∈ Supp, (wM A π - wM B π) * (Real.log (wM A π) - Real.log (wM B π)) = 0 := by
          have hrew : ∑ π ∈ Supp, (wM A π - wM B π) * (Real.log (wM A π) - Real.log (wM B π)) =
              ∑ π ∈ Supp, ∑ e : Fin n × Fin n,
                (wM A π - wM B π) * (vec π e * (Real.log (A e.1 e.2) - Real.log (B e.1 e.2))) := by
            refine Finset.sum_congr rfl fun π hπ => ?_
            have hπG : π ∈ GoodPerm := (Finset.mem_filter.mp hπ).1
            have hposA : 0 < wM A π := (Finset.mem_filter.mp hπ).2
            have hposB : 0 < wM B π := (hSupp_B π hπG).mp hπ
            rw [hlog_w A hAnn π hπG hposA, hlog_w B hBnn π hπG hposB,
              ← Finset.sum_sub_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => by ring
          rw [hrew, Finset.sum_comm]
          refine Finset.sum_eq_zero fun e _ => ?_
          have hfact : ∑ π ∈ Supp, (wM A π - wM B π) * (vec π e * (Real.log (A e.1 e.2) - Real.log (B e.1 e.2))) =
              (Real.log (A e.1 e.2) - Real.log (B e.1 e.2)) * ∑ π ∈ Supp, (wM A π - wM B π) * vec π e := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun π _ => by ring
          rw [hfact]
          have hsub_eq : ∑ π ∈ Supp, (wM A π - wM B π) * vec π e =
              ∑ π ∈ GoodPerm, (wM A π - wM B π) * vec π e := by
            have hsub : Supp ⊆ GoodPerm := Finset.filter_subset _ _
            rw [← Finset.sum_sdiff hsub]
            have hz : ∑ π ∈ GoodPerm \ Supp, (wM A π - wM B π) * vec π e = 0 := by
              refine Finset.sum_eq_zero fun π hπ => ?_
              have hπG : π ∈ GoodPerm := (Finset.mem_sdiff.mp hπ).1
              have hnotS : π ∉ Supp := (Finset.mem_sdiff.mp hπ).2
              have hA0 : wM A π = 0 := by
                have hnotA : ¬ 0 < wM A π := fun hp => hnotS (Finset.mem_filter.mpr ⟨hπG, hp⟩)
                exact le_antisymm (not_lt.mp hnotA) (hw_nn A hAnn π)
              have hB0 : wM B π = 0 := by
                have hnotB : ¬ 0 < wM B π := fun hp => hnotS ((hSupp_B π hπG).mpr hp)
                exact le_antisymm (not_lt.mp hnotB) (hw_nn B hBnn π)
              rw [hA0, hB0, sub_self, zero_mul]
            rw [hz, zero_add]
          rw [hsub_eq]
          have hm_diff : ∑ π ∈ GoodPerm, (wM A π - wM B π) * vec π e = mVec A e - mVec B e := by
            simp only [sub_mul, Finset.sum_sub_distrib, mVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wM]
          rw [hm_diff, hmEq, sub_self, mul_zero]
        have hterm_nn : ∀ π ∈ Supp, 0 ≤ (wM A π - wM B π) * (Real.log (wM A π) - Real.log (wM B π)) := by
          intro π hπ
          have hπG : π ∈ GoodPerm := (Finset.mem_filter.mp hπ).1
          have hposA : 0 < wM A π := (Finset.mem_filter.mp hπ).2
          have hposB : 0 < wM B π := (hSupp_B π hπG).mp hπ
          rcases lt_trichotomy (wM A π) (wM B π) with hlt | heq | hgt
          · have hlog := Real.log_lt_log hposA hlt
            exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
          · rw [heq, sub_self, zero_mul]
          · have hlog := Real.log_lt_log hposB hgt
            exact mul_nonneg (by linarith) (by linarith)
        have hterm_zero := (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hsum_zero
        intro π
        by_cases hπG : π ∈ GoodPerm
        · by_cases hπS : π ∈ Supp
          · have hz := hterm_zero π hπS
            have hposA : 0 < wM A π := (Finset.mem_filter.mp hπS).2
            have hposB : 0 < wM B π := (hSupp_B π hπG).mp hπS
            rcases mul_eq_zero.mp hz with h1 | h2
            · exact sub_eq_zero.mp h1
            · exact Real.log_injOn_pos hposA hposB (sub_eq_zero.mp h2)
          · have hA0 : wM A π = 0 := by
              have hnotA : ¬ 0 < wM A π := fun hp => hπS (Finset.mem_filter.mpr ⟨hπG, hp⟩)
              exact le_antisymm (not_lt.mp hnotA) (hw_nn A hAnn π)
            have hB0 : wM B π = 0 := by
              have hnotB : ¬ 0 < wM B π := fun hp => hπS ((hSupp_B π hπG).mpr hp)
              exact le_antisymm (not_lt.mp hnotB) (hw_nn B hBnn π)
            exact hA0.trans hB0.symm
        · have hnot : ¬ ∀ j : Fin n, H (π j) j = true := by
            simpa [GoodPerm] using hπG
          push_neg at hnot
          rcases hnot with ⟨j1, hj1⟩
          have hf := Bool.eq_false_iff.mpr hj1
          rw [Finset.prod_eq_zero (f := fun j => A (π j) j) (Finset.mem_univ j1) (hAsupp _ _ hf),
            Finset.prod_eq_zero (f := fun j => B (π j) j) (Finset.mem_univ j1) (hBsupp _ _ hf)]
      let queries : Fin d → (Fin n × Fin n) → Bool := fun h => candS (idx h)
      let read : (Fin d → ℝ) → Equiv.Perm (Fin n) → ℝ := fun y π =>
        if hex : ∃ B : Matrix (Fin n) (Fin n) ℝ,
            (∀ i j, 0 ≤ B i j) ∧ (∀ i j, H i j = false → B i j = 0) ∧
            (∀ h : Fin d, D (queries h) B = y h)
        then ∏ j : Fin n, Classical.choose hex (π j) j
        else 0
      refine ⟨queries, read, fun h => hcand_diff (idx h), fun A hAnn hAsupp π => ?_⟩
      have hex : ∃ B : Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, 0 ≤ B i j) ∧ (∀ i j, H i j = false → B i j = 0) ∧
          (∀ h : Fin d, D (queries h) B = D (queries h) A) :=
        ⟨A, hAnn, hAsupp, fun _ => rfl⟩
      dsimp only [read]
      rw [dif_pos hex]
      let B := Classical.choose hex
      have hB := Classical.choose_spec hex
      have hmEq : mVec B = mVec A := by
        have hvEq : (⟨mVec B, hmVec_mem B⟩ : V) = ⟨mVec A, hmVec_mem A⟩ := by
          apply hidx_inj
          intro h
          rw [hcand_eval (idx h) B hB.2.1, hcand_eval (idx h) A hAsupp]
          exact hB.2.2 h
        exact congrArg Subtype.val hvEq
      exact hunique_w B A hB.1 hB.2.1 hAnn hAsupp hmEq π

end PEqualNP.Outside.L_lib_1050

open PEqualNP.Outside.L_lib_1050 in
theorem PEqualNP.Outside.L_lib_1050 :
    ∀ (n : ℕ) (H : Fin n → Fin n → Bool),
      let I := Fin n
      let E := I × I
      let S := E → Bool
      let unit : Matrix I I ℝ := fun i j => if H i j then 1 else 0
      let D := fun (s : S) (M : Matrix I I ℝ) =>
        Matrix.det (fun i j => if s (i,j) then -M i j else M i j : Matrix I I ℝ)
      let vec := fun (π : Equiv.Perm I) (e : E) => if π e.2 = e.1 then (1 : ℝ) else 0
      let V := Submodule.span ℝ {v : E → ℝ | ∃ π : Equiv.Perm I, (∀ j, H (π j) j = true) ∧ v = vec π}
      let d := Module.finrank ℝ V
      ∀ s : S, |D s unit| = unit.permanent →
        ∃ (queries : Fin d → S) (read : (Fin d → ℝ) → Equiv.Perm I → ℝ),
          (∀ h, ((Finset.univ : Finset E).filter (fun e => queries h e ≠ s e)).card ≤ 1) ∧
          ∀ A : Matrix I I ℝ, (∀ i j, 0 ≤ A i j) → (∀ i j, H i j = false → A i j = 0) →
            ∀ π : Equiv.Perm I, read (fun h => D (queries h) A) π = ∏ j : I, A (π j) j := by
  intro n H I E S unit D vec V d s halign
  exact main_1050 n H s halign

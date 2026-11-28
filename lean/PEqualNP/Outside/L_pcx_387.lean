import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.BoolVanish

namespace PEqualNP.Outside.L_pcx_387_aux

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

lemma zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

lemma odd_of_natCast_eq_one {n : ℕ} (h : (n : ZMod 2) = 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · exfalso
    have h0 : ((k + k : ℕ) : ZMod 2) = 0 := by
      push_cast
      exact zmod2_add_self (k : ZMod 2)
    rw [h0] at h
    exact (by decide : (0 : ZMod 2) ≠ 1) h
  · exact hodd

lemma even_of_natCast_eq_zero {n : ℕ} (h : (n : ZMod 2) = 0) : Even n := by
  rcases Nat.even_or_odd n with hev | ⟨k, rfl⟩
  · exact hev
  · exfalso
    have h1 : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    rw [h1] at h
    exact (by decide : (1 : ZMod 2) ≠ 0) h

lemma prod_eq_ite_all_one {ι : Type*} [DecidableEq ι] (S : Finset ι) (y : ι → ZMod 2) :
    (∏ i ∈ S, y i) = if (∀ i ∈ S, y i = 1) then 1 else 0 := by
  split_ifs with hall
  · exact Finset.prod_eq_one hall
  · push Not at hall
    rcases hall with ⟨i, hi, hne⟩
    have hi0 : y i = 0 := (zmod2_eq_zero_or_one (y i)).resolve_right hne
    exact Finset.prod_eq_zero hi hi0

lemma exists_dual_sep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule (ZMod 2) (ι → ZMod 2)) (u : ι → ZMod 2) (hu : u ∉ K) :
    ∃ w : ι → ZMod 2,
      (∑ y : ι, w y * u y = 1) ∧ (∀ v ∈ K, ∑ y : ι, w y * v y = 0) := by
  classical
  let q : (ι → ZMod 2) ⧸ K := K.mkQ u
  have hq : q ≠ 0 := by
    intro h0
    exact hu ((Submodule.Quotient.mk_eq_zero K).mp h0)
  let Q1 : Submodule (ZMod 2) ((ι → ZMod 2) ⧸ K) := Submodule.span (ZMod 2) {q}
  obtain ⟨Q2, hQ2⟩ := Submodule.exists_isCompl Q1
  let proj : ((ι → ZMod 2) ⧸ K) →ₗ[ZMod 2] Q1 := Q1.projectionOnto Q2 hQ2
  have hQ1_cases : ∀ z : Q1, z.1 = 0 ∨ z.1 = q := by
    intro z
    rcases Submodule.mem_span_singleton.mp z.2 with ⟨c, hc⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · left; simpa using hc.symm
    · right; simpa using hc.symm
  have hq_add_q : q + q = 0 := by
    rw [← two_smul (ZMod 2) q, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  let coord : Q1 →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun z => if z.1 = 0 then 0 else 1
      map_add' := fun z1 z2 => by
        rcases hQ1_cases z1 with h1 | h1 <;> rcases hQ1_cases z2 with h2 | h2
        · simp [h1, h2]
        · simp [h1, h2, hq]
        · simp [h1, h2, hq]
        · simp [h1, h2, hq, hq_add_q]; decide
      map_smul' := fun c z => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp }
  let ψ : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (coord.comp proj).comp K.mkQ
  have hψu : ψ u = 1 := by
    change coord (proj q) = 1
    have hq_mem : q ∈ Q1 := Submodule.subset_span (Set.mem_singleton q)
    have hpq : proj q = ⟨q, hq_mem⟩ :=
      Submodule.projectionOnto_apply_left hQ2 ⟨q, hq_mem⟩
    rw [hpq]
    simp [coord, hq]
  have hψK : ∀ v ∈ K, ψ v = 0 := by
    intro v hv
    change coord (proj (K.mkQ v)) = 0
    have h0 : K.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hv
    rw [h0, map_zero, map_zero]
  let w : ι → ZMod 2 := fun y => ψ (Pi.single y 1)
  have hψ_eval : ∀ v : ι → ZMod 2, ψ v = ∑ y : ι, w y * v y := by
    intro v
    have hdecomp : v = ∑ y : ι, v y • Pi.single y (1 : ZMod 2) := by
      ext y
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨w, ?_, ?_⟩
  · rw [← hψ_eval u, hψu]
  · intro v hv
    rw [← hψ_eval v, hψK v hv]

lemma main_proof :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (MvPolynomial V (ZMod 2))) (t B : ℕ)
        (g : Fin t → MvPolynomial V (ZMod 2)) (c D : Fin t → ℕ)
        (E : Fin t → Set (MvPolynomial V (ZMod 2))),
      let pattern := fun (x : V → ZMod 2) (j : Fin t) => MvPolynomial.eval x (g j)
      let seen := Finset.univ.image pattern
      (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
      (∀ j, (g j).totalDegree ≤ c j) →
      (∀ x : V → ZMod 2, ∃ j : Fin t, pattern x j = 1) →
      (∀ (x : V → ZMod 2) j, pattern x j = 1 → ∀ e ∈ E j, MvPolynomial.eval x e = 0) →
      (∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ E j) (D j)) →
      ¬ PEqualNP.ProofComplexity.PCRefutable F B →
      ∃ Z : Finset (Fin t → ZMod 2), Z ⊆ seen ∧ Odd Z.card ∧
        ∀ S : Finset (Fin t), (∑ i ∈ S, c i) ≤ B → (∃ j ∈ S, D j + c j ≤ B) →
          Even ((Z.filter (fun y => ∀ j ∈ S, y j = 1)).card) := by
  classical
  intro V _ _ F t B g c D E pattern seen hBool hgDeg _ hE hRef hNotRef
  have hgj_der : ∀ j : Fin t, D j + c j ≤ B → PCDerivable F B (g j) := by
    intro j hDj
    have hreplay : PCDerivable F (1 * D j + c j) (g j * bind₁ X (1 : MvPolynomial V (ZMod 2))) := by
      refine pcDerivable_replay (F := F ∪ E j) (G := F) (T := 1) (D := D j) (s := c j)
        X (fun v => by rw [totalDegree_X]) (g j) (hgDeg j) ?_ (hRef j)
      intro a ha hdeg
      rw [bind₁_X_left]
      rcases ha with haF | haE
      · have hax : PCDerivable F (D j) a := PCDerivable.ax haF hdeg
        have hmul := pcDerivable_mul_left hax (g j)
        refine pcDerivable_mono hmul ?_ subset_rfl
        have h1 : (g j).totalDegree + a.totalDegree ≤ c j + D j := Nat.add_le_add (hgDeg j) hdeg
        omega
      · refine BoolVanish.vanish_derivable V F (1 * D j + c j) (g j * a) hBool ?_ ?_
        · refine (totalDegree_mul _ _).trans ?_
          have h1 : (g j).totalDegree + a.totalDegree ≤ c j + D j := Nat.add_le_add (hgDeg j) hdeg
          omega
        · intro x
          rw [map_mul]
          rcases zmod2_eq_zero_or_one (eval x (g j)) with h0 | h1
          · rw [h0, zero_mul]
          · rw [hE x j h1 a haE, mul_zero]
    rw [map_one, mul_one, one_mul] at hreplay
    exact pcDerivable_mono hreplay hDj subset_rfl
  let Good : Finset (Finset (Fin t)) :=
    Finset.univ.filter (fun S => (∑ i ∈ S, c i) ≤ B ∧ ∃ j ∈ S, D j + c j ≤ B)
  have hprod_der : ∀ S ∈ Good, PCDerivable F B (∏ i ∈ S, g i) := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with ⟨hsum, j, hjS, hDj⟩
    have hgj : PCDerivable F B (g j) := hgj_der j hDj
    have hsplit : (∏ i ∈ S, g i) = (∏ i ∈ S.erase j, g i) * g j := by
      rw [mul_comm, Finset.mul_prod_erase S g hjS]
    rw [hsplit]
    have hmul := pcDerivable_mul_left hgj (∏ i ∈ S.erase j, g i)
    refine pcDerivable_mono hmul ?_ subset_rfl
    have hdeg_rest : (∏ i ∈ S.erase j, g i).totalDegree ≤ ∑ i ∈ S.erase j, c i := by
      refine (totalDegree_finsetProd _ _).trans ?_
      exact Finset.sum_le_sum fun i _ => hgDeg i
    have hsum_split : (∑ i ∈ S.erase j, c i) + c j = ∑ i ∈ S, c i := by
      rw [add_comm, Finset.add_sum_erase S c hjS]
    have hdeg_g : (g j).totalDegree ≤ c j := hgDeg j
    omega
  let vVec : Finset (Fin t) → (seen → ZMod 2) := fun S y => ∏ i ∈ S, y.1 i
  let oneVec : seen → ZMod 2 := fun _ => 1
  let K : Submodule (ZMod 2) (seen → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range (fun S : Good => vVec S.1))
  have hone_notMem : oneVec ∉ K := by
    intro hmem
    rcases (Finsupp.mem_span_range_iff_exists_finsupp).mp hmem with ⟨α, hα⟩
    let T : Finset (Finset (Fin t)) :=
      Good.filter (fun S => if hS : S ∈ Good then α ⟨S, hS⟩ = 1 else False)
    have hT_sub : T ⊆ Good := Finset.filter_subset _ _
    have hT_eval : ∀ y : seen, (∑ S ∈ T, ∏ i ∈ S, y.1 i) = 1 := by
      intro y
      have hy : (α.sum fun S a => a • vVec S.1) y = 1 := congrFun hα y
      have hsum_eq : α.sum (fun S a => a • vVec S.1) = ∑ S : Good, α S • vVec S.1 :=
        Finsupp.sum_fintype α (fun S a => a • vVec S.1) (fun _ => zero_smul _ _)
      rw [hsum_eq, Finset.sum_apply] at hy
      rw [← hy]
      trans (∑ S ∈ Good, if hS : S ∈ Good then (α ⟨S, hS⟩) * ∏ i ∈ S, y.1 i else 0)
      · rw [← Finset.sum_filter_add_sum_filter_not Good
          (fun S => if hS : S ∈ Good then α ⟨S, hS⟩ = 1 else False)]
        have hzero : ∑ S ∈ Good.filter (fun S => ¬ if hS : S ∈ Good then α ⟨S, hS⟩ = 1 else False),
            (if hS : S ∈ Good then α ⟨S, hS⟩ * ∏ i ∈ S, y.1 i else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro S hS
          have hSG : S ∈ Good := (Finset.mem_filter.mp hS).1
          have hnot : ¬ (α ⟨S, hSG⟩ = 1) := by
            have := (Finset.mem_filter.mp hS).2
            rwa [dif_pos hSG] at this
          have h0 : α ⟨S, hSG⟩ = 0 := (zmod2_eq_zero_or_one _).resolve_right hnot
          rw [dif_pos hSG, h0, zero_mul]
        rw [hzero, add_zero]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSG : S ∈ Good := (Finset.mem_filter.mp hS).1
        have h1 : α ⟨S, hSG⟩ = 1 := by
          have := (Finset.mem_filter.mp hS).2
          rwa [dif_pos hSG] at this
        rw [dif_pos hSG, h1, one_mul]
      · refine Finset.sum_bij (fun S hS => (⟨S, hS⟩ : Good)) ?_ ?_ ?_ ?_
        · intro S _; exact Finset.mem_univ _
        · intro S1 _ S2 _ heq; exact congrArg Subtype.val heq
        · intro S _; exact ⟨S.1, S.2, rfl⟩
        · intro S hS
          rw [dif_pos hS]
          rfl
    let P : MvPolynomial V (ZMod 2) := ∑ S ∈ T, ∏ i ∈ S, g i
    have hP_der : PCDerivable F B P :=
      pcDerivable_sum T (fun S => ∏ i ∈ S, g i) (fun S hS => hprod_der S (hT_sub hS))
    have hP_deg : P.totalDegree ≤ B := by
      refine totalDegree_finsetSum_le fun S hS => ?_
      have hsum : (∑ i ∈ S, c i) ≤ B := (Finset.mem_filter.mp (hT_sub hS)).2.1
      refine (totalDegree_finsetProd _ _).trans ?_
      exact (Finset.sum_le_sum fun i _ => hgDeg i).trans hsum
    have hP1_deg : (P + 1).totalDegree ≤ B := by
      refine (totalDegree_add P 1).trans (max_le hP_deg ?_)
      simp
    have hP1_van : ∀ x : V → ZMod 2, eval x (P + 1) = 0 := by
      intro x
      have hx_mem : pattern x ∈ seen := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
      have hPx : eval x P = 1 := by
        simp only [P, map_sum, map_prod]
        exact hT_eval ⟨pattern x, hx_mem⟩
      rw [map_add, map_one, hPx]
      decide
    have hP1_der : PCDerivable F B (P + 1) :=
      BoolVanish.vanish_derivable V F B (P + 1) hBool hP1_deg hP1_van
    have h1_der : PCDerivable F B 1 := by
      have hadd := PCDerivable.add hP_der hP1_der
      have hEq : P + (P + 1) = 1 := by
        rw [← add_assoc, ← two_smul (ZMod 2) P, show (2 : ZMod 2) = 0 from rfl,
          zero_smul, zero_add]
      rwa [hEq] at hadd
    exact hNotRef h1_der
  obtain ⟨w, hw1, hwK⟩ := exists_dual_sep K oneVec hone_notMem
  let Z : Finset (Fin t → ZMod 2) :=
    seen.filter (fun y => if hy : y ∈ seen then w ⟨y, hy⟩ = 1 else False)
  have hZ_sub : Z ⊆ seen := Finset.filter_subset _ _
  have hcard_filter : ∀ (p : (Fin t → ZMod 2) → Prop) [DecidablePred p],
      ((Z.filter p).card : ZMod 2) = ∑ y : seen, w y * (if p y.1 then 1 else 0) := by
    intro p _
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    have hsum1 : (∑ _x ∈ Z.filter p, (1 : ZMod 2)) =
        ∑ y ∈ seen, if y ∈ Z ∧ p y then (1 : ZMod 2) else 0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hyZ, hpy⟩; exact ⟨hZ_sub hyZ, hyZ, hpy⟩
      · rintro ⟨_, hyZ, hpy⟩; exact ⟨hyZ, hpy⟩
    rw [hsum1]
    refine Finset.sum_bij (fun y hy => (⟨y, hy⟩ : seen)) ?_ ?_ ?_ ?_
    · intro y _; exact Finset.mem_univ _
    · intro y1 _ y2 _ heq; exact congrArg Subtype.val heq
    · intro y _; exact ⟨y.1, y.2, rfl⟩
    · intro y hy
      have hyZ : y ∈ Z ↔ w ⟨y, hy⟩ = 1 := by
        simp [Z, hy]
      rcases zmod2_eq_zero_or_one (w ⟨y, hy⟩) with hw0 | hw1'
      · have hnot : ¬ y ∈ Z := by rw [hyZ, hw0]; decide
        simp [hw0, hnot]
      · have hmem : y ∈ Z := hyZ.mpr hw1'
        simp [hw1', hmem]
  refine ⟨Z, hZ_sub, ?_, ?_⟩
  · apply odd_of_natCast_eq_one
    have hZ_eq : Z.filter (fun _ => True) = Z := by ext y; simp
    have h := hcard_filter (fun _ => True)
    rw [hZ_eq] at h
    rw [h]
    simpa [oneVec] using hw1
  · intro S hsum hDj
    have hS : S ∈ Good := Finset.mem_filter.mpr ⟨Finset.mem_univ S, hsum, hDj⟩
    apply even_of_natCast_eq_zero
    rw [hcard_filter]
    have hv_mem : vVec S ∈ K := Submodule.subset_span ⟨⟨S, hS⟩, rfl⟩
    have h0 := hwK (vVec S) hv_mem
    calc (∑ y : seen, w y * if ∀ j ∈ S, y.1 j = 1 then 1 else 0)
        = ∑ y : seen, w y * vVec S y := Finset.sum_congr rfl fun y _ => by
            simp only [vVec, prod_eq_ite_all_one]; split_ifs <;> rfl
      _ = 0 := h0

end PEqualNP.Outside.L_pcx_387_aux

theorem PEqualNP.Outside.L_pcx_387 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (MvPolynomial V (ZMod 2))) (t B : ℕ)
        (g : Fin t → MvPolynomial V (ZMod 2)) (c D : Fin t → ℕ)
        (E : Fin t → Set (MvPolynomial V (ZMod 2))),
      let pattern := fun (x : V → ZMod 2) (j : Fin t) => MvPolynomial.eval x (g j)
      let seen := Finset.univ.image pattern
      (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
      (∀ j, (g j).totalDegree ≤ c j) →
      (∀ x : V → ZMod 2, ∃ j : Fin t, pattern x j = 1) →
      (∀ (x : V → ZMod 2) j, pattern x j = 1 → ∀ e ∈ E j, MvPolynomial.eval x e = 0) →
      (∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ E j) (D j)) →
      ¬ PEqualNP.ProofComplexity.PCRefutable F B →
      ∃ Z : Finset (Fin t → ZMod 2), Z ⊆ seen ∧ Odd Z.card ∧
        ∀ S : Finset (Fin t), (∑ i ∈ S, c i) ≤ B → (∃ j ∈ S, D j + c j ≤ B) →
          Even ((Z.filter (fun y => ∀ j ∈ S, y j = 1)).card) :=
  PEqualNP.Outside.L_pcx_387_aux.main_proof

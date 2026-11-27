import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_501_aux

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_add_one_ne (a : ZMod 2) : a + 1 ≠ a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_ne_iff_eq_add_one (a b : ZMod 2) : a ≠ b ↔ a = b + 1 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma dotProduct_of_linearMap {n : ℕ} (ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (v : Fin n → ZMod 2) :
    dotProduct (fun i => ψ (Pi.single i 1)) v = ψ v := by
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ZMod 2) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j]
    simp
  conv_rhs => rw [hv]
  rw [map_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

private lemma exists_annihilator {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∉ U) :
    ∃ u : Fin n → ZMod 2, (∀ x ∈ U, dotProduct u x = 0) ∧ dotProduct u v = 1 := by
  classical
  let q : (Fin n → ZMod 2) ⧸ U := U.mkQ v
  have hq : q ≠ 0 := by
    intro h
    exact hv ((Submodule.Quotient.mk_eq_zero U).mp h)
  let K : Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ U) := Submodule.span (ZMod 2) {q}
  have hmemK : ∀ z ∈ K, z = 0 ∨ z = q := by
    intro z hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
    rcases zmod2_cases a with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  have hqq : q + q = 0 := by
    have h2 : (1 + 1 : ZMod 2) • q = 0 := by
      have : (1 + 1 : ZMod 2) = 0 := by decide
      rw [this, zero_smul]
    rwa [add_smul, one_smul] at h2
  let coord : K →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun z => if (z : (Fin n → ZMod 2) ⧸ U) = 0 then 0 else 1,
       map_add' := by
         intro x y
         rcases hmemK x.1 x.2 with hx | hx <;> rcases hmemK y.1 y.2 with hy | hy
         · simp [hx, hy]
         · simp [hx, hy, hq]
         · simp [hx, hy, hq]
         · simp only [Submodule.coe_add, hx, hy, hqq, ↓reduceIte, hq]
           decide,
       map_smul' := by
         intro c x
         rcases zmod2_cases c with rfl | rfl
         · simp
         · simp }
  obtain ⟨W, hKW⟩ := Submodule.exists_isCompl K
  let proj : ((Fin n → ZMod 2) ⧸ U) →ₗ[ZMod 2] K := Submodule.linearProjOfIsCompl K W hKW
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (coord.comp proj).comp U.mkQ
  refine ⟨fun i => ψ (Pi.single i 1), ?_, ?_⟩
  · intro x hx
    rw [dotProduct_of_linearMap]
    change coord (proj (U.mkQ x)) = 0
    have h0 : U.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hx
    rw [h0, map_zero, map_zero]
  · rw [dotProduct_of_linearMap]
    change coord (proj q) = 1
    have hqK : q ∈ K := Submodule.subset_span (Set.mem_singleton q)
    have hproj : proj q = ⟨q, hqK⟩ := Submodule.linearProjOfIsCompl_apply_left hKW ⟨q, hqK⟩
    rw [hproj]
    simp [coord, hq]

private lemma card_flat {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (p : Fin n → ZMod 2) [DecidablePred (fun y : Fin n → ZMod 2 => y - p ∈ U)] :
    ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y => y - p ∈ U)).card =
      2 ^ (Module.finrank (ZMod 2) U) := by
  classical
  have hbij :
      ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y => y - p ∈ U)).card =
        Fintype.card U := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun y hy => (⟨y - p, (Finset.mem_filter.mp hy).2⟩ : U))
      (fun _ _ => Finset.mem_univ _)
      (fun y1 _ y2 _ h => by
        have h1 : y1 - p = y2 - p := congrArg Subtype.val h
        exact sub_left_inj.mp h1)
      (fun x _ => ⟨p + x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [x.2]⟩,
        by ext i; simp⟩)
  rw [hbij, Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]

private lemma main_bound (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p c : Fin n → ZMod 2) (e : ZMod 2)
    (hagree : ∀ x ∈ U, f (p + x) = dotProduct c (p + x) + e) :
    ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
      2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => f x ≠ dotProduct a x + b)).card +
        2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
  classical
  let V := Fin n → ZMod 2
  let Uperp : Finset V := Finset.univ.filter (fun u : V => ∀ x ∈ U, dotProduct u x = 0)
  have h0_mem : (0 : V) ∈ Uperp := by
    simp [Uperp]
  have hUperp_add : ∀ u1 u2 : V, u1 ∈ Uperp → u2 ∈ Uperp → u1 + u2 ∈ Uperp := by
    intro u1 u2 h1 h2
    simp only [Uperp, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 ⊢
    intro x hx
    rw [add_dotProduct, h1 x hx, h2 x hx, add_zero]
  let g : V → V → ZMod 2 := fun u y => dotProduct (c + u) y + (e + dotProduct u p)
  let F : Finset V := Finset.univ.filter (fun y : V => y - p ∈ U)
  have hF_zero : ∀ y ∈ F, ∀ u ∈ Uperp, f y = g u y := by
    intro y hy u hu
    have hyp : y - p ∈ U := (Finset.mem_filter.mp hy).2
    have hu_ann : dotProduct u (y - p) = 0 := (Finset.mem_filter.mp hu).2 (y - p) hyp
    have hy_eq : p + (y - p) = y := add_sub_cancel p y
    have hf : f y = dotProduct c y + e := by
      have h := hagree (y - p) hyp
      rwa [hy_eq] at h
    rw [hf]
    dsimp only [g]
    rw [add_dotProduct]
    have hup : dotProduct u y = dotProduct u p := by
      have hsub : dotProduct u (y - p) = dotProduct u y - dotProduct u p := dotProduct_sub u y p
      rw [hsub] at hu_ann
      exact sub_eq_zero.mp hu_ann
    rw [hup]
    have h2 : dotProduct u p + dotProduct u p = 0 := zmod2_add_self _
    calc
      dotProduct c y + e = dotProduct c y + (e + (dotProduct u p + dotProduct u p)) := by
        rw [h2, add_zero]
      _ = dotProduct c y + dotProduct u p + (e + dotProduct u p) := by ring
  have hnotF_half : ∀ y ∉ F,
      2 * (Uperp.filter (fun u => f y ≠ g u y)).card = Uperp.card := by
    intro y hy
    have hnotU : y - p ∉ U := by
      intro hmem
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hmem⟩)
    obtain ⟨u0, hu0_ann, hu0_one⟩ := exists_annihilator U (y - p) hnotU
    have hu0_mem : u0 ∈ Uperp := Finset.mem_filter.mpr ⟨Finset.mem_univ u0, hu0_ann⟩
    have hshift : ∀ u : V, g (u + u0) y = g u y + 1 := by
      intro u
      dsimp only [g]
      have h1 : dotProduct (c + (u + u0)) y = dotProduct (c + u) y + dotProduct u0 y := by
        rw [← add_assoc, add_dotProduct]
      have h2 : dotProduct (u + u0) p = dotProduct u p + dotProduct u0 p := add_dotProduct u u0 p
      have h3 : dotProduct u0 y + dotProduct u0 p = 1 := by
        have hsub : dotProduct u0 (y - p) = dotProduct u0 y - dotProduct u0 p := dotProduct_sub u0 y p
        rw [zmod2_sub_eq_add] at hsub
        rw [← hsub, hu0_one]
      rw [h1, h2]
      calc
        dotProduct (c + u) y + dotProduct u0 y + (e + (dotProduct u p + dotProduct u0 p))
          = dotProduct (c + u) y + (e + dotProduct u p) + (dotProduct u0 y + dotProduct u0 p) := by ring
        _ = dotProduct (c + u) y + (e + dotProduct u p) + 1 := by rw [h3]
    have hpart : (Uperp.filter (fun u => f y ≠ g u y)).card =
        (Uperp.filter (fun u => ¬f y ≠ g u y)).card := by
      refine Finset.card_bij (fun u _ => u + u0) ?_ ?_ ?_
      · intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huU, hne⟩
        refine Finset.mem_filter.mpr ⟨hUperp_add u u0 huU hu0_mem, ?_⟩
        rw [hshift u, not_not]
        exact (zmod2_ne_iff_eq_add_one (f y) (g u y)).mp hne
      · intro u1 _ u2 _ h
        exact add_right_cancel h
      · intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huU, heq⟩
        rw [not_not] at heq
        refine ⟨u + u0, Finset.mem_filter.mpr ⟨hUperp_add u u0 huU hu0_mem, ?_⟩, ?_⟩
        · rw [hshift u, heq]
          exact (zmod2_add_one_ne (g u y)).symm
        · funext i
          change (u i + u0 i) + u0 i = u i
          have : u0 i + u0 i = 0 := zmod2_add_self (u0 i)
          rw [add_assoc, this, add_zero]
    have htot := Finset.card_filter_add_card_filter_not (s := Uperp) (p := fun u => f y ≠ g u y)
    omega
  have hsum :
      ∑ u ∈ Uperp, 2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card =
        (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) * Uperp.card := by
    have hswap :
        ∑ u ∈ Uperp, ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card =
          ∑ y : V, (Uperp.filter (fun u => f y ≠ g u y)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [← Finset.mul_sum, hswap, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : V => y ∈ F)]
    have hpart1 :
        ∑ y ∈ Finset.univ.filter (fun y : V => y ∈ F),
          2 * (Uperp.filter (fun u => f y ≠ g u y)).card = 0 := by
      refine Finset.sum_eq_zero fun y hy => ?_
      have hyF : y ∈ F := (Finset.mem_filter.mp hy).2
      have hemp : Uperp.filter (fun u => f y ≠ g u y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro u hu
        rw [not_not]
        exact hF_zero y hyF u hu
      rw [hemp, Finset.card_empty, mul_zero]
    have hpart2 :
        ∑ y ∈ Finset.univ.filter (fun y : V => ¬y ∈ F),
          2 * (Uperp.filter (fun u => f y ≠ g u y)).card =
        (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) * Uperp.card := by
      have hcongr :
          ∑ y ∈ Finset.univ.filter (fun y : V => ¬y ∈ F),
            2 * (Uperp.filter (fun u => f y ≠ g u y)).card =
          ∑ _y ∈ Finset.univ.filter (fun y : V => ¬y ∈ F), Uperp.card := by
        refine Finset.sum_congr rfl fun y hy => ?_
        exact hnotF_half y (Finset.mem_filter.mp hy).2
      rw [hcongr, Finset.sum_const, smul_eq_mul]
      congr 1
      have hfilt : Finset.univ.filter (fun y : V => ¬y ∈ F) = Finset.univ \ F := by
        ext y
        simp
      rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ F),
        Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, card_flat U p]
    rw [hpart1, zero_add, hpart2]
  have hF_le : 2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
    have h1 : F.card ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ F)
    rw [card_flat U p, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
    exact h1
  have hsum2 :
      ∑ u ∈ Uperp,
        (2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card +
          2 ^ (Module.finrank (ZMod 2) U)) =
        Uperp.card * 2 ^ n := by
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, smul_eq_mul]
    have hcalc : (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) * Uperp.card +
        Uperp.card * 2 ^ (Module.finrank (ZMod 2) U) = Uperp.card * 2 ^ n := by
      rw [mul_comm (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) Uperp.card, ← mul_add,
        Nat.sub_add_cancel hF_le]
    exact hcalc
  have hne : Uperp.Nonempty := ⟨0, h0_mem⟩
  obtain ⟨u, _hu, hbound⟩ :
      ∃ u ∈ Uperp,
        2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card +
          2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
    by_contra hall
    push Not at hall
    have hstrict :
        ∑ _u ∈ Uperp, (2 ^ n) <
          ∑ u ∈ Uperp,
            (2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card +
              2 ^ (Module.finrank (ZMod 2) U)) :=
      Finset.sum_lt_sum_of_nonempty hne fun u hu => hall u hu
    rw [Finset.sum_const, smul_eq_mul, hsum2] at hstrict
    exact lt_irrefl _ hstrict
  exact ⟨c + u, e + dotProduct u p, hbound⟩

end PEqualNP.Outside.L_lib_501_aux

theorem PEqualNP.Outside.L_lib_501 :
∀ n : ℕ,
  let V := Fin n → ZMod 2
  ∀ (f : V → ZMod 2) (U : Submodule (ZMod 2) V) (p c : V) (e : ZMod 2),
    (∀ x ∈ U, f (p+x) = dotProduct c (p+x) + e) →
    ∃ (a : V) (b : ZMod 2), 2*((Finset.univ : Finset V).filter (fun x => f x ≠ dotProduct a x + b)).card +
      2^(Module.finrank (ZMod 2) U) ≤ 2^n := by
  intro n V f U p c e hagree
  exact PEqualNP.Outside.L_lib_501_aux.main_bound n f U p c e hagree

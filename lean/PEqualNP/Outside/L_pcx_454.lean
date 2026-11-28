import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_454_aux

open scoped BigOperators

abbrev F2 := ZMod 2

private lemma zmod2_ne_zero_iff (x : F2) : x ≠ 0 ↔ x = 1 := by
  revert x; decide

private def mask {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : F2 :=
  if i ∈ S then 1 else 0

private def supp {m : ℕ} (v : Fin m → F2) : Finset (Fin m) :=
  Finset.univ.filter (fun i => v i = 1)

private lemma mask_supp {m : ℕ} (v : Fin m → F2) : mask (supp v) = v := by
  funext i
  simp only [mask, supp, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : v i = 1
  · simp [h]
  · have h0 : v i = 0 := by revert h; generalize v i = x; revert x; decide
    simp [h0]

private lemma supp_mask {m : ℕ} (S : Finset (Fin m)) : supp (mask S) = S := by
  ext i
  simp only [supp, mask, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i ∈ S <;> simp [h]

private lemma dot_eq_dotProduct {m : ℕ} (S : Finset (Fin m)) (a : Fin m → F2) :
    (∑ i ∈ S, a i) = dotProduct (mask S) a := by
  simp only [dotProduct, mask, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

private def orth {m : ℕ} (U : Submodule F2 (Fin m → F2)) : Submodule F2 (Fin m → F2) :=
  { carrier := {v | ∀ u ∈ U, dotProduct v u = 0},
    zero_mem' := fun u _ => by simp [dotProduct], add_mem' := fun {v w} hv hw u hu => by
      simp only [Set.mem_ofPred_eq] at hv hw ⊢
      rw [add_dotProduct, hv u hu, hw u hu, zero_add],
    smul_mem' := fun c {v} hv u hu => by
      simp only [Set.mem_ofPred_eq] at hv ⊢
      rw [smul_dotProduct, hv u hu, smul_zero] }

private lemma le_orth_orth {m : ℕ} (U : Submodule F2 (Fin m → F2)) : U ≤ orth (orth U) := by
  intro u hu v hv
  rw [dotProduct_comm]
  exact hv u hu

private lemma finrank_orth_add {m : ℕ} (U : Submodule F2 (Fin m → F2)) :
    Module.finrank F2 (orth U) + Module.finrank F2 U = m := by
  classical
  let d := Module.finrank F2 U
  let b : Module.Basis (Fin d) F2 U := Module.finBasis F2 U
  let ev : (Fin m → F2) →ₗ[F2] (Fin d → F2) :=
    { toFun := fun v j => dotProduct v (b j).1
      map_add' := fun v w => by funext j; exact add_dotProduct v w (b j).1
      map_smul' := fun c v => by funext j; exact smul_dotProduct c v (b j).1 }
  have hker : LinearMap.ker ev = orth U := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv u hu
      have hu_eq : ∑ j : Fin d, b.repr ⟨u, hu⟩ j • (b j).1 = u := by
        have h1 := congr_arg Subtype.val (b.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at h1
        exact h1
      rw [← hu_eq, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro j _
      have h0 : dotProduct v (b j).1 = 0 := congr_fun hv j
      rw [dotProduct_smul, h0, smul_zero]
    · intro hv
      funext j
      exact hv (b j).1 (b j).2
  have hsurj : Function.Surjective ev := by
    by_contra hns
    have hne : LinearMap.range ev ≠ ⊤ := fun htop =>
      hns (LinearMap.range_eq_top.mp htop)
    have hdim_lt : Module.finrank F2 (LinearMap.range ev) < d := by
      calc Module.finrank F2 (LinearMap.range ev)
          < Module.finrank F2 (Fin d → F2) := Submodule.finrank_lt hne
        _ = d := Module.finrank_fin_fun F2
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range ev)
    have hW_pos : 0 < Module.finrank F2 W := by
      have hmod := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ev) W
      rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero,
        Module.finrank_fin_fun F2] at hmod
      omega
    have hW_ne : W ≠ ⊥ := fun hbot => by rw [hbot, finrank_bot] at hW_pos; omega
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne
    let pW : (Fin d → F2) →ₗ[F2] W := Submodule.projectionOnto W (LinearMap.range ev) hW.symm
    let bw := Module.finBasis F2 W
    have hex_i : ∃ i, bw.repr ⟨w, hwW⟩ i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hw0
      have h1 := congr_arg Subtype.val (bw.sum_repr ⟨w, hwW⟩)
      simp only [hall, zero_smul, Finset.sum_const_zero] at h1
      exact h1.symm
    rcases hex_i with ⟨i0, hi0⟩
    let φ : (Fin d → F2) →ₗ[F2] F2 := (bw.coord i0).comp pW
    let c : Fin d → F2 := fun j => φ (Pi.single j 1)
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hφw : φ w = bw.repr ⟨w, hwW⟩ i0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_left hW.symm ⟨w, hwW⟩]
        rfl
      have hφ_zero : φ w = 0 := by
        have hw_sum : w = ∑ j : Fin d, w j • Pi.single j (1 : F2) := by
          funext t
          simp [Finset.sum_apply, Pi.single_apply]
        rw [hw_sum, map_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hcj : c j = 0 := congr_fun hc0 j
        rw [map_smul, show φ (Pi.single j 1) = c j from rfl, hcj, smul_zero]
      exact hi0 (hφw.symm.trans hφ_zero)
    have hcomb0 : ∑ j : Fin d, c j • (b j).1 = 0 := by
      funext t
      have hmem : ev (Pi.single t 1) ∈ LinearMap.range ev := ⟨Pi.single t 1, rfl⟩
      have hφ_ev : φ (ev (Pi.single t 1)) = 0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_right hW.symm ⟨_, hmem⟩, map_zero]
      have hev_sum : ev (Pi.single t 1) =
          ∑ j : Fin d, (b j).1 t • Pi.single j (1 : F2) := by
        funext j
        simp [ev, dotProduct, Pi.single_apply, Finset.sum_apply]
      rw [hev_sum, map_sum] at hφ_ev
      simp only [map_smul, smul_eq_mul] at hφ_ev
      rw [Finset.sum_apply]
      calc ∑ j : Fin d, (c j • (b j).1) t
          = ∑ j : Fin d, (b j).1 t * c j := by
              refine Finset.sum_congr rfl fun j _ => by
                change c j * (b j).1 t = (b j).1 t * c j
                ring
        _ = 0 := hφ_ev
    have hcombU : ∑ j : Fin d, c j • b j = 0 := by
      apply Subtype.ext
      simpa using hcomb0
    have hc_all0 := Fintype.linearIndependent_iff.mp b.linearIndependent c hcombU
    exact hc_ne (funext hc_all0)
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun F2,
    Module.finrank_fin_fun F2, hker, add_comm] at hrn
  exact hrn

private lemma orth_orth {m : ℕ} (U : Submodule F2 (Fin m → F2)) : orth (orth U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orth_orth U)
  have h1 := finrank_orth_add U
  have h2 := finrank_orth_add (orth U)
  omega

private lemma orth_le_orth {m : ℕ} {U V : Submodule F2 (Fin m → F2)} (h : U ≤ V) :
    orth V ≤ orth U :=
  fun _ hv u hu => hv u (h hu)

private lemma exists_subspace_finrank_between {m : ℕ} (U : Submodule F2 (Fin m → F2)) (r : ℕ)
    (h1 : Module.finrank F2 U ≤ r) (h2 : r ≤ m) :
    ∃ W : Submodule F2 (Fin m → F2), U ≤ W ∧ Module.finrank F2 W = r := by
  classical
  obtain ⟨C, hUC⟩ := Submodule.exists_isCompl U
  have hC_dim : Module.finrank F2 C = m - Module.finrank F2 U := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq U C
    rw [hUC.sup_eq_top, hUC.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun F2] at hmod
    omega
  let d := r - Module.finrank F2 U
  have hd_le : d ≤ Module.finrank F2 C := by omega
  let bC := Module.finBasis F2 C
  let C0 : Submodule F2 (Fin m → F2) :=
    Submodule.span F2 (Set.range (fun i : Fin d => (bC ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1))
  have hC0_le : C0 ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (bC _).2
  have hC0_li : LinearIndependent F2
      (fun i : Fin d => (bC ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let g' : Fin (Module.finrank F2 C) → F2 :=
      fun j => if hj : j.val < d then g ⟨j.val, hj⟩ else 0
    have hsum' : ∑ j : Fin (Module.finrank F2 C), g' j • bC j = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, Submodule.coe_sum]
      calc ∑ j : Fin (Module.finrank F2 C), (g' j • bC j).1
          = ∑ j ∈ (Finset.univ : Finset (Fin (Module.finrank F2 C))).filter (fun j => j.val < d),
              (g' j • bC j).1 := by
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro j _ hnot
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
              simp [g', hnot]
        _ = ∑ i : Fin d, g i • (bC ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1 := by
              refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
              · intro i _
                exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, Fin.ext rfl⟩
              · intro j hj
                have hjd := (Finset.mem_filter.mp hj).2
                simp [g', hjd]
        _ = 0 := hg
    have hg'0 := Fintype.linearIndependent_iff.mp bC.linearIndependent g' hsum'
      ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩
    simpa [g', i.isLt] using hg'0
  have hC0_dim : Module.finrank F2 C0 = d := by
    rw [finrank_span_eq_card hC0_li, Fintype.card_fin]
  refine ⟨U ⊔ C0, le_sup_left, ?_⟩
  have hinf : U ⊓ C0 = ⊥ := eq_bot_iff.mpr (le_trans (inf_le_inf_left U hC0_le) hUC.inf_eq_bot.le)
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq U C0
  rw [hinf, finrank_bot, add_zero, hC0_dim] at hmod
  omega

private lemma exists_linearEquiv_map_eq {m : ℕ} {v w : Fin m → F2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : (Fin m → F2) ≃ₗ[F2] (Fin m → F2), e v = w := by
  classical
  let V : Submodule F2 (Fin m → F2) := Submodule.span F2 {v}
  let W : Submodule F2 (Fin m → F2) := Submodule.span F2 {w}
  have hV_dim : Module.finrank F2 V = 1 := finrank_span_singleton hv
  have hW_dim : Module.finrank F2 W = 1 := finrank_span_singleton hw
  obtain ⟨V', hVV'⟩ := Submodule.exists_isCompl V
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hV'_dim : Module.finrank F2 V' = m - 1 := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq V V'
    rw [hVV'.sup_eq_top, hVV'.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun F2, hV_dim] at hmod
    omega
  have hW'_dim : Module.finrank F2 W' = m - 1 := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hWW'.sup_eq_top, hWW'.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun F2, hW_dim] at hmod
    omega
  let e1 : V ≃ₗ[F2] W :=
    ((LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv).symm).trans
      (LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) w hw)
  let e2 : V' ≃ₗ[F2] W' :=
    LinearEquiv.ofFinrankEq V' W' (hV'_dim.trans hW'_dim.symm)
  let eV : (V × V') ≃ₗ[F2] (Fin m → F2) := Submodule.prodEquivOfIsCompl V V' hVV'
  let eW : (W × W') ≃ₗ[F2] (Fin m → F2) := Submodule.prodEquivOfIsCompl W W' hWW'
  let e : (Fin m → F2) ≃ₗ[F2] (Fin m → F2) :=
    (eV.symm.trans (e1.prodCongr e2)).trans eW
  refine ⟨e, ?_⟩
  have hvV : v ∈ V := Submodule.subset_span (Set.mem_singleton v)
  have heV_v : eV (⟨v, hvV⟩, 0) = v := by simp [eV]
  have heV_symm : eV.symm v = (⟨v, hvV⟩, 0) := by
    apply eV.injective
    rw [eV.apply_symm_apply, heV_v]
  have he1_v : e1 ⟨v, hvV⟩ = ⟨w, Submodule.subset_span (Set.mem_singleton w)⟩ := by
    simp only [e1, LinearEquiv.trans_apply]
    have h1 : LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv (1 : F2) = ⟨v, hvV⟩ := by
      ext i; simp [LinearEquiv.toSpanNonzeroSingleton]
    have h2 : (LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv).symm ⟨v, hvV⟩ = 1 := by
      apply (LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv).injective
      rw [LinearEquiv.apply_symm_apply, h1]
    rw [h2]
    ext i; simp [LinearEquiv.toSpanNonzeroSingleton]
  simp only [e, LinearEquiv.trans_apply, heV_symm, LinearEquiv.prodCongr_apply, Prod.map_apply,
    he1_v, map_zero]
  simp [eW]

private lemma bernoulli_nat (x y : ℕ) : ∀ t : ℕ, 0 < t →
    x ^ t + t * x ^ (t - 1) * y ≤ (x + y) ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    cases n with
    | zero => simp
    | succ m =>
      have hm := ih (Nat.succ_pos m)
      have hmul := Nat.mul_le_mul_right (x + y) hm
      rw [← pow_succ] at hmul
      calc x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y
          ≤ (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) := by
            have hexp : (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) =
                (x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y) + (m + 1) * x ^ m * y ^ 2 := by ring
            omega
        _ ≤ (x + y) ^ (m + 2) := hmul

private lemma main_proof (m k : ℕ) (hkm : k < m) :
    let K := ZMod 2
    let I := Fin m
    let X := I → K
    let msk := fun (S : Finset I) (i : I) => if i ∈ S then (1 : K) else 0
    let dot := fun (S : Finset I) (a : X) => ∑ i ∈ S, a i
    let works := fun (H : Finset (Finset I)) =>
      ∀ (a : X) (b : Fin k → X),
        (∃ u : Fin k → K, ∀ i, a i = ∑ j, u j * b j i) ↔
        ∀ S ∈ H, (∀ j, dot S (b j) = 0) → dot S a = 0
    (∀ H : Finset (Finset I), works H ↔
      ∀ W : Submodule K X, Module.finrank K W = m - k →
        Submodule.span K {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W} = W) ∧
    (∀ H : Finset (Finset I), works H →
      (m - k) * (2 ^ m - 1) ≤ H.card * (2 ^ (m - k) - 1) ∧
      ∀ w : ℕ, (∀ S ∈ H, S.card ≤ w) → m.choose (k + 1) ≤ H.card * w.choose (k + 1)) ∧
    works (Finset.univ.filter (fun S : Finset I => S.card ≤ k + 1)) ∧
    ∃ H : Finset (Finset I), works H ∧ H.card ≤ 2 ^ (k + 1) * ((k + 1) * m + 1) := by
  classical
  intro K I X msk dot works
  have hchar : ∀ H : Finset (Finset I), works H ↔
      ∀ W : Submodule K X, Module.finrank K W = m - k →
        Submodule.span K {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W} = W := by
    intro H
    constructor
    · intro hH W hW
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨S, _, rfl, hxW⟩
        exact hxW
      · let M := Submodule.span K {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W}
        have hW_orth_dim : Module.finrank K (orth W) = k := by
          have := finrank_orth_add W
          change Module.finrank K (orth W) + Module.finrank K W = m at this
          omega
        let bW := Module.finBasis K (orth W)
        let b : Fin k → X := fun j => (bW ⟨j.val, by rw [hW_orth_dim]; exact j.isLt⟩).1
        have hspan_b : Submodule.span K (Set.range b) = orth W := by
          apply le_antisymm
          · apply Submodule.span_le.mpr
            rintro _ ⟨j, rfl⟩
            exact (bW _).2
          · intro x hx
            have h1 : (∑ i : Fin (Module.finrank K (orth W)), bW.repr ⟨x, hx⟩ i • (bW i).1) = x := by
              have h := congr_arg Subtype.val (bW.sum_repr ⟨x, hx⟩)
              rw [Submodule.coe_sum] at h
              exact h
            have hx_eq : x = ∑ j : Fin k,
                bW.repr ⟨x, hx⟩ ⟨j.val, by rw [hW_orth_dim]; exact j.isLt⟩ • b j := by
              conv_lhs => rw [← h1]
              refine Finset.sum_bij (fun i _ => ⟨i.val, by rw [← hW_orth_dim]; exact i.isLt⟩)
                ?_ ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro i1 _ i2 _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
              · intro j _
                exact ⟨⟨j.val, by rw [hW_orth_dim]; exact j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩
              · intro i _
                rfl
            rw [hx_eq]
            exact Submodule.sum_mem _ fun j _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        have horth_sub : orth M ≤ orth W := by
          intro a ha
          have ha_dot : ∀ S ∈ H, (∀ j, dot S (b j) = 0) → dot S a = 0 := by
            intro S hSH hSb
            have hSW : msk S ∈ W := by
              rw [← orth_orth W]
              intro u hu
              rw [← hspan_b] at hu
              refine Submodule.span_induction
                (p := fun v _ => dotProduct (msk S) v = 0) ?_ ?_ ?_ ?_ hu
              · rintro _ ⟨j, rfl⟩
                change dotProduct (mask S) (b j) = 0
                rw [← dot_eq_dotProduct]
                exact hSb j
              · simp [dotProduct]
              · intro v1 v2 _ _ h1 h2
                rw [dotProduct_add, h1, h2, zero_add]
              · intro c v _ hv
                rw [dotProduct_smul, hv, smul_zero]
            have hSM : msk S ∈ M := Submodule.subset_span ⟨S, hSH, rfl, hSW⟩
            change ∑ i ∈ S, a i = 0
            rw [dot_eq_dotProduct, dotProduct_comm]
            exact ha (msk S) hSM
          obtain ⟨u, hu⟩ := (hH a b).mpr ha_dot
          have ha_eq : a = ∑ j : Fin k, u j • b j := by
            funext i
            rw [Finset.sum_apply, hu i]
            rfl
          rw [ha_eq, ← hspan_b]
          exact Submodule.sum_mem _ fun j _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        have hle := orth_le_orth horth_sub
        rw [orth_orth W, orth_orth M] at hle
        exact hle
    · intro hspan a b
      constructor
      · rintro ⟨u, hu⟩ S _ hSb
        simp only [dot, hu]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro j _
        rw [← Finset.mul_sum]
        have hj : ∑ i ∈ S, b j i = 0 := hSb j
        rw [hj, mul_zero]
      · intro hdot
        let U := Submodule.span K (Set.range b)
        have hU_dim : Module.finrank K U ≤ k := by
          have h1 := finrank_span_le_card (R := K) (Set.range b)
          have hsub : (Set.range b).toFinset ⊆ Finset.univ.image b := by
            intro x hx; simp at hx ⊢; exact hx
          exact h1.trans ((Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp)))
        have ha_orth : a ∈ orth (orth U) := by
          intro v hv
          have horthU_dim : m - k ≤ Module.finrank K (orth U) := by
            have := finrank_orth_add U
            change Module.finrank K (orth U) + Module.finrank K U = m at this
            omega
          have hv_orth : ∃ W : Submodule K X, W ≤ orth U ∧ v ∈ W ∧ Module.finrank K W = m - k := by
            have hspanv_le : Submodule.span K {v} ≤ orth U :=
              Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
            have hspanv_dim : Module.finrank K (Submodule.span K {v}) ≤ m - k := by
              by_cases hv0 : v = 0
              · subst hv0
                rw [Submodule.span_zero_singleton, finrank_bot]
                omega
              · rw [finrank_span_singleton hv0]; omega
            obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span K {v})
            let C1 : Submodule K X := C ⊓ orth U
            have hsup1 : Submodule.span K {v} ⊔ C1 = orth U := by
              apply le_antisymm
              · exact sup_le hspanv_le inf_le_right
              · intro x hx
                have hmem : x ∈ Submodule.span K {v} ⊔ C := by rw [hC.sup_eq_top]; trivial
                rcases Submodule.mem_sup.mp hmem with ⟨y, hy, z, hz, rfl⟩
                have hzU : z ∈ orth U := by
                  have : y + z - y ∈ orth U := (orth U).sub_mem hx (hspanv_le hy)
                  simpa using this
                exact Submodule.add_mem_sup hy ⟨hz, hzU⟩
            have hinf1 : Submodule.span K {v} ⊓ C1 = ⊥ :=
              eq_bot_iff.mpr (le_trans (inf_le_inf_left _ inf_le_left) hC.inf_eq_bot.le)
            have hC1_dim : Module.finrank K (Submodule.span K {v}) + Module.finrank K C1 =
                Module.finrank K (orth U) := by
              have hmod := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {v}) C1
              rw [hsup1, hinf1, finrank_bot, add_zero] at hmod
              exact hmod.symm
            let d := (m - k) - Module.finrank K (Submodule.span K {v})
            have hd_le : d ≤ Module.finrank K C1 := by omega
            let bC1 := Module.finBasis K C1
            let C0 : Submodule K X := Submodule.span K
              (Set.range (fun i : Fin d => (bC1 ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1))
            have hC0_le : C0 ≤ C1 := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bC1 _).2)
            have hC0_li : LinearIndependent K
                (fun i : Fin d => (bC1 ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1) := by
              rw [Fintype.linearIndependent_iff]
              intro g hg i
              let g' : Fin (Module.finrank K C1) → K :=
                fun j => if hj : j.val < d then g ⟨j.val, hj⟩ else 0
              have hsum' : ∑ j : Fin (Module.finrank K C1), g' j • bC1 j = 0 := by
                apply Subtype.ext
                rw [ZeroMemClass.coe_zero, Submodule.coe_sum]
                calc ∑ j : Fin (Module.finrank K C1), (g' j • bC1 j).1
                    = ∑ j ∈ (Finset.univ : Finset (Fin (Module.finrank K C1))).filter (fun j => j.val < d),
                        (g' j • bC1 j).1 := by
                        symm
                        apply Finset.sum_subset (Finset.filter_subset _ _)
                        intro j _ hnot
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
                        simp [g', hnot]
                  _ = ∑ i : Fin d, g i • (bC1 ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1 := by
                        refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
                          ?_ ?_ ?_ ?_
                        · intro _ _; exact Finset.mem_univ _
                        · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
                        · intro i _
                          exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩,
                            Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, Fin.ext rfl⟩
                        · intro j hj
                          have hjd := (Finset.mem_filter.mp hj).2
                          simp [g', hjd]
                  _ = 0 := hg
              have hg'0 := Fintype.linearIndependent_iff.mp bC1.linearIndependent g' hsum'
                ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩
              simpa [g', i.isLt] using hg'0
            have hC0_dim : Module.finrank K C0 = d := by
              rw [finrank_span_eq_card hC0_li, Fintype.card_fin]
            refine ⟨Submodule.span K {v} ⊔ C0, sup_le hspanv_le (le_trans hC0_le inf_le_right),
              Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton v)), ?_⟩
            have hinf0 : Submodule.span K {v} ⊓ C0 = ⊥ :=
              eq_bot_iff.mpr (le_trans (inf_le_inf_left _ hC0_le) (le_of_eq hinf1))
            have hmod := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {v}) C0
            rw [hinf0, finrank_bot, add_zero, hC0_dim] at hmod
            exact hmod.trans (by omega)
          rcases hv_orth with ⟨W, hW_le, hvW, hW_dim⟩
          rw [← hspan W hW_dim] at hvW
          rw [dotProduct_comm]
          refine Submodule.span_induction (p := fun w _ => dotProduct w a = 0) ?_ ?_ ?_ ?_ hvW
          · rintro _ ⟨S, hSH, rfl, hSW⟩
            change dotProduct (mask S) a = 0
            rw [← dot_eq_dotProduct]
            apply hdot S hSH
            intro j
            change ∑ i ∈ S, b j i = 0
            rw [dot_eq_dotProduct]
            exact hW_le hSW (b j) (Submodule.subset_span ⟨j, rfl⟩)
          · simp [dotProduct]
          · intro w1 w2 _ _ h1 h2
            rw [add_dotProduct, h1, h2, zero_add]
          · intro c w _ hw
            rw [smul_dotProduct, hw, smul_zero]
        rw [orth_orth U] at ha_orth
        rcases Submodule.mem_span_range_iff_exists_fun K |>.mp ha_orth with ⟨u, hu⟩
        refine ⟨u, fun i => ?_⟩
        have hi := congr_fun hu.symm i
        rw [Finset.sum_apply] at hi
        exact hi
  refine ⟨hchar, ?_, ?_, ?_⟩
  · intro H hH
    have hH_span := (hchar H).mp hH
    constructor
    · haveI : Fintype (Submodule K X) := Fintype.ofFinite _
      let Subs : Finset (Submodule K X) :=
        Finset.univ.filter (fun W : Submodule K X => Module.finrank K W = m - k)
      have hSubs_pos : 0 < Subs.card := by
        obtain ⟨W0, _, hW0⟩ := exists_subspace_finrank_between (⊥ : Submodule K X) (m - k)
          (by simp) (by omega)
        exact Finset.card_pos.mpr ⟨W0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW0⟩⟩
      let NZ : Finset X := Finset.univ.filter (fun v : X => v ≠ 0)
      have hNZ_card : NZ.card = 2 ^ m - 1 := by
        have hcomp : NZ.card + (Finset.univ.filter (fun v : X => v = 0)).card = 2 ^ m := by
          rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
          calc ∑ v : X, ((if v ≠ 0 then 1 else 0) + (if v = 0 then 1 else 0))
              = ∑ _v : X, 1 := Finset.sum_congr rfl fun v _ => by by_cases h : v = 0 <;> simp [h]
            _ = Fintype.card X := by simp
            _ = 2 ^ m := by simp [X, K, I]
        have h0 : (Finset.univ.filter (fun v : X => v = 0)).card = 1 := by
          have : (Finset.univ.filter (fun v : X => v = 0)) = {0} := by ext v; simp
          rw [this, Finset.card_singleton]
        omega
      let deg : X → ℕ := fun v => (Subs.filter (fun W => v ∈ W)).card
      have hdeg_const : ∀ v ∈ NZ, ∀ w ∈ NZ, deg v = deg w := by
        intro v hv w hw
        simp only [NZ, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
        obtain ⟨e, he⟩ := exists_linearEquiv_map_eq hv hw
        refine Finset.card_bij (fun W _ => W.map e.toLinearMap) ?_ ?_ ?_
        · intro W hW
          simp only [Finset.mem_filter, Subs, Finset.mem_univ, true_and] at hW ⊢
          refine ⟨?_, ⟨v, hW.2, he⟩⟩
          rw [LinearEquiv.finrank_map_eq, hW.1]
        · intro W1 _ W2 _ h
          ext x
          have hx := congr_arg (fun U : Submodule K X => e x ∈ U) h
          simp only [Submodule.mem_map, LinearEquiv.coe_coe, e.injective.eq_iff, exists_eq_right] at hx
          exact eq_iff_iff.mp hx
        · intro W hW
          simp only [Finset.mem_filter, Subs, Finset.mem_univ, true_and] at hW
          refine ⟨W.map e.symm.toLinearMap, ?_, ?_⟩
          · simp only [Finset.mem_filter, Subs, Finset.mem_univ, true_and]
            refine ⟨?_, ⟨w, hW.2, by rw [← he]; exact e.symm_apply_apply v⟩⟩
            rw [LinearEquiv.finrank_map_eq, hW.1]
          · ext x
            simp only [Submodule.mem_map, LinearEquiv.coe_coe]
            constructor
            · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
              simpa using hy
            · intro hx
              exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
      have hNZ_ne : NZ.Nonempty := by
        have hpos : 0 < 2 ^ m - 1 := by
          have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        exact Finset.card_pos.mp (by omega)
      obtain ⟨v0, hv0⟩ := hNZ_ne
      let C1 := deg v0
      have hcount_nz : Subs.card * (2 ^ (m - k) - 1) = (2 ^ m - 1) * C1 := by
        have h1 : ∑ W ∈ Subs, (NZ.filter (fun v => v ∈ W)).card = ∑ v ∈ NZ, deg v := by
          simp only [deg, Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
        have hW_nz : ∀ W ∈ Subs, (NZ.filter (fun v => v ∈ W)).card = 2 ^ (m - k) - 1 := by
          intro W hW
          simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and] at hW
          have hcardW : (Finset.univ.filter (fun v : X => v ∈ W)).card = 2 ^ (m - k) := by
            rw [← Fintype.card_subtype]
            have hnc := Module.natCard_eq_pow_finrank (K := K) (V := W)
            rw [Nat.card_eq_fintype_card, Nat.card_zmod, hW] at hnc
            exact hnc
          have hsplit : (NZ.filter (fun v => v ∈ W)).card + 1 =
              (Finset.univ.filter (fun v : X => v ∈ W)).card := by
            have h0 : (0 : X) ∈ Finset.univ.filter (fun v : X => v ∈ W) := by simp
            have herase : NZ.filter (fun v => v ∈ W) =
                (Finset.univ.filter (fun v : X => v ∈ W)).erase 0 := by
              ext v; simp [NZ, and_comm]
            rw [herase, Finset.card_erase_of_mem h0]
            have hpos := Finset.card_pos.mpr ⟨0, h0⟩
            omega
          omega
        have hL : ∑ W ∈ Subs, (NZ.filter (fun v => v ∈ W)).card = Subs.card * (2 ^ (m - k) - 1) := by
          rw [Finset.sum_congr rfl hW_nz, Finset.sum_const, smul_eq_mul]
        have hR : ∑ v ∈ NZ, deg v = (2 ^ m - 1) * C1 := by
          rw [Finset.sum_congr rfl (fun v hv => hdeg_const v hv v0 hv0), Finset.sum_const,
            smul_eq_mul, hNZ_card]
        rw [← hL, h1, hR]
      have hcount_H : Subs.card * (m - k) ≤ H.card * C1 := by
        let Hnz := H.filter (fun S => msk S ≠ 0)
        have hper_W : ∀ W ∈ Subs, m - k ≤ (Hnz.filter (fun S => msk S ∈ W)).card := by
          intro W hW
          simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and] at hW
          have hsp := hH_span W hW
          have hsub : {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W} ⊆
              ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X) ∪ {0} := by
            rintro x ⟨S, hSH, rfl, hSW⟩
            by_cases h0 : msk S = 0
            · exact Or.inr h0
            · left
              simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Hnz]
              exact ⟨S, ⟨⟨hSH, h0⟩, hSW⟩, rfl⟩
          have hsp_le : W ≤ Submodule.span K ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X) := by
            conv_lhs => rw [← hsp]
            apply Submodule.span_le.mpr
            intro x hx
            rcases hsub hx with hx1 | hx0
            · exact Submodule.subset_span hx1
            · rw [Set.mem_singleton_iff.mp hx0]; exact Submodule.zero_mem _
          have hle_fin : m - k ≤
              Module.finrank K (Submodule.span K ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)) := by
            rw [← hW]
            exact Submodule.finrank_mono hsp_le
          have hle_card : Module.finrank K (Submodule.span K
              ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)) ≤
              ((Hnz.filter (fun S => msk S ∈ W)).image msk).card := by
            have h1 := finrank_span_le_card (R := K) ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)
            have h2 : (((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)).toFinset =
                (Hnz.filter (fun S => msk S ∈ W)).image msk := by
              ext x; simp
            rwa [h2] at h1
          exact le_trans hle_fin (le_trans hle_card Finset.card_image_le)
        have hswap : ∑ W ∈ Subs, (Hnz.filter (fun S => msk S ∈ W)).card =
            ∑ S ∈ Hnz, deg (msk S) := by
          simp only [deg, Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
        calc Subs.card * (m - k)
            = ∑ _W ∈ Subs, (m - k) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ W ∈ Subs, (Hnz.filter (fun S => msk S ∈ W)).card := Finset.sum_le_sum hper_W
          _ = ∑ S ∈ Hnz, deg (msk S) := hswap
          _ = ∑ _S ∈ Hnz, C1 := Finset.sum_congr rfl fun S hS =>
                hdeg_const (msk S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  (Finset.mem_filter.mp hS).2⟩) v0 hv0
          _ = Hnz.card * C1 := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ H.card * C1 := Nat.mul_le_mul_right C1 (Finset.card_filter_le _ _)
      have hmul : Subs.card * ((m - k) * (2 ^ m - 1)) ≤ Subs.card * (H.card * (2 ^ (m - k) - 1)) := by
        calc Subs.card * ((m - k) * (2 ^ m - 1))
            = (Subs.card * (m - k)) * (2 ^ m - 1) := by ring
          _ ≤ (H.card * C1) * (2 ^ m - 1) := Nat.mul_le_mul_right _ hcount_H
          _ = H.card * ((2 ^ m - 1) * C1) := by ring
          _ = H.card * (Subs.card * (2 ^ (m - k) - 1)) := by rw [← hcount_nz]
          _ = Subs.card * (H.card * (2 ^ (m - k) - 1)) := by ring
      exact Nat.le_of_mul_le_mul_left hmul hSubs_pos
    · intro w hw
      let SubsK : Finset (Finset I) := Finset.univ.powersetCard (k + 1)
      have hSubsK_card : SubsK.card = m.choose (k + 1) := by
        simp [SubsK, I, Finset.card_powersetCard]
      have hcover_T : ∀ T ∈ SubsK, ∃ S ∈ H, T ⊆ S := by
        intro T hT
        rw [Finset.mem_powersetCard] at hT
        have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨i0, hi0⟩ := hT_ne
        let W : Submodule K X :=
          { carrier := {v : X | ∀ i ∈ T, v i = v i0},
            zero_mem' := fun _ _ => rfl, add_mem' := fun {v1 v2} h1 h2 i hi => by
              change v1 i + v2 i = v1 i0 + v2 i0
              rw [h1 i hi, h2 i hi],
            smul_mem' := fun c {v} hv i hi => by
              change c * v i = c * v i0
              rw [hv i hi] }
        have hW_dim : Module.finrank K W = m - k := by
          let ev : X →ₗ[K] ({i : I // i ∈ T.erase i0} → K) :=
            { toFun := fun v j => v j.1 - v i0
              map_add' := fun v1 v2 => by
                funext j
                change (v1 j.1 + v2 j.1) - (v1 i0 + v2 i0) = (v1 j.1 - v1 i0) + (v2 j.1 - v2 i0)
                ring
              map_smul' := fun c v => by
                funext j
                change c * v j.1 - c * v i0 = c * (v j.1 - v i0)
                ring }
          have hker : LinearMap.ker ev = W := by
            ext v
            simp only [LinearMap.mem_ker]
            constructor
            · intro hv i hi
              by_cases hii : i = i0
              · rw [hii]
              · have hmem : i ∈ T.erase i0 := Finset.mem_erase.mpr ⟨hii, hi⟩
                exact sub_eq_zero.mp (congr_fun hv ⟨i, hmem⟩)
            · intro hv
              funext j
              exact sub_eq_zero.mpr (hv j.1 (Finset.mem_of_mem_erase j.2))
          have hsurj : Function.Surjective ev := by
            intro y
            let v : X := fun i => if hi : i ∈ T.erase i0 then y ⟨i, hi⟩ else 0
            refine ⟨v, ?_⟩
            funext j
            have hi0_not : i0 ∉ T.erase i0 := Finset.notMem_erase i0 T
            change v j.1 - v i0 = y j
            simp only [v, j.2, ↓reduceDIte, hi0_not, sub_zero]
          have hrn := LinearMap.finrank_range_add_finrank_ker ev
          rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
            Module.finrank_fin_fun F2, hker, Fintype.card_coe, Finset.card_erase_of_mem hi0,
            hT.2] at hrn
          omega
        have hmaskT : msk T ∈ W := fun i hi => by simp [msk, hi, hi0]
        rw [← hH_span W hW_dim] at hmaskT
        by_contra hno
        push Not at hno
        have hall0 : ∀ x ∈ {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W}, x i0 = 0 := by
          rintro x ⟨S, hSH, rfl, hSW⟩
          by_contra hx0
          have hx1 : msk S i0 = 1 := (zmod2_ne_zero_iff _).mp hx0
          apply hno S hSH
          intro i hi
          have h1 : msk S i = 1 := (hSW i hi).trans hx1
          simp only [msk] at h1
          by_contra hni
          simp [hni] at h1
        have hT0 : msk T i0 = 0 := by
          refine Submodule.span_induction (p := fun x _ => x i0 = 0) ?_ ?_ ?_ ?_ hmaskT
          · intro x hx; exact hall0 x hx
          · rfl
          · intro x y _ _ hx hy; change x i0 + y i0 = 0; rw [hx, hy, zero_add]
          · intro c x _ hx; change c * x i0 = 0; rw [hx, mul_zero]
        simp [msk, hi0] at hT0
      have hsub : SubsK ⊆ H.biUnion (fun S => S.powersetCard (k + 1)) := by
        intro T hT
        rcases hcover_T T hT with ⟨S, hSH, hTS⟩
        exact Finset.mem_biUnion.mpr ⟨S, hSH, Finset.mem_powersetCard.mpr ⟨hTS, (Finset.mem_powersetCard.mp hT).2⟩⟩
      calc m.choose (k + 1)
          = SubsK.card := hSubsK_card.symm
        _ ≤ (H.biUnion (fun S => S.powersetCard (k + 1))).card := Finset.card_le_card hsub
        _ ≤ ∑ S ∈ H, (S.powersetCard (k + 1)).card := Finset.card_biUnion_le
        _ = ∑ S ∈ H, S.card.choose (k + 1) := by
              refine Finset.sum_congr rfl fun S _ => Finset.card_powersetCard (k + 1) S
        _ ≤ ∑ _S ∈ H, w.choose (k + 1) :=
              Finset.sum_le_sum fun S hS => Nat.choose_le_choose (k + 1) (hw S hS)
        _ = H.card * w.choose (k + 1) := by rw [Finset.sum_const, smul_eq_mul]
  · rw [hchar]
    intro W hW
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨S, _, rfl, hxW⟩
      exact hxW
    · let q : X →ₗ[K] (X ⧸ W) := Submodule.mkQ W
      let gen : Set (X ⧸ W) := Set.range (fun i : I => q (Pi.single i 1))
      have hgen_span : Submodule.span K gen = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W y
        have hx_sum : x = ∑ i : I, x i • Pi.single i (1 : K) := by
          funext t; simp [Finset.sum_apply, Pi.single_apply]
        rw [hx_sum, map_sum]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range.mpr ⟨i, rfl⟩))
      obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent K gen
      have hB_card : B.toFinset.card = k := by
        have h1 := finrank_span_set_eq_card (R := K) hBli
        rw [hBspan, hgen_span, finrank_top] at h1
        have hq_dim : Module.finrank K (X ⧸ W) = k := by
          have := Submodule.finrank_quotient_add_finrank W
          rw [Module.finrank_fin_fun F2, hW] at this
          omega
        omega
      have hex_idx : ∀ y ∈ B.toFinset, ∃ i : I, q (Pi.single i 1) = y := by
        intro y hy
        exact hBsub (Set.mem_toFinset.mp hy)
      choose idx hidx using hex_idx
      let P : Finset I := B.toFinset.attach.image (fun y => idx y.1 y.2)
      have hP_card : P.card ≤ k := by
        calc P.card
            ≤ B.toFinset.attach.card := Finset.card_image_le
          _ = B.toFinset.card := Finset.card_attach
          _ = k := hB_card
      have hP_span : Submodule.span K (Set.range (fun i : P => q (Pi.single i.1 1))) = ⊤ := by
        rw [eq_top_iff, ← hgen_span, ← hBspan]
        apply Submodule.span_le.mpr
        intro y hy
        have hyf : y ∈ B.toFinset := Set.mem_toFinset.mpr hy
        have hmemP : idx y hyf ∈ P :=
          Finset.mem_image.mpr ⟨⟨y, hyf⟩, Finset.mem_attach _ _, rfl⟩
        exact Submodule.subset_span ⟨⟨idx y hyf, hmemP⟩, hidx y hyf⟩
      have hex_v : ∀ j : I, j ∉ P →
          ∃ v : X, v ∈ W ∧ (supp v).card ≤ k + 1 ∧ ∀ t : I, t ∉ P → v t = if t = j then 1 else 0 := by
        intro j hjP
        have hqj : q (Pi.single j 1) ∈ Submodule.span K (Set.range (fun i : P => q (Pi.single i.1 1))) := by
          rw [hP_span]; trivial
        rcases (Submodule.mem_span_range_iff_exists_fun K).mp hqj with ⟨c, hc⟩
        let v : X := Pi.single j 1 - ∑ i : P, c i • Pi.single i.1 (1 : K)
        have hvW : v ∈ W := by
          rw [← Submodule.Quotient.mk_eq_zero W]
          change q v = 0
          simp only [v, map_sub, map_sum, map_smul, hc, sub_self]
        have hv_out : ∀ t : I, t ∉ P → v t = if t = j then 1 else 0 := by
          intro t htP
          change (Pi.single (M := fun _ : I => K) j (1 : K) t) -
            (∑ i : P, c i • Pi.single (M := fun _ : I => K) i.1 (1 : K)) t = _
          rw [Pi.single_apply, Finset.sum_apply]
          have hsum0 : ∑ i : P, (c i • Pi.single (M := fun _ : I => K) i.1 (1 : K)) t = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            have hit : t ≠ i.1 := fun h => htP (h ▸ i.2)
            simp [Pi.single_apply, hit]
          rw [hsum0, sub_zero]
        have hsupp_sub : supp v ⊆ insert j P := by
          intro t ht
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          by_cases htj : t = j
          · exact Finset.mem_insert.mpr (Or.inl htj)
          · by_cases htP : t ∈ P
            · exact Finset.mem_insert.mpr (Or.inr htP)
            · exfalso
              have hv0 : v t = 0 := by rw [hv_out t htP, if_neg htj]
              rw [hv0] at ht
              exact zero_ne_one ht
        have hsupp_card : (supp v).card ≤ k + 1 := by
          calc (supp v).card
              ≤ (insert j P).card := Finset.card_le_card hsupp_sub
            _ ≤ P.card + 1 := Finset.card_insert_le j P
            _ ≤ k + 1 := by omega
        exact ⟨v, hvW, hsupp_card, hv_out⟩
      let Pc : Finset I := Finset.univ \ P
      have hPc_card : m - k ≤ Pc.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        omega
      choose vs hvsW hvs_card hvs_coord using hex_v
      let f : Pc → X := fun j => vs j.1 (Finset.mem_sdiff.mp j.2).2
      have hf_li : LinearIndependent K f := by
        rw [Fintype.linearIndependent_iff]
        intro g hg j
        have h0 : (∑ i : Pc, g i • f i) j.1 = 0 := by rw [hg]; rfl
        rw [Finset.sum_apply] at h0
        have hsum : (∑ i : Pc, (g i • f i) j.1) = g j := by
          calc ∑ i : Pc, (g i • f i) j.1
              = ∑ i : Pc, g i * (if j.1 = i.1 then 1 else 0) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  change g i * vs i.1 (Finset.mem_sdiff.mp i.2).2 j.1 = _
                  rw [hvs_coord i.1 (Finset.mem_sdiff.mp i.2).2 j.1 (Finset.mem_sdiff.mp j.2).2]
            _ = ∑ i : Pc, if i = j then g i else 0 := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  by_cases hij : i = j
                  · subst hij; simp
                  · have hne : j.1 ≠ i.1 := fun h => hij (Subtype.ext h.symm)
                    simp [hij, hne]
            _ = g j := by simp
        rw [hsum] at h0
        exact h0
      let M := Submodule.span K {x : X | ∃ S ∈ Finset.univ.filter (fun S : Finset I => S.card ≤ k + 1),
        x = msk S ∧ x ∈ W}
      have hspan_f_le : Submodule.span K (Set.range f) ≤ M := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        apply Submodule.subset_span
        refine ⟨supp (f j), ?_, (mask_supp (f j)).symm, hvsW j.1 (Finset.mem_sdiff.mp j.2).2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hvs_card j.1 (Finset.mem_sdiff.mp j.2).2
      have hM_le : M ≤ W := Submodule.span_le.mpr (by rintro _ ⟨_, _, rfl, hxW⟩; exact hxW)
      have hdim_M : Module.finrank K M = m - k := by
        have h1 : Pc.card ≤ Module.finrank K M := by
          calc Pc.card = Fintype.card Pc := (Fintype.card_coe Pc).symm
            _ = Module.finrank K (Submodule.span K (Set.range f)) :=
                (finrank_span_eq_card hf_li).symm
            _ ≤ Module.finrank K M := Submodule.finrank_mono hspan_f_le
        have h2 : Module.finrank K M ≤ m - k := by
          rw [← hW]; exact Submodule.finrank_mono hM_le
        omega
      have hMW : M = W := Submodule.eq_of_le_of_finrank_eq hM_le (hdim_M.trans hW.symm)
      exact le_of_eq hMW.symm
  · let M := 2 ^ (k + 1)
    let L := (k + 1) * m
    let N := M * (L + 1)
    have hM_ge2 : 2 ≤ M := by
      have : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hpow_strict : (M - 1) ^ N * 2 ^ L < M ^ N := by
      have hstep : 2 * (M - 1) ^ M ≤ M ^ M := by
        have h1 := bernoulli_nat (M - 1) 1 M (by omega)
        rw [Nat.sub_add_cancel (by omega), mul_one] at h1
        have h2 : (M - 1) ^ M ≤ M * (M - 1) ^ (M - 1) := by
          have hpow : (M - 1) ^ M = (M - 1) * (M - 1) ^ (M - 1) := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
          rw [hpow]
          exact Nat.mul_le_mul_right _ (Nat.sub_le M 1)
        omega
      have hpow_le : (2 * (M - 1) ^ M) ^ (L + 1) ≤ (M ^ M) ^ (L + 1) :=
        Nat.pow_le_pow_left hstep (L + 1)
      rw [mul_pow, ← pow_mul, ← pow_mul] at hpow_le
      have hpos : 0 < (M - 1) ^ N := Nat.pow_pos (by omega)
      have h2lt : 2 ^ L < 2 ^ (L + 1) := Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self L)
      calc (M - 1) ^ N * 2 ^ L
          < (M - 1) ^ N * 2 ^ (L + 1) := Nat.mul_lt_mul_of_pos_left h2lt hpos
        _ = 2 ^ (L + 1) * (M - 1) ^ N := by ring
        _ ≤ M ^ N := hpow_le
    let GoodPair := (Fin k → X) × X
    let hit : GoodPair → X → Prop := fun p v =>
      (∀ j : Fin k, dotProduct v (p.1 j) = 0) ∧ dotProduct v p.2 = 1
    let Valid : Finset GoodPair := Finset.univ.filter (fun p =>
      ∃ v : X, hit p v)
    have hValid_card : Valid.card ≤ 2 ^ L := by
      calc Valid.card
          ≤ Fintype.card GoodPair := Finset.card_le_univ Valid
        _ = (2 ^ m) ^ k * 2 ^ m := by simp [GoodPair, X, K, I]
        _ = 2 ^ L := by rw [← pow_mul, ← pow_add]; congr 1; simp [L]; ring
    have hmiss_card : ∀ p ∈ Valid,
        ((Finset.univ : Finset X).filter (fun v => ¬ hit p v)).card ≤ 2 ^ (m - k - 1) * (M - 1) := by
      intro p hp
      simp only [Valid, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨v0, hv0_orth, hv0_dot⟩
      let U : Submodule K X := Submodule.span K (Set.range p.1)
      let W0 : Submodule K X := orth U
      let W1 : Submodule K X := W0 ⊓ orth (Submodule.span K {p.2})
      have hadd_W1 : ∀ v : X, hit p v → v + v0 ∈ W1 := by
        intro v hv
        refine ⟨?_, ?_⟩
        · intro u hu
          refine Submodule.span_induction (p := fun w _ => dotProduct (v + v0) w = 0) ?_ ?_ ?_ ?_ hu
          · rintro _ ⟨j, rfl⟩; rw [add_dotProduct, hv.1 j, hv0_orth j, zero_add]
          · simp [dotProduct]
          · intro w1 w2 _ _ h1 h2; rw [dotProduct_add, h1, h2, zero_add]
          · intro c w _ hw; rw [dotProduct_smul, hw, smul_zero]
        · intro u hu
          refine Submodule.span_induction (p := fun w _ => dotProduct (v + v0) w = 0) ?_ ?_ ?_ ?_ hu
          · rintro _ rfl
            rw [add_dotProduct, hv.2, hv0_dot]
            decide
          · simp [dotProduct]
          · intro w1 w2 _ _ h1 h2; rw [dotProduct_add, h1, h2, zero_add]
          · intro c w _ hw; rw [dotProduct_smul, hw, smul_zero]
      have hhit_eq : (Finset.univ.filter (fun v : X => hit p v)).card = Fintype.card W1 := by
        rw [← Finset.card_univ]
        refine Finset.card_bij
          (fun v hv => (⟨v + v0, hadd_W1 v (Finset.mem_filter.mp hv).2⟩ : W1)) ?_ ?_ ?_
        · intro _ _
          exact Finset.mem_univ _
        · intro v1 _ v2 _ h
          have hval : v1 + v0 = v2 + v0 := congr_arg Subtype.val h
          exact add_right_cancel hval
        · intro w _
          refine ⟨w.1 + v0, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hit]
            refine ⟨fun j => ?_, ?_⟩
            · rw [add_dotProduct, w.2.1 (p.1 j) (Submodule.subset_span ⟨j, rfl⟩), hv0_orth j, zero_add]
            · rw [add_dotProduct, w.2.2 p.2 (Submodule.subset_span (Set.mem_singleton p.2)), hv0_dot, zero_add]
          · apply Subtype.ext
            funext i
            change (w.1 i + v0 i) + v0 i = w.1 i
            have : v0 i + v0 i = 0 := by generalize v0 i = x; revert x; decide
            rw [add_assoc, this, add_zero]
      have hU_dim : Module.finrank K U ≤ k := by
        have h1 := finrank_span_le_card (R := K) (Set.range p.1)
        have hsub : (Set.range p.1).toFinset ⊆ Finset.univ.image p.1 := by
          intro x hx; simp at hx ⊢; exact hx
        exact h1.trans ((Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp)))
      have hW1_dim : m - k - 1 ≤ Module.finrank K W1 := by
        have hW0_dim : m - k ≤ Module.finrank K W0 := by
          have := finrank_orth_add U
          change Module.finrank K W0 + Module.finrank K U = m at this
          omega
        let φ : W0 →ₗ[K] K :=
          { toFun := fun w => dotProduct w.1 p.2
            map_add' := fun w1 w2 => add_dotProduct w1.1 w2.1 p.2
            map_smul' := fun c w => smul_dotProduct c w.1 p.2 }
        have hker : Module.finrank K (LinearMap.ker φ) = Module.finrank K W1 := by
          let e : LinearMap.ker φ ≃ₗ[K] W1 :=
            { toFun := fun w => ⟨w.1.1, w.1.2, fun u hu => by
                refine Submodule.span_induction (p := fun z _ => dotProduct w.1.1 z = 0) ?_ ?_ ?_ ?_ hu
                · rintro _ rfl; exact w.2
                · simp [dotProduct]
                · intro z1 z2 _ _ h1 h2; rw [dotProduct_add, h1, h2, zero_add]
                · intro c z _ hz; rw [dotProduct_smul, hz, smul_zero]⟩
              invFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2 p.2 (Submodule.subset_span (Set.mem_singleton p.2))⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact e.finrank_eq
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        have hrg : Module.finrank K (LinearMap.range φ) ≤ 1 := by
          calc Module.finrank K (LinearMap.range φ)
              ≤ Module.finrank K K := Submodule.finrank_le _
            _ = 1 := Module.finrank_self K
        omega
      have hhit_lb : 2 ^ (m - k - 1) ≤ (Finset.univ.filter (fun v : X => hit p v)).card := by
        rw [hhit_eq]
        have hnc := Module.natCard_eq_pow_finrank (K := K) (V := W1)
        rw [Nat.card_eq_fintype_card, Nat.card_zmod] at hnc
        rw [hnc]
        exact Nat.pow_le_pow_right (by omega) hW1_dim
      have hcomp : (Finset.univ.filter (fun v : X => hit p v)).card +
          (Finset.univ.filter (fun v : X => ¬ hit p v)).card = 2 ^ m := by
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        calc ∑ v : X, ((if hit p v then 1 else 0) + (if ¬ hit p v then 1 else 0))
            = ∑ _v : X, 1 := Finset.sum_congr rfl fun v _ => by by_cases h : hit p v <;> simp [h]
          _ = Fintype.card X := by simp
          _ = 2 ^ m := by simp [X, K, I]
      have h2m : 2 ^ (m - k - 1) * M = 2 ^ m := by
        simp only [M, ← pow_add]
        congr 1
        omega
      have hmul : 2 ^ (m - k - 1) * (M - 1) + 2 ^ (m - k - 1) = 2 ^ m := by
        rw [← h2m]
        have : M = (M - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      omega
    let BadTuples : Finset (Fin N → X) :=
      Valid.biUnion (fun p =>
        (Finset.univ : Finset (Fin N → X)).filter (fun f => ∀ t : Fin N, ¬ hit p (f t)))
    have hBad_lt : BadTuples.card < (Finset.univ : Finset (Fin N → X)).card := by
      have hcard_univ : (Finset.univ : Finset (Fin N → X)).card = (2 ^ (m - k - 1) * M) ^ N := by
        have h2m : 2 ^ (m - k - 1) * M = 2 ^ m := by
          simp only [M, ← pow_add]
          congr 1
          omega
        have hcardX : Fintype.card X = 2 ^ m := by simp [X, K, I]
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcardX, h2m]
      have hBad_le : BadTuples.card ≤ Valid.card * (2 ^ (m - k - 1) * (M - 1)) ^ N := by
        calc BadTuples.card
            ≤ ∑ p ∈ Valid, ((Finset.univ : Finset (Fin N → X)).filter
                (fun f => ∀ t : Fin N, ¬ hit p (f t))).card := Finset.card_biUnion_le
          _ = ∑ p ∈ Valid, ((Finset.univ : Finset X).filter (fun v => ¬ hit p v)).card ^ N := by
                refine Finset.sum_congr rfl fun p _ => ?_
                have heq : (Finset.univ : Finset (Fin N → X)).filter (fun f => ∀ t : Fin N, ¬ hit p (f t)) =
                    Fintype.piFinset (fun _ : Fin N => (Finset.univ : Finset X).filter (fun v => ¬ hit p v)) := by
                  ext f; simp [Fintype.mem_piFinset]
                rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ ∑ _p ∈ Valid, (2 ^ (m - k - 1) * (M - 1)) ^ N :=
                Finset.sum_le_sum fun p hp => Nat.pow_le_pow_left (hmiss_card p hp) N
          _ = Valid.card * (2 ^ (m - k - 1) * (M - 1)) ^ N := by
                rw [Finset.sum_const, smul_eq_mul]
      rw [hcard_univ, mul_pow]
      calc BadTuples.card
          ≤ Valid.card * (2 ^ (m - k - 1) * (M - 1)) ^ N := hBad_le
        _ ≤ 2 ^ L * (2 ^ (m - k - 1) * (M - 1)) ^ N := Nat.mul_le_mul_right _ hValid_card
        _ = (2 ^ (m - k - 1)) ^ N * ((M - 1) ^ N * 2 ^ L) := by rw [mul_pow]; ring
        _ < (2 ^ (m - k - 1)) ^ N * M ^ N :=
              Nat.mul_lt_mul_of_pos_left hpow_strict (Nat.pow_pos (Nat.pow_pos (by omega)))
    have hex_good : ∃ f : Fin N → X, f ∉ BadTuples := by
      have hne : ((Finset.univ : Finset (Fin N → X)) \ BadTuples).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff, Finset.inter_univ]
        omega
      rcases hne with ⟨f, hf⟩
      exact ⟨f, (Finset.mem_sdiff.mp hf).2⟩
    rcases hex_good with ⟨f, hf⟩
    let H : Finset (Finset I) := (Finset.univ : Finset (Fin N)).image (fun t => supp (f t))
    refine ⟨H, ?_, ?_⟩
    · intro a b
      constructor
      · rintro ⟨u, hu⟩ S _ hSb
        simp only [dot, hu]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro j _
        rw [← Finset.mul_sum]
        have hj : ∑ i ∈ S, b j i = 0 := hSb j
        rw [hj, mul_zero]
      · intro hdot
        by_contra hno
        let U := Submodule.span K (Set.range b)
        have ha_notU : a ∉ U := by
          intro haU
          rcases (Submodule.mem_span_range_iff_exists_fun K).mp haU with ⟨u, hu⟩
          apply hno
          refine ⟨u, fun i => ?_⟩
          have hi := congr_fun hu.symm i
          rw [Finset.sum_apply] at hi
          exact hi
        rw [← orth_orth U] at ha_notU
        have hex_v : ∃ v : X, hit (b, a) v := by
          by_contra hnv
          push Not at hnv
          apply ha_notU
          intro v hv
          have hvj : ∀ j : Fin k, dotProduct v (b j) = 0 :=
            fun j => hv (b j) (Submodule.subset_span ⟨j, rfl⟩)
          have hne1 : dotProduct v a ≠ 1 := fun h1 => hnv v ⟨hvj, h1⟩
          rw [dotProduct_comm]
          by_contra hne0
          exact hne1 ((zmod2_ne_zero_iff _).mp hne0)
        have hval : (b, a) ∈ Valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex_v⟩
        have hnot_bad : ¬ ∀ t : Fin N, ¬ hit (b, a) (f t) := by
          intro hall
          apply hf
          exact Finset.mem_biUnion.mpr ⟨(b, a), hval, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩
        push Not at hnot_bad
        rcases hnot_bad with ⟨t0, ht0_orth, ht0_dot⟩
        have hS_mem : supp (f t0) ∈ H := Finset.mem_image.mpr ⟨t0, Finset.mem_univ _, rfl⟩
        have hS_b : ∀ j : Fin k, dot (supp (f t0)) (b j) = 0 := by
          intro j
          change ∑ i ∈ supp (f t0), b j i = 0
          rw [dot_eq_dotProduct, mask_supp]
          exact ht0_orth j
        have hS_a : ∑ i ∈ supp (f t0), a i = 0 := hdot (supp (f t0)) hS_mem hS_b
        rw [dot_eq_dotProduct, mask_supp, ht0_dot] at hS_a
        exact one_ne_zero hS_a
    · calc H.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
        _ = N := by simp

end PEqualNP.Outside.L_pcx_454_aux

theorem PEqualNP.Outside.L_pcx_454 :
  ∀ m k : ℕ, k < m →
  let K := ZMod 2
  let I := Fin m
  let X := I → K
  let mask := fun (S : Finset I) (i : I) => if i ∈ S then (1 : K) else 0
  let dot := fun (S : Finset I) (a : X) => ∑ i ∈ S, a i
  let works := fun (H : Finset (Finset I)) =>
    ∀ (a : X) (b : Fin k → X),
      (∃ u : Fin k → K, ∀ i, a i = ∑ j, u j * b j i) ↔
      ∀ S ∈ H, (∀ j, dot S (b j) = 0) → dot S a = 0
  (∀ H : Finset (Finset I), works H ↔
    ∀ W : Submodule K X, Module.finrank K W = m-k →
      Submodule.span K {x : X | ∃ S ∈ H, x = mask S ∧ x ∈ W} = W) ∧
  (∀ H : Finset (Finset I), works H →
    (m-k)*(2^m-1) ≤ H.card*(2^(m-k)-1) ∧
    ∀ w : ℕ, (∀ S ∈ H, S.card ≤ w) → m.choose (k+1) ≤ H.card * w.choose (k+1)) ∧
  works (Finset.univ.filter (fun S : Finset I => S.card ≤ k+1)) ∧
  ∃ H : Finset (Finset I), works H ∧ H.card ≤ 2^(k+1)*((k+1)*m+1) := by
  intro m k hkm
  exact PEqualNP.Outside.L_pcx_454_aux.main_proof m k hkm

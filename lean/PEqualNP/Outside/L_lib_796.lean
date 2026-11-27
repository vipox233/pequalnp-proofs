import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_796_aux

private abbrev F2 := ZMod 2
private abbrev B (width : Nat) := Fin width → F2
private abbrev V (blocks width spare : Nat) := (Fin blocks → B width) × (Fin spare → F2)
private abbrev P (blocks width spare : Nat) := F2 × V blocks width spare

private lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma z2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_ne_zero_iff (a : F2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

private lemma z2_ne_iff_eq_add_one (a b : F2) : a ≠ b ↔ a = b + 1 := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> rcases z2_eq_zero_or_one b with rfl | rfl
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => (by decide : (0 : F2) = 1 + 1), fun _ => zero_ne_one⟩
  · exact ⟨fun _ => by ring, fun _ => one_ne_zero⟩
  · exact ⟨fun h => absurd rfl h, fun h => absurd h (by decide)⟩

private lemma finrank_V (blocks width spare : Nat) :
    Module.finrank F2 (V blocks width spare) = blocks * width + spare := by
  unfold V B
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp

private lemma finrank_P (blocks width spare : Nat) :
    Module.finrank F2 (P blocks width spare) = blocks * width + spare + 1 := by
  unfold P
  rw [Module.finrank_prod, finrank_V, Module.finrank_self]
  omega

private lemma finrank_ker_pi_ge {M : Type*} [AddCommGroup M] [Module F2 M] [Module.Finite F2 M]
    {d : Nat} (f : M →ₗ[F2] (Fin d → F2)) :
    Module.finrank F2 M ≤ Module.finrank F2 (LinearMap.ker f) + d := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank F2 (LinearMap.range f) ≤ d := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_fin_fun] at this
  omega

private lemma sum_linear_eq_zero {M : Type*} [AddCommGroup M] [Module F2 M] [Fintype M]
    (hcard : 2 ≤ Module.finrank F2 M) (φ : M →ₗ[F2] F2) :
    ∑ x : M, φ x = 0 := by
  classical
  have hker_pos : 0 < Module.finrank F2 (LinearMap.ker φ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank F2 (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_self] at this
    omega
  have hker_ne : (LinearMap.ker φ : Submodule F2 M) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hφv : φ v = 0 := hv_mem
  have hcard_pos : ∀ y : F2, Even (Finset.univ.filter (fun x : M => φ x = y)).card := by
    intro y
    let S := Finset.univ.filter (fun x : M => φ x = y)
    have hinv : ∀ x ∈ S, x + v ∈ S ∧ x + v ≠ x ∧ (x + v) + v = x := by
      intro x hx
      have hφx : φ x = y := (Finset.mem_filter.mp hx).2
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [map_add, hφx, hφv, add_zero]⟩,
        fun heq => hv_ne (by
          have : x + v = x + 0 := by simpa using heq
          exact add_left_cancel this),
        by rw [add_assoc, show v + v = (0 : M) by
          have : (2 : F2) • v = 0 := by
            have h20 : (2 : F2) = 0 := by decide
            rw [h20, zero_smul]
          simpa [two_smul] using this, add_zero]⟩
    have hpart : Even S.card := by
      have hcard_S : Even S.card := by
        have hstep : ∀ T : Finset M, (∀ x ∈ T, x + v ∈ T) → Even T.card := by
          intro T
          induction T using Finset.strongInduction with
          | H T ih =>
            intro hclosed
            by_cases hne : T.Nonempty
            · obtain ⟨a, ha⟩ := hne
              have hav : a + v ∈ T := hclosed a ha
              have hne_av : a + v ≠ a := fun heq => hv_ne (add_left_cancel (by simpa using heq : a + v = a + 0))
              let T' := (T.erase a).erase (a + v)
              have hsub : T' ⊂ T := by
                refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
                · exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
                · intro heq
                  have : a ∈ T' := heq ▸ ha
                  simp [T'] at this
              have hvv : v + v = (0 : M) := by
                have h20 : (2 : F2) = 0 := by decide
                have : (2 : F2) • v = 0 := by rw [h20, zero_smul]
                simpa [two_smul] using this
              have hcl' : ∀ x ∈ T', x + v ∈ T' := by
                intro x hx
                simp only [T', Finset.mem_erase] at hx ⊢
                refine ⟨?_, ?_, hclosed x hx.2.2⟩
                · intro heq; apply hx.2.1; exact add_right_cancel heq
                · intro heq
                  apply hx.1
                  calc x = x + (v + v) := by rw [hvv, add_zero]
                    _ = (x + v) + v := by rw [add_assoc]
                    _ = a + v := by rw [heq]
              have hev' := ih T' hsub hcl'
              have hcard_eq : T.card = T'.card + 2 := by
                have h1 : a + v ∈ T.erase a := Finset.mem_erase.mpr ⟨hne_av, hav⟩
                have hc1 : T'.card + 1 = (T.erase a).card := Finset.card_erase_add_one h1
                have hc2 : (T.erase a).card + 1 = T.card := Finset.card_erase_add_one ha
                omega
              rw [hcard_eq]
              exact hev'.add even_two
            · rw [Finset.not_nonempty_iff_eq_empty] at hne
              subst hne; simp
        exact hstep S (fun x hx => (hinv x hx).1)
      exact hcard_S
    exact hpart
  have h1 := hcard_pos 1
  have hsum : ∑ x : M, φ x = ((Finset.univ.filter (fun x : M => φ x = 1)).card : F2) := by
    have hsplit : ∑ x : M, φ x = ∑ x : M, if φ x = 1 then (1 : F2) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases z2_eq_zero_or_one (φ x) with h0 | h1'
      · simp [h0]
      · simp [h1']
    rw [hsplit, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum]
  rcases h1 with ⟨k, hk⟩
  rw [hk, show (k + k : Nat) = 2 * k by omega, Nat.cast_mul]
  have h20 : ((2 : Nat) : F2) = 0 := by decide
  rw [h20, zero_mul]

private lemma sum_const_eq_zero {M : Type*} [AddCommGroup M] [Module F2 M] [Fintype M]
    (hcard : 2 ≤ Module.finrank F2 M) (c : F2) :
    ∑ _x : M, c = 0 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcm : Fintype.card M = 2 ^ Module.finrank F2 M := by
    rw [Module.card_eq_pow_finrank (K := F2) (V := M)]
    rfl
  rw [hcm]
  have hpow : 2 ^ Module.finrank F2 M = 2 * 2 ^ (Module.finrank F2 M - 1) := by
    conv_lhs => rw [show Module.finrank F2 M = (Module.finrank F2 M - 1) + 1 by omega, pow_succ]
    ring
  rw [hpow, Nat.cast_mul]
  have h20 : ((2 : Nat) : F2) = 0 := by decide
  rw [h20, zero_mul, zero_mul]

private lemma exists_separating_functional {M : Type*} [AddCommGroup M] [Module F2 M] [Module.Finite F2 M]
    (K : Submodule F2 M) (a : M) (ha : a ∉ K) :
    ∃ ℓ : M →ₗ[F2] F2, (∀ x ∈ K, ℓ x = 0) ∧ ℓ a = 1 := by
  classical
  let q := K.mkQ a
  have hq_ne : q ≠ 0 := by
    intro h0
    exact ha ((Submodule.Quotient.mk_eq_zero K).mp h0)
  let b := Module.Basis.ofVectorSpace F2 (M ⧸ K)
  have hrepr_ne : b.repr q ≠ 0 := by
    intro h0; exact hq_ne (b.repr.injective (by simpa using h0))
  have hex : ∃ i, (b.repr q) i ≠ 0 := by
    by_contra hnot
    push Not at hnot
    exact hrepr_ne (Finsupp.ext hnot)
  obtain ⟨i, hi⟩ := hex
  let ℓ : M →ₗ[F2] F2 := (Finsupp.lapply i).comp (b.repr.toLinearMap.comp K.mkQ)
  refine ⟨ℓ, ?_, ?_⟩
  · intro x hx
    dsimp only [ℓ, LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hx, map_zero, Finsupp.lapply_apply, Finsupp.zero_apply]
  · exact (z2_ne_zero_iff _).mp hi

private lemma exists_annihilator_eqs {M : Type*} [AddCommGroup M] [Module F2 M] [Module.Finite F2 M]
    (W : Submodule F2 M) (k : Nat) (hk : Module.finrank F2 M - Module.finrank F2 W = k) :
    ∃ eqs : Fin k → (M →ₗ[F2] F2), ∀ x : M, (∀ j : Fin k, eqs j x = 0) ↔ x ∈ W := by
  classical
  have hq : Module.finrank F2 (M ⧸ W) = k := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    omega
  let b : Module.Basis (Fin k) F2 (M ⧸ W) :=
    (Module.finBasis F2 (M ⧸ W)).reindex (finCongr hq)
  refine ⟨fun j => (Finsupp.lapply j).comp (b.repr.toLinearMap.comp W.mkQ), fun x => ?_⟩
  constructor
  · intro h0
    have hr0 : b.repr (W.mkQ x) = 0 := Finsupp.ext h0
    have hq0 : W.mkQ x = 0 := b.repr.injective (by simpa using hr0)
    exact (Submodule.Quotient.mk_eq_zero W).mp hq0
  · intro hx j
    dsimp only [LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hx, map_zero, Finsupp.lapply_apply, Finsupp.zero_apply]

private lemma fixed_iff (blocks width spare depth : Nat)
    (center : Fin blocks → B width) (tilt : V blocks width spare →ₗ[F2] F2) (offset : F2) :
    let label := fun x : V blocks width spare => tilt x + offset +
      ∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0)
    let correct := fun (out : P blocks width spare → Bool) =>
      (∀ b : F2, out (b, 0) = false) ∧ (∀ x : V blocks width spare, x ≠ 0 → out (label x, x) = true)
    (∃ (Q : P blocks width spare →ₗ[F2] (Fin depth → F2)) (read : (Fin depth → F2) → Bool),
      correct (fun p => read (Q p))) ↔ blocks * width + spare ≤ depth := by
  classical
  intro label correct
  constructor
  · rintro ⟨Q, read, h0, h1⟩
    by_contra hlt
    push Not at hlt
    let QV : V blocks width spare →ₗ[F2] (Fin depth → F2) := Q.comp (LinearMap.inr F2 F2 (V blocks width spare))
    have hker := finrank_ker_pi_ge QV
    rw [finrank_V] at hker
    have hpos : 0 < Module.finrank F2 (LinearMap.ker QV) := by omega
    have hne : (LinearMap.ker QV : Submodule F2 (V blocks width spare)) ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hpos; omega
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hQx : Q (0, x) = 0 := hx_mem
    have hQeq : Q (label x, x) = Q (label x, 0) := by
      have hsplit : ((label x, x) : P blocks width spare) = (label x, 0) + (0, x) := by
        ext <;> simp
      rw [hsplit, map_add, hQx, add_zero]
    have htrue := h1 x hx_ne
    have hfalse := h0 (label x)
    dsimp only at htrue hfalse
    rw [hQeq, hfalse] at htrue
    exact Bool.false_ne_true htrue
  · intro hle
    let eV : V blocks width spare ≃ₗ[F2] (Fin (blocks * width + spare) → F2) :=
      LinearEquiv.ofFinrankEq (V blocks width spare) (Fin (blocks * width + spare) → F2)
        (by rw [finrank_V, Module.finrank_fin_fun])
    let Q : P blocks width spare →ₗ[F2] (Fin depth → F2) :=
      { toFun := fun p j => if hj : j.val < blocks * width + spare then eV p.2 ⟨j.val, hj⟩ else 0
        map_add' := fun p1 p2 => by
          funext j
          dsimp only [Pi.add_apply]
          by_cases hj : j.val < blocks * width + spare
          · simp only [hj, ↓reduceDIte, Prod.snd_add, map_add, Pi.add_apply]
          · simp only [hj, ↓reduceDIte, add_zero]
        map_smul' := fun c p => by
          funext j
          dsimp only [Pi.smul_apply, RingHom.id_apply]
          by_cases hj : j.val < blocks * width + spare
          · simp only [hj, ↓reduceDIte, Prod.smul_snd, map_smul, Pi.smul_apply]
          · simp only [hj, ↓reduceDIte, smul_zero] }
    refine ⟨Q, fun y => decide (y ≠ 0), ?_, ?_⟩
    · intro b
      have hQ0 : Q (b, 0) = 0 := by
        funext j; dsimp only [Q, LinearMap.coe_mk, AddHom.coe_mk]; split_ifs <;> simp
      simp [hQ0]
    · intro x hx
      have hQne : Q (label x, x) ≠ 0 := by
        intro h0
        have he0 : eV x = 0 := by
          funext i
          have hi := congrFun h0 ⟨i.val, by omega⟩
          dsimp only [Q, LinearMap.coe_mk, AddHom.coe_mk] at hi
          simp only [i.isLt, ↓reduceDIte] at hi
          exact hi
        exact hx (eV.injective (by simpa using he0))
      simp [hQne]

private lemma adaptive_lower_bound (blocks width spare depth : Nat)
    (center : Fin blocks → B width) (tilt : V blocks width spare →ₗ[F2] F2) (offset : F2) :
    let label := fun x : V blocks width spare => tilt x + offset +
      ∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0)
    let saved := if ∃ i : Fin blocks, center i = 0 then width - 1 else min blocks (width - 1)
    let correct := fun (out : P blocks width spare → Bool) =>
      (∀ b : F2, out (b, 0) = false) ∧ (∀ x : V blocks width spare, x ≠ 0 → out (label x, x) = true)
    (∃ (ask : (j : Fin depth) → (Fin j.val → F2) → (P blocks width spare →ₗ[F2] F2))
        (ans : P blocks width spare → Fin depth → F2) (read : (Fin depth → F2) → Bool),
      (∀ (p : P blocks width spare) (j : Fin depth), ans p j =
        ask j (fun prev => ans p ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p) ∧
      correct (fun p => read (ans p))) →
    blocks * width + spare - saved ≤ depth := by
  classical
  intro label saved correct
  rintro ⟨ask, ans, read, hans, hcorr0, hcorr1⟩
  let n := blocks * width + spare
  by_cases hdn : n ≤ depth
  · omega
  push Not at hdn
  have hsub_from_b : ∀ b0 : F2,
      ∃ (W : Submodule F2 (V blocks width spare)) (φ : W →ₗ[F2] F2),
        n + 1 ≤ Module.finrank F2 W + depth ∧
        ∀ x : W, x.val ≠ 0 → label x.val = φ x + (b0 + 1) := by
    intro b0
    let t := ans (b0, 0)
    let L : P blocks width spare →ₗ[F2] (Fin depth → F2) :=
      { toFun := fun p j => ask j (fun prev => t ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p
        map_add' := fun p1 p2 => by funext j; exact map_add _ p1 p2
        map_smul' := fun c p => by funext j; exact map_smul _ c p }
    have hL_eq : ∀ p : P blocks width spare, L p = t → ans p = t := by
      intro p hp
      funext j
      obtain ⟨jv, hjv⟩ := j
      induction jv using Nat.strong_induction_on with
      | ind jv ih =>
        rw [hans p ⟨jv, hjv⟩]
        have hprev : (fun prev : Fin jv => ans p ⟨prev.val, Nat.lt_trans prev.isLt hjv⟩) =
            (fun prev : Fin jv => t ⟨prev.val, Nat.lt_trans prev.isLt hjv⟩) := by
          funext prev
          exact ih prev.val prev.isLt (Nat.lt_trans prev.isLt hjv)
        rw [hprev]
        exact congrFun hp ⟨jv, hjv⟩
    have hLb0 : L (b0, 0) = t := by
      funext j; exact (hans (b0, 0) j).symm
    let U : Submodule F2 (P blocks width spare) := LinearMap.ker L
    have hUdim : n + 1 ≤ Module.finrank F2 U + depth := by
      have := finrank_ker_pi_ge L
      rwa [finrank_P] at this
    have hnot_10 : ((1, 0) : P blocks width spare) ∉ U := by
      intro hmem
      have hL10 : L (1, 0) = 0 := hmem
      have hL0 : ∀ b : F2, L (b, 0) = 0 := by
        intro b
        rcases z2_eq_zero_or_one b with rfl | rfl
        · exact map_zero L
        · exact hL10
      let LV : V blocks width spare →ₗ[F2] (Fin depth → F2) :=
        L.comp (LinearMap.inr F2 F2 (V blocks width spare))
      have hkerV := finrank_ker_pi_ge LV
      rw [finrank_V] at hkerV
      have hpos : 0 < Module.finrank F2 (LinearMap.ker LV) := by omega
      have hne : (LinearMap.ker LV : Submodule F2 (V blocks width spare)) ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hpos; omega
      obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hL0x : L (0, x) = 0 := hx_mem
      have hLx : L (label x, x) = t := by
        have hsplit : ((label x, x) : P blocks width spare) = (label x, 0) + (0, x) := by ext <;> simp
        rw [hsplit, map_add, hL0 (label x), hL0x, add_zero, ← hLb0, hL0 b0]
      have hans_x := hL_eq (label x, x) hLx
      have htrue := hcorr1 x hx_ne
      have hfalse := hcorr0 b0
      dsimp only at htrue hfalse
      rw [hans_x] at htrue
      rw [htrue] at hfalse
      exact Bool.false_ne_true hfalse.symm
    let proj : U →ₗ[F2] V blocks width spare :=
      (LinearMap.snd F2 F2 (V blocks width spare)).comp U.subtype
    have hproj_inj : Function.Injective proj := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨⟨b, x⟩, hu⟩ hpx
      have hx0 : x = 0 := hpx
      subst hx0
      rcases z2_eq_zero_or_one b with rfl | rfl
      · rfl
      · exact absurd hu hnot_10
    let W : Submodule F2 (V blocks width spare) := LinearMap.range proj
    have hWdim : Module.finrank F2 W = Module.finrank F2 U :=
      LinearMap.finrank_range_of_inj hproj_inj
    let eUW : U ≃ₗ[F2] W := LinearEquiv.ofInjective proj hproj_inj
    let φ : W →ₗ[F2] F2 :=
      ((LinearMap.fst F2 F2 (V blocks width spare)).comp U.subtype).comp eUW.symm.toLinearMap
    refine ⟨W, φ, by omega, ?_⟩
    intro x hx_ne
    have hmemU : ((φ x, x.val) : P blocks width spare) ∈ U := by
      have hu := (eUW.symm x).property
      have heq : eUW (eUW.symm x) = x := eUW.apply_symm_apply x
      have hx_eq : (eUW.symm x).val.2 = x.val := congrArg Subtype.val heq
      have hb_eq : (eUW.symm x).val.1 = φ x := rfl
      have hpair : ((φ x, x.val) : P blocks width spare) = (eUW.symm x).val :=
        Prod.ext hb_eq.symm hx_eq.symm
      rw [hpair]; exact hu
    have hL_not : L (label x.val, x.val) ≠ t := by
      intro heq
      have hans_x := hL_eq (label x.val, x.val) heq
      have htrue := hcorr1 x.val hx_ne
      have hfalse := hcorr0 b0
      dsimp only at htrue hfalse
      rw [hans_x] at htrue
      rw [htrue] at hfalse
      exact Bool.false_ne_true hfalse.symm
    have hne : label x.val ≠ φ x + b0 := by
      intro heq
      apply hL_not
      have hsplit : ((label x.val, x.val) : P blocks width spare) = (b0, 0) + (φ x, x.val) :=
        Prod.ext (by dsimp only [Prod.fst_add]; rw [heq, add_comm]) (by simp)
      rw [hsplit, map_add, hLb0, show L (φ x, x.val) = 0 from hmemU, add_zero]
    have h1 := (z2_ne_iff_eq_add_one (label x.val) (φ x + b0)).mp hne
    rw [h1]; ring
  obtain ⟨W, φ, c0, hWdim, hWval, hL0⟩ :
      ∃ (W : Submodule F2 (V blocks width spare)) (φ : W →ₗ[F2] F2) (c0 : F2),
        n + 1 ≤ Module.finrank F2 W + depth ∧
        (∀ x : W, x.val ≠ 0 → label x.val = φ x + c0) ∧
        label 0 = c0 + 1 := by
    rcases z2_eq_zero_or_one (label 0) with hl0 | hl1
    · obtain ⟨W, φ, hdim, hval⟩ := hsub_from_b 0
      refine ⟨W, φ, 1, hdim, ?_, ?_⟩
      · intro x hx; simpa using hval x hx
      · rw [hl0]; decide
    · obtain ⟨W, φ, hdim, hval⟩ := hsub_from_b 1
      refine ⟨W, φ, 0, hdim, ?_, ?_⟩
      · intro x hx
        have := hval x hx
        have h11 : (1 : F2) + 1 = 0 := by decide
        simpa [h11] using this
      · rw [hl1]; decide
  by_cases hDle1 : Module.finrank F2 W ≤ 1
  · omega
  have hDge2 : 2 ≤ Module.finrank F2 W := by omega
  let δ : W → F2 := fun x => label x.val + φ x + c0
  have hδ0 : δ 0 = 1 := by
    dsimp only [δ]
    change label 0 + φ 0 + c0 = 1
    rw [map_zero, add_zero, hL0]
    have hcc := z2_add_self c0
    linear_combination hcc
  have hδne : ∀ x : W, x ≠ 0 → δ x = 0 := by
    intro x hx
    have hxv : x.val ≠ 0 := fun h0 => hx (Subtype.ext h0)
    dsimp only [δ]
    rw [hWval x hxv]
    have h1 := z2_add_self (φ x)
    have h2 := z2_add_self c0
    linear_combination h1 + h2
  have hsum_δ : ∑ x : W, δ x = 1 := by
    rw [Finset.sum_eq_single (0 : W)]
    · exact hδ0
    · intro x _ hx0; exact hδne x hx0
    · intro h0; exact absurd (Finset.mem_univ 0) h0
  let π : Fin blocks → (W →ₗ[F2] B width) := fun i =>
    { toFun := fun x => x.val.1 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hD_le_width : Module.finrank F2 W ≤ width := by
    have hsum_expand : ∑ x : W, δ x =
        ∑ i : Fin blocks, ∑ x : W, (if π i x = center i then (1 : F2) else 0) := by
      let linPart : W →ₗ[F2] F2 := tilt.comp W.subtype + φ
      have hδ_eq : ∀ x : W, δ x = linPart x + (offset + c0) +
          ∑ i : Fin blocks, (if π i x = center i then (1 : F2) else 0) := by
        intro x
        dsimp only [δ, label, linPart, π, LinearMap.add_apply, LinearMap.comp_apply,
          Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk]
        ring
      rw [Finset.sum_congr rfl fun x _ => hδ_eq x, Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_linear_eq_zero hDge2 linPart, sum_const_eq_zero hDge2 (offset + c0), zero_add, zero_add]
      exact Finset.sum_comm
    rw [hsum_δ] at hsum_expand
    have hex_i : ∃ i : Fin blocks, (∑ x : W, (if π i x = center i then (1 : F2) else 0)) ≠ 0 := by
      by_contra hnot
      push Not at hnot
      have h0 : ∑ i : Fin blocks, ∑ x : W, (if π i x = center i then (1 : F2) else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => hnot i
      rw [h0] at hsum_expand
      exact one_ne_zero hsum_expand
    obtain ⟨i, hi_ne⟩ := hex_i
    have hker_zero : Module.finrank F2 (LinearMap.ker (π i)) = 0 := by
      by_contra hpos_ne
      have hpos : 0 < Module.finrank F2 (LinearMap.ker (π i)) := Nat.pos_of_ne_zero hpos_ne
      have hne_bot : (LinearMap.ker (π i) : Submodule F2 W) ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hpos; omega
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
      have hπv : π i v = 0 := hv_mem
      have hS_even : Even (Finset.univ.filter (fun x : W => π i x = center i)).card := by
        have hvv : v + v = (0 : W) := by
          have h20 : (2 : F2) = 0 := by decide
          have : (2 : F2) • v = 0 := by rw [h20, zero_smul]
          simpa [two_smul] using this
        have hstep : ∀ T : Finset W, (∀ x ∈ T, x + v ∈ T) → Even T.card := by
          intro T
          induction T using Finset.strongInduction with
          | H T ih =>
            intro hclosed
            by_cases hne : T.Nonempty
            · obtain ⟨a, ha⟩ := hne
              have hav : a + v ∈ T := hclosed a ha
              have hne_av : a + v ≠ a := fun heq => hv_ne (add_left_cancel (by simpa using heq : a + v = a + 0))
              let T' := (T.erase a).erase (a + v)
              have hsub : T' ⊂ T :=
                Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _),
                  fun heq => by have : a ∈ T' := heq ▸ ha; simp [T'] at this⟩
              have hcl' : ∀ x ∈ T', x + v ∈ T' := by
                intro x hx
                simp only [T', Finset.mem_erase] at hx ⊢
                refine ⟨fun heq => hx.2.1 (add_right_cancel heq), fun heq => hx.1 ?_, hclosed x hx.2.2⟩
                calc x = x + (v + v) := by rw [hvv, add_zero]
                  _ = (x + v) + v := by rw [add_assoc]
                  _ = a + v := by rw [heq]
              have hev' := ih T' hsub hcl'
              have hcard_eq : T.card = T'.card + 2 := by
                have hc1 : T'.card + 1 = (T.erase a).card :=
                  Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne_av, hav⟩)
                have hc2 : (T.erase a).card + 1 = T.card := Finset.card_erase_add_one ha
                omega
              rw [hcard_eq]; exact hev'.add even_two
            · rw [Finset.not_nonempty_iff_eq_empty] at hne; subst hne; simp
        refine hstep _ fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, (Finset.mem_filter.mp hx).2, hπv, add_zero]
      apply hi_ne
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      rcases hS_even with ⟨k, hk⟩
      rw [hk, show k + k = 2 * k by omega, Nat.cast_mul]
      have h20 : ((2 : Nat) : F2) = 0 := by decide
      rw [h20, zero_mul]
    have h1 := LinearMap.finrank_range_add_finrank_ker (π i)
    have h2 : Module.finrank F2 (LinearMap.range (π i)) ≤ width := by
      have := Submodule.finrank_le (LinearMap.range (π i))
      rwa [Module.finrank_fin_fun] at this
    omega
  by_cases hzero : ∃ i : Fin blocks, center i = 0
  · dsimp only [saved]
    simp only [hzero, ↓reduceIte]
    omega
  · dsimp only [saved]
    simp only [hzero, ↓reduceIte]
    push Not at hzero
    have hD_le_blocks : Module.finrank F2 W ≤ blocks + 1 := by
      have hsep : ∀ i : Fin blocks, ∃ ℓ : W →ₗ[F2] F2,
          ∀ x : W, ℓ x = 0 → π i x ≠ center i := by
        intro i
        by_cases hex : ∃ a : W, π i a = center i
        · obtain ⟨a, ha⟩ := hex
          have ha_not_ker : a ∉ LinearMap.ker (π i) := by
            intro hmem
            have : π i a = 0 := hmem
            rw [ha] at this
            exact hzero i this
          obtain ⟨ℓ, hℓker, hℓa⟩ := exists_separating_functional (LinearMap.ker (π i)) a ha_not_ker
          refine ⟨ℓ, fun x hℓx hπx => ?_⟩
          have hdiff : x - a ∈ LinearMap.ker (π i) := by
            show π i (x - a) = 0
            rw [map_sub, hπx, ha, sub_self]
          have h0 := hℓker (x - a) hdiff
          rw [map_sub, hℓx, hℓa] at h0
          have hne1 : (0 : F2) - 1 ≠ 0 := by decide
          exact hne1 h0
        · push Not at hex
          exact ⟨0, fun x _ => hex x⟩
      choose ℓs hℓs using hsep
      let Lall : W →ₗ[F2] (Fin blocks → F2) :=
        { toFun := fun x i => ℓs i x
          map_add' := fun x y => by funext i; exact map_add _ x y
          map_smul' := fun c x => by funext i; exact map_smul _ c x }
      let W' : Submodule F2 W := LinearMap.ker Lall
      have hW'dim : Module.finrank F2 W ≤ Module.finrank F2 W' + blocks := finrank_ker_pi_ge Lall
      have hW'le1 : Module.finrank F2 W' ≤ 1 := by
        by_contra hgt1
        have hW'ge2 : 2 ≤ Module.finrank F2 W' := by omega
        have hW'ne : W' ≠ ⊥ := by
          intro hbot; rw [hbot, finrank_bot] at hW'ge2; omega
        obtain ⟨x1, hx1_mem, hx1_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'ne
        let K1 : Submodule F2 W := Submodule.span F2 ({x1} : Set W)
        have hK1_le1 : Module.finrank F2 K1 ≤ 1 := by
          dsimp only [K1]
          rw [finrank_span_singleton (K := F2) hx1_ne]
        have hnot_le : ¬(W' ≤ K1) := by
          intro hle
          have := Submodule.finrank_mono hle
          omega
        have hex2 : ∃ x2 ∈ W', x2 ∉ K1 := by
          by_contra hnot; push Not at hnot
          exact hnot_le (fun x hx => hnot x hx)
        obtain ⟨x2, hx2_mem, hx2_notK1⟩ := hex2
        have hx2_ne : x2 ≠ 0 := fun h0 => hx2_notK1 (h0 ▸ Submodule.zero_mem K1)
        have hx12_ne : x1 + x2 ≠ 0 := by
          intro h0
          have hx11 : x1 + x1 = 0 := by
            have h20 : (2 : F2) = 0 := by decide
            have : (2 : F2) • x1 = 0 := by rw [h20, zero_smul]
            simpa [two_smul] using this
          have h21 : x2 = x1 := by
            calc x2 = 0 + x2 := (zero_add x2).symm
              _ = (x1 + x1) + x2 := by rw [hx11]
              _ = x1 + (x1 + x2) := by rw [add_assoc]
              _ = x1 + 0 := by rw [h0]
              _ = x1 := add_zero x1
          exact hx2_notK1 (h21 ▸ Submodule.subset_span (Set.mem_singleton x1))
        have haff_W' : ∀ x ∈ W', δ x = tilt x.val + φ x + (offset + c0) := by
          intro x hxW'
          have hno : ∀ i : Fin blocks, x.val.1 i ≠ center i := fun i => hℓs i x (congrFun hxW' i)
          dsimp only [δ, label]
          have hsum0 : ∑ i : Fin blocks, (if x.val.1 i = center i then (1 : F2) else 0) = 0 :=
            Finset.sum_eq_zero fun i _ => by simp only [hno i, ↓reduceIte]
          rw [hsum0, add_zero]; ring
        have h00 : δ 0 = tilt 0 + φ 0 + (offset + c0) := haff_W' 0 (Submodule.zero_mem W')
        have h01 : δ x1 = tilt x1.val + φ x1 + (offset + c0) := haff_W' x1 hx1_mem
        have h02 : δ x2 = tilt x2.val + φ x2 + (offset + c0) := haff_W' x2 hx2_mem
        have h03 : δ (x1 + x2) = tilt (x1.val + x2.val) + φ (x1 + x2) + (offset + c0) :=
          haff_W' (x1 + x2) (Submodule.add_mem W' hx1_mem hx2_mem)
        have hsum4 : δ 0 + δ x1 + δ x2 + δ (x1 + x2) = 0 := by
          rw [h00, h01, h02, h03, map_zero, map_zero, map_add, map_add]
          have h1 := z2_add_self (tilt x1.val)
          have h2 := z2_add_self (tilt x2.val)
          have h3 := z2_add_self (φ x1)
          have h4 := z2_add_self (φ x2)
          have h5 := z2_add_self (offset + c0)
          linear_combination h1 + h2 + h3 + h4 + 2 * h5
        rw [hδ0, hδne x1 hx1_ne, hδne x2 hx2_ne, hδne (x1 + x2) hx12_ne] at hsum4
        simp at hsum4
      omega
    omega

private lemma build_adaptive_from_pair {blocks width spare depth : Nat}
    (label : V blocks width spare → F2)
    (d : Nat) (hd_pos : 0 < d) (hd_le : d ≤ depth) (hle_n : d ≤ blocks * width + spare + 1)
    (ψ : V blocks width spare →ₗ[F2] F2) (c0 : F2)
    (W0 W1 : Submodule F2 (V blocks width spare))
    (hW0_dim : Module.finrank F2 W0 = blocks * width + spare + 1 - d)
    (hW1_dim : Module.finrank F2 W1 = blocks * width + spare + 1 - d)
    (hW0_ok : ∀ x ∈ W0, x ≠ 0 → label x ≠ ψ x + c0)
    (hW1_ok : ∀ x ∈ W1, x ≠ 0 → label x ≠ ψ x + (c0 + 1)) :
    ∃ (ask : (j : Fin depth) → (Fin j.val → F2) → (P blocks width spare →ₗ[F2] F2))
      (ans : P blocks width spare → Fin depth → F2) (read : (Fin depth → F2) → Bool),
      (∀ (p : P blocks width spare) (j : Fin depth), ans p j =
        ask j (fun prev => ans p ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p) ∧
      ((∀ b : F2, read (ans (b, 0)) = false) ∧
        (∀ x : V blocks width spare, x ≠ 0 → read (ans (label x, x)) = true)) := by
  classical
  obtain ⟨eqs0, heqs0⟩ := exists_annihilator_eqs W0 (d - 1) (by rw [finrank_V, hW0_dim]; omega)
  obtain ⟨eqs1, heqs1⟩ := exists_annihilator_eqs W1 (d - 1) (by rw [finrank_V, hW1_dim]; omega)
  let q0 : P blocks width spare →ₗ[F2] F2 :=
    LinearMap.fst F2 F2 (V blocks width spare) + ψ.comp (LinearMap.snd F2 F2 (V blocks width spare))
  let ask : (j : Fin depth) → (Fin j.val → F2) → (P blocks width spare →ₗ[F2] F2) := fun j hist =>
    if hj0 : j.val = 0 then q0
    else if hjd : j.val < d then
      if hist ⟨0, by omega⟩ = c0 then
        (eqs0 ⟨j.val - 1, by omega⟩).comp (LinearMap.snd F2 F2 (V blocks width spare))
      else
        (eqs1 ⟨j.val - 1, by omega⟩).comp (LinearMap.snd F2 F2 (V blocks width spare))
    else 0
  let ans : P blocks width spare → Fin depth → F2 := fun p j =>
    if hj0 : j.val = 0 then q0 p
    else if hjd : j.val < d then
      if q0 p = c0 then eqs0 ⟨j.val - 1, by omega⟩ p.2
      else eqs1 ⟨j.val - 1, by omega⟩ p.2
    else 0
  let read : (Fin depth → F2) → Bool := fun y =>
    decide (∃ j : Fin depth, j.val ≠ 0 ∧ j.val < d ∧ y j ≠ 0)
  refine ⟨ask, ans, read, ?_, ?_, ?_⟩
  · intro p j
    dsimp only [ask, ans]
    by_cases hj0 : j.val = 0
    · simp only [hj0, ↓reduceDIte]
    · simp only [hj0, ↓reduceDIte]
      by_cases hjd : j.val < d
      · simp only [hjd, ↓reduceDIte]
        by_cases hq : q0 p = c0
        · simp only [hq, ↓reduceIte]; rfl
        · simp only [hq, ↓reduceIte]; rfl
      · simp only [hjd, ↓reduceDIte]; rfl
  · intro b
    dsimp only [read]
    rw [decide_eq_false_iff_not]
    rintro ⟨j, hj0, hjd, hne⟩
    dsimp only [ans] at hne
    simp only [hj0, hjd, ↓reduceDIte] at hne
    split_ifs at hne <;> simp at hne
  · intro x hx
    dsimp only [read]
    rw [decide_eq_true_eq]
    by_contra hnot
    push Not at hnot
    by_cases hq : q0 (label x, x) = c0
    · have hxW0 : x ∈ W0 := (heqs0 x).mp fun k => by
        have hklt := k.isLt
        let j : Fin depth := ⟨k.val + 1, by omega⟩
        have hk := hnot j (by dsimp only [j]; omega) (by dsimp only [j]; omega)
        dsimp only [ans, j] at hk
        have hne0 : k.val + 1 ≠ 0 := by omega
        have hlt : k.val + 1 < d := by omega
        simp only [hne0, hlt, hq, ↓reduceDIte, ↓reduceIte] at hk
        simpa using hk
      have hlab : label x = ψ x + c0 := by
        have h1 : label x + ψ x = c0 := hq
        have h2 := z2_add_self (ψ x)
        linear_combination h1 - h2
      exact hW0_ok x hxW0 hx hlab
    · have hxW1 : x ∈ W1 := (heqs1 x).mp fun k => by
        have hklt := k.isLt
        let j : Fin depth := ⟨k.val + 1, by omega⟩
        have hk := hnot j (by dsimp only [j]; omega) (by dsimp only [j]; omega)
        dsimp only [ans, j] at hk
        have hne0 : k.val + 1 ≠ 0 := by omega
        have hlt : k.val + 1 < d := by omega
        simp only [hne0, hlt, hq, ↓reduceDIte, ↓reduceIte] at hk
        simpa using hk
      have hlab : label x = ψ x + (c0 + 1) := by
        have h1 : label x + ψ x = c0 + 1 := (z2_ne_iff_eq_add_one _ _).mp hq
        have h2 := z2_add_self (ψ x)
        linear_combination h1 - h2
      exact hW1_ok x hxW1 hx hlab

private lemma adaptive_upper_centered {blocks width spare depth : Nat}
    (hb : 2 ≤ blocks) (hw : 3 ≤ width)
    (center : Fin blocks → B width) (tilt : V blocks width spare →ₗ[F2] F2) (offset : F2)
    (i0 : Fin blocks) (hi0 : center i0 = 0)
    (hd : blocks * width + spare - (width - 1) ≤ depth) :
    let label := fun x : V blocks width spare => tilt x + offset +
      ∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0)
    ∃ (ask : (j : Fin depth) → (Fin j.val → F2) → (P blocks width spare →ₗ[F2] F2))
      (ans : P blocks width spare → Fin depth → F2) (read : (Fin depth → F2) → Bool),
      (∀ (p : P blocks width spare) (j : Fin depth), ans p j =
        ask j (fun prev => ans p ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p) ∧
      ((∀ b : F2, read (ans (b, 0)) = false) ∧
        (∀ x : V blocks width spare, x ≠ 0 → read (ans (label x, x)) = true)) := by
  classical
  intro label
  let n := blocks * width + spare
  let d := n - (width - 1)
  have hd_pos : 0 < d := by
    have : width ≤ blocks * width := by nlinarith
    omega
  have hdim_eq : n + 1 - d = width := by
    have : width ≤ blocks * width := by nlinarith
    omega
  let i1 : Fin blocks := if i0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hi1_ne : i1 ≠ i0 := by
    dsimp only [i1]
    split_ifs with h0
    · intro heq; have := congrArg Fin.val heq; dsimp only at this; omega
    · intro heq; have := congrArg Fin.val heq; dsimp only at this; omega
  let c0 : F2 := label 0
  have hlab_diff : ∀ x : V blocks width spare,
      (∀ i, i ≠ i0 → i ≠ i1 → x.1 i = 0) →
      label x = tilt x + c0 +
        ((if x.1 i0 = center i0 then (1 : F2) else 0) + (if (0 : B width) = center i0 then 1 else 0)) +
        ((if x.1 i1 = center i1 then (1 : F2) else 0) + (if (0 : B width) = center i1 then 1 else 0)) := by
    intro x hother
    dsimp only [label, c0]
    rw [map_zero, zero_add]
    change tilt x + offset + ∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0) =
      tilt x + (offset + ∑ i : Fin blocks, (if (0 : B width) = center i then (1 : F2) else 0)) + _ + _
    have hsum : (∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0)) +
        (∑ i : Fin blocks, (if (0 : B width) = center i then (1 : F2) else 0)) =
        ((if x.1 i0 = center i0 then (1 : F2) else 0) + (if (0 : B width) = center i0 then 1 else 0)) +
        ((if x.1 i1 = center i1 then (1 : F2) else 0) + (if (0 : B width) = center i1 then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
      have hpair : ({i0, i1} : Finset (Fin blocks)) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hpair]
      · rw [Finset.sum_pair hi1_ne.symm]
      · intro i _ hi_not
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi_not
        rw [hother i hi_not.1 hi_not.2]
        exact z2_add_self _
    have hsum0 := z2_add_self (∑ i : Fin blocks, (if (0 : B width) = center i then (1 : F2) else 0))
    linear_combination hsum - hsum0
  by_cases hi1z : center i1 = 0
  · let φ0 : B width →ₗ[F2] V blocks width spare :=
      { toFun := fun u => (fun i => if i = i0 then u else 0, 0)
        map_add' := fun u1 u2 => by ext i t <;> simp [ite_apply] <;> split_ifs <;> simp
        map_smul' := fun c u => by ext i t <;> simp [ite_apply] <;> split_ifs <;> simp }
    have hφ0_inj : Function.Injective φ0 := by
      intro u1 u2 h
      have := congrFun (congrArg Prod.fst h) i0
      simpa [φ0] using this
    let φ1 : B width →ₗ[F2] V blocks width spare :=
      { toFun := fun u => (fun i => if i = i0 ∨ i = i1 then u else 0, 0)
        map_add' := fun u1 u2 => by ext i t <;> simp [ite_apply] <;> split_ifs <;> simp
        map_smul' := fun c u => by ext i t <;> simp [ite_apply] <;> split_ifs <;> simp }
    have hφ1_inj : Function.Injective φ1 := by
      intro u1 u2 h
      have := congrFun (congrArg Prod.fst h) i0
      simpa [φ1] using this
    refine build_adaptive_from_pair label d hd_pos hd (by omega) tilt c0 (LinearMap.range φ0) (LinearMap.range φ1)
      (by rw [LinearMap.finrank_range_of_inj hφ0_inj, Module.finrank_fin_fun, hdim_eq])
      (by rw [LinearMap.finrank_range_of_inj hφ1_inj, Module.finrank_fin_fun, hdim_eq]) ?_ ?_
    · rintro x ⟨u, rfl⟩ hx_ne
      have hu_ne : u ≠ 0 := fun hu0 => hx_ne (by subst hu0; exact map_zero φ0)
      have hld := hlab_diff (φ0 u) (fun i h1 _ => by simp [φ0, h1])
      have h0u : (φ0 u).1 i0 = u := by simp [φ0]
      have h1u : (φ0 u).1 i1 = 0 := by simp [φ0, hi1_ne]
      rw [h0u, h1u, hi0, hi1z] at hld
      simp only [hu_ne, ↓reduceIte] at hld
      rw [hld]
      have h11 : (1 : F2) + 1 = 0 := by decide
      intro heq
      have h10 : (1 : F2) = 0 := by linear_combination heq - h11
      exact one_ne_zero h10
    · rintro x ⟨u, rfl⟩ hx_ne
      have hu_ne : u ≠ 0 := fun hu0 => hx_ne (by subst hu0; exact map_zero φ1)
      have hld := hlab_diff (φ1 u) (fun i h1 h2 => by simp [φ1, h1, h2])
      have h0u : (φ1 u).1 i0 = u := by simp [φ1]
      have h1u : (φ1 u).1 i1 = u := by simp [φ1]
      rw [h0u, h1u, hi0, hi1z] at hld
      simp only [hu_ne, ↓reduceIte] at hld
      rw [hld]
      have h11 : (1 : F2) + 1 = 0 := by decide
      intro heq
      have h10 : (1 : F2) = 0 := by linear_combination -heq + h11
      exact one_ne_zero h10
  · have hex_t1 : ∃ t1 : Fin width, center i1 t1 = 1 := by
      by_contra hnot; push Not at hnot
      apply hi1z; funext t
      rcases z2_eq_zero_or_one (center i1 t) with h0 | h1
      · exact h0
      · exact absurd h1 (hnot t)
    obtain ⟨t1, ht1⟩ := hex_t1
    let t2 : Fin width := if t1.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have ht2_ne : t2 ≠ t1 := by
      dsimp only [t2]; split_ifs with h0
      · intro heq; have := congrArg Fin.val heq; dsimp only at this; omega
      · intro heq; have := congrArg Fin.val heq; dsimp only at this; omega
    let u1 : B width := Pi.single t1 1
    let u2 : B width := Pi.single t1 1 + Pi.single t2 1
    have hu12_ne : u1 ≠ u2 := by
      intro heq
      have h := congrFun heq t2
      simp [u1, u2, ht2_ne] at h
    let v2 : B width := if u1 = center i1 then u2 else u1
    have hv2_ne : v2 ≠ center i1 := by
      dsimp only [v2]; split_ifs with h
      · rw [← h]; exact hu12_ne.symm
      · exact h
    have hv2_t1 : v2 t1 = 1 := by
      dsimp only [v2]; split_ifs
      · simp [u2, ht2_ne.symm]
      · simp [u1]
    let z0 : Fin width := ⟨0, by omega⟩
    let ψ : V blocks width spare →ₗ[F2] F2 :=
      { toFun := fun x => tilt x + x.1 i1 t1 + x.1 i0 z0
        map_add' := fun x y => by simp only [map_add, Prod.fst_add, Pi.add_apply]; ring
        map_smul' := fun c x => by simp only [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    let φ0 : B width →ₗ[F2] V blocks width spare :=
      { toFun := fun u => (fun i => if i = i0 then u else if i = i1 then u z0 • v2 else 0, 0)
        map_add' := fun u1 u2 => by
          ext i t
          · dsimp only [Prod.fst_add, Pi.add_apply]
            split_ifs <;> simp [add_mul]
          · simp
        map_smul' := fun c u => by
          ext i t
          · dsimp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
            split_ifs <;> simp [mul_assoc]
          · simp }
    have hφ0_inj : Function.Injective φ0 := by
      intro a b h
      have := congrFun (congrArg Prod.fst h) i0
      simpa [φ0] using this
    let H1 : Submodule F2 (B width) := LinearMap.ker (LinearMap.proj (R := F2) t1)
    have hH1_dim : Module.finrank F2 H1 = width - 1 := by
      have h1 : Module.finrank F2 (LinearMap.range (LinearMap.proj (R := F2) (φ := fun _ : Fin width => F2) t1)) +
          Module.finrank F2 H1 = Module.finrank F2 (Fin width → F2) :=
        LinearMap.finrank_range_add_finrank_ker (LinearMap.proj (R := F2) (φ := fun _ : Fin width => F2) t1)
      have hr : Module.finrank F2 (LinearMap.range (LinearMap.proj (R := F2) (φ := fun _ : Fin width => F2) t1)) = 1 := by
        have hsurj : LinearMap.range (LinearMap.proj (R := F2) (φ := fun _ : Fin width => F2) t1) = ⊤ := by
          rw [LinearMap.range_eq_top]
          intro c; exact ⟨Pi.single t1 c, by simp⟩
        rw [hsurj, finrank_top, Module.finrank_self]
      rw [hr, Module.finrank_fin_fun] at h1
      omega
    let eH1 : (Fin (width - 1) → F2) ≃ₗ[F2] H1 :=
      LinearEquiv.ofFinrankEq (Fin (width - 1) → F2) H1 (by rw [Module.finrank_fin_fun, hH1_dim])
    let φ1 : (F2 × (Fin (width - 1) → F2)) →ₗ[F2] V blocks width spare :=
      { toFun := fun p => (fun i => if i = i0 then p.1 • Pi.single z0 1 else if i = i1 then (eH1 p.2).val else 0, 0)
        map_add' := fun p1 p2 => by
          ext i t
          · dsimp only [Prod.fst_add, Pi.add_apply]
            split_ifs <;> simp [add_mul]
          · simp
        map_smul' := fun c p => by
          ext i t
          · dsimp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
            split_ifs <;> simp [mul_assoc]
          · simp }
    have hφ1_inj : Function.Injective φ1 := by
      intro p1 p2 h
      have h0 := congrFun (congrArg Prod.fst h) i0
      have h1 := congrFun (congrArg Prod.fst h) i1
      simp only [φ1, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte, hi1_ne] at h0 h1
      have hp1 : p1.1 = p2.1 := by
        have := congrFun h0 z0; simpa using this
      have hp2 : p1.2 = p2.2 := eH1.injective (Subtype.ext h1)
      exact Prod.ext hp1 hp2
    have hdim_dom1 : Module.finrank F2 (F2 × (Fin (width - 1) → F2)) = width := by
      rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]; omega
    refine build_adaptive_from_pair label d hd_pos hd (by omega) ψ c0 (LinearMap.range φ0) (LinearMap.range φ1)
      (by rw [LinearMap.finrank_range_of_inj hφ0_inj, Module.finrank_fin_fun, hdim_eq])
      (by rw [LinearMap.finrank_range_of_inj hφ1_inj, hdim_dom1, hdim_eq]) ?_ ?_
    · rintro x ⟨u, rfl⟩ hx_ne
      have hu_ne : u ≠ 0 := fun hu0 => hx_ne (by subst hu0; exact map_zero φ0)
      have hld := hlab_diff (φ0 u) (fun i h1 h2 => by simp [φ0, h1, h2])
      have hi1_ne_c : (u z0 • v2) ≠ center i1 := by
        rcases z2_eq_zero_or_one (u z0) with h0 | h1
        · rw [h0, zero_smul]; exact Ne.symm hi1z
        · rw [h1, one_smul]; exact hv2_ne
      have h0_ne_c1 : (0 : B width) ≠ center i1 := Ne.symm hi1z
      have h0u : (φ0 u).1 i0 = u := by simp [φ0]
      have h1u : (φ0 u).1 i1 = u z0 • v2 := by simp [φ0, hi1_ne]
      rw [h0u, h1u, hi0] at hld
      simp only [hu_ne, hi1_ne_c, h0_ne_c1, ↓reduceIte, add_zero, zero_add] at hld
      have hψ0 : ψ (φ0 u) = tilt (φ0 u) := by
        dsimp only [ψ, φ0, LinearMap.coe_mk, AddHom.coe_mk]
        simp only [hi1_ne, ↓reduceIte, Pi.smul_apply, smul_eq_mul, hv2_t1, mul_one]
        have hz := z2_add_self (u z0)
        linear_combination hz
      rw [hld, hψ0]
      intro heq
      have h10 : (1 : F2) = 0 := by linear_combination heq
      exact one_ne_zero h10
    · rintro x ⟨⟨b, y⟩, rfl⟩ _
      have hld := hlab_diff (φ1 (b, y)) (fun i h1 h2 => by simp [φ1, h1, h2])
      have hi1_t1 : (eH1 y).val t1 = 0 := (eH1 y).property
      have hi1_ne_c : (eH1 y).val ≠ center i1 := by
        intro heq; have := congrFun heq t1; rw [hi1_t1, ht1] at this; exact zero_ne_one this
      have h0_ne_c1 : (0 : B width) ≠ center i1 := Ne.symm hi1z
      have hψ1 : ψ (φ1 (b, y)) = tilt (φ1 (b, y)) + b := by
        dsimp only [ψ, φ1, LinearMap.coe_mk, AddHom.coe_mk]
        simp only [hi1_ne, ↓reduceIte, hi1_t1, add_zero, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      have hbi0 : (if b • Pi.single z0 (1 : F2) = 0 then (1 : F2) else 0) + 1 = b := by
        rcases z2_eq_zero_or_one b with rfl | rfl
        · simp; decide
        · have hne : (1 : F2) • Pi.single z0 (1 : F2) ≠ 0 := by
            intro h0; have := congrFun h0 z0; simp at this
          simp
      have h0u : (φ1 (b, y)).1 i0 = b • Pi.single z0 1 := by simp [φ1]
      have h1u : (φ1 (b, y)).1 i1 = (eH1 y).val := by simp [φ1, hi1_ne]
      rw [h0u, h1u, hi0] at hld
      simp only [hi1_ne_c, h0_ne_c1, ↓reduceIte, add_zero] at hld
      rw [hld, hbi0, hψ1]
      intro heq
      have h10 : (1 : F2) = 0 := by linear_combination -heq
      exact one_ne_zero h10

private lemma adaptive_upper_noncentered {blocks width spare depth : Nat}
    (hb : 2 ≤ blocks) (hw : 3 ≤ width)
    (center : Fin blocks → B width) (tilt : V blocks width spare →ₗ[F2] F2) (offset : F2)
    (hnc : ∀ i : Fin blocks, center i ≠ 0)
    (hd : blocks * width + spare - min blocks (width - 1) ≤ depth) :
    let label := fun x : V blocks width spare => tilt x + offset +
      ∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0)
    ∃ (ask : (j : Fin depth) → (Fin j.val → F2) → (P blocks width spare →ₗ[F2] F2))
      (ans : P blocks width spare → Fin depth → F2) (read : (Fin depth → F2) → Bool),
      (∀ (p : P blocks width spare) (j : Fin depth), ans p j =
        ask j (fun prev => ans p ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p) ∧
      ((∀ b : F2, read (ans (b, 0)) = false) ∧
        (∀ x : V blocks width spare, x ≠ 0 → read (ans (label x, x)) = true)) := by
  classical
  intro label
  let m := min blocks (width - 1)
  have hm_le_b : m ≤ blocks := min_le_left _ _
  have hm_le_w : m + 1 ≤ width := by
    have : m ≤ width - 1 := min_le_right _ _
    omega
  have hm_ge2 : 2 ≤ m := by
    dsimp only [m]; omega
  let n := blocks * width + spare
  let d := n - m
  have hd_pos : 0 < d := by
    have : width ≤ blocks * width := by nlinarith
    omega
  have hdim_eq : n + 1 - d = m + 1 := by
    have : width ≤ blocks * width := by nlinarith
    omega
  have hex_coord : ∀ i : Fin blocks, ∃ t : Fin width, center i t = 1 := by
    intro i
    by_contra hnot; push Not at hnot
    apply hnc i; funext t
    rcases z2_eq_zero_or_one (center i t) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot t)
  choose pivot hpivot using hex_coord
  let basisVec (i : Fin blocks) (t : Fin width) : B width :=
    if t = pivot i then center i else Pi.single t 1
  have hbasis_li : ∀ i : Fin blocks, LinearIndependent F2 (basisVec i) := by
    intro i
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc_piv : c (pivot i) = 0 := by
      have h := congrFun hc (pivot i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, basisVec] at h
      have hterm : ∀ t : Fin width, c t * (if t = pivot i then center i else Pi.single t 1) (pivot i) =
          if t = pivot i then c (pivot i) else 0 := by
        intro t
        by_cases ht : t = pivot i
        · subst ht; simp [hpivot i]
        · simp [ht, Pi.single_apply, Ne.symm ht]
      simp_rw [hterm] at h
      simpa using h
    intro t
    by_cases ht : t = pivot i
    · subst ht; exact hc_piv
    · have h := congrFun hc t
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, basisVec] at h
      have hterm : ∀ s : Fin width, c s * (if s = pivot i then center i else Pi.single s 1) t =
          if s = t then c t else 0 := by
        intro s
        by_cases hsp : s = pivot i
        · subst hsp; simp [hc_piv, Ne.symm ht]
        · by_cases hst : s = t
          · subst hst; simp [hsp]
          · simp [hsp, hst, Pi.single_apply, Ne.symm hst]
      simp_rw [hterm] at h
      simpa using h
  let perm (i : Fin blocks) : Equiv.Perm (Fin width) :=
    Equiv.swap (pivot i) ⟨i.val % width, Nat.mod_lt _ (by omega)⟩
  let bvec (i : Fin blocks) (r : Fin width) : B width :=
    basisVec i ((perm i) r)
  have hbvec_li : ∀ i : Fin blocks, LinearIndependent F2 (bvec i) := fun i =>
    (hbasis_li i).comp (perm i) (perm i).injective
  have hbvec_center : ∀ (i : Fin m), bvec ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = center ⟨i.val, by omega⟩ := by
    intro i
    dsimp only [bvec, perm, basisVec]
    have hmod : i.val % width = i.val := Nat.mod_eq_of_lt (by omega)
    have hfin : (⟨i.val % width, Nat.mod_lt _ (by omega)⟩ : Fin width) = ⟨i.val, by omega⟩ := Fin.ext hmod
    rw [hfin, Equiv.swap_apply_right]
    simp
  let idxM : Fin width := ⟨m, by omega⟩
  let φ0 : (Fin (m + 1) → F2) →ₗ[F2] V blocks width spare :=
    { toFun := fun y =>
        (fun i =>
          if hi : i.val < m then
            (∑ r : Fin (i.val + 1), y ⟨r.val, by omega⟩ • bvec i ⟨r.val, by omega⟩) +
            y ⟨m, by omega⟩ • bvec i idxM
          else 0, 0)
      map_add' := fun y1 y2 => by
        ext i t
        · dsimp only [Prod.fst_add, Pi.add_apply]
          split_ifs with hi
          · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
            ring
          · simp
        · simp
      map_smul' := fun c y => by
        ext i t
        · dsimp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          split_ifs with hi
          · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
              Finset.mul_sum, mul_add]
            congr 1
            · refine Finset.sum_congr rfl fun r _ => by ring
            · ring
          · simp
        · simp }
  have hφ0_coord : ∀ (y : Fin (m + 1) → F2) (i : Fin m),
      (φ0 y).1 ⟨i.val, by omega⟩ =
        ∑ s : Fin width,
          (if hs : s.val ≤ i.val then y ⟨s.val, by omega⟩
           else if s = idxM then y ⟨m, by omega⟩ else 0) • bvec ⟨i.val, by omega⟩ s := by
    intro y i
    dsimp only [φ0, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [i.isLt, ↓reduceDIte]
    let f : Fin width → B width := fun s =>
      (if hs : s.val ≤ i.val then y ⟨s.val, by have := i.isLt; omega⟩
       else if s = idxM then y ⟨m, by omega⟩ else 0) • bvec ⟨i.val, by omega⟩ s
    let S1 := (Finset.univ : Finset (Fin width)).filter (fun s => s.val ≤ i.val)
    have hidxM_not : idxM ∉ S1 := by
      simp only [S1, idxM, Finset.mem_filter, Finset.mem_univ, true_and, not_le]; omega
    have hsplit : ∑ s : Fin width, f s =
        (∑ s ∈ S1, f s) + y ⟨m, by omega⟩ • bvec ⟨i.val, by omega⟩ idxM := by
      rw [← Finset.sum_subset (Finset.subset_univ (insert idxM S1))]
      · rw [Finset.sum_insert hidxM_not, add_comm]
        congr 1
        dsimp only [f]
        have hlt_not : ¬(idxM.val ≤ i.val) := by dsimp only [idxM]; omega
        simp only [hlt_not, ↓reduceDIte, ↓reduceIte]
      · intro s _ hs_not
        simp only [Finset.mem_insert, S1, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hs_not
        dsimp only [f]
        simp only [hs_not.2, hs_not.1, ↓reduceDIte, ↓reduceIte, zero_smul]
    change _ = ∑ s : Fin width, f s
    rw [hsplit]
    congr 1
    refine Finset.sum_bij (fun r _ => ⟨r.val, by have := r.isLt; have := i.isLt; omega⟩) ?_ ?_ ?_ ?_
    · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; have := r.isLt; omega⟩
    · intro r1 _ r2 _ heq; exact Fin.ext (congrArg (Fin.val : Fin width → Nat) heq)
    · intro s hs
      have hle : s.val ≤ i.val := (Finset.mem_filter.mp hs).2
      exact ⟨⟨s.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro r _
      dsimp only [f]
      have hle : r.val ≤ i.val := by have := r.isLt; omega
      simp only [hle, ↓reduceDIte]
  have hφ0_hit : ∀ (y : Fin (m + 1) → F2) (i : Fin m),
      (φ0 y).1 ⟨i.val, by omega⟩ = center ⟨i.val, by omega⟩ ↔
        (∀ r : Fin i.val, y ⟨r.val, by omega⟩ = 0) ∧ y ⟨i.val, by omega⟩ = 1 ∧ y ⟨m, by omega⟩ = 0 := by
    intro y i
    rw [hφ0_coord y i, ← hbvec_center i]
    have hcenter_sum : bvec ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ =
        ∑ s : Fin width, (if s = ⟨i.val, by omega⟩ then (1 : F2) else 0) • bvec ⟨i.val, by omega⟩ s := by
      simp
    rw [hcenter_sum]
    have hinj : ∀ f g : Fin width → F2,
        (∑ s : Fin width, f s • bvec ⟨i.val, by omega⟩ s = ∑ s : Fin width, g s • bvec ⟨i.val, by omega⟩ s) ↔
        ∀ s : Fin width, f s = g s := by
      intro f g
      constructor
      · intro heq s
        have hdiff : ∑ s : Fin width, (f s - g s) • bvec ⟨i.val, by omega⟩ s = 0 := by
          simp_rw [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
        have h0 := (Fintype.linearIndependent_iff.mp (hbvec_li ⟨i.val, by omega⟩)) (fun s => f s - g s) hdiff s
        exact sub_eq_zero.mp h0
      · intro h; refine Finset.sum_congr rfl fun s _ => by rw [h s]
    rw [hinj]
    constructor
    · intro h
      refine ⟨fun r => ?_, ?_, ?_⟩
      · have hr := h ⟨r.val, by have := r.isLt; have := i.isLt; omega⟩
        have hle : r.val ≤ i.val := by have := r.isLt; omega
        have hne : (⟨r.val, by have := r.isLt; have := i.isLt; omega⟩ : Fin width) ≠ ⟨i.val, by omega⟩ := by
          intro heq; have := congrArg Fin.val heq; dsimp only at this; have := r.isLt; omega
        simp only [hle, hne, ↓reduceDIte, ↓reduceIte] at hr
        exact hr
      · have hi' := h ⟨i.val, by omega⟩
        simp only [le_refl, ↓reduceDIte, ↓reduceIte] at hi'
        exact hi'
      · have hm' := h idxM
        have hnotle : ¬(idxM.val ≤ i.val) := by dsimp only [idxM]; omega
        have hne : idxM ≠ ⟨i.val, by omega⟩ := by
          intro heq; have := congrArg Fin.val heq; dsimp only [idxM] at this; omega
        simp only [hnotle, hne, ↓reduceDIte, ↓reduceIte] at hm'
        exact hm'
    · rintro ⟨hprev, hi1, hm0⟩ s
      by_cases hs : s.val ≤ i.val
      · by_cases hsi : s = ⟨i.val, by omega⟩
        · rw [hsi]
          simp only [le_refl, ↓reduceDIte, ↓reduceIte]
          exact hi1
        · have hlt : s.val < i.val := by
            have hne : s.val ≠ i.val := fun heq => hsi (Fin.ext heq)
            omega
          simp only [hs, hsi, ↓reduceDIte, ↓reduceIte]
          exact hprev ⟨s.val, hlt⟩
      · by_cases hsm : s = idxM
        · subst hsm
          have hnotle : ¬(idxM.val ≤ i.val) := by dsimp only [idxM]; omega
          have hne : idxM ≠ ⟨i.val, by omega⟩ := by
            intro heq; have := congrArg Fin.val heq; dsimp only [idxM] at this; omega
          simp only [hnotle, hne, ↓reduceDIte, ↓reduceIte, hm0]
        · have hne : s ≠ ⟨i.val, by omega⟩ := fun heq => hs (by rw [heq])
          simp only [hs, hsm, hne, ↓reduceDIte, ↓reduceIte]
  have hφ0_inj : Function.Injective φ0 := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have h0 : φ0 y = 0 := hy
    have hzero_coord : ∀ i : Fin m,
        ∀ s : Fin width,
          (if hs : s.val ≤ i.val then y ⟨s.val, by have := i.isLt; omega⟩
           else if s = idxM then y ⟨m, by omega⟩ else 0) = 0 := by
      intro i
      have hi0 : (φ0 y).1 ⟨i.val, by omega⟩ = 0 := congrFun (congrArg Prod.fst h0) ⟨i.val, by omega⟩
      rw [hφ0_coord y i] at hi0
      exact (Fintype.linearIndependent_iff.mp (hbvec_li ⟨i.val, by omega⟩)) _ hi0
    funext r
    by_cases hrm : r.val < m
    · have := hzero_coord ⟨r.val, hrm⟩ ⟨r.val, by omega⟩
      simp only [le_refl, ↓reduceDIte] at this
      exact this
    · have hreq : r = ⟨m, by omega⟩ := Fin.ext (by dsimp only; have := r.isLt; omega)
      rw [hreq]
      have := hzero_coord ⟨0, by omega⟩ idxM
      have hnotle : ¬(idxM.val ≤ 0) := by dsimp only [idxM]; omega
      simp only [hnotle, ↓reduceDIte, ↓reduceIte] at this
      exact this
  let i0 : Fin blocks := ⟨0, by omega⟩
  let i1 : Fin blocks := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp only [i0, i1] at this; omega
  let p0 : Fin width := pivot i0
  let p1 : Fin width := pivot i1
  let q0 : Fin width := (perm i0) idxM
  have hq0_ne_p0 : q0 ≠ p0 := by
    dsimp only [q0, perm, p0]
    have hne : idxM ≠ ⟨i0.val % width, Nat.mod_lt _ (by omega)⟩ := by
      intro heq; have := congrArg Fin.val heq; simp only [idxM, i0, Nat.zero_mod] at this; omega
    have h1 : (Equiv.swap (pivot i0) ⟨i0.val % width, Nat.mod_lt _ (by omega)⟩) idxM ≠
        (Equiv.swap (pivot i0) ⟨i0.val % width, Nat.mod_lt _ (by omega)⟩) ⟨i0.val % width, Nat.mod_lt _ (by omega)⟩ :=
      (Equiv.swap _ _).injective.ne hne
    simpa [Equiv.swap_apply_right] using h1
  let lam0 : B width →ₗ[F2] F2 :=
    { toFun := fun z => z q0 + center i0 q0 * z p0
      map_add' := fun a b => by simp only [Pi.add_apply]; ring
      map_smul' := fun c a => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hlam0_c0 : lam0 (center i0) = 0 := by
    dsimp only [lam0, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hpivot i0, mul_one]
    exact z2_add_self _
  have hlam0_bm : lam0 (bvec i0 idxM) = 1 := by
    dsimp only [lam0, LinearMap.coe_mk, AddHom.coe_mk, bvec, basisVec]
    change (if q0 = p0 then center i0 else Pi.single q0 1) q0 +
      center i0 q0 * (if q0 = p0 then center i0 else Pi.single q0 1) p0 = 1
    simp [hq0_ne_p0, Pi.single_apply, Ne.symm hq0_ne_p0]
  let ψ : V blocks width spare →ₗ[F2] F2 :=
    { toFun := fun x => tilt x + lam0 (x.1 i0)
      map_add' := fun a b => by simp only [map_add, Prod.fst_add, Pi.add_apply]; ring
      map_smul' := fun c a => by simp only [map_smul, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]; ring }
  have hψ_φ0 : ∀ y : Fin (m + 1) → F2, ψ (φ0 y) = tilt (φ0 y) + y ⟨m, by omega⟩ := by
    intro y
    dsimp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    have h0 : (φ0 y).1 i0 = y ⟨0, by omega⟩ • center i0 + y ⟨m, by omega⟩ • bvec i0 idxM := by
      dsimp only [φ0, LinearMap.coe_mk, AddHom.coe_mk, i0]
      have hlt : 0 < m := by omega
      simp only [hlt, ↓reduceDIte, Fin.sum_univ_one]
      have hbc := hbvec_center ⟨0, hlt⟩
      simpa [i0] using congrArg (fun z => y ⟨0, by omega⟩ • z + y ⟨m, by omega⟩ • bvec i0 idxM) hbc
    rw [h0, map_add, map_smul, map_smul, hlam0_c0, hlam0_bm, smul_zero, zero_add, smul_eq_mul, mul_one]
  have hex_t2 : ∃ t2 : Fin width, t2 ≠ p0 ∧ t2 ≠ q0 := by
    let S : Finset (Fin width) := {p0, q0}
    have hlt : S.card < (Finset.univ : Finset (Fin width)).card := by
      have h1 : S.card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨t2, _, ht2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at ht2
    exact ⟨t2, ht2.1, ht2.2⟩
  obtain ⟨t2, ht2_p0, ht2_q0⟩ := hex_t2
  have hcard_other1 : Fintype.card {s : Fin width // s ≠ p1} = width - 1 := by
    have : Fintype.card {s : Fin width // s ≠ p1} = ((Finset.univ : Finset (Fin width)).erase p1).card := by
      rw [Fintype.card_subtype]; congr 1; ext s; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ p1), Finset.card_univ, Fintype.card_fin]
  let e1 : Fin (width - 1) ≃ {s : Fin width // s ≠ p1} :=
    (Fintype.equivFinOfCardEq hcard_other1).symm
  let φ1 : (Fin (m + 1) → F2) →ₗ[F2] V blocks width spare :=
    { toFun := fun y =>
        (fun i =>
          if i = i0 then y ⟨m, by omega⟩ • Pi.single t2 1
          else if i = i1 then ∑ r : Fin m, y ⟨r.val, by omega⟩ • Pi.single (e1 ⟨r.val, by omega⟩).val 1
          else 0, 0)
      map_add' := fun y1 y2 => by
        ext i t
        · dsimp only [Prod.fst_add, Pi.add_apply]
          split_ifs
          · simp [add_mul]
          · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
          · simp
        · simp
      map_smul' := fun c y => by
        ext i t
        · dsimp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          split_ifs
          · simp [mul_assoc]
          · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => by ring
          · simp
        · simp }
  have hφ1_inj : Function.Injective φ1 := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have h0 : φ1 y = 0 := hy
    funext r
    by_cases hrm : r.val < m
    · have h1 := congrFun (congrFun (congrArg Prod.fst h0) i1) (e1 ⟨r.val, by omega⟩).val
      simp only [φ1, LinearMap.coe_mk, AddHom.coe_mk, hi01.symm, ↓reduceIte, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have hterm : ∀ k : Fin m,
          y ⟨k.val, by omega⟩ * (Pi.single (e1 ⟨k.val, by omega⟩).val (1 : F2) : B width) (e1 ⟨r.val, by omega⟩).val =
          if k = ⟨r.val, hrm⟩ then y r else 0 := by
        intro k
        by_cases hkr : k = ⟨r.val, hrm⟩
        · subst hkr; simp
        · have hne : (e1 ⟨r.val, by omega⟩).val ≠ (e1 ⟨k.val, by omega⟩).val := by
            intro heq
            have he2 := e1.injective (Subtype.ext heq)
            exact hkr (Fin.ext (congrArg Fin.val he2).symm)
          simp [hkr, Pi.single_apply, hne]
      simp_rw [hterm] at h1
      simpa using h1
    · have hreq : r = ⟨m, by omega⟩ := Fin.ext (by dsimp only; have := r.isLt; omega)
      rw [hreq]
      have h1 := congrFun (congrFun (congrArg Prod.fst h0) i0) t2
      simp only [φ1, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one, Pi.zero_apply] at h1
      exact h1
  refine build_adaptive_from_pair label d hd_pos hd (by omega) ψ offset (LinearMap.range φ0) (LinearMap.range φ1)
    (by rw [LinearMap.finrank_range_of_inj hφ0_inj, Module.finrank_fin_fun, hdim_eq])
    (by rw [LinearMap.finrank_range_of_inj hφ1_inj, Module.finrank_fin_fun, hdim_eq]) ?_ ?_
  · rintro x ⟨y, rfl⟩ hx_ne
    have hy_ne : y ≠ 0 := fun hy0 => hx_ne (by subst hy0; exact map_zero φ0)
    have hsum_guard : ∑ i : Fin blocks, (if (φ0 y).1 i = center i then (1 : F2) else 0) =
        y ⟨m, by omega⟩ + 1 := by
      have hsum_m : ∑ i : Fin blocks, (if (φ0 y).1 i = center i then (1 : F2) else 0) =
          ∑ i : Fin m, (if (φ0 y).1 ⟨i.val, by omega⟩ = center ⟨i.val, by omega⟩ then (1 : F2) else 0) := by
        let Sm : Finset (Fin blocks) := Finset.univ.filter (fun i => i.val < m)
        rw [← Finset.sum_subset (Finset.subset_univ Sm)]
        · refine Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ heq; exact Fin.ext (congrArg (Fin.val : Fin m → Nat) heq)
          · intro i _; exact ⟨⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, Fin.ext rfl⟩
          · intro _ _; rfl
        · intro i _ hi_not
          have hge : ¬(i.val < m) := by simpa [Sm] using hi_not
          have h0i : (φ0 y).1 i = 0 := by simp [φ0, hge]
          simp only [h0i, Ne.symm (hnc i), ↓reduceIte]
      rw [hsum_m]
      rcases z2_eq_zero_or_one (y ⟨m, by omega⟩) with hym0 | hym1
      · rw [hym0, zero_add]
        have hex_nz : ∃ r : Fin m, y ⟨r.val, by omega⟩ ≠ 0 := by
          by_contra hnot; push Not at hnot
          apply hy_ne; funext r
          by_cases hrm : r.val < m
          · exact hnot ⟨r.val, hrm⟩
          · have hreq : r = ⟨m, by omega⟩ := Fin.ext (by dsimp only; have := r.isLt; omega)
            rw [hreq, hym0]; rfl
        let Spos : Finset (Fin m) := Finset.univ.filter (fun r => y ⟨r.val, by omega⟩ ≠ 0)
        have hSpos_ne : Spos.Nonempty := by
          obtain ⟨r, hr⟩ := hex_nz
          exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
        let iFirst := Spos.min' hSpos_ne
        have hiF_mem : iFirst ∈ Spos := Finset.min'_mem Spos hSpos_ne
        have hiF_1 : y ⟨iFirst.val, by omega⟩ = 1 := (z2_ne_zero_iff _).mp (Finset.mem_filter.mp hiF_mem).2
        have hiF_prev : ∀ r : Fin iFirst.val, y ⟨r.val, by omega⟩ = 0 := by
          intro r
          by_contra hne
          have hmem : (⟨r.val, by omega⟩ : Fin m) ∈ Spos := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          have hle : iFirst ≤ ⟨r.val, by omega⟩ := Finset.min'_le Spos _ hmem
          have : iFirst.val ≤ r.val := hle
          omega
        rw [Finset.sum_eq_single iFirst]
        · have hhitF := (hφ0_hit y iFirst).mpr ⟨hiF_prev, hiF_1, hym0⟩
          simp only [hhitF, ↓reduceIte]
        · intro i _ hne
          have hnot_hit : (φ0 y).1 ⟨i.val, by omega⟩ ≠ center ⟨i.val, by omega⟩ := by
            intro hhit
            rcases (hφ0_hit y i).mp hhit with ⟨hprev, hi1, _⟩
            by_cases hlt : i.val < iFirst.val
            · have := hiF_prev ⟨i.val, hlt⟩
              rw [this] at hi1; exact zero_ne_one hi1
            · have hgt : iFirst.val < i.val := by
                have : i.val ≠ iFirst.val := fun heq => hne (Fin.ext heq)
                omega
              have := hprev ⟨iFirst.val, hgt⟩
              rw [hiF_1] at this; exact one_ne_zero this
          simp only [hnot_hit, ↓reduceIte]
        · intro h; exact absurd (Finset.mem_univ iFirst) h
      · rw [hym1, show (1 : F2) + 1 = 0 by decide]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hnot_hit : (φ0 y).1 ⟨i.val, by omega⟩ ≠ center ⟨i.val, by omega⟩ := by
          intro hhit
          have h0 := ((hφ0_hit y i).mp hhit).2.2
          rw [hym1] at h0; exact one_ne_zero h0
        simp only [hnot_hit, ↓reduceIte]
    dsimp only [label]
    rw [hsum_guard, hψ_φ0 y]
    intro heq
    have h10 : (1 : F2) = 0 := by linear_combination heq
    exact one_ne_zero h10
  · rintro x ⟨y, rfl⟩ _
    have hno_hit : ∀ i : Fin blocks, (φ1 y).1 i ≠ center i := by
      intro i
      by_cases hi0 : i = i0
      · subst hi0
        intro heq
        have h := congrFun heq p0
        simp only [φ1, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte, Pi.smul_apply, Pi.single_apply,
          Ne.symm ht2_p0, smul_zero] at h
        dsimp only [p0] at h
        rw [hpivot i0] at h
        exact zero_ne_one h
      · by_cases hi1 : i = i1
        · subst hi1
          intro heq
          have h := congrFun heq p1
          simp only [φ1, LinearMap.coe_mk, AddHom.coe_mk, hi0, ↓reduceIte, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul] at h
          have hsum0 : ∑ r : Fin m, y ⟨r.val, by omega⟩ * (Pi.single (e1 ⟨r.val, by omega⟩).val (1 : F2) : B width) p1 = 0 := by
            refine Finset.sum_eq_zero fun r _ => ?_
            have hne : p1 ≠ (e1 ⟨r.val, by omega⟩).val := Ne.symm (e1 ⟨r.val, by omega⟩).property
            simp [hne]
          rw [hsum0] at h
          dsimp only [p1] at h
          rw [hpivot i1] at h
          exact zero_ne_one h
        · simp only [φ1, LinearMap.coe_mk, AddHom.coe_mk, hi0, hi1, ↓reduceIte]
          exact Ne.symm (hnc i)
    have hsum0 : ∑ i : Fin blocks, (if (φ1 y).1 i = center i then (1 : F2) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp only [hno_hit i, ↓reduceIte]
    have hlam0_val : lam0 ((φ1 y).1 i0) = 0 := by
      dsimp only [lam0, φ1, LinearMap.coe_mk, AddHom.coe_mk]
      simp [Pi.single_apply, Ne.symm ht2_q0, Ne.symm ht2_p0]
    have hψ1 : ψ (φ1 y) = tilt (φ1 y) := by
      dsimp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]; rw [hlam0_val, add_zero]
    dsimp only [label]
    rw [hsum0, add_zero, hψ1]
    intro heq
    have h10 : (1 : F2) = 0 := by linear_combination -heq
    exact one_ne_zero h10

private lemma main_796 (blocks width spare depth : Nat) (hb : 2 ≤ blocks) (hw : 3 ≤ width)
    (center : Fin blocks → B width) (tilt : V blocks width spare →ₗ[F2] F2) (offset : F2) :
    let label := fun x : V blocks width spare => tilt x + offset +
      ∑ i : Fin blocks, (if x.1 i = center i then (1 : F2) else 0)
    let saved := if ∃ i : Fin blocks, center i = 0
      then width - 1 else min blocks (width - 1)
    let correct := fun (out : P blocks width spare → Bool) =>
      (∀ b : F2, out (b, 0) = false) ∧ (∀ x : V blocks width spare, x ≠ 0 → out (label x, x) = true)
    let adaptive := ∃ (ask : (j : Fin depth) → (Fin j.val → F2) → (P blocks width spare →ₗ[F2] F2))
        (ans : P blocks width spare → Fin depth → F2) (read : (Fin depth → F2) → Bool),
      (∀ (p : P blocks width spare) (j : Fin depth), ans p j =
        ask j (fun prev => ans p ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p) ∧
      correct (fun p => read (ans p))
    let fixed := ∃ (Q : P blocks width spare →ₗ[F2] (Fin depth → F2)) (read : (Fin depth → F2) → Bool),
      correct (fun p => read (Q p))
    And (Iff adaptive (blocks * width + spare - saved ≤ depth))
        (Iff fixed (blocks * width + spare ≤ depth)) := by
  classical
  refine ⟨⟨adaptive_lower_bound blocks width spare depth center tilt offset, ?_⟩,
    fixed_iff blocks width spare depth center tilt offset⟩
  intro hd
  by_cases hzero : ∃ i : Fin blocks, center i = 0
  · obtain ⟨i0, hi0⟩ := hzero
    have hd' : blocks * width + spare - (width - 1) ≤ depth := by
      have : (if ∃ i : Fin blocks, center i = 0 then width - 1 else min blocks (width - 1)) = width - 1 := by
        simp only [show ∃ i : Fin blocks, center i = 0 from ⟨i0, hi0⟩, ↓reduceIte]
      simpa [this] using hd
    exact adaptive_upper_centered hb hw center tilt offset i0 hi0 hd'
  · have hd' : blocks * width + spare - min blocks (width - 1) ≤ depth := by
      have : (if ∃ i : Fin blocks, center i = 0 then width - 1 else min blocks (width - 1)) = min blocks (width - 1) := by
        simp only [hzero, ↓reduceIte]
      simpa [this] using hd
    push Not at hzero
    exact adaptive_upper_noncentered hb hw center tilt offset hzero hd'

end PEqualNP.Outside.L_lib_796_aux

theorem PEqualNP.Outside.L_lib_796 : ∀ (blocks width spare depth : Nat), 2 ≤ blocks → 3 ≤ width →
  let F := ZMod 2
  let B := Fin width → F
  let V := (Fin blocks → B) × (Fin spare → F)
  let P := F × V
  let n := blocks*width + spare
  ∀ (center : Fin blocks → B) (tilt : V →ₗ[F] F) (offset : F),
    let label := fun x : V => tilt x + offset +
      ∑ i : Fin blocks, (if x.1 i = center i then (1 : F) else 0)
    let saved := if ∃ i : Fin blocks, center i = 0
      then width-1 else min blocks (width-1)
    let correct := fun (out : P → Bool) =>
      (∀ b : F, out (b,0) = false) ∧ (∀ x : V, x ≠ 0 → out (label x,x) = true)
    let adaptive := ∃ (ask : (j : Fin depth) → (Fin j.val → F) → (P →ₗ[F] F))
        (ans : P → Fin depth → F) (read : (Fin depth → F) → Bool),
      (∀ (p : P) (j : Fin depth), ans p j =
        ask j (fun prev => ans p ⟨prev.val, Nat.lt_trans prev.isLt j.isLt⟩) p) ∧
      correct (fun p => read (ans p))
    let fixed := ∃ (Q : P →ₗ[F] (Fin depth → F)) (read : (Fin depth → F) → Bool),
      correct (fun p => read (Q p))
    And (Iff adaptive (n-saved ≤ depth)) (Iff fixed (n ≤ depth)) := by
  intro blocks width spare depth hb hw F B V P n center tilt offset
  exact PEqualNP.Outside.L_lib_796_aux.main_796 blocks width spare depth hb hw center tilt offset

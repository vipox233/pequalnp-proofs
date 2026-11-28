import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1002_aux

lemma mulVecLin_sub {K : Type} [Field K] {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) K) :
    (M - N).mulVecLin = M.mulVecLin - N.mulVecLin := by
  apply LinearMap.ext
  intro x
  ext i
  simp

lemma finrank_range_mulVecLin {K : Type} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) K) :
    Module.finrank K (LinearMap.range M.mulVecLin) = Matrix.rank M := rfl

lemma rank_eq_finrank_range_sub {K : Type} [Field K] {r : ℕ}
    (M N : Matrix (Fin r) (Fin r) K) :
    Matrix.rank (M - N) = Module.finrank K (LinearMap.range (M.mulVecLin - N.mulVecLin)) := by
  rw [← finrank_range_mulVecLin, mulVecLin_sub]

lemma exists_dual_eq_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (v : V) (hv : v ≠ 0) :
    ∃ ψ : V →ₗ[K] K, ψ v = 1 := by
  let S : Submodule K V := Submodule.span K {v}
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  let proj : V →ₗ[K] S := Submodule.projectionOnto S C hC
  let f : S →ₗ[K] K :=
    { toFun := fun x => Classical.choose (Submodule.mem_span_singleton.mp x.2)
      map_add' := fun x y => by
        have hx := Classical.choose_spec (Submodule.mem_span_singleton.mp x.2)
        have hy := Classical.choose_spec (Submodule.mem_span_singleton.mp y.2)
        have hxy := Classical.choose_spec (Submodule.mem_span_singleton.mp (x + y).2)
        have h1 : Classical.choose (Submodule.mem_span_singleton.mp (x + y).2) • v =
            (Classical.choose (Submodule.mem_span_singleton.mp x.2) +
              Classical.choose (Submodule.mem_span_singleton.mp y.2)) • v := by
          rw [add_smul, hx, hy]
          exact hxy
        exact smul_left_injective K hv h1
      map_smul' := fun c x => by
        have hx := Classical.choose_spec (Submodule.mem_span_singleton.mp x.2)
        have hcx := Classical.choose_spec (Submodule.mem_span_singleton.mp (c • x).2)
        have h1 : Classical.choose (Submodule.mem_span_singleton.mp (c • x).2) • v =
            (c * Classical.choose (Submodule.mem_span_singleton.mp x.2)) • v := by
          rw [mul_smul, hx]
          exact hcx
        exact smul_left_injective K hv h1 }
  refine ⟨f.comp proj, ?_⟩
  have hvS : v ∈ S := Submodule.subset_span (Set.mem_singleton v)
  have hp : proj v = ⟨v, hvS⟩ := Submodule.projectionOnto_apply_left hC ⟨v, hvS⟩
  simp only [LinearMap.comp_apply, hp, f, LinearMap.coe_mk, AddHom.coe_mk]
  have hspec := Classical.choose_spec (Submodule.mem_span_singleton.mp hvS)
  have h1 : Classical.choose (Submodule.mem_span_singleton.mp hvS) • v = (1 : K) • v := by
    rw [one_smul]
    exact hspec
  exact smul_left_injective K hv h1

lemma exists_dual_two_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (S : Submodule K V) (w z : V) (hw : w ∉ S) (hz : z ∉ S) :
    ∃ φ : V →ₗ[K] K, (∀ x ∈ S, φ x = 0) ∧ φ w = 1 ∧ φ z ≠ 0 := by
  let Q := V ⧸ S
  let w' : Q := S.mkQ w
  let z' : Q := S.mkQ z
  have hw' : w' ≠ 0 := by
    intro h
    exact hw ((Submodule.Quotient.mk_eq_zero S).mp h)
  have hz' : z' ≠ 0 := by
    intro h
    exact hz ((Submodule.Quotient.mk_eq_zero S).mp h)
  by_cases hdep : z' ∈ Submodule.span K ({w'} : Set Q)
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdep
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_smul] at hc
      exact hz' hc.symm
    obtain ⟨ψ, hψ⟩ := exists_dual_eq_one (K := K) w' hw'
    refine ⟨ψ.comp S.mkQ, ?_, ?_, ?_⟩
    · intro x hx
      show ψ (S.mkQ x) = 0
      have h0 : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [h0]
      exact map_zero ψ
    · exact hψ
    · show ψ z' ≠ 0
      rw [← hc, ψ.map_smul, hψ, smul_eq_mul, mul_one]
      exact hc0
  · let Sw : Submodule K Q := Submodule.span K {w'}
    let Sz : Submodule K Q := Submodule.span K {z'}
    let U : Submodule K Q := Sw ⊔ Sz
    have hdisj : Disjoint Sw Sz := by
      rw [Submodule.disjoint_def]
      intro x hxw hxz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxw
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hxz
      by_cases hb0 : b = 0
      · rw [hb0, zero_smul] at hb
        exact hb.symm
      · exfalso
        apply hdep
        rw [Submodule.mem_span_singleton]
        refine ⟨b⁻¹ * a, ?_⟩
        rw [mul_smul, ← hb, inv_smul_smul₀ hb0]
    obtain ⟨ψw, hψw⟩ := exists_dual_eq_one (K := K) w' hw'
    obtain ⟨ψz, hψz⟩ := exists_dual_eq_one (K := K) z' hz'
    let pw : U →ₗ[K] Sw :=
      Submodule.projectionOnto (Sw.comap U.subtype) (Sz.comap U.subtype)
        (by
          constructor
          · rw [Submodule.disjoint_def]
            intro x h1 h2
            apply Subtype.ext
            exact Submodule.disjoint_def.mp hdisj x.1 h1 h2
          · rw [codisjoint_iff, eq_top_iff]
            intro x _
            obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp x.2
            have haU : a ∈ U := Submodule.mem_sup_left ha
            have hbU : b ∈ U := Submodule.mem_sup_right hb
            rw [Submodule.mem_sup]
            refine ⟨⟨a, haU⟩, ha, ⟨b, hbU⟩, hb, ?_⟩
            apply Subtype.ext
            exact hab) |>.comp LinearMap.id |> fun g =>
        { toFun := fun x => ⟨(g x).1.1, (g x).2⟩
          map_add' := fun x y => by ext; simp [map_add]
          map_smul' := fun c x => by ext; simp [map_smul] }
    let pz : U →ₗ[K] Sz :=
      { toFun := fun x => ⟨x.1 - (pw x).1, by
          have h1 : x.1 = (pw x).1 + (x.1 - (pw x).1) := by abel
          have hmem : x.1 - (pw x).1 ∈ Sz := by
            obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp x.2
            have haU : a ∈ U := Submodule.mem_sup_left ha
            have hbU : b ∈ U := Submodule.mem_sup_right hb
            have hx_eq : x = ⟨a, haU⟩ + ⟨b, hbU⟩ := by apply Subtype.ext; exact hab.symm
            have hpw_a : (pw ⟨a, haU⟩).1 = a := by
              have h := Submodule.projectionOnto_apply_left
                (p := Sw.comap U.subtype) (q := Sz.comap U.subtype)
                (by
                  constructor
                  · rw [Submodule.disjoint_def]
                    intro y h1 h2
                    apply Subtype.ext
                    exact Submodule.disjoint_def.mp hdisj y.1 h1 h2
                  · rw [codisjoint_iff, eq_top_iff]
                    intro y _
                    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp y.2
                    rw [Submodule.mem_sup]
                    exact ⟨⟨u, Submodule.mem_sup_left hu⟩, hu, ⟨v, Submodule.mem_sup_right hv⟩, hv,
                      Subtype.ext huv⟩) ⟨⟨a, haU⟩, ha⟩
              exact congrArg (fun t => t.1.1) h
            have hpw_b : (pw ⟨b, hbU⟩).1 = 0 := by
              have h := Submodule.projectionOnto_apply_right
                (p := Sw.comap U.subtype) (q := Sz.comap U.subtype)
                (by
                  constructor
                  · rw [Submodule.disjoint_def]
                    intro y h1 h2
                    apply Subtype.ext
                    exact Submodule.disjoint_def.mp hdisj y.1 h1 h2
                  · rw [codisjoint_iff, eq_top_iff]
                    intro y _
                    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp y.2
                    rw [Submodule.mem_sup]
                    exact ⟨⟨u, Submodule.mem_sup_left hu⟩, hu, ⟨v, Submodule.mem_sup_right hv⟩, hv,
                      Subtype.ext huv⟩) ⟨⟨b, hbU⟩, hb⟩
              exact congrArg (fun t => t.1.1) h
            have hpw_x : (pw x).1 = a := by
              rw [hx_eq, map_add]
              show (pw ⟨a, haU⟩).1 + (pw ⟨b, hbU⟩).1 = a
              rw [hpw_a, hpw_b, add_zero]
            rw [hpw_x, ← hab, add_sub_cancel_left]
            exact hb
          exact hmem⟩
        map_add' := fun x y => by ext; simp [map_add]; abel
        map_smul' := fun c x => by ext; simp [map_smul, smul_sub] }
    let fU : U →ₗ[K] K := (ψw.comp Sw.subtype).comp pw + (ψz.comp Sz.subtype).comp pz
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
    let pU : Q →ₗ[K] U := Submodule.projectionOnto U C hC
    let ψ : Q →ₗ[K] K := fU.comp pU
    have hwSw : w' ∈ Sw := Submodule.subset_span (Set.mem_singleton w')
    have hzSz : z' ∈ Sz := Submodule.subset_span (Set.mem_singleton z')
    have hwU : w' ∈ U := Submodule.mem_sup_left hwSw
    have hzU : z' ∈ U := Submodule.mem_sup_right hzSz
    have hpw_w : (pw ⟨w', hwU⟩).1 = w' := by
      have h := Submodule.projectionOnto_apply_left
        (p := Sw.comap U.subtype) (q := Sz.comap U.subtype)
        (by
          constructor
          · rw [Submodule.disjoint_def]
            intro y h1 h2
            apply Subtype.ext
            exact Submodule.disjoint_def.mp hdisj y.1 h1 h2
          · rw [codisjoint_iff, eq_top_iff]
            intro y _
            obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp y.2
            rw [Submodule.mem_sup]
            exact ⟨⟨u, Submodule.mem_sup_left hu⟩, hu, ⟨v, Submodule.mem_sup_right hv⟩, hv,
              Subtype.ext huv⟩) ⟨⟨w', hwU⟩, hwSw⟩
      exact congrArg (fun t => t.1.1) h
    have hpw_z : (pw ⟨z', hzU⟩).1 = 0 := by
      have h := Submodule.projectionOnto_apply_right
        (p := Sw.comap U.subtype) (q := Sz.comap U.subtype)
        (by
          constructor
          · rw [Submodule.disjoint_def]
            intro y h1 h2
            apply Subtype.ext
            exact Submodule.disjoint_def.mp hdisj y.1 h1 h2
          · rw [codisjoint_iff, eq_top_iff]
            intro y _
            obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp y.2
            rw [Submodule.mem_sup]
            exact ⟨⟨u, Submodule.mem_sup_left hu⟩, hu, ⟨v, Submodule.mem_sup_right hv⟩, hv,
              Subtype.ext huv⟩) ⟨⟨z', hzU⟩, hzSz⟩
      exact congrArg (fun t => t.1.1) h
    refine ⟨ψ.comp S.mkQ, ?_, ?_, ?_⟩
    · intro x hx
      have h0 : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
      simp [ψ, h0]
    · show fU (pU w') = 1
      rw [Submodule.projectionOnto_apply_left hC ⟨w', hwU⟩]
      simp only [fU, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        pz, LinearMap.coe_mk, AddHom.coe_mk, hpw_w, sub_self, map_zero, add_zero]
      exact hψw
    · show fU (pU z') ≠ 0
      rw [Submodule.projectionOnto_apply_left hC ⟨z', hzU⟩]
      simp only [fU, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        pz, LinearMap.coe_mk, AddHom.coe_mk, hpw_z, sub_zero, map_zero, zero_add]
      rw [hψz]
      exact one_ne_zero

lemma finrank_range_rankOne_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (u : W) (φ : V →ₗ[K] K) :
    Module.finrank K (LinearMap.range (φ.smulRight u)) ≤ 1 := by
  have hcomp : φ.smulRight u = (LinearMap.toSpanSingleton K W u).comp φ := by
    ext x
    rfl
  rw [hcomp, LinearMap.range_comp]
  have h1 := Submodule.finrank_map_le (LinearMap.toSpanSingleton K W u) (LinearMap.range φ)
  have h2 : Module.finrank K (LinearMap.range φ) ≤ Module.finrank K K := Submodule.finrank_le _
  rw [Module.finrank_self K] at h2
  exact le_trans h1 h2

lemma rank_one_step {K : Type} [Field K] {r : ℕ} (H : Matrix (Fin r) (Fin r) K)
    (hd : 0 < Matrix.rank (1 - H)) :
    ∃ H1 : Matrix (Fin r) (Fin r) K,
      Matrix.rank (H - H1) ≤ 1 ∧
      Matrix.rank (1 - H1) + 1 ≤ Matrix.rank (1 - H) ∧
      Module.finrank K (LinearMap.ker H1.mulVecLin) ≤
        Module.finrank K (LinearMap.ker H.mulVecLin) - 1 := by
  let D : Matrix (Fin r) (Fin r) K := 1 - H
  have hD_ker_lt : Module.finrank K (LinearMap.ker D.mulVecLin) < r := by
    have hrn := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
    rw [Module.finrank_fin_fun] at hrn
    have : Module.finrank K (LinearMap.range D.mulVecLin) = Matrix.rank (1 - H) := rfl
    omega
  by_cases hc : 0 < Module.finrank K (LinearMap.ker H.mulVecLin)
  · have hrange_not_le : ¬ (LinearMap.range D.mulVecLin ≤ LinearMap.range H.mulVecLin) := by
      intro hle
      have htop : LinearMap.range H.mulVecLin = ⊤ := by
        rw [eq_top_iff]
        intro v _
        have hv : v = H.mulVecLin v + D.mulVecLin v := by
          have : H.mulVecLin v + D.mulVecLin v = (H + D).mulVecLin v := by
            rw [Matrix.mulVecLin_add, LinearMap.add_apply]
          rw [this]
          simp [D]
        rw [hv]
        exact Submodule.add_mem _ ⟨v, rfl⟩ (hle ⟨v, rfl⟩)
      have hrn := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
      rw [htop, finrank_top, Module.finrank_fin_fun] at hrn
      omega
    have hw_ex : ∃ w : Fin r → K, D.mulVecLin w ∉ LinearMap.range H.mulVecLin := by
      by_contra hall
      push Not at hall
      apply hrange_not_le
      rintro _ ⟨w, rfl⟩
      exact hall w
    obtain ⟨w, hw⟩ := hw_ex
    have hw_nker : w ∉ LinearMap.ker D.mulVecLin := by
      intro h
      rw [LinearMap.mem_ker] at h
      rw [h] at hw
      exact hw (Submodule.zero_mem _)
    have hz_ex : ∃ z : Fin r → K, z ∈ LinearMap.ker H.mulVecLin ∧ z ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have hbot : LinearMap.ker H.mulVecLin = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro z hz
        exact hnone z hz
      rw [hbot, finrank_bot] at hc
      omega
    obtain ⟨z, hz_ker, hz0⟩ := hz_ex
    have hz_nkerD : z ∉ LinearMap.ker D.mulVecLin := by
      intro hzD
      rw [LinearMap.mem_ker] at hz_ker hzD
      have : z = H.mulVecLin z + D.mulVecLin z := by
        have h1 : H.mulVecLin z + D.mulVecLin z = (H + D).mulVecLin z := by
          rw [Matrix.mulVecLin_add, LinearMap.add_apply]
        rw [h1]
        simp [D]
      rw [hz_ker, hzD, add_zero] at this
      exact hz0 this
    obtain ⟨φ, hφD, hφw, hφz⟩ :=
      exists_dual_two_ne_zero (LinearMap.ker D.mulVecLin) w z hw_nker hz_nkerD
    let u : Fin r → K := D.mulVecLin w
    let T1 : (Fin r → K) →ₗ[K] (Fin r → K) := H.mulVecLin + φ.smulRight u
    let H1 : Matrix (Fin r) (Fin r) K := LinearMap.toMatrix' T1
    have hH1_lin : H1.mulVecLin = T1 := Matrix.toLin'_toMatrix' T1
    refine ⟨H1, ?_, ?_, ?_⟩
    · rw [rank_eq_finrank_range_sub, hH1_lin]
      have hsub : H.mulVecLin - T1 = (-φ).smulRight u := by
        ext x i
        simp [T1]
      rw [hsub]
      exact finrank_range_rankOne_le u (-φ)
    · have hD1_lin : (1 - H1).mulVecLin = D.mulVecLin - φ.smulRight u := by
        rw [mulVecLin_sub, Matrix.mulVecLin_one, hH1_lin]
        apply LinearMap.ext
        intro x
        ext i
        simp [T1, D, mulVecLin_sub]
        abel
      have hker_lt : LinearMap.ker D.mulVecLin < LinearMap.ker (1 - H1).mulVecLin := by
        rw [lt_iff_le_and_ne]
        constructor
        · intro x hx
          rw [LinearMap.mem_ker, hD1_lin, LinearMap.sub_apply, LinearMap.smulRight_apply,
            LinearMap.mem_ker.mp hx, hφD x hx, zero_smul, sub_zero]
        · intro heq
          apply hw_nker
          rw [heq, LinearMap.mem_ker, hD1_lin, LinearMap.sub_apply, LinearMap.smulRight_apply,
            hφw, one_smul, sub_self]
      have hfin_lt : Module.finrank K (LinearMap.ker D.mulVecLin) <
          Module.finrank K (LinearMap.ker (1 - H1).mulVecLin) :=
        Submodule.finrank_lt_finrank_of_lt hker_lt
      have hrn1 := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
      have hrn2 := LinearMap.finrank_range_add_finrank_ker (1 - H1).mulVecLin
      have hr1 : Module.finrank K (LinearMap.range D.mulVecLin) = Matrix.rank (1 - H) := rfl
      have hr2 : Module.finrank K (LinearMap.range (1 - H1).mulVecLin) = Matrix.rank (1 - H1) := rfl
      omega
    · have hker_lt : LinearMap.ker H1.mulVecLin < LinearMap.ker H.mulVecLin := by
        rw [lt_iff_le_and_ne]
        constructor
        · intro x hx
          rw [LinearMap.mem_ker, hH1_lin] at hx
          have h1 : H.mulVecLin x + φ x • u = 0 := hx
          have hφx0 : φ x = 0 := by
            by_contra hne
            apply hw
            refine ⟨-(φ x)⁻¹ • x, ?_⟩
            rw [map_smul, show H.mulVecLin x = -(φ x • u) from eq_neg_of_add_eq_zero_left h1]
            rw [smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hne, one_smul]
          rw [hφx0, zero_smul, add_zero] at h1
          exact h1
        · intro heq
          have hz1 : z ∈ LinearMap.ker H1.mulVecLin := by rw [heq]; exact hz_ker
          rw [LinearMap.mem_ker, hH1_lin] at hz1
          have h1 : H.mulVecLin z + φ z • u = 0 := hz1
          rw [LinearMap.mem_ker.mp hz_ker, zero_add] at h1
          have hu0 : u = 0 := (smul_eq_zero.mp h1).resolve_left hφz
          apply hw
          show u ∈ LinearMap.range H.mulVecLin
          rw [hu0]
          exact Submodule.zero_mem _
      have hfin_lt := Submodule.finrank_lt_finrank_of_lt hker_lt
      omega
  · have hc0 : Module.finrank K (LinearMap.ker H.mulVecLin) = 0 := by omega
    have hkerH : LinearMap.ker H.mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp hc0
    have hinjH : Function.Injective H.mulVecLin := LinearMap.ker_eq_bot.mp hkerH
    have hsurjH : Function.Surjective H.mulVecLin := by
      have hrn := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
      rw [hc0, add_zero] at hrn
      have htop : LinearMap.range H.mulVecLin = ⊤ :=
        Submodule.eq_top_of_finrank_eq hrn
      intro y
      have : y ∈ LinearMap.range H.mulVecLin := htop ▸ trivial
      exact this
    let eH : (Fin r → K) ≃ₗ[K] (Fin r → K) := LinearEquiv.ofBijective H.mulVecLin ⟨hinjH, hsurjH⟩
    have hw_ex : ∃ w : Fin r → K, w ∉ LinearMap.ker D.mulVecLin := by
      by_contra hall
      push Not at hall
      have htop : LinearMap.ker D.mulVecLin = ⊤ := by
        rw [eq_top_iff]
        intro w _
        exact hall w
      rw [htop, finrank_top, Module.finrank_fin_fun] at hD_ker_lt
      omega
    obtain ⟨w, hw_nker⟩ := hw_ex
    let z : Fin r → K := eH.symm w
    have hz_nkerD : z ∉ LinearMap.ker D.mulVecLin := by
      intro hzD
      rw [LinearMap.mem_ker] at hzD
      have hHz : H.mulVecLin z = w := eH.apply_symm_apply w
      have hDz : D.mulVecLin z = z - H.mulVecLin z := by
        simp [D, mulVecLin_sub]
      rw [hDz, hHz] at hzD
      have hzw : z = w := sub_eq_zero.mp hzD
      rw [hzw] at hHz
      apply hw_nker
      rw [LinearMap.mem_ker]
      simp [D, mulVecLin_sub, hHz]
    obtain ⟨φ, hφD, hφw, hφz⟩ :=
      exists_dual_two_ne_zero (LinearMap.ker D.mulVecLin) w z hw_nker hz_nkerD
    let u : Fin r → K := D.mulVecLin w
    let T1 : (Fin r → K) →ₗ[K] (Fin r → K) := H.mulVecLin + φ.smulRight u
    let H1 : Matrix (Fin r) (Fin r) K := LinearMap.toMatrix' T1
    have hH1_lin : H1.mulVecLin = T1 := Matrix.toLin'_toMatrix' T1
    refine ⟨H1, ?_, ?_, ?_⟩
    · rw [rank_eq_finrank_range_sub, hH1_lin]
      have hsub : H.mulVecLin - T1 = (-φ).smulRight u := by
        ext x i
        simp [T1]
      rw [hsub]
      exact finrank_range_rankOne_le u (-φ)
    · have hD1_lin : (1 - H1).mulVecLin = D.mulVecLin - φ.smulRight u := by
        rw [mulVecLin_sub, Matrix.mulVecLin_one, hH1_lin]
        apply LinearMap.ext
        intro x
        ext i
        simp [T1, D, mulVecLin_sub]
        abel
      have hker_lt : LinearMap.ker D.mulVecLin < LinearMap.ker (1 - H1).mulVecLin := by
        rw [lt_iff_le_and_ne]
        constructor
        · intro x hx
          rw [LinearMap.mem_ker, hD1_lin, LinearMap.sub_apply, LinearMap.smulRight_apply,
            LinearMap.mem_ker.mp hx, hφD x hx, zero_smul, sub_zero]
        · intro heq
          apply hw_nker
          rw [heq, LinearMap.mem_ker, hD1_lin, LinearMap.sub_apply, LinearMap.smulRight_apply,
            hφw, one_smul, sub_self]
      have hfin_lt := Submodule.finrank_lt_finrank_of_lt hker_lt
      have hrn1 := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
      have hrn2 := LinearMap.finrank_range_add_finrank_ker (1 - H1).mulVecLin
      have hr1 : Module.finrank K (LinearMap.range D.mulVecLin) = Matrix.rank (1 - H) := rfl
      have hr2 : Module.finrank K (LinearMap.range (1 - H1).mulVecLin) = Matrix.rank (1 - H1) := rfl
      omega
    · have hker1 : LinearMap.ker H1.mulVecLin = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker, hH1_lin] at hx
        have h1 : H.mulVecLin x + φ x • u = 0 := hx
        have hu_eq : eH.symm u = z - w := by
          apply eH.injective
          rw [eH.apply_symm_apply, map_sub]
          have hHz : eH z = w := eH.apply_symm_apply w
          rw [hHz]
          show D.mulVecLin w = w - H.mulVecLin w
          simp [D, mulVecLin_sub]
        have hx_eq : x = -(φ x) • (z - w) := by
          apply eH.injective
          have h2 : eH x = -(φ x • u) := eq_neg_of_add_eq_zero_left h1
          have hHz : eH z = w := eH.apply_symm_apply w
          rw [h2, map_smul, map_sub, hHz, neg_smul]
          congr 1
          show φ x • D.mulVecLin w = φ x • (w - H.mulVecLin w)
          simp [D, mulVecLin_sub]
        have hφx : φ x = -(φ x) * (φ z - 1) := by
          conv_lhs => rw [hx_eq]
          rw [map_smul, map_sub, hφw, smul_eq_mul]
        have hmul : φ x * φ z = 0 := by
          have h1 := congrArg (fun t => t + φ x * (φ z - 1)) hφx
          have h2 : φ x + φ x * (φ z - 1) = φ x * φ z := by ring
          have h3 : -(φ x) * (φ z - 1) + φ x * (φ z - 1) = 0 := by ring
          rw [h2, h3] at h1
          exact h1
        have hφx0 : φ x = 0 := (mul_eq_zero.mp hmul).resolve_right hφz
        rw [hx_eq, hφx0, neg_zero, zero_smul]
      rw [hker1, finrank_bot]
      exact Nat.zero_le _

lemma rank_sub_le_add {K : Type} [Field K] {r : ℕ}
    (A B C : Matrix (Fin r) (Fin r) K) :
    Matrix.rank (A - C) ≤ Matrix.rank (A - B) + Matrix.rank (B - C) := by
  have h : (A - C).mulVecLin = (A - B).mulVecLin + (B - C).mulVecLin := by
    rw [← Matrix.mulVecLin_add, sub_add_sub_cancel]
  have hle : LinearMap.range (A - C).mulVecLin ≤
      LinearMap.range (A - B).mulVecLin ⊔ LinearMap.range (B - C).mulVecLin := by
    rw [h]
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (A - B).mulVecLin) (LinearMap.range (B - C).mulVecLin)
  change Module.finrank K (LinearMap.range (A - C).mulVecLin) ≤
    Module.finrank K (LinearMap.range (A - B).mulVecLin) +
      Module.finrank K (LinearMap.range (B - C).mulVecLin)
  omega

lemma rank_multi_step {K : Type} [Field K] {r : ℕ} :
    ∀ (t : ℕ) (H : Matrix (Fin r) (Fin r) K),
      ∃ H' : Matrix (Fin r) (Fin r) K,
        Matrix.rank (H - H') ≤ t ∧
        Matrix.rank (1 - H') ≤ Matrix.rank (1 - H) - t ∧
        Module.finrank K (LinearMap.ker H'.mulVecLin) ≤
          Module.finrank K (LinearMap.ker H.mulVecLin) - t
  | 0, H => ⟨H, by simp, by simp, by simp⟩
  | t + 1, H => by
      by_cases hd : Matrix.rank (1 - H) = 0
      · have h1H : 1 - H = 0 := by
          by_contra hne
          have hpos : 0 < Matrix.rank (1 - H) := by
            have hne_lin : (1 - H).mulVecLin ≠ 0 := by
              intro h0
              apply hne
              ext i j
              have := LinearMap.congr_fun h0 (Pi.single j 1)
              have hval := congrFun this i
              simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single, Matrix.one_apply,
                Pi.single_apply, eq_comm] using hval
            have hbot : LinearMap.range (1 - H).mulVecLin ≠ ⊥ := by
              intro hb
              apply hne_lin
              apply LinearMap.ext
              intro x
              ext i
              have : (1 - H).mulVecLin x ∈ (⊥ : Submodule K (Fin r → K)) := hb ▸ ⟨x, rfl⟩
              have h0 : (1 - H).mulVecLin x = 0 := (Submodule.mem_bot K).mp this
              exact congrFun h0 i
            exact Nat.pos_of_ne_zero (fun h0 => hbot (Submodule.finrank_eq_zero.mp h0))
          omega
        have hH1 : H = 1 := (sub_eq_zero.mp h1H).symm
        refine ⟨1, ?_, ?_, ?_⟩
        · rw [hH1, sub_self, Matrix.rank_zero]
          exact Nat.zero_le _
        · rw [sub_self, Matrix.rank_zero]
          exact Nat.zero_le _
        · rw [Matrix.mulVecLin_one, LinearMap.ker_id, finrank_bot]
          exact Nat.zero_le _
      · obtain ⟨H1, hdiff1, hdec1, hker1⟩ := rank_one_step H (Nat.pos_of_ne_zero hd)
        obtain ⟨H', hdiff2, hdec2, hker2⟩ := rank_multi_step t H1
        refine ⟨H', ?_, ?_, ?_⟩
        · have htri := rank_sub_le_add H H1 H'
          omega
        · omega
        · omega

lemma factor_rank_le {K : Type} [Field K] {r s : ℕ}
    (M : Matrix (Fin r) (Fin r) K) (hM : Matrix.rank M ≤ s) :
    ∃ (B : (Fin s → K) →ₗ[K] (Fin r → K)) (C : (Fin r → K) →ₗ[K] (Fin s → K)),
      B.comp C = M.mulVecLin := by
  let R := LinearMap.range M.mulVecLin
  let d := Module.finrank K R
  have hd : d ≤ s := hM
  let e : R ≃ₗ[K] (Fin d → K) := (Module.finBasis K R).equivFun
  let emb : (Fin d → K) →ₗ[K] (Fin s → K) :=
    { toFun := fun v j => if hj : j.val < d then v ⟨j.val, hj⟩ else 0
      map_add' := fun u v => by ext j; dsimp; split_ifs <;> simp
      map_smul' := fun c u => by ext j; dsimp; split_ifs <;> simp }
  let proj : (Fin s → K) →ₗ[K] (Fin d → K) :=
    { toFun := fun v i => v ⟨i.val, lt_of_lt_of_le i.isLt hd⟩
      map_add' := fun u v => by ext i; rfl
      map_smul' := fun c u => by ext i; rfl }
  have hpe : proj.comp emb = LinearMap.id := by
    ext v i
    simp [proj, emb]
  let C : (Fin r → K) →ₗ[K] (Fin s → K) := emb.comp (e.toLinearMap.comp M.mulVecLin.rangeRestrict)
  let B : (Fin s → K) →ₗ[K] (Fin r → K) := R.subtype.comp (e.symm.toLinearMap.comp proj)
  refine ⟨B, C, ?_⟩
  apply LinearMap.ext
  intro x
  ext i
  have h1 : proj (emb (e (M.mulVecLin.rangeRestrict x))) = e (M.mulVecLin.rangeRestrict x) :=
    LinearMap.congr_fun hpe (e (M.mulVecLin.rangeRestrict x))
  show (R.subtype (e.symm (proj (emb (e (M.mulVecLin.rangeRestrict x)))))) i = M.mulVecLin x i
  rw [h1, LinearEquiv.symm_apply_apply]
  rfl

lemma exists_chain {K : Type} [Field K] {r s : ℕ} :
    ∀ (k : ℕ) (H : Matrix (Fin r) (Fin r) K),
      r ≤ Matrix.rank H + s →
      Matrix.rank (1 - H) ≤ (k + 1) * s →
      ∃ (L : Fin (k + 2) → ((Fin r ⊕ Fin s → K) →ₗ[K] (Fin r → K)))
        (R : Fin (k + 2) → ((Fin r → K) →ₗ[K] (Fin r ⊕ Fin s → K))),
        (∀ i : Fin (k + 2), (L i).comp (R i) = LinearMap.id) ∧
        (∀ j : Fin (k + 1), (L j.castSucc).comp (R j.succ) = LinearMap.id) ∧
        (L (Fin.last (k + 1))).comp (R 0) = H.mulVecLin ∧
        L (Fin.last (k + 1)) =
          { toFun := fun w i => w (Sum.inl i)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl } ∧
        R (Fin.last (k + 1)) =
          { toFun := fun x p => Sum.elim x 0 p
            map_add' := fun _ _ => by ext p; cases p <;> simp
            map_smul' := fun _ _ => by ext p; cases p <;> simp }
  | 0, H, _, h1H => by
      have h1H' : Matrix.rank (1 - H) ≤ s := by simpa using h1H
      obtain ⟨B, C, hBC⟩ := factor_rank_le (1 - H) h1H'
      let fst : (Fin r ⊕ Fin s → K) →ₗ[K] (Fin r → K) :=
        { toFun := fun w i => w (Sum.inl i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let snd : (Fin r ⊕ Fin s → K) →ₗ[K] (Fin s → K) :=
        { toFun := fun w i => w (Sum.inr i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let inl : (Fin r → K) →ₗ[K] (Fin r ⊕ Fin s → K) :=
        { toFun := fun x p => Sum.elim x 0 p
          map_add' := fun _ _ => by ext p; cases p <;> simp
          map_smul' := fun _ _ => by ext p; cases p <;> simp }
      let R0 : (Fin r → K) →ₗ[K] (Fin r ⊕ Fin s → K) :=
        { toFun := fun x p => Sum.elim (H.mulVecLin x) (C x) p
          map_add' := fun _ _ => by ext p; cases p <;> simp [map_add]
          map_smul' := fun _ _ => by ext p; cases p <;> simp [map_smul] }
      let L0 : (Fin r ⊕ Fin s → K) →ₗ[K] (Fin r → K) := fst + B.comp snd
      let L : Fin 2 → ((Fin r ⊕ Fin s → K) →ₗ[K] (Fin r → K)) := fun i =>
        if i = 0 then L0 else fst
      let R : Fin 2 → ((Fin r → K) →ₗ[K] (Fin r ⊕ Fin s → K)) := fun i =>
        if i = 0 then R0 else inl
      refine ⟨L, R, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · apply LinearMap.ext
          intro x
          ext a
          have h1 : B (C x) = (1 - H).mulVecLin x := LinearMap.congr_fun hBC x
          have h2 : H.mulVecLin x + (1 - H).mulVecLin x = x := by
            have : H.mulVecLin x + (1 - H).mulVecLin x = (H + (1 - H)).mulVecLin x := by
              rw [Matrix.mulVecLin_add, LinearMap.add_apply]
            rw [this]
            simp
          change H.mulVecLin x a + B (C x) a = x a
          rw [h1]
          exact congrFun h2 a
        · apply LinearMap.ext
          intro x
          ext a
          simp [L, R, fst, inl]
      · intro j
        fin_cases j
        apply LinearMap.ext
        intro x
        ext a
        show (L 0 (R 1 x)) a = x a
        simp only [L, R, L0, fst, snd, inl, ↓reduceIte, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
        have h0 : B 0 = 0 := map_zero B
        change x a + B 0 a = x a
        rw [h0]
        simp
      · apply LinearMap.ext
        intro x
        ext a
        simp [L, R, fst, R0]
      · rfl
      · rfl
  | k + 1, H, hH, h1H => by
      obtain ⟨H', hdiff, hdec, hker'⟩ := rank_multi_step s H
      have hkerH : Module.finrank K (LinearMap.ker H.mulVecLin) ≤ s := by
        have hrn := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
        rw [Module.finrank_fin_fun] at hrn
        have : Module.finrank K (LinearMap.range H.mulVecLin) = Matrix.rank H := rfl
        omega
      have hker'0 : Module.finrank K (LinearMap.ker H'.mulVecLin) = 0 := by omega
      have hker'_bot : LinearMap.ker H'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker'0
      have hinj' : Function.Injective H'.mulVecLin := LinearMap.ker_eq_bot.mp hker'_bot
      have hsurj' : Function.Surjective H'.mulVecLin := by
        have hrn := LinearMap.finrank_range_add_finrank_ker H'.mulVecLin
        rw [hker'0, add_zero] at hrn
        have htop : LinearMap.range H'.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq hrn
        intro y
        have hy : y ∈ LinearMap.range H'.mulVecLin := by rw [htop]; trivial
        exact hy
      let eH' : (Fin r → K) ≃ₗ[K] (Fin r → K) :=
        LinearEquiv.ofBijective H'.mulVecLin ⟨hinj', hsurj'⟩
      have hrH' : r ≤ Matrix.rank H' + s := by
        have hrn := LinearMap.finrank_range_add_finrank_ker H'.mulVecLin
        rw [hker'0, add_zero, Module.finrank_fin_fun] at hrn
        have : Module.finrank K (LinearMap.range H'.mulVecLin) = Matrix.rank H' := rfl
        omega
      have h1H' : Matrix.rank (1 - H') ≤ (k + 1) * s := by
        have : (k + 1 + 1) * s - s = (k + 1) * s := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
        omega
      obtain ⟨L', R', hdiag', hsup', hclose', hLlast', hRlast'⟩ := exists_chain k H' hrH' h1H'
      obtain ⟨B, W, hBW⟩ := factor_rank_le (H - H') hdiff
      let fst : (Fin r ⊕ Fin s → K) →ₗ[K] (Fin r → K) :=
        { toFun := fun w i => w (Sum.inl i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let snd : (Fin r ⊕ Fin s → K) →ₗ[K] (Fin s → K) :=
        { toFun := fun w i => w (Sum.inr i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let inl : (Fin r → K) →ₗ[K] (Fin r ⊕ Fin s → K) :=
        { toFun := fun x p => Sum.elim x 0 p
          map_add' := fun _ _ => by ext p; cases p <;> simp
          map_smul' := fun _ _ => by ext p; cases p <;> simp }
      let Y0 : (Fin r → K) →ₗ[K] (Fin s → K) := snd.comp (R' 0)
      let Z : (Fin r → K) →ₗ[K] (Fin s → K) := (Y0 - W).comp eH'.symm.toLinearMap
      let Φ : (Fin r ⊕ Fin s → K) ≃ₗ[K] (Fin r ⊕ Fin s → K) :=
        { toFun := fun w p =>
            Sum.elim (fst w + B (snd w - Z (fst w))) (snd w - Z (fst w)) p
          map_add' := fun u v => by
            ext p
            cases p with
            | inl i =>
              change (fst (u + v) + B (snd (u + v) - Z (fst (u + v)))) i =
                (fst u + B (snd u - Z (fst u))) i + (fst v + B (snd v - Z (fst v))) i
              have h1 : snd (u + v) - Z (fst (u + v)) =
                  (snd u - Z (fst u)) + (snd v - Z (fst v)) := by
                rw [map_add, map_add, map_add]
                abel
              rw [h1, map_add, map_add]
              simp only [Pi.add_apply]
              abel
            | inr j =>
              change (snd (u + v) - Z (fst (u + v))) j =
                (snd u - Z (fst u)) j + (snd v - Z (fst v)) j
              rw [map_add, map_add, map_add]
              simp only [Pi.sub_apply, Pi.add_apply]
              abel
          map_smul' := fun c u => by
            ext p
            cases p with
            | inl i =>
              change (fst (c • u) + B (snd (c • u) - Z (fst (c • u)))) i =
                c * (fst u + B (snd u - Z (fst u))) i
              rw [map_smul, map_smul, map_smul, ← smul_sub, map_smul]
              simp [mul_add]
            | inr j =>
              change (snd (c • u) - Z (fst (c • u))) j = c * (snd u - Z (fst u)) j
              rw [map_smul, map_smul, map_smul]
              simp [mul_sub]
          invFun := fun w p =>
            Sum.elim (fst w - B (snd w)) (snd w + Z (fst w - B (snd w))) p
          left_inv := fun w => by
            ext p
            cases p with
            | inl i =>
              change (fst w + B (snd w - Z (fst w)) - B (snd w - Z (fst w))) i = w (Sum.inl i)
              simp [fst]
            | inr j =>
              change (snd w - Z (fst w) +
                Z (fst w + B (snd w - Z (fst w)) - B (snd w - Z (fst w)))) j = w (Sum.inr j)
              simp [snd]
          right_inv := fun w => by
            ext p
            cases p with
            | inl i =>
              change (fst w - B (snd w) +
                B (snd w + Z (fst w - B (snd w)) - Z (fst w - B (snd w)))) i = w (Sum.inl i)
              simp [fst]
            | inr j =>
              change (snd w + Z (fst w - B (snd w)) - Z (fst w - B (snd w))) j = w (Sum.inr j)
              simp [snd] }
      let L : Fin (k + 3) → ((Fin r ⊕ Fin s → K) →ₗ[K] (Fin r → K)) :=
        Fin.lastCases fst (fun i => (L' i).comp Φ.symm.toLinearMap)
      let R : Fin (k + 3) → ((Fin r → K) →ₗ[K] (Fin r ⊕ Fin s → K)) :=
        Fin.lastCases inl (fun i => Φ.toLinearMap.comp (R' i))
      have hΦinv : Φ.symm.toLinearMap.comp Φ.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro w
        exact Φ.left_inv w
      refine ⟨L, R, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · apply LinearMap.ext
          intro x
          ext a
          simp [L, R, fst, inl]
        · intro j
          simp only [L, R, Fin.lastCases_castSucc]
          calc
            ((L' j).comp Φ.symm.toLinearMap).comp (Φ.toLinearMap.comp (R' j))
                = (L' j).comp ((Φ.symm.toLinearMap.comp Φ.toLinearMap).comp (R' j)) := by
                  simp only [LinearMap.comp_assoc]
            _ = (L' j).comp (R' j) := by rw [hΦinv, LinearMap.id_comp]
            _ = LinearMap.id := hdiag' j
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simp only [L, R, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last]
          rw [hLlast']
          apply LinearMap.ext
          intro x
          ext a
          show (fst (Φ.symm (inl x))) a = x a
          change (fst (inl x) - B (snd (inl x))) a = x a
          have h0 : snd (inl x) = 0 := rfl
          rw [h0, map_zero, sub_zero]
          rfl
        · intro i
          have h1 : i.castSucc.succ = i.succ.castSucc := rfl
          rw [h1]
          simp only [L, R, Fin.lastCases_castSucc]
          calc
            ((L' i.castSucc).comp Φ.symm.toLinearMap).comp (Φ.toLinearMap.comp (R' i.succ))
                = (L' i.castSucc).comp ((Φ.symm.toLinearMap.comp Φ.toLinearMap).comp (R' i.succ)) := by
                  simp only [LinearMap.comp_assoc]
            _ = (L' i.castSucc).comp (R' i.succ) := by rw [hΦinv, LinearMap.id_comp]
            _ = LinearMap.id := hsup' i
      · have h0 : (0 : Fin (k + 3)) = (0 : Fin (k + 2)).castSucc := rfl
        rw [h0]
        simp only [L, R, Fin.lastCases_last, Fin.lastCases_castSucc]
        apply LinearMap.ext
        intro x
        ext a
        have hfst0 : fst (R' 0 x) = H'.mulVecLin x := by
          have := LinearMap.congr_fun hclose' x
          rw [hLlast'] at this
          exact this
        have hZ : Z (H'.mulVecLin x) = Y0 x - W x := by
          simp only [Z, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
          have : eH'.symm (H'.mulVecLin x) = x := eH'.symm_apply_apply x
          rw [this]
          rfl
        have hBWx : B (W x) = (H - H').mulVecLin x := LinearMap.congr_fun hBW x
        show (fst (Φ (R' 0 x))) a = H.mulVecLin x a
        change (fst (R' 0 x) + B (snd (R' 0 x) - Z (fst (R' 0 x)))) a = H.mulVecLin x a
        rw [hfst0, hZ]
        have hsub : snd (R' 0 x) - (Y0 x - W x) = W x := by
          change Y0 x - (Y0 x - W x) = W x
          abel
        rw [hsub, hBWx]
        have hsum : H'.mulVecLin x + (H - H').mulVecLin x = H.mulVecLin x := by
          have : H'.mulVecLin x + (H - H').mulVecLin x = (H' + (H - H')).mulVecLin x := by
            rw [Matrix.mulVecLin_add, LinearMap.add_apply]
          rw [this, add_sub_cancel]
        exact congrFun hsum a
      · simp [L, fst]
      · simp [R, inl]

lemma finrank_range_sum_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {ι : Type}
    (s : Finset ι) (f : ι → (V →ₗ[K] W)) :
    Module.finrank K (LinearMap.range (∑ i ∈ s, f i)) ≤
      ∑ i ∈ s, Module.finrank K (LinearMap.range (f i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, LinearMap.range_zero, finrank_bot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hle : LinearMap.range (f a + ∑ i ∈ s, f i) ≤
        LinearMap.range (f a) ⊔ LinearMap.range (∑ i ∈ s, f i) := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (f a)) (LinearMap.range (∑ i ∈ s, f i))
    omega

lemma telescope_fin {M : Type} [AddCommGroup M] :
    ∀ (k : ℕ) (f : Fin (k + 2) → M),
      f (Fin.last (k + 1)) - f 0 = ∑ j : Fin (k + 1), (f j.succ - f j.castSucc)
  | 0, f => by simp
  | k + 1, f => by
      rw [Fin.sum_univ_castSucc]
      have ih := telescope_fin k (fun i => f i.castSucc)
      have h0 : (0 : Fin (k + 3)) = (0 : Fin (k + 2)).castSucc := rfl
      have hcast : ∀ j : Fin (k + 1), j.castSucc.succ = j.succ.castSucc := fun _ => rfl
      simp only [hcast]
      rw [← ih, Fin.succ_last, h0]
      abel

end PEqualNP.Outside.L_lib_1002_aux

theorem PEqualNP.Outside.L_lib_1002 : ∀ (K : Type) [Field K] (k r s : ℕ) (H : Matrix (Fin r) (Fin r) K),
  let I := Fin (k+2)
  let last : I := Fin.last (k+1)
  (∃ A : Matrix (I × Fin r) (I × Fin r) K,
    Matrix.rank A ≤ r+s ∧
    (∀ i : I, A.submatrix (fun a => (i,a)) (fun b => (i,b)) = 1) ∧
    (∀ j : Fin (k+1), A.submatrix (fun a => (j.castSucc,a)) (fun b => (j.succ,b)) = 1) ∧
    A.submatrix (fun a => (last,a)) (fun b => (0,b)) = H) ↔
  r ≤ Matrix.rank H + s ∧ Matrix.rank (1-H) ≤ (k+1)*s := by
  intro K _ k r s H
  dsimp only
  let I := Fin (k + 2)
  let last : I := Fin.last (k + 1)
  constructor
  · rintro ⟨A, hrankA, hdiag, hsup, hclose⟩
    let E := LinearMap.range A.mulVecLin
    let f : ((I × Fin r) → K) →ₗ[K] E := A.mulVecLin.rangeRestrict
    let g : E →ₗ[K] ((I × Fin r) → K) := E.subtype
    let ι : I → (Fin r → K) →ₗ[K] ((I × Fin r) → K) := fun i =>
      { toFun := fun v p => if p.1 = i then v p.2 else 0
        map_add' := fun u v => by ext p; dsimp; split_ifs <;> simp
        map_smul' := fun c u => by ext p; dsimp; split_ifs <;> simp }
    let π : I → ((I × Fin r) → K) →ₗ[K] (Fin r → K) := fun i =>
      { toFun := fun w a => w (i, a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let R : I → (Fin r → K) →ₗ[K] E := fun i => f.comp (ι i)
    let L : I → E →ₗ[K] (Fin r → K) := fun i => (π i).comp g
    have hblock : ∀ i j : I,
        (L i).comp (R j) = (A.submatrix (fun a => (i, a)) (fun b => (j, b))).mulVecLin := by
      intro i j
      ext v a
      simp only [L, R, LinearMap.comp_apply, π, g, f, ι, LinearMap.coe_mk, AddHom.coe_mk,
        Submodule.coe_subtype, LinearMap.codRestrict_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
        dotProduct, Matrix.submatrix_apply]
      rw [Fintype.sum_prod_type]
      simp
    have hLdiag : ∀ i : I, (L i).comp (R i) = LinearMap.id := by
      intro i
      rw [hblock i i, hdiag i, Matrix.mulVecLin_one]
    have hLsup : ∀ j : Fin (k + 1), (L j.castSucc).comp (R j.succ) = LinearMap.id := by
      intro j
      rw [hblock j.castSucc j.succ, hsup j, Matrix.mulVecLin_one]
    have hLclose : (L last).comp (R 0) = H.mulVecLin := by
      rw [hblock last 0, hclose]
    have hkerL_le : ∀ i : I, Module.finrank K (LinearMap.ker (L i)) ≤ s := by
      intro i
      have hsurj : Function.Surjective (L i) :=
        Function.RightInverse.surjective (fun v => by simpa using LinearMap.congr_fun (hLdiag i) v)
      have hrn := LinearMap.finrank_range_add_finrank_ker (L i)
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrn
      have hE : Module.finrank K E ≤ r + s := hrankA
      omega
    constructor
    · have hinj0 : Function.Injective (R 0) :=
        Function.LeftInverse.injective (fun v => by simpa using LinearMap.congr_fun (hLdiag 0) v)
      have hker_le : Module.finrank K (LinearMap.ker H.mulVecLin) ≤
          Module.finrank K (LinearMap.ker (L last)) := by
        let φ : LinearMap.ker H.mulVecLin →ₗ[K] LinearMap.ker (L last) :=
          { toFun := fun x => ⟨R 0 x.1, by
              rw [LinearMap.mem_ker]
              have h1 := LinearMap.congr_fun hLclose x.1
              have hx : H.mulVecLin x.1 = 0 := x.2
              rw [hx] at h1
              exact h1⟩
            map_add' := fun _ _ => by ext; simp [map_add]
            map_smul' := fun _ _ => by ext; simp [map_smul] }
        have hinjφ : Function.Injective φ := by
          intro x y hxy
          apply Subtype.ext
          exact hinj0 (congrArg Subtype.val hxy)
        exact LinearMap.finrank_le_finrank_of_injective hinjφ
      have hrn := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
      rw [Module.finrank_fin_fun] at hrn
      have h1 := hkerL_le last
      have hrH : Module.finrank K (LinearMap.range H.mulVecLin) = Matrix.rank H := rfl
      omega
    · have h1H_eq : (1 - H).mulVecLin =
          ∑ j : Fin (k + 1), (L last).comp (R j.succ - R j.castSucc) := by
        have htel := PEqualNP.Outside.L_lib_1002_aux.telescope_fin k R
        calc
          (1 - H).mulVecLin = LinearMap.id - H.mulVecLin := by
            rw [PEqualNP.Outside.L_lib_1002_aux.mulVecLin_sub, Matrix.mulVecLin_one]
          _ = (L last).comp (R last) - (L last).comp (R 0) := by
            rw [hLdiag last, hLclose]
          _ = (L last).comp (R last - R 0) := by rw [LinearMap.comp_sub]
          _ = (L last).comp (∑ j : Fin (k + 1), (R j.succ - R j.castSucc)) := by rw [htel]
          _ = ∑ j : Fin (k + 1), (L last).comp (R j.succ - R j.castSucc) := by
            apply LinearMap.ext
            intro x
            ext a
            simp [map_sum]
      have hterm : ∀ j : Fin (k + 1),
          Module.finrank K (LinearMap.range ((L last).comp (R j.succ - R j.castSucc))) ≤ s := by
        intro j
        have hle_ker : LinearMap.range (R j.succ - R j.castSucc) ≤
            LinearMap.ker (L j.castSucc) := by
          rintro _ ⟨x, rfl⟩
          rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub]
          have h1 := LinearMap.congr_fun (hLsup j) x
          have h2 := LinearMap.congr_fun (hLdiag j.castSucc) x
          simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
          rw [h1, h2, sub_self]
        have h1 : Module.finrank K (LinearMap.range ((L last).comp (R j.succ - R j.castSucc))) ≤
            Module.finrank K (LinearMap.range (R j.succ - R j.castSucc)) := by
          rw [LinearMap.range_comp]
          exact Submodule.finrank_map_le (L last) _
        exact le_trans h1 (le_trans (Submodule.finrank_mono hle_ker) (hkerL_le j.castSucc))
      have hsum := PEqualNP.Outside.L_lib_1002_aux.finrank_range_sum_le
        (Finset.univ : Finset (Fin (k + 1))) (fun j => (L last).comp (R j.succ - R j.castSucc))
      have hbd : ∑ j : Fin (k + 1),
          Module.finrank K (LinearMap.range ((L last).comp (R j.succ - R j.castSucc))) ≤
            (k + 1) * s := by
        calc
          ∑ j : Fin (k + 1),
              Module.finrank K (LinearMap.range ((L last).comp (R j.succ - R j.castSucc)))
              ≤ ∑ _j : Fin (k + 1), s := Finset.sum_le_sum (fun j _ => hterm j)
          _ = (k + 1) * s := by simp
      have hr1H : Matrix.rank (1 - H) = Module.finrank K (LinearMap.range (1 - H).mulVecLin) := rfl
      rw [hr1H, h1H_eq]
      exact le_trans hsum hbd
  · rintro ⟨hrH, h1H⟩
    obtain ⟨L, R, hdiag, hsup, hclose, _, _⟩ :=
      PEqualNP.Outside.L_lib_1002_aux.exists_chain k H hrH h1H
    let Rbig : ((I × Fin r) → K) →ₗ[K] (Fin r ⊕ Fin s → K) :=
      { toFun := fun v => ∑ j : I, R j (fun b => v (j, b))
        map_add' := fun u v => by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _
          exact map_add (R j) (fun b => u (j, b)) (fun b => v (j, b))
        map_smul' := fun c u => by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          exact map_smul (R j) c (fun b => u (j, b)) }
    let Lbig : (Fin r ⊕ Fin s → K) →ₗ[K] ((I × Fin r) → K) :=
      { toFun := fun w p => L p.1 w p.2
        map_add' := fun u v => by ext p; simp [map_add]
        map_smul' := fun c u => by ext p; simp [map_smul] }
    let T : ((I × Fin r) → K) →ₗ[K] ((I × Fin r) → K) := Lbig.comp Rbig
    let A : Matrix (I × Fin r) (I × Fin r) K := LinearMap.toMatrix' T
    have hA_lin : A.mulVecLin = T := Matrix.toLin'_toMatrix' T
    have hblock : ∀ i j : I,
        A.submatrix (fun a => (i, a)) (fun b => (j, b)) = LinearMap.toMatrix' ((L i).comp (R j)) := by
      intro i j
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      ext a
      have h1 : (A.submatrix (fun a => (i, a)) (fun b => (j, b))).mulVecLin v a =
          T (fun p => if p.1 = j then v p.2 else 0) (i, a) := by
        rw [← hA_lin]
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
        rw [Fintype.sum_prod_type]
        simp
      have h2 : T (fun p => if p.1 = j then v p.2 else 0) (i, a) = L i (R j v) a := by
        simp only [T, Lbig, Rbig, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
        have hsum : ∑ t : I, R t (fun b => if t = j then v b else 0) = R j v := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro t _ htj
            simp only [htj, ↓reduceIte]
            exact map_zero (R t)
          · intro hj
            exact absurd (Finset.mem_univ j) hj
        rw [hsum]
      simpa [Matrix.toLin'_toMatrix'] using h1.trans h2
    refine ⟨A, ?_, ?_, ?_, ?_⟩
    · have h1 : Matrix.rank A = Module.finrank K (LinearMap.range T) := by
        change Module.finrank K (LinearMap.range A.mulVecLin) = _
        rw [hA_lin]
      rw [h1, LinearMap.range_comp]
      have h2 := Submodule.finrank_map_le Lbig (LinearMap.range Rbig)
      have h3 : Module.finrank K (LinearMap.range Rbig) ≤ Module.finrank K (Fin r ⊕ Fin s → K) :=
        Submodule.finrank_le _
      have h4 : Module.finrank K (Fin r ⊕ Fin s → K) = r + s := by
        simp
      omega
    · intro i
      rw [hblock i i, hdiag i]
      exact LinearMap.toMatrix'_id
    · intro j
      rw [hblock j.castSucc j.succ, hsup j]
      exact LinearMap.toMatrix'_id
    · rw [hblock last 0, hclose]
      exact LinearMap.toMatrix'_toLin' H

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_440_aux

open scoped BigOperators

abbrev F2 := ZMod 2

lemma zmod2_add_self (a : F2) : a + a = 0 := by
  revert a; decide

lemma zmod2_add_eq_zero_iff (a b : F2) : a + b = 0 ↔ a = b := by
  revert a b; decide

lemma zmod2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma zmod2_ne_zero_iff (a : F2) : a ≠ 0 ↔ a = 1 := by
  revert a; decide

def chi (a : F2) : ℤ := if a = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl
lemma chi_one : chi 1 = -1 := rfl

lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  revert a b; decide

lemma sum_chi_lin {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    (φ : V →ₗ[F2] F2) :
    (∑ v : V, chi (φ v)) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  by_cases hφ : φ = 0
  · subst hφ
    simp [chi_zero]
  · rw [if_neg hφ]
    have hex : ∃ v₀ : V, φ v₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext fun v => h v)
    obtain ⟨v₀, hv₀⟩ := hex
    have hv1 : φ v₀ = 1 := (zmod2_ne_zero_iff _).mp hv₀
    have hshift : (∑ v : V, chi (φ v)) = ∑ v : V, chi (φ (v + v₀)) :=
      (Fintype.sum_equiv (Equiv.addRight v₀) (fun v => chi (φ (v + v₀)))
        (fun v => chi (φ v)) (fun _ => rfl)).symm
    have hneg : (∑ v : V, chi (φ (v + v₀))) = -(∑ v : V, chi (φ v)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_add, hv1, chi_add, chi_one]
      ring
    linarith

lemma card_filter_eq_chi {α : Type*} [Fintype α] (q : α → F2) (b : F2) :
    2 * ((Finset.univ.filter fun u : α => q u = b).card : ℤ) - (Fintype.card α : ℤ) =
      chi b * ∑ u : α, chi (q u) := by
  have hterm : ∀ u : α, (if q u = b then (2 : ℤ) else 0) - 1 = chi b * chi (q u) := by
    intro u
    have h1 := zmod2_eq_zero_or_one b
    have h2 := zmod2_eq_zero_or_one (q u)
    rcases h1 with rfl | rfl <;> rcases h2 with hq | hq <;> simp [hq, chi]
  have hsum : ∑ u : α, ((if q u = b then (2 : ℤ) else 0) - 1) =
      ∑ u : α, chi b * chi (q u) :=
    Finset.sum_congr rfl fun u _ => hterm u
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hcard : (∑ u : α, if q u = b then (2 : ℤ) else 0) =
      2 * ((Finset.univ.filter fun u : α => q u = b).card : ℤ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  exact hsum

lemma card_filter_le_abs_chi {α : Type*} [Fintype α] (q : α → F2) (b : F2) :
    2 * ((Finset.univ.filter fun u : α => q u = b).card : ℤ) ≤
      (Fintype.card α : ℤ) + |∑ u : α, chi (q u)| := by
  have h := card_filter_eq_chi q b
  rcases zmod2_eq_zero_or_one b with rfl | rfl
  · rw [chi_zero, one_mul] at h
    have := le_abs_self (∑ u : α, chi (q u))
    linarith
  · rw [chi_one] at h
    have := neg_le_abs (∑ u : α, chi (q u))
    linarith

lemma exists_card_filter_eq_abs_chi {α : Type*} [Fintype α] (q : α → F2) :
    ∃ b : F2, 2 * ((Finset.univ.filter fun u : α => q u = b).card : ℤ) =
      (Fintype.card α : ℤ) + |∑ u : α, chi (q u)| := by
  by_cases h : 0 ≤ ∑ u : α, chi (q u)
  · refine ⟨0, ?_⟩
    have hc := card_filter_eq_chi q 0
    rw [chi_zero, one_mul] at hc
    rw [abs_of_nonneg h]
    linarith
  · refine ⟨1, ?_⟩
    have hc := card_filter_eq_chi q 1
    rw [chi_one] at hc
    rw [abs_of_neg (not_le.mp h)]
    linarith

lemma card_subspace {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (W : Submodule F2 V) :
    Nat.card W = 2 ^ Module.finrank F2 W := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Nat.card_zmod]

lemma fintype_card_subspace {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (W : Submodule F2 V) [Fintype W] :
    Fintype.card W = 2 ^ Module.finrank F2 W := by
  rw [← Nat.card_eq_fintype_card, card_subspace]

lemma nat_log2_two_pow (k : ℕ) : (2 ^ k).log2 = k := by
  rw [Nat.log2_eq_iff (by positivity)]
  constructor
  · exact le_rfl
  · exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)

lemma finrank_dual_F2 {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V] :
    Module.finrank F2 (V →ₗ[F2] F2) = Module.finrank F2 V := by
  rw [Module.finrank_linearMap, Module.finrank_self, mul_one]

set_option maxHeartbeats 800000 in
lemma pairing_range_eq_ann
    {A B : Type*} [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A]
    [AddCommGroup B] [Module F2 B] [FiniteDimensional F2 B]
    (Φ : A →ₗ[F2] (B →ₗ[F2] F2)) :
    let G : Submodule F2 B :=
      { carrier := {b : B | ∀ a : A, Φ a b = 0}, add_mem' := fun ha hb a => by rw [map_add, ha a, hb a, add_zero]
        zero_mem' := fun a => map_zero _
        smul_mem' := fun c _ hb a => by rw [map_smul, hb a, smul_zero] }
    let ann : Submodule F2 (B →ₗ[F2] F2) :=
      { carrier := {φ : B →ₗ[F2] F2 | ∀ b ∈ G, φ b = 0}, add_mem' := fun h1 h2 b hb => by simp [h1 b hb, h2 b hb]
        zero_mem' := fun _ _ => rfl
        smul_mem' := fun c _ h1 b hb => by simp [h1 b hb] }
    LinearMap.range Φ = ann ∧
      Module.finrank F2 (LinearMap.range Φ) + Module.finrank F2 G = Module.finrank F2 B := by
  intro G ann
  have hG : G = (LinearMap.range Φ).dualCoannihilator := by
    ext b
    rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro h φ hφ
      obtain ⟨a, rfl⟩ := hφ
      exact h a
    · intro h a
      exact h (Φ a) ⟨a, rfl⟩
  have ha : ann = G.dualAnnihilator := by
    ext φ
    exact (Submodule.mem_dualAnnihilator (W := G) φ).symm
  rw [ha, hG, Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact ⟨rfl, Subspace.finrank_add_finrank_dualCoannihilator_eq _⟩

open Classical in
lemma card_preimage_linearMap
    {A W : Type*} [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A] [Fintype A]
    [AddCommGroup W] [Module F2 W] [FiniteDimensional F2 W]
    (Φ : A →ₗ[F2] W) (y : W) (hy : y ∈ LinearMap.range Φ) :
    (Finset.univ.filter fun a : A => Φ a = y).card * 2 ^ Module.finrank F2 (LinearMap.range Φ) =
      Fintype.card A := by
  obtain ⟨a₀, rfl⟩ := hy
  have hbij : (Finset.univ.filter fun a : A => Φ a = Φ a₀).card =
      Fintype.card (LinearMap.ker Φ) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun x => ⟨x.1 - a₀, by
          have hx : Φ x.1 = Φ a₀ := (Finset.mem_filter.mp x.2).2
          rw [LinearMap.mem_ker, map_sub, hx, sub_self]⟩
        invFun := fun k => ⟨k.1 + a₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [map_add, k.2, zero_add]⟩⟩
        left_inv := fun x => by ext; simp
        right_inv := fun k => by ext; simp }
  rw [hbij, fintype_card_subspace, ← pow_add, add_comm,
    LinearMap.finrank_range_add_finrank_ker, ← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := F2), Nat.card_zmod]

def radIn {V : Type*} [AddCommGroup V] [Module F2 V]
    (ω : V →ₗ[F2] (V →ₗ[F2] F2)) (U : Submodule F2 V) : Submodule F2 V :=
  { carrier := {u ∈ U | ∀ v ∈ U, ω u v = 0}, add_mem' := fun {u₁ u₂} h₁ h₂ =>
      ⟨U.add_mem h₁.1 h₂.1, fun v hv => by rw [map_add, LinearMap.add_apply, h₁.2 v hv, h₂.2 v hv, add_zero]⟩
    zero_mem' := ⟨U.zero_mem, fun v _ => by simp⟩
    smul_mem' := fun c {u} hu =>
      ⟨U.smul_mem c hu.1, fun v hv => by rw [map_smul, LinearMap.smul_apply, hu.2 v hv, smul_zero]⟩ }

lemma radIn_le {V : Type*} [AddCommGroup V] [Module F2 V]
    (ω : V →ₗ[F2] (V →ₗ[F2] F2)) (U : Submodule F2 V) :
    radIn ω U ≤ U := fun _ h => h.1

lemma exists_symplectic_subspace
    {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (ω : V →ₗ[F2] (V →ₗ[F2] F2))
    (hself : ∀ v : V, ω v v = 0)
    (hsymm : ∀ u v : V, ω u v = ω v u) :
    ∀ (d : ℕ) (U : Submodule F2 V), Module.finrank F2 U = d →
      ∃ m : ℕ,
        Module.finrank F2 U = Module.finrank F2 (radIn ω U) + 2 * m ∧
        ∀ (k : ℕ), k ≤ m → ∀ (R' : Submodule F2 V), R' ≤ radIn ω U →
          ∃ K : Submodule F2 V,
            K ≤ U ∧
            K ⊓ radIn ω U = R' ∧
            radIn ω K = R' ∧
            Module.finrank F2 K = Module.finrank F2 R' + 2 * (m - k) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro U hUd
    by_cases hrad : radIn ω U = U
    · refine ⟨0, by rw [hrad, mul_zero, add_zero], ?_⟩
      intro k hk R' hR'
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      refine ⟨R', le_trans hR' (radIn_le ω U), inf_of_le_left hR', ?_, by simp⟩
      ext u
      constructor
      · intro hu; exact hu.1
      · intro hu
        refine ⟨hu, fun v hv => ?_⟩
        exact (hR' hu).2 v (radIn_le ω U (hR' hv))
    · have hex : ∃ x ∈ U, ∃ y ∈ U, ω x y = 1 := by
        by_contra h
        push Not at h
        apply hrad
        apply le_antisymm (radIn_le ω U)
        intro x hx
        refine ⟨hx, fun y hy => ?_⟩
        by_contra hne
        exact h x hx y hy ((zmod2_ne_zero_iff _).mp hne)
      obtain ⟨x, hxU, y, hyU, hxy⟩ := hex
      have hyx : ω y x = 1 := by rw [hsymm, hxy]
      let P : Submodule F2 V := Submodule.span F2 ({x, y} : Set V)
      let H : Submodule F2 V := U ⊓ LinearMap.ker (ω x) ⊓ LinearMap.ker (ω y)
      have hPU : P ≤ U := by
        rw [Submodule.span_le]
        intro z hz
        rcases hz with rfl | rfl <;> assumption
      have hHU : H ≤ U := le_trans inf_le_left inf_le_left
      have hmemP : ∀ z ∈ P, ∃ a b : F2, z = a • x + b • y := by
        intro z hz
        rw [Submodule.mem_span_pair] at hz
        obtain ⟨a, b, hab⟩ := hz
        exact ⟨a, b, hab.symm⟩
      have hinf_HP : H ⊓ P = ⊥ := by
        rw [eq_bot_iff]
        intro z ⟨hzH, hzP⟩
        obtain ⟨a, b, rfl⟩ := hmemP z hzP
        have hzx : ω x (a • x + b • y) = 0 := hzH.1.2
        have hzy : ω y (a • x + b • y) = 0 := hzH.2
        rw [map_add, map_smul, map_smul, hself x, hxy, smul_zero, zero_add, smul_eq_mul, mul_one] at hzx
        rw [map_add, map_smul, map_smul, hyx, hself y, smul_zero, add_zero, smul_eq_mul, mul_one] at hzy
        simp [hzx, hzy]
      have hsup_HP : H ⊔ P = U := by
        apply le_antisymm (sup_le hHU hPU)
        intro u hu
        let v := u + (ω y u) • x + (ω x u) • y
        have hvU : v ∈ U := U.add_mem (U.add_mem hu (U.smul_mem _ hxU)) (U.smul_mem _ hyU)
        have hvx : ω x v = 0 := by
          dsimp only [v]
          rw [map_add, map_add, map_smul, map_smul, hself x, hxy, smul_zero, add_zero,
            smul_eq_mul, mul_one, zmod2_add_self]
        have hvy : ω y v = 0 := by
          dsimp only [v]
          rw [map_add, map_add, map_smul, map_smul, hyx, hself y, smul_zero, add_zero,
            smul_eq_mul, mul_one, zmod2_add_self]
        have hvH : v ∈ H := ⟨⟨hvU, hvx⟩, hvy⟩
        have hremP : (ω y u) • x + (ω x u) • y ∈ P :=
          P.add_mem (P.smul_mem _ (Submodule.subset_span (Set.mem_insert x {y})))
            (P.smul_mem _ (Submodule.subset_span (Set.mem_insert_of_mem x rfl)))
        have hu_eq : u = v + ((ω y u) • x + (ω x u) • y) := by
          dsimp only [v]
          have h1 : (ω y u) • x + (ω y u) • x = 0 := by
            rw [← add_smul, zmod2_add_self, zero_smul]
          have h2 : (ω x u) • y + (ω x u) • y = 0 := by
            rw [← add_smul, zmod2_add_self, zero_smul]
          calc u = u + ((ω y u) • x + (ω y u) • x) + ((ω x u) • y + (ω x u) • y) := by
                rw [h1, h2, add_zero, add_zero]
            _ = (u + (ω y u) • x + (ω x u) • y) + ((ω y u) • x + (ω x u) • y) := by abel
        rw [hu_eq]
        exact Submodule.add_mem_sup hvH hremP
      have hfinP : Module.finrank F2 P = 2 := by
        have hli : LinearIndependent F2 ![x, y] := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          have h01 : g 0 • x + g 1 • y = 0 := by
            simpa [Fin.sum_univ_two] using hg
          have h1 := congrArg (ω x) h01
          rw [map_add, map_smul, map_smul, map_zero, hself x, hxy, smul_zero, zero_add,
            smul_eq_mul, mul_one] at h1
          have h2 := congrArg (ω y) h01
          rw [map_add, map_smul, map_smul, map_zero, hyx, hself y, smul_zero, add_zero,
            smul_eq_mul, mul_one] at h2
          intro i
          fin_cases i <;> assumption
        have hsp : Submodule.span F2 (Set.range ![x, y]) = P := by
          congr 1
          ext z
          simp [Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm, or_comm]
        rw [← hsp, finrank_span_eq_card hli, Fintype.card_fin]
      have hfinU : Module.finrank F2 U = Module.finrank F2 H + 2 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq H P
        rw [hsup_HP, hinf_HP, finrank_bot, add_zero, hfinP] at h
        exact h
      have hradH : radIn ω H = radIn ω U := by
        ext u
        constructor
        · intro ⟨huH, hu_perp⟩
          refine ⟨hHU huH, fun v hvU => ?_⟩
          have hvsup : v ∈ H ⊔ P := by rw [hsup_HP]; exact hvU
          obtain ⟨h', hh', p', hp', rfl⟩ := Submodule.mem_sup.mp hvsup
          obtain ⟨a, b, rfl⟩ := hmemP p' hp'
          rw [map_add, map_add, map_smul, map_smul, hu_perp h' hh', hsymm u x, huH.1.2,
            hsymm u y, huH.2]
          simp
        · intro ⟨huU, hu_perp⟩
          refine ⟨⟨⟨huU, ?_⟩, ?_⟩, fun v hvH => hu_perp v (hHU hvH)⟩
          · change ω x u = 0; rw [hsymm]; exact hu_perp x hxU
          · change ω y u = 0; rw [hsymm]; exact hu_perp y hyU
      have hHlt : Module.finrank F2 H < d := by omega
      obtain ⟨m', hm', hbuild⟩ := ih (Module.finrank F2 H) hHlt H rfl
      rw [hradH] at hm' hbuild
      refine ⟨m' + 1, by omega, ?_⟩
      intro k hk R' hR'
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨K', hK'H, hK'inf, hK'rad, hK'fin⟩ := hbuild 0 (Nat.zero_le m') R' hR'
        let K : Submodule F2 V := K' ⊔ P
        have hK'P : K' ⊓ P = ⊥ := by
          rw [eq_bot_iff]
          intro z ⟨hzK', hzP⟩
          have : z ∈ H ⊓ P := ⟨hK'H hzK', hzP⟩
          rw [hinf_HP] at this
          exact this
        have hKfin : Module.finrank F2 K = Module.finrank F2 R' + 2 * (m' + 1 - 0) := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq K' P
          rw [hK'P, finrank_bot, add_zero, hfinP, hK'fin] at h
          omega
        have hKinf : K ⊓ radIn ω U = R' := by
          apply le_antisymm
          · intro z ⟨hzK, hzR⟩
            obtain ⟨k', hk', p', hp', rfl⟩ := Submodule.mem_sup.mp hzK
            obtain ⟨a, b, rfl⟩ := hmemP p' hp'
            have hzx : ω x (k' + (a • x + b • y)) = 0 := by
              rw [hsymm]; exact hzR.2 x hxU
            have hzy : ω y (k' + (a • x + b • y)) = 0 := by
              rw [hsymm]; exact hzR.2 y hyU
            rw [map_add, (hK'H hk').1.2, zero_add, map_add, map_smul, map_smul,
              hself x, hxy, smul_zero, zero_add, smul_eq_mul, mul_one] at hzx
            rw [map_add, (hK'H hk').2, zero_add, map_add, map_smul, map_smul,
              hyx, hself y, smul_zero, add_zero, smul_eq_mul, mul_one] at hzy
            simp only [hzx, hzy, zero_smul, add_zero] at hzR ⊢
            have : k' ∈ K' ⊓ radIn ω U := ⟨hk', hzR⟩
            rwa [hK'inf] at this
          · refine le_inf (le_trans (by rw [← hK'inf]; exact inf_le_left) le_sup_left) hR'
        have hKrad : radIn ω K = R' := by
          apply le_antisymm
          · intro z ⟨hzK, hz_perp⟩
            obtain ⟨k', hk', p', hp', rfl⟩ := Submodule.mem_sup.mp hzK
            obtain ⟨a, b, rfl⟩ := hmemP p' hp'
            have hxK : x ∈ K := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert x {y}))
            have hyK : y ∈ K := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem x rfl))
            have hzx : ω x (k' + (a • x + b • y)) = 0 := by rw [hsymm]; exact hz_perp x hxK
            have hzy : ω y (k' + (a • x + b • y)) = 0 := by rw [hsymm]; exact hz_perp y hyK
            rw [map_add, (hK'H hk').1.2, zero_add, map_add, map_smul, map_smul,
              hself x, hxy, smul_zero, zero_add, smul_eq_mul, mul_one] at hzx
            rw [map_add, (hK'H hk').2, zero_add, map_add, map_smul, map_smul,
              hyx, hself y, smul_zero, add_zero, smul_eq_mul, mul_one] at hzy
            simp only [hzx, hzy, zero_smul, add_zero] at hz_perp ⊢
            have : k' ∈ radIn ω K' := ⟨hk', fun v hv => hz_perp v (Submodule.mem_sup_left hv)⟩
            rwa [hK'rad] at this
          · intro z hzR'
            have hzK : z ∈ K := by
              rw [← hKinf] at hzR'
              exact hzR'.1
            refine ⟨hzK, fun v hvK => ?_⟩
            exact (hR' hzR').2 v ((sup_le (le_trans hK'H hHU) hPU) hvK)
        exact ⟨K, sup_le (le_trans hK'H hHU) hPU, hKinf, hKrad, hKfin⟩
      · have hk1 : k - 1 ≤ m' := by omega
        obtain ⟨K, hKH, hKinf, hKrad, hKfin⟩ := hbuild (k - 1) hk1 R' hR'
        have hsub : m' + 1 - k = m' - (k - 1) := by omega
        rw [← hsub] at hKfin
        exact ⟨K, le_trans hKH hHU, hKinf, hKrad, hKfin⟩

lemma exists_linearMap_ker_eq
    {X : Type*} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X]
    (S : Submodule F2 X) (K : Submodule F2 X) (hKS : K ≤ S)
    (e : ℕ) (hcod : Module.finrank F2 S - Module.finrank F2 K ≤ e) :
    ∃ L : X →ₗ[F2] (Fin e → F2),
      LinearMap.ker (L.comp S.subtype) = K.comap S.subtype := by
  let K' : Submodule F2 S := K.comap S.subtype
  have hfinK' : Module.finrank F2 K' = Module.finrank F2 K := by
    let eK : K' ≃ₗ[F2] K :=
      { toFun := fun u => ⟨u.1.1, u.2⟩
        invFun := fun u => ⟨⟨u.1, hKS u.2⟩, u.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact eK.finrank_eq
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K'
  have hfinC : Module.finrank F2 C ≤ e := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq K' C
    rw [hC.sup_eq_top, hC.inf_eq_bot, finrank_top, finrank_bot, add_zero, hfinK'] at h
    omega
  let eKC := Submodule.prodEquivOfIsCompl K' C hC
  let bC : C ≃ₗ[F2] (Fin (Module.finrank F2 C) → F2) :=
    (Module.finBasis F2 C).equivFun
  let emb : (Fin (Module.finrank F2 C) → F2) →ₗ[F2] (Fin e → F2) :=
    { toFun := fun v i => if hi : i.1 < Module.finrank F2 C then v ⟨i.1, hi⟩ else 0
      map_add' := fun v w => by ext i; by_cases hi : i.1 < Module.finrank F2 C <;> simp [hi]
      map_smul' := fun c v => by ext i; by_cases hi : i.1 < Module.finrank F2 C <;> simp [hi] }
  have hemb_inj : Function.Injective emb := by
    intro v w hvw
    ext j
    have hj : j.1 < e := lt_of_lt_of_le j.2 hfinC
    have := congrFun hvw ⟨j.1, hj⟩
    simpa [emb, j.2] using this
  let LS : S →ₗ[F2] (Fin e → F2) :=
    emb.comp (bC.toLinearMap.comp ((LinearMap.snd F2 K' C).comp eKC.symm.toLinearMap))
  have hkerLS : LinearMap.ker LS = K' := by
    ext u
    simp only [LinearMap.mem_ker, LS, LinearMap.comp_apply, LinearEquiv.coe_coe]
    constructor
    · intro h
      have h1 : bC ((eKC.symm u).2) = 0 := hemb_inj (by simpa using h)
      have h2 : (eKC.symm u).2 = 0 := bC.injective (by simpa using h1)
      have hp : eKC.symm u = ((eKC.symm u).1, 0) := Prod.ext rfl h2
      have hu : u = eKC ((eKC.symm u).1, 0) := by
        rw [← hp, eKC.apply_symm_apply]
      have hu' : u = ((eKC.symm u).1 : S) := by
        exact hu.trans (show ((eKC.symm u).1 : S) + 0 = ((eKC.symm u).1 : S) from add_zero _)
      rw [hu']
      exact (eKC.symm u).1.2
    · intro hu
      have he : eKC (⟨u, hu⟩, 0) = u := by change u + 0 = u; exact add_zero _
      have hsym : eKC.symm u = (⟨u, hu⟩, 0) := by
        apply eKC.injective
        rw [eKC.apply_symm_apply, he]
      rw [hsym]
      simp
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl S
  let eSD := Submodule.prodEquivOfIsCompl S D hD
  let L : X →ₗ[F2] (Fin e → F2) :=
    LS.comp ((LinearMap.fst F2 S D).comp eSD.symm.toLinearMap)
  refine ⟨L, ?_⟩
  have hcomp : L.comp S.subtype = LS := by
    refine LinearMap.ext fun u => ?_
    change LS ((eSD.symm (u : X)).1) = LS u
    have he : eSD (u, 0) = (u : X) := by change (u : X) + 0 = (u : X); exact add_zero _
    have hsym : eSD.symm (u : X) = (u, 0) := by
      apply eSD.injective
      rw [eSD.apply_symm_apply, he]
    rw [hsym]
  rw [hcomp, hkerLS]

open Classical in
lemma sum_abs_chi_coset
    {X : Type*} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X] [Fintype X]
    (q : X → F2) (ω : X →ₗ[F2] (X →ₗ[F2] F2))
    (hself : ∀ v : X, ω v v = 0)
    (hsymm : ∀ u v : X, ω u v = ω v u)
    (hq : ∀ z u v : X, q (z + u + v) + q (z + u) + q (z + v) + q z = ω u v)
    (S K : Submodule F2 X) (hKS : K ≤ S) :
    let R : Submodule F2 X := radIn ω S
    let K0 : Submodule F2 X := radIn ω K
    let s := Module.finrank F2 K - Module.finrank F2 (K ⊓ R : Submodule F2 X)
    let s0 := Module.finrank F2 K0 - Module.finrank F2 (K ⊓ R : Submodule F2 X)
    Even (s + s0) ∧
    (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))|) * (2 ^ ((s + s0) / 2) : ℤ) =
      if (∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0)
      then (Fintype.card S : ℤ) * (Fintype.card K : ℤ)
      else 0 := by
  intro R K0 s s0
  obtain ⟨mK, hmK, _⟩ := exists_symplectic_subspace ω hself hsymm (Module.finrank F2 K) K rfl
  change Module.finrank F2 K = Module.finrank F2 K0 + 2 * mK at hmK
  have hKR_le_K0 : (K ⊓ R : Submodule F2 X) ≤ K0 := by
    intro u ⟨huK, huR⟩
    exact ⟨huK, fun v hvK => huR.2 v (hKS hvK)⟩
  have hfin_KR_le_K0 : Module.finrank F2 (K ⊓ R : Submodule F2 X) ≤ Module.finrank F2 K0 :=
    Submodule.finrank_mono hKR_le_K0
  have hfin_K0_le_K : Module.finrank F2 K0 ≤ Module.finrank F2 K :=
    Submodule.finrank_mono (radIn_le ω K)
  have heven : Even (s + s0) := by
    refine ⟨mK + s0, ?_⟩
    dsimp only [s, s0]
    omega
  refine ⟨heven, ?_⟩
  have hhalf_eq : Module.finrank F2 K + Module.finrank F2 K0 =
      2 * (Module.finrank F2 K0 + mK) := by omega
  have hsq_term : ∀ z : S,
      (∑ u : K, chi (q (z.1 + u.1))) ^ 2 =
        (Fintype.card K : ℤ) *
          if (∀ w ∈ K0, q (z.1 + w) + q z.1 = 0) then (Fintype.card K0 : ℤ) else 0 := by
    intro z
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hreindex : (∑ u : K, ∑ v : K, chi (q (z.1 + u.1)) * chi (q (z.1 + v.1))) =
        ∑ w : K, chi (q (z.1 + w.1) + q z.1) * ∑ u : K, chi (ω u.1 w.1) := by
      have h1 : (∑ u : K, ∑ v : K, chi (q (z.1 + u.1)) * chi (q (z.1 + v.1))) =
          ∑ u : K, ∑ w : K, chi (q (z.1 + u.1)) * chi (q (z.1 + (u + w).1)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        exact (Fintype.sum_equiv (Equiv.addLeft u)
          (fun w => chi (q (z.1 + u.1)) * chi (q (z.1 + (u + w).1)))
          (fun v => chi (q (z.1 + u.1)) * chi (q (z.1 + v.1))) (fun _ => rfl)).symm
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← chi_add, ← chi_add]
      congr 1
      have hpol := hq z.1 u.1 w.1
      have huw : (u + w).1 = u.1 + w.1 := rfl
      rw [huw, ← add_assoc]
      rw [← zmod2_add_eq_zero_iff]
      rw [← hpol]
      have : (q (z.1 + u.1) + q (z.1 + u.1 + w.1)) +
          ((q (z.1 + w.1) + q z.1) + (q (z.1 + u.1 + w.1) + q (z.1 + u.1) + q (z.1 + w.1) + q z.1)) =
          (q (z.1 + u.1) + q (z.1 + u.1)) + (q (z.1 + u.1 + w.1) + q (z.1 + u.1 + w.1)) +
          (q (z.1 + w.1) + q (z.1 + w.1)) + (q z.1 + q z.1) := by abel
      rw [this]
      simp only [zmod2_add_self, add_zero]
    rw [hreindex]
    have hinner : ∀ w : K,
        (∑ u : K, chi (ω u.1 w.1)) = if w.1 ∈ K0 then (Fintype.card K : ℤ) else 0 := by
      intro w
      let φw : K →ₗ[F2] F2 :=
        { toFun := fun u => ω u.1 w.1
          map_add' := fun u1 u2 => by
            change ω (u1.1 + u2.1) w.1 = ω u1.1 w.1 + ω u2.1 w.1
            rw [map_add, LinearMap.add_apply]
          map_smul' := fun c u => by
            change ω (c • u.1) w.1 = c • ω u.1 w.1
            rw [map_smul, LinearMap.smul_apply] }
      have hs := sum_chi_lin φw
      have hiff : φw = 0 ↔ w.1 ∈ K0 := by
        constructor
        · intro h0
          refine ⟨w.2, fun v hv => ?_⟩
          rw [hsymm]
          exact LinearMap.congr_fun h0 ⟨v, hv⟩
        · intro hw
          refine LinearMap.ext fun u => ?_
          change ω u.1 w.1 = 0
          rw [hsymm]
          exact hw.2 u.1 u.2
      change (∑ u : K, chi (φw u)) = _
      rw [hs]
      by_cases hw : w.1 ∈ K0
      · rw [if_pos (hiff.mpr hw), if_pos hw]
      · rw [if_neg (mt hiff.mp hw), if_neg hw]
    have hstep : (∑ w : K, chi (q (z.1 + w.1) + q z.1) * ∑ u : K, chi (ω u.1 w.1)) =
        (Fintype.card K : ℤ) * ∑ w : K0, chi (q (z.1 + w.1) + q z.1) := by
      simp_rw [hinner]
      have hfilt : (∑ w : K, chi (q (z.1 + w.1) + q z.1) *
            if w.1 ∈ K0 then (Fintype.card K : ℤ) else 0) =
          (Fintype.card K : ℤ) *
            ∑ w ∈ Finset.univ.filter (fun w : K => w.1 ∈ K0), chi (q (z.1 + w.1) + q z.1) := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun w _ => ?_
        split_ifs <;> ring
      rw [hfilt]
      congr 1
      rw [← Finset.sum_coe_sort]
      refine Fintype.sum_equiv
        { toFun := fun w => ⟨w.1.1, (Finset.mem_filter.mp w.2).2⟩
          invFun := fun w => ⟨⟨w.1, radIn_le ω K w.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } _ _ (fun _ => rfl)
    rw [hstep]
    congr 1
    let lamZ : K0 →ₗ[F2] F2 :=
      { toFun := fun w => q (z.1 + w.1) + q z.1
        map_add' := fun w1 w2 => by
          have hpol := hq z.1 w1.1 w2.1
          have hw0 : ω w1.1 w2.1 = 0 := w1.2.2 w2.1 (radIn_le ω K w2.2)
          rw [hw0] at hpol
          change q (z.1 + (w1.1 + w2.1)) + q z.1 = (q (z.1 + w1.1) + q z.1) + (q (z.1 + w2.1) + q z.1)
          rw [← add_assoc, ← zmod2_add_eq_zero_iff]
          have : (q (z.1 + w1.1 + w2.1) + q z.1) +
              ((q (z.1 + w1.1) + q z.1) + (q (z.1 + w2.1) + q z.1)) =
              (q (z.1 + w1.1 + w2.1) + q (z.1 + w1.1) + q (z.1 + w2.1) + q z.1) + (q z.1 + q z.1) := by abel
          rw [this, hpol, zmod2_add_self, add_zero]
        map_smul' := fun c w => by
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · simp only [zero_smul, ZeroMemClass.coe_zero, add_zero, RingHom.id_apply, zmod2_add_self]
          · simp }
    have hsumLam := sum_chi_lin lamZ
    have hLamIff : lamZ = 0 ↔ ∀ w ∈ K0, q (z.1 + w) + q z.1 = 0 := by
      constructor
      · intro h0 w hw
        exact LinearMap.congr_fun h0 ⟨w, hw⟩
      · intro hall
        exact LinearMap.ext fun w => hall w.1 w.2
    rw [show (∑ w : K0, chi (q (z.1 + w.1) + q z.1)) = ∑ w : K0, chi (lamZ w) from rfl, hsumLam]
    by_cases h0 : ∀ w ∈ K0, q (z.1 + w) + q z.1 = 0
    · rw [if_pos (hLamIff.mpr h0), if_pos h0]
    · rw [if_neg (mt hLamIff.mp h0), if_neg h0]
  have habs_term : ∀ z : S,
      |∑ u : K, chi (q (z.1 + u.1))| =
        if (∀ w ∈ K0, q (z.1 + w) + q z.1 = 0)
        then (2 ^ (Module.finrank F2 K0 + mK) : ℤ)
        else 0 := by
    intro z
    have hsq := hsq_term z
    by_cases h0 : ∀ w ∈ K0, q (z.1 + w) + q z.1 = 0
    · rw [if_pos h0] at hsq ⊢
      rw [fintype_card_subspace K, fintype_card_subspace K0] at hsq
      have hpow : ((2 ^ Module.finrank F2 K : ℕ) : ℤ) * ((2 ^ Module.finrank F2 K0 : ℕ) : ℤ) =
          ((2 ^ (Module.finrank F2 K0 + mK) : ℤ)) ^ 2 := by
        push_cast
        rw [← pow_add, ← pow_mul, hhalf_eq, mul_comm 2]
      rw [hpow] at hsq
      have hsq2 : |∑ u : K, chi (q (z.1 + u.1))| ^ 2 = (2 ^ (Module.finrank F2 K0 + mK) : ℤ) ^ 2 := by
        rw [sq_abs]; exact hsq
      have hnonneg1 : 0 ≤ |∑ u : K, chi (q (z.1 + u.1))| := abs_nonneg _
      have hnonneg2 : (0 : ℤ) ≤ 2 ^ (Module.finrank F2 K0 + mK) := by positivity
      nlinarith
    · rw [if_neg h0, mul_zero] at hsq
      rw [if_neg h0]
      have hzero : (∑ u : K, chi (q (z.1 + u.1))) = 0 := sq_eq_zero_iff.mp hsq
      rw [hzero, abs_zero]
  simp_rw [habs_term]
  have hsum_ite : (∑ z : S, if (∀ w ∈ K0, q (z.1 + w) + q z.1 = 0)
        then (2 ^ (Module.finrank F2 K0 + mK) : ℤ) else 0) =
      ((Finset.univ.filter fun z : S => ∀ w ∈ K0, q (z.1 + w) + q z.1 = 0).card : ℤ) *
        (2 ^ (Module.finrank F2 K0 + mK) : ℤ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hsum_ite]
  have hshift_q : ∀ (z : S) (w : K0), q (z.1 + w.1) + q z.1 = (q w.1 + q 0) + ω z.1 w.1 := by
    intro z w
    have hpol := hq 0 z.1 w.1
    simp only [zero_add] at hpol
    rw [← zmod2_add_eq_zero_iff, ← hpol]
    have : (q (z.1 + w.1) + q z.1) + ((q w.1 + q 0) + (q (z.1 + w.1) + q z.1 + q w.1 + q 0)) =
        (q (z.1 + w.1) + q (z.1 + w.1)) + (q z.1 + q z.1) + (q w.1 + q w.1) + (q 0 + q 0) := by abel
    rw [this]
    simp only [zmod2_add_self, add_zero]
  by_cases hmask : ∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0
  · rw [if_pos hmask]
    let Θ : S →ₗ[F2] (K0 →ₗ[F2] F2) :=
      { toFun := fun z =>
          { toFun := fun w => ω z.1 w.1
            map_add' := fun w1 w2 => by
              change ω z.1 (w1.1 + w2.1) = ω z.1 w1.1 + ω z.1 w2.1
              rw [map_add]
            map_smul' := fun c w => by
              change ω z.1 (c • w.1) = c • ω z.1 w.1
              rw [map_smul] }
        map_add' := fun z1 z2 => LinearMap.ext fun w => by
          change ω (z1.1 + z2.1) w.1 = ω z1.1 w.1 + ω z2.1 w.1
          rw [map_add, LinearMap.add_apply]
        map_smul' := fun c z => LinearMap.ext fun w => by
          change ω (c • z.1) w.1 = c • ω z.1 w.1
          rw [map_smul, LinearMap.smul_apply] }
    let lam0 : K0 →ₗ[F2] F2 :=
      { toFun := fun w => q w.1 + q 0
        map_add' := fun w1 w2 => by
          have hpol := hq 0 w1.1 w2.1
          simp only [zero_add] at hpol
          have hw0 : ω w1.1 w2.1 = 0 := w1.2.2 w2.1 (radIn_le ω K w2.2)
          rw [hw0] at hpol
          change q (w1.1 + w2.1) + q 0 = (q w1.1 + q 0) + (q w2.1 + q 0)
          rw [← zmod2_add_eq_zero_iff]
          have : (q (w1.1 + w2.1) + q 0) + ((q w1.1 + q 0) + (q w2.1 + q 0)) =
              (q (w1.1 + w2.1) + q w1.1 + q w2.1 + q 0) + (q 0 + q 0) := by abel
          rw [this, hpol, zmod2_add_self, add_zero]
        map_smul' := fun c w => by
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · simp only [zero_smul, ZeroMemClass.coe_zero, RingHom.id_apply, zmod2_add_self]
          · simp }
    obtain ⟨hrange_eq, hfin_range⟩ := pairing_range_eq_ann Θ
    let GΘ : Submodule F2 K0 :=
      { carrier := {w : K0 | ∀ z : S, Θ z w = 0}, add_mem' := fun ha hb z => by rw [map_add, ha z, hb z, add_zero]
        zero_mem' := fun z => map_zero _
        smul_mem' := fun c _ hb z => by rw [map_smul, hb z, smul_zero] }
    have hGΘ_iso : Module.finrank F2 GΘ = Module.finrank F2 (K ⊓ R : Submodule F2 X) := by
      let eG : GΘ ≃ₗ[F2] (K ⊓ R : Submodule F2 X) :=
        { toFun := fun w => ⟨w.1.1, radIn_le ω K w.1.2, hKS (radIn_le ω K w.1.2), fun v hv => by
            rw [hsymm]; exact w.2 ⟨v, hv⟩⟩
          invFun := fun w => ⟨⟨w.1, hKR_le_K0 w.2⟩, fun z => by
            change ω z.1 w.1 = 0
            rw [hsymm]; exact w.2.2.2 z.1 z.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact eG.finrank_eq
    have hlam0_mem : lam0 ∈ LinearMap.range Θ := by
      rw [hrange_eq]
      intro w hw
      have hwKR : w.1 ∈ (K ⊓ R : Submodule F2 X) := ⟨radIn_le ω K w.2, hKS (radIn_le ω K w.2), fun v hv => by
        rw [hsymm]; exact hw ⟨v, hv⟩⟩
      exact hmask w.1 hwKR
    have hfin_Θ : Module.finrank F2 (LinearMap.range Θ) = s0 := by
      dsimp only [s0]
      change Module.finrank F2 (LinearMap.range Θ) + Module.finrank F2 GΘ = Module.finrank F2 K0 at hfin_range
      omega
    have hfilt_eq : (Finset.univ.filter fun z : S => ∀ w ∈ K0, q (z.1 + w) + q z.1 = 0) =
        (Finset.univ.filter fun z : S => Θ z = lam0) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.ext_iff, Subtype.forall]
      constructor
      · intro hz w hw
        have h1 := hshift_q z ⟨w, hw⟩
        have h2 := hz w hw
        rw [h2] at h1
        change ω z.1 w = q w + q 0
        exact ((zmod2_add_eq_zero_iff _ _).mp h1.symm).symm
      · intro hz w hw
        rw [hshift_q z ⟨w, hw⟩]
        have h1 : ω z.1 w = q w + q 0 := hz w hw
        rw [h1, zmod2_add_self]
    rw [hfilt_eq]
    have hpre := card_preimage_linearMap Θ lam0 hlam0_mem
    rw [hfin_Θ] at hpre
    have hpreZ : ((Finset.univ.filter fun z : S => Θ z = lam0).card : ℤ) * (2 ^ s0 : ℤ) =
        (Fintype.card S : ℤ) := by
      have hn : (Finset.univ.filter fun z : S => Θ z = lam0).card * 2 ^ s0 = Fintype.card S := by
        convert hpre using 2
        apply congrArg Finset.card
        ext z
        simp
      exact_mod_cast hn
    have hexp_eq : (Module.finrank F2 K0 + mK) + (s + s0) / 2 = s0 + Module.finrank F2 K := by
      dsimp only [s, s0]
      omega
    calc ((Finset.univ.filter fun z : S => Θ z = lam0).card : ℤ) *
            (2 ^ (Module.finrank F2 K0 + mK) : ℤ) * (2 ^ ((s + s0) / 2) : ℤ)
        = ((Finset.univ.filter fun z : S => Θ z = lam0).card : ℤ) *
            (2 ^ ((Module.finrank F2 K0 + mK) + (s + s0) / 2) : ℤ) := by
              rw [mul_assoc, ← pow_add]
      _ = ((Finset.univ.filter fun z : S => Θ z = lam0).card : ℤ) *
            ((2 ^ s0 : ℤ) * (2 ^ Module.finrank F2 K : ℤ)) := by
              rw [hexp_eq, pow_add]
      _ = (((Finset.univ.filter fun z : S => Θ z = lam0).card : ℤ) * (2 ^ s0 : ℤ)) *
            (Fintype.card K : ℤ) := by
              rw [fintype_card_subspace K]; push_cast; ring
      _ = (Fintype.card S : ℤ) * (Fintype.card K : ℤ) := by rw [hpreZ]
  · rw [if_neg hmask]
    push Not at hmask
    obtain ⟨w₀, hw₀, hqne⟩ := hmask
    have hempty : (Finset.univ.filter fun z : S => ∀ w ∈ K0, q (z.1 + w) + q z.1 = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z _
      push Not
      refine ⟨w₀, hKR_le_K0 hw₀, ?_⟩
      rw [hshift_q z ⟨w₀, hKR_le_K0 hw₀⟩]
      have hω0 : ω z.1 w₀ = 0 := by rw [hsymm]; exact hw₀.2.2 z.1 z.2
      rw [hω0, add_zero]
      exact hqne
    rw [hempty, Finset.card_empty]
    simp

open Classical in
lemma single_coset_upper
    {X : Type*} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X] [Fintype X]
    (f : X → F2) (ω : X →ₗ[F2] (X →ₗ[F2] F2))
    (hself : ∀ v : X, ω v v = 0)
    (hsymm : ∀ u v : X, ω u v = ω v u)
    (hf : ∀ p u v : X, f (p + u + v) + f (p + u) + f (p + v) + f p = ω u v)
    (S : Submodule F2 X) (e : ℕ) (p : X)
    (L : X →ₗ[F2] (Fin e → F2)) (out : (Fin e → F2) → F2) :
    let R : Submodule F2 X := radIn ω S
    let m := (Module.finrank F2 S - Module.finrank F2 R) / 2
    let U := (1 : ℚ) / 2 ^ (m - e / 2)
    let M := if e = 0 then (0 : ℚ) else 1 / 2 ^ (m - (e - 1) / 2)
    let target := if (∀ w ∈ R, f (p + w) + f p = 0) then U else M
    ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ) ≤
      (Fintype.card S : ℚ) * (1 + target) / 2 := by
  intro R m U M target
  let q : X → F2 := fun u => f (p + u)
  have hq : ∀ z u v : X, q (z + u + v) + q (z + u) + q (z + v) + q z = ω u v := by
    intro z u v
    dsimp only [q]
    have h1 : p + (z + u + v) = (p + z) + u + v := by abel
    have h2 : p + (z + u) = (p + z) + u := by abel
    have h3 : p + (z + v) = (p + z) + v := by abel
    rw [h1, h2, h3]
    exact hf (p + z) u v
  let LS : S →ₗ[F2] (Fin e → F2) := L.comp S.subtype
  let K : Submodule F2 X := S ⊓ LinearMap.ker L
  have hKS : K ≤ S := inf_le_left
  have hcod : Module.finrank F2 S - Module.finrank F2 K ≤ e := by
    have hker : Module.finrank F2 (LinearMap.ker LS) = Module.finrank F2 K := by
      let eK : LinearMap.ker LS ≃ₗ[F2] K :=
        { toFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
          invFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact eK.finrank_eq
    have hrk := LinearMap.finrank_range_add_finrank_ker LS
    have hle : Module.finrank F2 (LinearMap.range LS) ≤ e := by
      calc Module.finrank F2 (LinearMap.range LS)
          ≤ Module.finrank F2 (Fin e → F2) := Submodule.finrank_le _
        _ = e := Module.finrank_fin_fun F2
    omega
  have hdouble : (Fintype.card K : ℤ) *
        (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℤ)) ≤
      (Fintype.card K : ℤ) * (Fintype.card S : ℤ) +
        ∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| := by
    have hcnt : (Fintype.card K : ℤ) *
          ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℤ) =
        ∑ z : S, ((Finset.univ.filter fun u : K =>
            q (z.1 + u.1) = out (L (p + z.1))).card : ℤ) := by
      have hnat : Fintype.card K *
            (Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card =
          ∑ z : S, (Finset.univ.filter fun u : K =>
            q (z.1 + u.1) = out (L (p + z.1))).card := by
        have hLshift : ∀ (z : S) (u : K), L (p + (z.1 + u.1)) = L (p + z.1) := by
          intro z u
          rw [show p + (z.1 + u.1) = (p + z.1) + u.1 by abel, map_add, u.2.2, add_zero]
        calc Fintype.card K *
              (Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card
            = ∑ _u : K, ∑ w : S, if out (L (p + w.1)) = f (p + w.1) then 1 else 0 := by
                rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.card_filter]
          _ = ∑ u : K, ∑ z : S, if out (L (p + (z.1 + u.1))) = f (p + (z.1 + u.1)) then 1 else 0 := by
                refine Finset.sum_congr rfl fun u _ => ?_
                let uS : S := ⟨u.1, hKS u.2⟩
                exact (Fintype.sum_equiv (Equiv.addRight uS)
                  (fun z => if out (L (p + (z.1 + u.1))) = f (p + (z.1 + u.1)) then 1 else 0)
                  (fun w => if out (L (p + w.1)) = f (p + w.1) then 1 else 0) (fun _ => rfl)).symm
          _ = ∑ z : S, ∑ u : K, if q (z.1 + u.1) = out (L (p + z.1)) then 1 else 0 := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => ?_
                rw [hLshift z u]
                dsimp only [q]
                by_cases h : out (L (p + z.1)) = f (p + (z.1 + u.1))
                · rw [if_pos h, if_pos h.symm]
                · rw [if_neg h, if_neg (Ne.symm h)]
          _ = ∑ z : S, (Finset.univ.filter fun u : K =>
                q (z.1 + u.1) = out (L (p + z.1))).card := by
                refine Finset.sum_congr rfl fun z _ => (Finset.card_filter _ _).symm
      exact_mod_cast hnat
    calc (Fintype.card K : ℤ) *
          (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℤ))
        = ∑ z : S, 2 * ((Finset.univ.filter fun u : K =>
            q (z.1 + u.1) = out (L (p + z.1))).card : ℤ) := by
              rw [← Finset.mul_sum, ← hcnt]; ring
      _ ≤ ∑ z : S, ((Fintype.card K : ℤ) + |∑ u : K, chi (q (z.1 + u.1))|) := by
              refine Finset.sum_le_sum fun z _ => ?_
              exact card_filter_le_abs_chi (fun u : K => q (z.1 + u.1)) (out (L (p + z.1)))
      _ = (Fintype.card K : ℤ) * (Fintype.card S : ℤ) +
            ∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  obtain ⟨mS, hmS, _⟩ := exists_symplectic_subspace ω hself hsymm (Module.finrank F2 S) S rfl
  have hm_eq : m = mS := by dsimp only [m, R]; omega
  obtain ⟨heven, hsum_eq⟩ := sum_abs_chi_coset q ω hself hsymm hq S K hKS
  set K0 : Submodule F2 X := radIn ω K
  set s := Module.finrank F2 K - Module.finrank F2 (K ⊓ R : Submodule F2 X)
  set s0 := Module.finrank F2 K0 - Module.finrank F2 (K ⊓ R : Submodule F2 X)
  have hKpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    rw [fintype_card_subspace K]; positivity
  have hSnonneg : (0 : ℚ) ≤ (Fintype.card S : ℚ) := Nat.cast_nonneg _
  have hbias_le : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) ≤
      (Fintype.card S : ℚ) * (Fintype.card K : ℚ) * target := by
    have hsumQ : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) * (2 ^ ((s + s0) / 2) : ℚ) =
        if (∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0)
        then (Fintype.card S : ℚ) * (Fintype.card K : ℚ)
        else 0 := by
      have hcast : ((∑ z : S, |∑ u : K, chi (q (z.1 + u.1))|) * (2 ^ ((s + s0) / 2) : ℤ) : ℚ) =
          ((if (∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0)
            then (Fintype.card S : ℤ) * (Fintype.card K : ℤ) else 0 : ℤ) : ℚ) := by
        exact_mod_cast hsum_eq
      split_ifs at hcast ⊢ <;> push_cast at hcast ⊢ <;> exact hcast
    have h2pos : (0 : ℚ) < (2 ^ ((s + s0) / 2) : ℚ) := by positivity
    by_cases hKR_ok : ∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0
    · rw [if_pos hKR_ok] at hsumQ
      have hval : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) =
          (Fintype.card S : ℚ) * (Fintype.card K : ℚ) * ((1 : ℚ) / 2 ^ ((s + s0) / 2)) := by
        field_simp [ne_of_gt h2pos]
        linarith
      rw [hval]
      have hsup_le : Module.finrank F2 K + Module.finrank F2 R - Module.finrank F2 (K ⊓ R : Submodule F2 X) ≤
          Module.finrank F2 S := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq K R
        have h2 : Module.finrank F2 (K ⊔ R : Submodule F2 X) ≤ Module.finrank F2 S :=
          Submodule.finrank_mono (sup_le hKS (radIn_le ω S))
        omega
      have hfin_KR_le_R : Module.finrank F2 (K ⊓ R : Submodule F2 X) ≤ Module.finrank F2 R :=
        Submodule.finrank_mono inf_le_right
      have hfin_KR_le_K : Module.finrank F2 (K ⊓ R : Submodule F2 X) ≤ Module.finrank F2 K :=
        Submodule.finrank_mono inf_le_left
      have h2m_le : 2 * m ≤ s + (Module.finrank F2 S - Module.finrank F2 K) -
          (Module.finrank F2 R - Module.finrank F2 (K ⊓ R : Submodule F2 X)) := by
        have hK_le_S : Module.finrank F2 K ≤ Module.finrank F2 S := Submodule.finrank_mono hKS
        dsimp only [s]
        omega
      obtain ⟨t', ht'⟩ := heven
      by_cases hunm : ∀ w ∈ R, f (p + w) + f p = 0
      · have htarget : target = U := by dsimp only [target]; rw [if_pos hunm]
        rw [htarget]
        have hexp : m - e / 2 ≤ (s + s0) / 2 := by omega
        have hpow_le : (2 : ℚ) ^ (m - e / 2) ≤ (2 : ℚ) ^ ((s + s0) / 2) :=
          pow_le_pow_right₀ (by norm_num) hexp
        have hinv_le : (1 : ℚ) / 2 ^ ((s + s0) / 2) ≤ U := by
          dsimp only [U]
          exact one_div_le_one_div_of_le (by positivity) hpow_le
        have hSK_nonneg : 0 ≤ (Fintype.card S : ℚ) * (Fintype.card K : ℚ) := by positivity
        exact mul_le_mul_of_nonneg_left hinv_le hSK_nonneg
      · have htarget : target = M := by dsimp only [target]; rw [if_neg hunm]
        rw [htarget]
        have hKR_lt : Module.finrank F2 (K ⊓ R : Submodule F2 X) < Module.finrank F2 R := by
          by_contra hge
          have heq_fin : Module.finrank F2 (K ⊓ R : Submodule F2 X) = Module.finrank F2 R :=
            le_antisymm hfin_KR_le_R (not_lt.mp hge)
          have hKR_eq : (K ⊓ R : Submodule F2 X) = R :=
            Submodule.eq_of_le_of_finrank_eq inf_le_right heq_fin
          apply hunm
          intro w hw
          have hmem : w ∈ (K ⊓ R : Submodule F2 X) := by rw [hKR_eq]; exact hw
          have := hKR_ok w hmem
          simpa [q] using this
        have he_pos : 0 < e := by
          have hS_le : Module.finrank F2 K + (Module.finrank F2 R - Module.finrank F2 (K ⊓ R : Submodule F2 X)) ≤
              Module.finrank F2 S := by omega
          omega
        have hM_eq : M = (1 : ℚ) / 2 ^ (m - (e - 1) / 2) := by
          dsimp only [M]; rw [if_neg (Nat.ne_of_gt he_pos)]
        rw [hM_eq]
        have hexp : m - (e - 1) / 2 ≤ (s + s0) / 2 := by omega
        have hpow_le : (2 : ℚ) ^ (m - (e - 1) / 2) ≤ (2 : ℚ) ^ ((s + s0) / 2) :=
          pow_le_pow_right₀ (by norm_num) hexp
        have hinv_le : (1 : ℚ) / 2 ^ ((s + s0) / 2) ≤ (1 : ℚ) / 2 ^ (m - (e - 1) / 2) :=
          one_div_le_one_div_of_le (by positivity) hpow_le
        have hSK_nonneg : 0 ≤ (Fintype.card S : ℚ) * (Fintype.card K : ℚ) := by positivity
        exact mul_le_mul_of_nonneg_left hinv_le hSK_nonneg
    · rw [if_neg hKR_ok] at hsumQ
      have hzero : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) = 0 := by
        nlinarith
      rw [hzero]
      have htarget_nonneg : 0 ≤ target := by
        dsimp only [target, U, M]
        split_ifs <;> positivity
      positivity
  have hdoubleQ : (Fintype.card K : ℚ) *
        (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ)) ≤
      (Fintype.card K : ℚ) * (Fintype.card S : ℚ) +
        (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) := by
    exact_mod_cast hdouble
  have hcomb : (Fintype.card K : ℚ) *
        (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ)) ≤
      (Fintype.card K : ℚ) * ((Fintype.card S : ℚ) * (1 + target)) := by
    linarith
  have hdiv : 2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ) ≤
      (Fintype.card S : ℚ) * (1 + target) := by
    nlinarith
  linarith

open Classical in
lemma single_coset_achieve
    {X : Type*} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X] [Fintype X]
    (f : X → F2) (ω : X →ₗ[F2] (X →ₗ[F2] F2))
    (hself : ∀ v : X, ω v v = 0)
    (hsymm : ∀ u v : X, ω u v = ω v u)
    (hf : ∀ p u v : X, f (p + u + v) + f (p + u) + f (p + v) + f p = ω u v)
    (S : Submodule F2 X) (e : ℕ) (p : X) :
    let R : Submodule F2 X := radIn ω S
    let m := (Module.finrank F2 S - Module.finrank F2 R) / 2
    let U := (1 : ℚ) / 2 ^ (m - e / 2)
    let M := if e = 0 then (0 : ℚ) else 1 / 2 ^ (m - (e - 1) / 2)
    let target := if (∀ w ∈ R, f (p + w) + f p = 0) then U else M
    ∃ (L : X →ₗ[F2] (Fin e → F2)) (out : (Fin e → F2) → F2),
      ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ) =
        (Fintype.card S : ℚ) * (1 + target) / 2 := by
  intro R m U M target
  let q : X → F2 := fun u => f (p + u)
  have hq : ∀ z u v : X, q (z + u + v) + q (z + u) + q (z + v) + q z = ω u v := by
    intro z u v
    dsimp only [q]
    have h1 : p + (z + u + v) = (p + z) + u + v := by abel
    have h2 : p + (z + u) = (p + z) + u := by abel
    have h3 : p + (z + v) = (p + z) + v := by abel
    rw [h1, h2, h3]
    exact hf (p + z) u v
  obtain ⟨mS, hmS, hbuild⟩ := exists_symplectic_subspace ω hself hsymm (Module.finrank F2 S) S rfl
  change Module.finrank F2 S = Module.finrank F2 R + 2 * mS at hmS
  have hm_eq : m = mS := by dsimp only [m]; rw [hmS]; omega
  have hfromK : ∀ (K : Submodule F2 X) (hKS : K ≤ S),
      Module.finrank F2 S - Module.finrank F2 K ≤ e →
      ∃ (L : X →ₗ[F2] (Fin e → F2)) (out : (Fin e → F2) → F2),
        (Fintype.card K : ℤ) *
          (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℤ)) =
        (Fintype.card K : ℤ) * (Fintype.card S : ℤ) +
          ∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| := by
    intro K hKS hcod
    obtain ⟨L, hLker⟩ := exists_linearMap_ker_eq S K hKS e hcod
    have hL_eq_K : ∀ u : S, L u.1 = 0 ↔ u.1 ∈ K := by
      intro u
      have := SetLike.ext_iff.mp hLker u
      simpa using this
    let opt : (Fin e → F2) → F2 := fun y =>
      if h : ∃ z : S, L (p + z.1) = y then
        let z0 := Classical.choose h
        Classical.choose (exists_card_filter_eq_abs_chi (fun u : K => q (z0.1 + u.1)))
      else 0
    refine ⟨L, opt, ?_⟩
    have hLshift : ∀ (z : S) (u : K), L (p + (z.1 + u.1)) = L (p + z.1) := by
      intro z u
      rw [show p + (z.1 + u.1) = (p + z.1) + u.1 by abel, map_add,
        (hL_eq_K ⟨u.1, hKS u.2⟩).mpr u.2, add_zero]
    have hcnt : (Fintype.card K : ℤ) *
          ((Finset.univ.filter fun u : S => opt (L (p + u.1)) = f (p + u.1)).card : ℤ) =
        ∑ z : S, ((Finset.univ.filter fun u : K =>
            q (z.1 + u.1) = opt (L (p + z.1))).card : ℤ) := by
      have hnat : Fintype.card K *
            (Finset.univ.filter fun u : S => opt (L (p + u.1)) = f (p + u.1)).card =
          ∑ z : S, (Finset.univ.filter fun u : K =>
            q (z.1 + u.1) = opt (L (p + z.1))).card := by
        calc Fintype.card K *
              (Finset.univ.filter fun u : S => opt (L (p + u.1)) = f (p + u.1)).card
            = ∑ _u : K, ∑ w : S, if opt (L (p + w.1)) = f (p + w.1) then 1 else 0 := by
                rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.card_filter]
          _ = ∑ u : K, ∑ z : S, if opt (L (p + (z.1 + u.1))) = f (p + (z.1 + u.1)) then 1 else 0 := by
                refine Finset.sum_congr rfl fun u _ => ?_
                let uS : S := ⟨u.1, hKS u.2⟩
                exact (Fintype.sum_equiv (Equiv.addRight uS)
                  (fun z => if opt (L (p + (z.1 + u.1))) = f (p + (z.1 + u.1)) then 1 else 0)
                  (fun w => if opt (L (p + w.1)) = f (p + w.1) then 1 else 0) (fun _ => rfl)).symm
          _ = ∑ z : S, ∑ u : K, if q (z.1 + u.1) = opt (L (p + z.1)) then 1 else 0 := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => ?_
                rw [hLshift z u]
                dsimp only [q]
                by_cases h : opt (L (p + z.1)) = f (p + (z.1 + u.1))
                · rw [if_pos h, if_pos h.symm]
                · rw [if_neg h, if_neg (Ne.symm h)]
          _ = ∑ z : S, (Finset.univ.filter fun u : K =>
                q (z.1 + u.1) = opt (L (p + z.1))).card := by
                refine Finset.sum_congr rfl fun z _ => (Finset.card_filter _ _).symm
      exact_mod_cast hnat
    have hopt_z : ∀ z : S,
        2 * ((Finset.univ.filter fun u : K => q (z.1 + u.1) = opt (L (p + z.1))).card : ℤ) =
          (Fintype.card K : ℤ) + |∑ u : K, chi (q (z.1 + u.1))| := by
      intro z
      have hex : ∃ z' : S, L (p + z'.1) = L (p + z.1) := ⟨z, rfl⟩
      set z0 := Classical.choose hex
      have hz0L : L (p + z0.1) = L (p + z.1) := Classical.choose_spec hex
      have hdiffK : z.1 - z0.1 ∈ K := by
        have hsub : L (z.1 - z0.1) = 0 := by
          have : L (p + z.1) - L (p + z0.1) = 0 := by rw [hz0L, sub_self]
          simpa [map_add, map_sub] using this
        exact (hL_eq_K ⟨z.1 - z0.1, S.sub_mem z.2 z0.2⟩).mp hsub
      let dK : K := ⟨z.1 - z0.1, hdiffK⟩
      have hopt_val : opt (L (p + z.1)) =
          Classical.choose (exists_card_filter_eq_abs_chi (fun u : K => q (z0.1 + u.1))) := by
        dsimp only [opt]
        rw [dif_pos hex]
      rw [hopt_val]
      have hspec := Classical.choose_spec
        (exists_card_filter_eq_abs_chi (fun u : K => q (z0.1 + u.1)))
      have hbij_card : (Finset.univ.filter fun u : K => q (z.1 + u.1) =
            Classical.choose (exists_card_filter_eq_abs_chi (fun u : K => q (z0.1 + u.1)))).card =
          (Finset.univ.filter fun u : K => q (z0.1 + u.1) =
            Classical.choose (exists_card_filter_eq_abs_chi (fun u : K => q (z0.1 + u.1)))).card := by
        rw [Finset.card_filter, Finset.card_filter]
        refine Fintype.sum_equiv (Equiv.addLeft dK) _ _ fun u => ?_
        have hpt : z.1 + u.1 = z0.1 + ((Equiv.addLeft dK) u).1 := by
          change z.1 + u.1 = z0.1 + ((z.1 - z0.1) + u.1)
          abel
        rw [hpt]
      have hbij_sum : (∑ u : K, chi (q (z.1 + u.1))) = ∑ u : K, chi (q (z0.1 + u.1)) := by
        refine Fintype.sum_equiv (Equiv.addLeft dK) _ _ fun u => ?_
        have hpt : z.1 + u.1 = z0.1 + ((Equiv.addLeft dK) u).1 := by
          change z.1 + u.1 = z0.1 + ((z.1 - z0.1) + u.1)
          abel
        rw [hpt]
      rw [hbij_card, hbij_sum]
      exact hspec
    calc (Fintype.card K : ℤ) *
          (2 * ((Finset.univ.filter fun u : S => opt (L (p + u.1)) = f (p + u.1)).card : ℤ))
        = ∑ z : S, 2 * ((Finset.univ.filter fun u : K =>
            q (z.1 + u.1) = opt (L (p + z.1))).card : ℤ) := by
              rw [← Finset.mul_sum, ← hcnt]; ring
      _ = ∑ z : S, ((Fintype.card K : ℤ) + |∑ u : K, chi (q (z.1 + u.1))|) :=
              Finset.sum_congr rfl fun z _ => hopt_z z
      _ = (Fintype.card K : ℤ) * (Fintype.card S : ℤ) +
            ∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  by_cases hunm : ∀ w ∈ R, f (p + w) + f p = 0
  · have htarget : target = U := by dsimp only [target]; rw [if_pos hunm]
    rw [htarget]
    let k := min mS (e / 2)
    have hk_le_m : k ≤ mS := min_le_left _ _
    have hk_le_e : k ≤ e / 2 := min_le_right _ _
    obtain ⟨K, hKS, hKinf, hKrad, hKfin⟩ := hbuild k hk_le_m R le_rfl
    have hcod : Module.finrank F2 S - Module.finrank F2 K ≤ e := by omega
    obtain ⟨L, out, heq⟩ := hfromK K hKS hcod
    refine ⟨L, out, ?_⟩
    obtain ⟨_, hsum⟩ := sum_abs_chi_coset q ω hself hsymm hq S K hKS
    have hKR_ok : ∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0 := by
      intro w hw
      have := hunm w hw.2
      simpa [q] using this
    rw [if_pos hKR_ok] at hsum
    have hs0 : Module.finrank F2 (radIn ω K) - Module.finrank F2 (K ⊓ R : Submodule F2 X) = 0 := by
      rw [hKrad, hKinf, Nat.sub_self]
    have hs : Module.finrank F2 K - Module.finrank F2 (K ⊓ R : Submodule F2 X) = 2 * (mS - k) := by
      rw [hKinf, hKfin]; omega
    have hexp : (Module.finrank F2 K - Module.finrank F2 (K ⊓ R : Submodule F2 X) +
        (Module.finrank F2 (radIn ω K) - Module.finrank F2 (K ⊓ R : Submodule F2 X))) / 2 = m - e / 2 := by
      rw [hs, hs0, add_zero, Nat.mul_div_right _ (by norm_num)]
      dsimp only [k]
      omega
    rw [hexp] at hsum
    have hsumQ : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) =
        (Fintype.card S : ℚ) * (Fintype.card K : ℚ) * U := by
      have hcast : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) * (2 ^ (m - e / 2) : ℚ) =
          (Fintype.card S : ℚ) * (Fintype.card K : ℚ) := by
        exact_mod_cast hsum
      dsimp only [U]
      have h2pos : (0 : ℚ) < (2 ^ (m - e / 2) : ℚ) := by positivity
      field_simp [ne_of_gt h2pos]
      linarith
    have heqQ : (Fintype.card K : ℚ) *
          (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ)) =
        (Fintype.card K : ℚ) * (Fintype.card S : ℚ) +
          (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) := by
      exact_mod_cast heq
    rw [hsumQ] at heqQ
    have hKpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
      rw [fintype_card_subspace K]; positivity
    nlinarith
  · have htarget : target = M := by dsimp only [target]; rw [if_neg hunm]
    rw [htarget]
    by_cases he0 : e = 0
    · have hM0 : M = 0 := by dsimp only [M]; rw [if_pos he0]
      rw [hM0]
      obtain ⟨L, out, heq⟩ := hfromK S le_rfl (by omega)
      refine ⟨L, out, ?_⟩
      obtain ⟨_, hsum⟩ := sum_abs_chi_coset q ω hself hsymm hq S S le_rfl
      have hnot : ¬ (∀ w ∈ (S ⊓ R : Submodule F2 X), q w + q 0 = 0) := by
        intro h
        apply hunm
        intro w hw
        have := h w ⟨radIn_le ω S hw, hw⟩
        simpa [q] using this
      rw [if_neg hnot] at hsum
      have hzero : (∑ z : S, |∑ u : S, chi (q (z.1 + u.1))| : ℤ) = 0 := by
        have hpos : (0 : ℤ) < 2 ^ ((Module.finrank F2 S - Module.finrank F2 (S ⊓ R : Submodule F2 X) +
            (Module.finrank F2 (radIn ω S) - Module.finrank F2 (S ⊓ R : Submodule F2 X))) / 2) := by positivity
        nlinarith
      rw [hzero, add_zero] at heq
      have heqQ : (Fintype.card S : ℚ) *
            (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ)) =
          (Fintype.card S : ℚ) * (Fintype.card S : ℚ) := by
        exact_mod_cast heq
      have hSpos : (0 : ℚ) < (Fintype.card S : ℚ) := by
        rw [fintype_card_subspace S]; positivity
      nlinarith
    · have hMval : M = (1 : ℚ) / 2 ^ (m - (e - 1) / 2) := by dsimp only [M]; rw [if_neg he0]
      rw [hMval]
      let ℓ : R →ₗ[F2] F2 :=
        { toFun := fun w => f (p + w.1) + f p
          map_add' := fun w1 w2 => by
            have hpol := hf p w1.1 w2.1
            have hw0 : ω w1.1 w2.1 = 0 := w1.2.2 w2.1 (radIn_le ω S w2.2)
            rw [hw0] at hpol
            change f (p + (w1.1 + w2.1)) + f p = (f (p + w1.1) + f p) + (f (p + w2.1) + f p)
            rw [← add_assoc, ← zmod2_add_eq_zero_iff]
            have : (f (p + w1.1 + w2.1) + f p) +
                ((f (p + w1.1) + f p) + (f (p + w2.1) + f p)) =
                (f (p + w1.1 + w2.1) + f (p + w1.1) + f (p + w2.1) + f p) + (f p + f p) := by abel
            rw [this, hpol, zmod2_add_self, add_zero]
          map_smul' := fun c w => by
            rcases zmod2_eq_zero_or_one c with rfl | rfl
            · simp only [zero_smul, ZeroMemClass.coe_zero, add_zero, RingHom.id_apply, zmod2_add_self]
            · simp }
      have hℓ_ne : ℓ ≠ 0 := by
        intro h0
        apply hunm
        intro w hw
        exact LinearMap.congr_fun h0 ⟨w, hw⟩
      have hℓ_surj : Function.Surjective ℓ := by
        intro y
        have hex : ∃ w : R, ℓ w ≠ 0 := by
          by_contra h; push Not at h; exact hℓ_ne (LinearMap.ext h)
        obtain ⟨w, hw⟩ := hex
        have hw1 : ℓ w = 1 := (zmod2_ne_zero_iff _).mp hw
        rcases zmod2_eq_zero_or_one y with rfl | rfl
        · exact ⟨0, map_zero ℓ⟩
        · exact ⟨w, hw1⟩
      let R' : Submodule F2 X := (LinearMap.ker ℓ).map R.subtype
      have hR'le : R' ≤ R := by
        rintro x ⟨w, _, rfl⟩; exact w.2
      have hfinR' : Module.finrank F2 R' + 1 = Module.finrank F2 R := by
        have h1 : Module.finrank F2 R' = Module.finrank F2 (LinearMap.ker ℓ) :=
          Submodule.finrank_map_subtype_eq R (LinearMap.ker ℓ)
        have h2 := LinearMap.finrank_range_add_finrank_ker ℓ
        rw [LinearMap.range_eq_top.mpr hℓ_surj, finrank_top, Module.finrank_self] at h2
        omega
      let k := min mS ((e - 1) / 2)
      have hk_le_m : k ≤ mS := min_le_left _ _
      have hk_le_e : k ≤ (e - 1) / 2 := min_le_right _ _
      obtain ⟨K, hKS, hKinf, hKrad, hKfin⟩ := hbuild k hk_le_m R' hR'le
      have hcod : Module.finrank F2 S - Module.finrank F2 K ≤ e := by omega
      obtain ⟨L, out, heq⟩ := hfromK K hKS hcod
      refine ⟨L, out, ?_⟩
      obtain ⟨_, hsum⟩ := sum_abs_chi_coset q ω hself hsymm hq S K hKS
      have hKR_ok : ∀ w ∈ (K ⊓ R : Submodule F2 X), q w + q 0 = 0 := by
        intro w hw
        rw [hKinf] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        have : f (p + w'.1) + f p = 0 := hw'
        simpa [q] using this
      rw [if_pos hKR_ok] at hsum
      have hs0 : Module.finrank F2 (radIn ω K) - Module.finrank F2 (K ⊓ R : Submodule F2 X) = 0 := by
        rw [hKrad, hKinf, Nat.sub_self]
      have hs : Module.finrank F2 K - Module.finrank F2 (K ⊓ R : Submodule F2 X) = 2 * (mS - k) := by
        rw [hKinf, hKfin]; omega
      have hexp : (Module.finrank F2 K - Module.finrank F2 (K ⊓ R : Submodule F2 X) +
          (Module.finrank F2 (radIn ω K) - Module.finrank F2 (K ⊓ R : Submodule F2 X))) / 2 = m - (e - 1) / 2 := by
        rw [hs, hs0, add_zero, Nat.mul_div_right _ (by norm_num)]
        dsimp only [k]
        omega
      rw [hexp] at hsum
      have hsumQ : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) =
          (Fintype.card S : ℚ) * (Fintype.card K : ℚ) * ((1 : ℚ) / 2 ^ (m - (e - 1) / 2)) := by
        have hcast : (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) * (2 ^ (m - (e - 1) / 2) : ℚ) =
            (Fintype.card S : ℚ) * (Fintype.card K : ℚ) := by
          exact_mod_cast hsum
        have h2pos : (0 : ℚ) < (2 ^ (m - (e - 1) / 2) : ℚ) := by positivity
        field_simp [ne_of_gt h2pos]
        linarith
      have heqQ : (Fintype.card K : ℚ) *
            (2 * ((Finset.univ.filter fun u : S => out (L (p + u.1)) = f (p + u.1)).card : ℚ)) =
          (Fintype.card K : ℚ) * (Fintype.card S : ℚ) +
            (∑ z : S, |∑ u : K, chi (q (z.1 + u.1))| : ℚ) := by
        exact_mod_cast heq
      rw [hsumQ] at heqQ
      have hKpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
        rw [fintype_card_subspace K]; positivity
      nlinarith

end PEqualNP.Outside.L_pcx_440_aux

set_option maxHeartbeats 3000000 in
open PEqualNP.Outside.L_pcx_440_aux in
theorem PEqualNP.Outside.L_pcx_440 : (∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ (f : X → F),
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) →
    let U := fun (m j : ℕ) => (1 : ℚ)/2^(m-j/2)
    let M := fun (m j : ℕ) => if j=0 then (0 : ℚ) else 1/2^(m-(j-1)/2)
    ∀ (d e : ℕ) (first : X →ₗ[F] (Fin d → F)),
      let S := LinearMap.ker first
      let h := Module.finrank F S
      let t := (Nat.card {u : S // ∀ v : S, B u.val v.val = 0}).log2
      let c := Nat.card {u : S // ∀ v : X, B u.val v = 0}
      let c0 := Nat.card {u : S // (∀ v : X, B u.val v = 0) ∧ f u.val = f 0}
      let m := (h-t)/2
      let w := if c0=c then (1 : ℚ)/2^(t-c.log2) else 0
      let bias := w*U m e + (1-w)*M m e
      ∀ p : ℚ, (∃ (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
        (out : (Fin d → F) → (Fin e → F) → F),
        p*(Nat.card X : ℚ) ≤ (Nat.card {x : X //
          out (first x) (second (first x) x) = f x} : ℚ)) ↔ p ≤ (1+bias)/2) := by
  classical
  intro n F X f B hf U M d e first S h t c c0 m w bias
  have hB_self : ∀ v : X, B v v = 0 := by
    intro v
    dsimp only [B]
    have hvv : v + v = 0 := by ext i; exact zmod2_add_self (v i)
    rw [hvv]
    have : f 0 + f v + f v + f 0 = (f 0 + f 0) + (f v + f v) := by abel
    rw [this, zmod2_add_self, zmod2_add_self, add_zero]
  have hB_symm : ∀ u v : X, B u v = B v u := by
    intro u v
    dsimp only [B]
    rw [add_comm u v]
    abel
  have hB_add_left : ∀ u₁ u₂ v : X, B (u₁ + u₂) v = B u₁ v + B u₂ v := by
    intro u₁ u₂ v
    have h1 := hf u₁ u₂ v
    dsimp only [B] at h1 ⊢
    rw [← zmod2_add_eq_zero_iff, ← h1]
    have : (f (u₁ + u₂ + v) + f (u₁ + u₂) + f v + f 0) +
        ((f (u₁ + v) + f u₁ + f v + f 0) + (f (u₁ + u₂ + v) + f (u₁ + u₂) + f (u₁ + v) + f u₁)) =
        (f (u₁ + u₂ + v) + f (u₁ + u₂ + v)) + (f (u₁ + u₂) + f (u₁ + u₂)) +
        (f (u₁ + v) + f (u₁ + v)) + (f u₁ + f u₁) + (f v + f v) + (f 0 + f 0) := by abel
    simpa only [F, zmod2_add_self, add_zero] using this
  have hB_add_right : ∀ u v₁ v₂ : X, B u (v₁ + v₂) = B u v₁ + B u v₂ := by
    intro u v₁ v₂
    rw [hB_symm, hB_add_left, hB_symm v₁, hB_symm v₂]
  have hB_zero_right : ∀ u : X, B u 0 = 0 := by
    intro u
    dsimp only [B]
    rw [add_zero]
    have : f u + f u + f 0 + f 0 = (f u + f u) + (f 0 + f 0) := by abel
    rw [this, zmod2_add_self, zmod2_add_self, add_zero]
  let ω : X →ₗ[F2] (X →ₗ[F2] F2) :=
    { toFun := fun u =>
        { toFun := fun v => B u v
          map_add' := fun v₁ v₂ => hB_add_right u v₁ v₂
          map_smul' := fun r v => by
            rcases zmod2_eq_zero_or_one r with rfl | rfl
            · simp [hB_zero_right]
            · simp }
      map_add' := fun u₁ u₂ => LinearMap.ext fun v => hB_add_left u₁ u₂ v
      map_smul' := fun r u => LinearMap.ext fun v => by
        rcases zmod2_eq_zero_or_one r with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.zero_apply]
          rw [hB_symm]; exact hB_zero_right v
        · simp }
  let R : Submodule F2 X := radIn ω S
  let G : Submodule F2 X :=
    { carrier := {u ∈ S | ∀ v : X, B u v = 0}, add_mem' := fun {u₁ u₂} h₁ h₂ =>
        ⟨S.add_mem h₁.1 h₂.1, fun v => by rw [hB_add_left, h₁.2 v, h₂.2 v, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, fun v => by rw [hB_symm]; exact hB_zero_right v⟩
      smul_mem' := fun r {u} hu =>
        ⟨S.smul_mem r hu.1, fun v => by
          rcases zmod2_eq_zero_or_one r with rfl | rfl
          · rw [zero_smul, hB_symm]; exact hB_zero_right v
          · rw [one_smul]; exact hu.2 v⟩ }
  have ht_eq : t = Module.finrank F2 R := by
    have heq : Nat.card {u : S // ∀ v : S, B u.val v.val = 0} = Nat.card R := by
      refine Nat.card_congr
        { toFun := fun u => ⟨u.1.1, u.1.2, fun v hv => u.2 ⟨v, hv⟩⟩
          invFun := fun u => ⟨⟨u.1, u.2.1⟩, fun v => u.2.2 v.1 v.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    dsimp only [t]
    rw [heq, card_subspace R, nat_log2_two_pow]
  have hc_eq : c = 2 ^ Module.finrank F2 G := by
    have heq : Nat.card {u : S // ∀ v : X, B u.val v = 0} = Nat.card G := by
      refine Nat.card_congr
        { toFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
          invFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    dsimp only [c]
    rw [heq, card_subspace G]
  have hclog2 : c.log2 = Module.finrank F2 G := by
    rw [hc_eq, nat_log2_two_pow]
  have hc0_iff : c0 = c ↔ ∀ u ∈ G, f u = f 0 := by
    let A := Finset.univ.filter fun u : G => f u.1 = f 0
    have hc0_card : c0 = A.card := by
      have heq : Nat.card {u : S // (∀ v : X, B u.val v = 0) ∧ f u.val = f 0} =
          Nat.card A := by
        refine Nat.card_congr
          { toFun := fun u => ⟨⟨u.1.1, u.1.2, u.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2.2⟩⟩
            invFun := fun u => ⟨⟨u.1.1, u.1.2.1⟩, u.1.2.2, (Finset.mem_filter.mp u.2).2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      dsimp only [c0]
      rw [heq, Nat.card_eq_fintype_card, Fintype.card_coe]
    have hc_card : c = (Finset.univ : Finset G).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_subspace G, hc_eq]
    rw [hc0_card, hc_card]
    constructor
    · intro hcard u hu
      have hAeq : A = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ A) (le_of_eq hcard.symm)
      have hmem : (⟨u, hu⟩ : G) ∈ A := by rw [hAeq]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp hmem).2
    · intro hall
      have hAeq : A = Finset.univ := by
        ext u
        simp [A, hall u.1 u.2]
      rw [hAeq]
  let Φ : X →ₗ[F2] (R →ₗ[F2] F2) :=
    { toFun := fun x =>
        { toFun := fun w => B x w.1
          map_add' := fun w1 w2 => hB_add_right x w1.1 w2.1
          map_smul' := fun r w => by
            rcases zmod2_eq_zero_or_one r with rfl | rfl
            · simp [hB_zero_right]
            · simp }
      map_add' := fun x1 x2 => LinearMap.ext fun w => hB_add_left x1 x2 w.1
      map_smul' := fun r x => LinearMap.ext fun w => by
        rcases zmod2_eq_zero_or_one r with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.zero_apply]
          rw [hB_symm]; exact hB_zero_right w.1
        · simp }
  let g0 : R →ₗ[F2] F2 :=
    { toFun := fun w => f w.1 + f 0
      map_add' := fun w1 w2 => by
        have hpol := hf 0 w1.1 w2.1
        simp only [zero_add] at hpol
        have hw0 : B w1.1 w2.1 = 0 := w1.2.2 w2.1 w2.2.1
        rw [hw0] at hpol
        change f (w1.1 + w2.1) + f 0 = (f w1.1 + f 0) + (f w2.1 + f 0)
        rw [← zmod2_add_eq_zero_iff]
        have : (f (w1.1 + w2.1) + f 0) + ((f w1.1 + f 0) + (f w2.1 + f 0)) =
            (f (w1.1 + w2.1) + f w1.1 + f w2.1 + f 0) + (f 0 + f 0) := by abel
        rw [this, hpol, zmod2_add_self, add_zero]
      map_smul' := fun r w => by
        rcases zmod2_eq_zero_or_one r with rfl | rfl
        · simp only [zero_smul, ZeroMemClass.coe_zero, RingHom.id_apply]
          exact zmod2_add_self _
        · simp }
  obtain ⟨hΦ_range, hΦ_fin⟩ := pairing_range_eq_ann Φ
  let GΦ : Submodule F2 R :=
    { carrier := {w : R | ∀ x : X, Φ x w = 0}, add_mem' := fun ha hb x => by rw [map_add, ha x, hb x, add_zero]
      zero_mem' := fun x => map_zero _
      smul_mem' := fun r _ hb x => by rw [map_smul, hb x, smul_zero] }
  have hGΦ_iso : Module.finrank F2 GΦ = Module.finrank F2 G := by
    let eG : GΦ ≃ₗ[F2] G :=
      { toFun := fun w => ⟨w.1.1, w.1.2.1, fun v => by rw [hB_symm]; exact w.2 v⟩
        invFun := fun w => ⟨⟨w.1, w.2.1, fun v _ => w.2.2 v⟩, fun x => by
          change B x w.1 = 0; rw [hB_symm]; exact w.2.2 x⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact eG.finrank_eq
  have hΦ_rank : Module.finrank F2 (LinearMap.range Φ) = t - c.log2 := by
    rw [ht_eq, hclog2, ← hGΦ_iso]
    change Module.finrank F2 (LinearMap.range Φ) + Module.finrank F2 GΦ = Module.finrank F2 R at hΦ_fin
    omega
  have hunm_iff : ∀ p : X, (∀ w ∈ R, f (p + w) + f p = 0) ↔ Φ p = g0 := by
    intro p
    rw [LinearMap.ext_iff]
    constructor
    · intro hp w
      have h1 : B p w.1 = f (p + w.1) + f p + f w.1 + f 0 := rfl
      have h2 := hp w.1 w.2
      change B p w.1 = f w.1 + f 0
      rw [h1, h2, zero_add]
    · intro hp w hw
      have h1 : B p w = (f (p + w) + f p) + (f w + f 0) := by
        dsimp only [B]; abel
      have h2 : B p w = f w + f 0 := hp ⟨w, hw⟩
      rw [h1] at h2
      have h3 : (f (p + w) + f p) + (f w + f 0) + (f w + f 0) = (f w + f 0) + (f w + f 0) :=
        congrArg (fun a => a + (f w + f 0)) h2
      rw [add_assoc, zmod2_add_self, add_zero] at h3
      exact h3
  have hcount_unm : ((Finset.univ.filter fun p : X => ∀ w ∈ R, f (p + w) + f p = 0).card : ℚ) =
      w * (Fintype.card X : ℚ) := by
    have hfilt : (Finset.univ.filter fun p : X => ∀ w ∈ R, f (p + w) + f p = 0) =
        Finset.univ.filter fun p : X => Φ p = g0 := by
      ext p; simp [hunm_iff]
    rw [hfilt]
    by_cases hc0c : c0 = c
    · have hw_val : w = (1 : ℚ) / 2 ^ (t - c.log2) := by dsimp only [w]; rw [if_pos hc0c]
      rw [hw_val]
      have hg0_mem : g0 ∈ LinearMap.range Φ := by
        rw [hΦ_range]
        intro u hu
        have huG : u.1 ∈ G := ⟨u.2.1, fun v => by rw [hB_symm]; exact hu v⟩
        have hfu : f u.1 = f 0 := (hc0_iff.mp hc0c) u.1 huG
        change f u.1 + f 0 = 0
        rw [hfu, zmod2_add_self]
      have hpre := card_preimage_linearMap Φ g0 hg0_mem
      rw [hΦ_rank] at hpre
      have hpre_eq : (Finset.univ.filter fun p : X => Φ p = g0).card * 2 ^ (t - c.log2) =
          Fintype.card X := by
        convert hpre using 2
        apply congrArg Finset.card
        ext z
        simp
      have hpreQ : ((Finset.univ.filter fun p : X => Φ p = g0).card : ℚ) * (2 ^ (t - c.log2) : ℚ) =
          (Fintype.card X : ℚ) := by
        exact_mod_cast hpre_eq
      have h2pos : (0 : ℚ) < (2 ^ (t - c.log2) : ℚ) := by positivity
      field_simp [ne_of_gt h2pos]
      linarith
    · have hw_val : w = 0 := by dsimp only [w]; rw [if_neg hc0c]
      rw [hw_val, zero_mul]
      have hg0_not : g0 ∉ LinearMap.range Φ := by
        rw [hΦ_range]
        intro hmem
        apply hc0c
        rw [hc0_iff]
        intro u huG
        let uR : R := ⟨u, huG.1, fun v _ => huG.2 v⟩
        have huGΦ : uR ∈ GΦ := fun x => by change B x u = 0; rw [hB_symm]; exact huG.2 x
        have h0 : f u + f 0 = 0 := hmem uR huGΦ
        exact (zmod2_add_eq_zero_iff _ _).mp h0
      have hempty : (Finset.univ.filter fun p : X => Φ p = g0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p _ hp
        exact hg0_not ⟨p, hp⟩
      rw [hempty, Finset.card_empty]
      simp
  have hsum_target :
      (∑ p : X, (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) =
        (Fintype.card X : ℚ) * bias := by
    have hsplit : (∑ p : X, (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) =
        ((Finset.univ.filter fun p : X => ∀ w ∈ R, f (p + w) + f p = 0).card : ℚ) * U m e +
        (((Fintype.card X : ℚ) -
          ((Finset.univ.filter fun p : X => ∀ w ∈ R, f (p + w) + f p = 0).card : ℚ)) * M m e) := by
      have h1 : ∀ p : X, (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e) =
          (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e - M m e else 0) + M m e := by
        intro p; split_ifs <;> ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsplit, hcount_unm]
    dsimp only [bias]
    ring
  have hm_def : m = (Module.finrank F2 S - Module.finrank F2 R) / 2 := by
    dsimp only [m, h]; rw [ht_eq]
  have hSpos : (0 : ℚ) < (Fintype.card S : ℚ) := by
    rw [fintype_card_subspace S]; positivity
  have hXpos : (0 : ℚ) < (Nat.card X : ℚ) := by
    rw [Nat.card_eq_fintype_card]; positivity
  have hdouble_global : ∀ (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
      (out : (Fin d → F) → (Fin e → F) → F),
      (Fintype.card S : ℚ) *
        (Nat.card {x : X // out (first x) (second (first x) x) = f x} : ℚ) =
      ∑ p : X, ((Finset.univ.filter fun u : S =>
        out (first p) (second (first p) (p + u.1)) = f (p + u.1)).card : ℚ) := by
    intro second out
    have hnat : Fintype.card S *
          Nat.card {x : X // out (first x) (second (first x) x) = f x} =
        ∑ p : X, (Finset.univ.filter fun u : S =>
          out (first p) (second (first p) (p + u.1)) = f (p + u.1)).card := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype (fun x : X => out (first x) (second (first x) x) = f x)]
      calc Fintype.card S * (Finset.univ.filter fun x : X =>
              out (first x) (second (first x) x) = f x).card
          = ∑ _u : S, ∑ x : X, if out (first x) (second (first x) x) = f x then 1 else 0 := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.card_filter]
        _ = ∑ u : S, ∑ p : X, if out (first (p + u.1)) (second (first (p + u.1)) (p + u.1)) =
              f (p + u.1) then 1 else 0 := by
              refine Finset.sum_congr rfl fun u _ =>
                (Fintype.sum_equiv (Equiv.addRight u.1)
                  (fun p => if out (first (p + u.1)) (second (first (p + u.1)) (p + u.1)) = f (p + u.1) then 1 else 0)
                  (fun x => if out (first x) (second (first x) x) = f x then 1 else 0) (fun _ => rfl)).symm
        _ = ∑ p : X, ∑ u : S, if out (first p) (second (first p) (p + u.1)) =
              f (p + u.1) then 1 else 0 := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun u _ => ?_
              have hfp : first (p + u.1) = first p := by
                rw [map_add, u.2, add_zero]
              rw [hfp]
        _ = ∑ p : X, (Finset.univ.filter fun u : S =>
              out (first p) (second (first p) (p + u.1)) = f (p + u.1)).card := by
              refine Finset.sum_congr rfl fun p _ => (Finset.card_filter _ _).symm
    exact_mod_cast hnat
  have hrhs_common : (∑ p : X, (Fintype.card S : ℚ) *
        (1 + (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) / 2) =
      (Fintype.card S : ℚ) * (((1 + bias) / 2) * (Nat.card X : ℚ)) := by
    have h1 : (∑ p : X, (Fintype.card S : ℚ) *
          (1 + (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) / 2) =
        (Fintype.card S : ℚ) / 2 *
          ((Fintype.card X : ℚ) +
            ∑ p : X, (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) := by
      rw [mul_add, Finset.mul_sum]
      have hconst : (Fintype.card S : ℚ) / 2 * (Fintype.card X : ℚ) =
          ∑ _p : X, (Fintype.card S : ℚ) / 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      rw [hconst, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [h1, hsum_target, Nat.card_eq_fintype_card]
    ring
  have hupper : ∀ (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
      (out : (Fin d → F) → (Fin e → F) → F),
      (Nat.card {x : X // out (first x) (second (first x) x) = f x} : ℚ) ≤
        ((1 + bias) / 2) * (Nat.card X : ℚ) := by
    intro second out
    have hdbl := hdouble_global second out
    have hsum_le : (∑ p : X, ((Finset.univ.filter fun u : S =>
          out (first p) (second (first p) (p + u.1)) = f (p + u.1)).card : ℚ)) ≤
        ∑ p : X, (Fintype.card S : ℚ) *
          (1 + (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) / 2 := by
      refine Finset.sum_le_sum fun p _ => ?_
      have hsc := single_coset_upper f ω hB_self hB_symm hf S e p (second (first p)) (out (first p))
      dsimp only at hsc
      rw [← hm_def] at hsc
      exact hsc
    nlinarith
  have hachieve : ∃ (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
      (out : (Fin d → F) → (Fin e → F) → F),
      (Nat.card {x : X // out (first x) (second (first x) x) = f x} : ℚ) =
        ((1 + bias) / 2) * (Nat.card X : ℚ) := by
    let choosePair : (y : Fin d → F) → (X →ₗ[F] (Fin e → F)) × ((Fin e → F) → F) := fun y =>
      if hy : ∃ p0 : X, first p0 = y then
        let p0 := Classical.choose hy
        let hEx := single_coset_achieve f ω hB_self hB_symm hf S e p0
        (Classical.choose hEx, Classical.choose (Classical.choose_spec hEx))
      else (0, fun _ => 0)
    refine ⟨fun y => (choosePair y).1, fun y => (choosePair y).2, ?_⟩
    have hdbl := hdouble_global (fun y => (choosePair y).1) (fun y => (choosePair y).2)
    have hcoset_eq : ∀ p : X,
        ((Finset.univ.filter fun u : S =>
            (choosePair (first p)).2 ((choosePair (first p)).1 (p + u.1)) = f (p + u.1)).card : ℚ) =
          (Fintype.card S : ℚ) *
            (1 + (if (∀ w ∈ R, f (p + w) + f p = 0) then U m e else M m e)) / 2 := by
      intro p
      have hy : ∃ p0 : X, first p0 = first p := ⟨p, rfl⟩
      set p0 := Classical.choose hy
      have hp0_eq : first p0 = first p := Classical.choose_spec hy
      have hdiffS : p - p0 ∈ S := by
        change first (p - p0) = 0
        rw [map_sub, hp0_eq, sub_self]
      let dS : S := ⟨p - p0, hdiffS⟩
      have hunm_same : (∀ w ∈ R, f (p + w) + f p = 0) ↔ (∀ w ∈ R, f (p0 + w) + f p0 = 0) := by
        rw [hunm_iff p, hunm_iff p0]
        have hΦeq : Φ p = Φ p0 := by
          refine LinearMap.ext fun w => ?_
          change B p w.1 = B p0 w.1
          have h0 : B (p - p0) w.1 = 0 := by rw [hB_symm]; exact w.2.2 (p - p0) hdiffS
          have hsub : p = p0 + (p - p0) := by abel
          rw [hsub, hB_add_left, h0, add_zero]
        rw [hΦeq]
      have hcp : choosePair (first p) =
          (Classical.choose (single_coset_achieve f ω hB_self hB_symm hf S e p0),
           Classical.choose (Classical.choose_spec (single_coset_achieve f ω hB_self hB_symm hf S e p0))) := by
        dsimp only [choosePair]
        rw [dif_pos hy]
      have hspec := Classical.choose_spec (Classical.choose_spec
        (single_coset_achieve f ω hB_self hB_symm hf S e p0))
      have hcard_shift : (Finset.univ.filter fun u : S =>
            (choosePair (first p)).2 ((choosePair (first p)).1 (p + u.1)) = f (p + u.1)).card =
          (Finset.univ.filter fun u : S =>
            (choosePair (first p)).2 ((choosePair (first p)).1 (p0 + u.1)) = f (p0 + u.1)).card := by
        rw [Finset.card_filter, Finset.card_filter]
        refine Fintype.sum_equiv (Equiv.addLeft dS) _ _ fun u => ?_
        have hpt : p + u.1 = p0 + ((Equiv.addLeft dS) u).1 := by
          change p + u.1 = p0 + ((p - p0) + u.1)
          abel
        rw [hpt]
      rw [hcard_shift]
      let m0 := (Module.finrank F2 S - Module.finrank F2 R) / 2
      calc
        _ = (Fintype.card S : ℚ) *
            (1 + (if (∀ w ∈ R, f (p0 + w) + f p0 = 0) then U m0 e else M m0 e)) / 2 := by
              rw [hcp]
              exact hspec
        _ = _ := by
          change m = m0 at hm_def
          rw [← hm_def]
          by_cases hp : ∀ v ∈ R, f (p + v) + f p = 0
          · simp only [if_pos hp, if_pos (hunm_same.mp hp)]
          · simp only [if_neg hp, if_neg (mt hunm_same.mpr hp)]
    have hsum_eq : (∑ p : X, ((Finset.univ.filter fun u : S =>
          (choosePair (first p)).2 ((choosePair (first p)).1 (p + u.1)) = f (p + u.1)).card : ℚ)) =
        (Fintype.card S : ℚ) * (((1 + bias) / 2) * (Nat.card X : ℚ)) := by
      simp_rw [hcoset_eq]
      exact hrhs_common
    nlinarith
  intro p
  constructor
  · rintro ⟨second, out, hle⟩
    have hu := hupper second out
    nlinarith
  · intro hp
    obtain ⟨second, out, heq⟩ := hachieve
    refine ⟨second, out, ?_⟩
    nlinarith

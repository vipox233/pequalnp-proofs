import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Roots
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_791_aux

open scoped Matrix BigOperators

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

private def chi (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

private lemma chi_zero : chi 0 = 1 := rfl

private lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

private lemma sum_chi_mul (t : ZMod 2) :
    (∑ b : ZMod 2, chi (b * t)) = if t = 0 then 2 else 0 := by
  rcases zmod2_eq_zero_or_one t with rfl | rfl <;> decide

private def dot {j : ℕ} (u v : Fin j → ZMod 2) : ZMod 2 :=
  ∑ r : Fin j, u r * v r

private lemma dot_zero_left {j : ℕ} (u : Fin j → ZMod 2) : dot 0 u = 0 := by
  simp [dot]

private lemma dot_add_right {j : ℕ} (c u v : Fin j → ZMod 2) :
    dot c (u + v) = dot c u + dot c v := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma sum_chi_dot {j : ℕ} (u : Fin j → ZMod 2) :
    (∑ c : Fin j → ZMod 2, chi (dot c u)) = if u = 0 then (2 : ℤ) ^ j else 0 := by
  have hrew : ∀ c : Fin j → ZMod 2, chi (dot c u) = ∏ r : Fin j, chi (c r * u r) := fun c =>
    chi_sum Finset.univ (fun r => c r * u r)
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun r b => chi (b * u r))]
  simp_rw [sum_chi_mul]
  by_cases hu : u = 0
  · subst hu
    simp
  · simp only [hu, ↓reduceIte]
    have hex : ∃ r : Fin j, u r ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu (funext hall)
    rcases hex with ⟨r₀, hr₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ r₀) (by simp [hr₀])

private lemma sum_chi_dot_nz {j : ℕ} (u : Fin j → ZMod 2) :
    (∑ c ∈ (Finset.univ : Finset (Fin j → ZMod 2)).erase 0, chi (dot c u)) =
      if u = 0 then (2 : ℤ) ^ j - 1 else -1 := by
  have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin j → ZMod 2))
    (fun c => chi (dot c u)) (Finset.mem_univ 0)
  have h0 : chi (dot (0 : Fin j → ZMod 2) u) = 1 := by
    simp [dot, chi_zero]
  rw [h0, sum_chi_dot] at h1
  split_ifs at h1 ⊢ <;> omega

private lemma iso_pair_iff {j : ℕ} (u w : Fin j → ZMod 2) :
    (∀ r s : Fin j, u r * w s = w r * u s) ↔ (u = 0 ∨ w = 0 ∨ u = w) := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · by_cases hw : w = 0
      · exact Or.inr (Or.inl hw)
      · right; right
        have hex_u : ∃ r₀ : Fin j, u r₀ = 1 := by
          by_contra hall; push Not at hall
          apply hu; funext r
          rcases zmod2_eq_zero_or_one (u r) with h0 | h1
          · exact h0
          · exact absurd h1 (hall r)
        have hex_w : ∃ s₀ : Fin j, w s₀ = 1 := by
          by_contra hall; push Not at hall
          apply hw; funext s
          rcases zmod2_eq_zero_or_one (w s) with h0 | h1
          · exact h0
          · exact absurd h1 (hall s)
        rcases hex_u with ⟨r₀, hr₀⟩
        rcases hex_w with ⟨s₀, hs₀⟩
        have hwr₀ : w r₀ = 1 := by
          have h1 := h r₀ s₀
          rw [hr₀, hs₀, one_mul] at h1
          rcases zmod2_eq_zero_or_one (w r₀) with hw0 | hw1
          · rw [hw0, zero_mul] at h1; exact absurd h1.symm (by decide)
          · exact hw1
        funext r
        have h1 := h r r₀
        rw [hwr₀, hr₀, mul_one, mul_one] at h1
        exact h1
  · rintro (rfl | rfl | rfl) r s
    · simp
    · simp
    · ring

private instance instFiniteLinearMap {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Finite V] [Finite W] :
    Finite (V →ₗ[ZMod 2] W) :=
  Finite.of_injective (fun f : V →ₗ[ZMod 2] W => (f : V → W)) DFunLike.coe_injective

private noncomputable instance instFintypeLinearMap {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Finite V] [Finite W] :
    Fintype (V →ₗ[ZMod 2] W) :=
  Fintype.ofFinite (V →ₗ[ZMod 2] W)

open Classical in
private lemma card_inj_lin_fin (h j : ℕ) :
    (Fintype.card {L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L} : ℤ) =
      ∏ r ∈ Finset.range h, ((2 : ℤ) ^ j - (2 : ℤ) ^ r) := by
  induction h with
  | zero =>
    have hcard : Fintype.card {L : (Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L} = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨0, fun x y _ => Subsingleton.elim x y⟩, ?_⟩
      rintro ⟨L, _⟩
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      rw [Subsingleton.elim x 0, map_zero, map_zero]
    rw [hcard]
    simp
  | succ h ih =>
    let Z := Fin j → ZMod 2
    let InjH := {L : (Fin h → ZMod 2) →ₗ[ZMod 2] Z // Function.Injective L}
    let InjS := {L : (Fin (h + 1) → ZMod 2) →ₗ[ZMod 2] Z // Function.Injective L}
    let SigmaType := Σ L' : InjH, {v : Z // v ∉ LinearMap.range L'.val}
    let emb : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin (h + 1) → ZMod 2) :=
      { toFun := fun u => Fin.snoc u 0
        map_add' := fun u₁ u₂ => by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc]
        map_smul' := fun c u => by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp [Fin.snoc] }
    let restMap (L : (Fin (h + 1) → ZMod 2) →ₗ[ZMod 2] Z) : (Fin h → ZMod 2) →ₗ[ZMod 2] Z :=
      L.comp emb
    let toSigma : InjS → SigmaType := fun ⟨L, hL⟩ =>
      have hrest : Function.Injective (restMap L) := by
        intro u₁ u₂ heq
        have hsnoc : Fin.snoc (α := fun _ => ZMod 2) u₁ 0 = Fin.snoc u₂ 0 := hL heq
        funext i
        have := congrFun hsnoc i.castSucc
        simpa [Fin.snoc] using this
      have hv : L (Pi.single (Fin.last h) 1) ∉ LinearMap.range (restMap L) := by
        rintro ⟨u, hu⟩
        have hzero : L (Fin.snoc u 1) = 0 := by
          have hdecomp : Fin.snoc (α := fun _ => ZMod 2) u 1 =
              Fin.snoc u 0 + Pi.single (Fin.last h) 1 := by
            funext i
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc, Pi.single_eq_same]
            · intro i'; simp [Fin.snoc]
          rw [hdecomp, map_add]
          change restMap L u + L (Pi.single (Fin.last h) 1) = 0
          rw [hu]
          funext r
          change L (Pi.single (Fin.last h) 1) r + L (Pi.single (Fin.last h) 1) r = 0
          rcases zmod2_eq_zero_or_one (L (Pi.single (Fin.last h) 1) r) with h0 | h1
          · rw [h0]; decide
          · rw [h1]; decide
        have hsnoc0 : Fin.snoc (α := fun _ => ZMod 2) u 1 = 0 :=
          hL (hzero.trans (map_zero L).symm)
        have hlast := congrFun hsnoc0 (Fin.last h)
        simp [Fin.snoc] at hlast
      ⟨⟨restMap L, hrest⟩, ⟨L (Pi.single (Fin.last h) 1), hv⟩⟩
    let ofSigma : SigmaType → InjS := fun ⟨⟨L', hL'⟩, ⟨v, hv⟩⟩ =>
      let L : (Fin (h + 1) → ZMod 2) →ₗ[ZMod 2] Z :=
        { toFun := fun w => L' (Fin.init w) + w (Fin.last h) • v
          map_add' := fun w₁ w₂ => by
            have hinit : Fin.init (w₁ + w₂) = Fin.init w₁ + Fin.init w₂ := rfl
            rw [hinit, map_add, Pi.add_apply, add_smul]
            abel
          map_smul' := fun c w => by
            have hinit : Fin.init (c • w) = c • Fin.init w := rfl
            rw [hinit, map_smul, Pi.smul_apply, smul_add, smul_assoc]
            rfl }
      have hLinj : Function.Injective L := by
        rw [injective_iff_map_eq_zero]
        intro w hw
        dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hw
        rcases zmod2_eq_zero_or_one (w (Fin.last h)) with hc0 | hc1
        · rw [hc0, zero_smul, add_zero] at hw
          have hinit0 : Fin.init w = 0 := (injective_iff_map_eq_zero L').mp hL' _ hw
          funext i
          refine Fin.lastCases ?_ ?_ i
          · exact hc0
          · intro i'; exact congrFun hinit0 i'
        · exfalso
          rw [hc1, one_smul] at hw
          apply hv
          refine ⟨Fin.init w, ?_⟩
          funext r
          have hr : L' (Fin.init w) r + v r = 0 := congrFun hw r
          revert hr
          rcases zmod2_eq_zero_or_one (L' (Fin.init w) r) with ha | ha <;>
          rcases zmod2_eq_zero_or_one (v r) with hb | hb <;>
            rw [ha, hb] <;> decide
      ⟨L, hLinj⟩
    have hequiv : InjS ≃ SigmaType :=
      { toFun := toSigma
        invFun := ofSigma
        left_inv := by
          rintro ⟨L, hL⟩
          apply Subtype.ext
          apply LinearMap.ext
          intro w
          funext r
          have hw : w = Fin.snoc (Fin.init w) 0 + w (Fin.last h) • Pi.single (Fin.last h) 1 := by
            funext i
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc, Pi.single_eq_same]
            · intro i'; simp [Fin.snoc, Fin.init]
          conv_rhs => rw [hw]
          rw [map_add, map_smul]
          rfl
        right_inv := by
          rintro ⟨⟨L', hL'⟩, ⟨v, hv⟩⟩
          have hfst : (toSigma (ofSigma ⟨⟨L', hL'⟩, ⟨v, hv⟩⟩)).1 = ⟨L', hL'⟩ := by
            apply Subtype.ext
            apply LinearMap.ext
            intro u
            funext r
            change (L' (Fin.init (Fin.snoc (α := fun _ => ZMod 2) u 0)) +
              (Fin.snoc (α := fun _ => ZMod 2) u 0) (Fin.last h) • v) r = L' u r
            simp [Fin.init_snoc]
          refine Sigma.ext hfst ?_
          rw [Subtype.heq_iff_coe_eq (fun _ => by rw [hfst])]
          let eLast : Fin (h + 1) → ZMod 2 := Pi.single (Fin.last h) 1
          have hinit : Fin.init eLast = 0 := by
            funext i; simp [eLast, Fin.init]
          change L' (Fin.init eLast) + eLast (Fin.last h) • v = v
          rw [hinit, map_zero, zero_add]
          simp [eLast] }
    have hcard_eq : Fintype.card InjS = ∑ L' : InjH, Fintype.card {v : Z // v ∉ LinearMap.range L'.val} := by
      rw [Fintype.card_congr hequiv, Fintype.card_sigma]
    have hfiber : ∀ L' : InjH,
        (Fintype.card {v : Z // v ∉ LinearMap.range L'.val} : ℤ) = (2 : ℤ) ^ j - (2 : ℤ) ^ h := by
      intro ⟨L', hL'⟩
      have hcard_range : Fintype.card (LinearMap.range L') = 2 ^ h := by
        have heq : (Fin h → ZMod 2) ≃ LinearMap.range L' :=
          Equiv.ofBijective (LinearMap.rangeRestrict L')
            ⟨fun a b hab => hL' (congrArg Subtype.val hab), LinearMap.surjective_rangeRestrict L'⟩
        rw [← Fintype.card_congr heq]
        simp [Fintype.card_pi]
      have hcompl := Fintype.card_subtype_compl (fun v : Z => v ∈ LinearMap.range L')
      have hcardZ : Fintype.card Z = 2 ^ j := by simp [Z, Fintype.card_pi]
      have hle : Fintype.card (LinearMap.range L') ≤ Fintype.card Z :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      change (Fintype.card {v : Z // v ∉ LinearMap.range L'} : ℤ) = _
      rw [hcompl, hcardZ]
      have hsub : Fintype.card {v : Z // v ∈ LinearMap.range L'} = 2 ^ h := hcard_range
      rw [hsub]
      rw [Nat.cast_sub (by omega : 2 ^ h ≤ 2 ^ j)]
      push_cast
      rfl
    rw [Finset.prod_range_succ, ← ih]
    calc (Fintype.card InjS : ℤ)
        = ∑ L' : InjH, (Fintype.card {v : Z // v ∉ LinearMap.range L'.val} : ℤ) := by
            rw [hcard_eq]; push_cast; rfl
      _ = ∑ _L' : InjH, ((2 : ℤ) ^ j - (2 : ℤ) ^ h) :=
            Finset.sum_congr rfl fun L' _ => hfiber L'
      _ = (Fintype.card InjH : ℤ) * ((2 : ℤ) ^ j - (2 : ℤ) ^ h) := by
            simp; ring

open Classical in
private lemma card_inj_lin_of_equiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [FiniteDimensional (ZMod 2) V] (j : ℕ) :
    (Fintype.card {L : V →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L} : ℤ) =
      ∏ r ∈ Finset.range (Module.finrank (ZMod 2) V), ((2 : ℤ) ^ j - (2 : ℤ) ^ r) := by
  let h := Module.finrank (ZMod 2) V
  let e : V ≃ₗ[ZMod 2] (Fin h → ZMod 2) := (Module.finBasis (ZMod 2) V).equivFun
  let eqv : {L : V →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L} ≃
      {L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L} :=
    { toFun := fun ⟨L, hL⟩ => ⟨L.comp e.symm.toLinearMap, hL.comp e.symm.injective⟩
      invFun := fun ⟨L, hL⟩ => ⟨L.comp e.toLinearMap, hL.comp e.injective⟩
      left_inv := fun ⟨L, _⟩ => by apply Subtype.ext; ext v; simp
      right_inv := fun ⟨L, _⟩ => by apply Subtype.ext; ext v; simp }
  rw [Fintype.card_congr eqv]
  exact card_inj_lin_fin h j

open Classical in
private lemma card_spanning_tuples {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (j : ℕ) :
    (Fintype.card {M : Fin j → (Fin n → ZMod 2) // Submodule.span (ZMod 2) (Set.range M) = U} : ℤ) =
      ∏ r ∈ Finset.range (Module.finrank (ZMod 2) U), ((2 : ℤ) ^ j - (2 : ℤ) ^ r) := by
  let h := Module.finrank (ZMod 2) U
  let e : U ≃ₗ[ZMod 2] (Fin h → ZMod 2) := (Module.finBasis (ZMod 2) U).equivFun
  have hmemU : ∀ (M : {M : Fin j → (Fin n → ZMod 2) // Submodule.span (ZMod 2) (Set.range M) = U})
      (r : Fin j), M.val r ∈ U := fun ⟨M, hM⟩ r => by
    dsimp only; rw [← hM]; exact Submodule.subset_span ⟨r, rfl⟩
  let toL (M : {M : Fin j → (Fin n → ZMod 2) // Submodule.span (ZMod 2) (Set.range M) = U}) :
      (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) :=
    { toFun := fun c r => ∑ t : Fin h, c t * e ⟨M.val r, hmemU M r⟩ t
      map_add' := fun c₁ c₂ => by funext r; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by funext r; simp [mul_assoc, Finset.mul_sum] }
  have htoL_inj : ∀ M, Function.Injective (toL M) := by
    intro M
    rw [injective_iff_map_eq_zero]
    intro c hc
    let φU : U →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun u => ∑ t : Fin h, c t * e u t
        map_add' := fun u₁ u₂ => by simp [map_add, mul_add, Finset.sum_add_distrib]
        map_smul' := fun a u => by
          simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => by ring }
    have hvan : ∀ u : U, φU u = 0 := by
      intro u
      have hu : u.val ∈ Submodule.span (ZMod 2) (Set.range M.val) := by
        rw [M.property]; exact u.property
      have hker : Submodule.span (ZMod 2) (Set.range M.val) ≤
          (LinearMap.ker φU).map U.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨r, rfl⟩
        refine ⟨⟨M.val r, hmemU M r⟩, ?_, rfl⟩
        exact congrFun hc r
      rcases hker hu with ⟨u', hu'ker, hu'eq⟩
      have heq : u' = u := Subtype.ext hu'eq
      subst heq
      exact hu'ker
    funext t₀
    have h1 := hvan (e.symm (Pi.single t₀ 1))
    dsimp only [φU, LinearMap.coe_mk, AddHom.coe_mk] at h1
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [Finset.sum_eq_single t₀] at h1
    · simpa [Pi.single_eq_same] using h1
    · intro t _ hne; simp [Pi.single_eq_of_ne hne]
    · intro h; exact absurd (Finset.mem_univ t₀) h
  let ofL (L : {L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L}) :
      {M : Fin j → (Fin n → ZMod 2) // Submodule.span (ZMod 2) (Set.range M) = U} :=
    let M : Fin j → (Fin n → ZMod 2) := fun r => (e.symm (fun t => L.val (Pi.single t 1) r)).val
    have hspan_le : Submodule.span (ZMod 2) (Set.range M) ≤ U := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact (e.symm _).property
    have hspan_eq : Submodule.span (ZMod 2) (Set.range M) = U := by
      by_contra hne
      let S : Submodule (ZMod 2) U := (Submodule.span (ZMod 2) (Set.range M)).comap U.subtype
      have hS_ne_top : S ≠ ⊤ := by
        intro htop
        apply hne
        apply le_antisymm hspan_le
        intro x hx
        have : (⟨x, hx⟩ : U) ∈ S := htop ▸ Submodule.mem_top
        exact this
      have hfin_pos : 0 < Module.finrank (ZMod 2) (U ⧸ S) := by
        have hsum := Submodule.finrank_quotient_add_finrank S
        have hlt : Module.finrank (ZMod 2) S < Module.finrank (ZMod 2) U :=
          Submodule.finrank_lt hS_ne_top
        omega
      let qBasis := Module.finBasis (ZMod 2) (U ⧸ S)
      let ψ : (U ⧸ S) →ₗ[ZMod 2] ZMod 2 :=
        (LinearMap.proj (⟨0, hfin_pos⟩ : Fin (Module.finrank (ZMod 2) (U ⧸ S)))).comp
          qBasis.equivFun.toLinearMap
      have hψ_ne : ψ ≠ 0 := by
        intro h0
        have h1 := LinearMap.congr_fun h0 (qBasis ⟨0, hfin_pos⟩)
        simp [ψ, qBasis] at h1
      let α : (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        ψ.comp (S.mkQ.comp e.symm.toLinearMap)
      let c : Fin h → ZMod 2 := fun t => α (Pi.single t 1)
      have hc_ne : c ≠ 0 := by
        intro hc0
        apply hψ_ne
        apply LinearMap.ext
        intro q
        rcases Submodule.Quotient.mk_surjective S q with ⟨u, rfl⟩
        have heq : α (e u) = ∑ t : Fin h, e u t * c t := by
          have hdecomp : e u = ∑ t : Fin h, e u t • Pi.single t (1 : ZMod 2) := by
            funext t₀
            simp [Finset.sum_apply, Pi.single_apply]
          conv_lhs => rw [hdecomp]
          simp [map_sum, map_smul, c]
        have hzero : α (e u) = 0 := by rw [heq]; simp [hc0]
        simpa [α] using hzero
      have hLc : L.val c = 0 := by
        funext r
        have hdecomp : c = ∑ t : Fin h, c t • Pi.single t (1 : ZMod 2) := by
          funext t₀; simp [Finset.sum_apply, Pi.single_apply]
        have h1 : L.val c r = ∑ t : Fin h, c t * L.val (Pi.single t 1) r := by
          conv_lhs => rw [hdecomp]
          simp [map_sum, map_smul, Finset.sum_apply]
        rw [h1]
        have hmem : e.symm (fun t => L.val (Pi.single t 1) r) ∈ S :=
          Submodule.subset_span ⟨r, rfl⟩
        have hα0 : α (fun t => L.val (Pi.single t 1) r) = 0 := by
          simp only [α, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero S).mpr hmem, map_zero]
        have hdecomp2 : (fun t => L.val (Pi.single t 1) r) =
            ∑ t : Fin h, L.val (Pi.single t 1) r • Pi.single t (1 : ZMod 2) := by
          funext t₀; simp [Finset.sum_apply, Pi.single_apply]
        rw [hdecomp2, map_sum] at hα0
        simp only [map_smul, smul_eq_mul] at hα0
        rw [Pi.zero_apply, ← hα0]
        refine Finset.sum_congr rfl fun t _ => by dsimp only [c]; ring
      exact hc_ne ((injective_iff_map_eq_zero L.val).mp L.property c hLc)
    ⟨M, hspan_eq⟩
  let eqv : {M : Fin j → (Fin n → ZMod 2) // Submodule.span (ZMod 2) (Set.range M) = U} ≃
      {L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) // Function.Injective L} :=
    { toFun := fun M => ⟨toL M, htoL_inj M⟩
      invFun := ofL
      left_inv := fun M => by
        apply Subtype.ext
        funext r
        change (e.symm (fun t => toL M (Pi.single t 1) r)).val = M.val r
        have hfun : (fun t => toL M (Pi.single t 1) r) = e ⟨M.val r, hmemU M r⟩ := by
          funext t₀
          dsimp only [toL, LinearMap.coe_mk, AddHom.coe_mk]
          rw [Finset.sum_eq_single t₀]
          · simp [Pi.single_eq_same]
          · intro t _ hne; simp [Pi.single_eq_of_ne hne]
          · intro h; exact absurd (Finset.mem_univ t₀) h
        rw [hfun, LinearEquiv.symm_apply_apply]
      right_inv := fun L => by
        apply Subtype.ext
        apply LinearMap.ext
        intro c
        funext r
        change (∑ t : Fin h, c t * e ⟨(ofL L).val r, hmemU (ofL L) r⟩ t) = L.val c r
        have hval : (ofL L).val r = (e.symm (fun t => L.val (Pi.single t 1) r)).val := rfl
        have hsub : (⟨(ofL L).val r, hmemU (ofL L) r⟩ : U) =
            e.symm (fun t => L.val (Pi.single t 1) r) := Subtype.ext hval
        rw [hsub, LinearEquiv.apply_symm_apply]
        have hdecomp : c = ∑ t : Fin h, c t • Pi.single t (1 : ZMod 2) := by
          funext t₀; simp [Finset.sum_apply, Pi.single_apply]
        conv_rhs => rw [hdecomp]
        simp [map_sum, map_smul, Finset.sum_apply] }
  rw [Fintype.card_congr eqv]
  exact card_inj_lin_fin h j

open Classical in
private lemma card_lin_with_ker {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) (j : ℕ) :
    (Fintype.card {ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) // LinearMap.ker ψ = D} : ℤ) =
      ∏ r ∈ Finset.range (m - Module.finrank (ZMod 2) D), ((2 : ℤ) ^ j - (2 : ℤ) ^ r) := by
  let A := Fin m → ZMod 2
  let Z := Fin j → ZMod 2
  let : Fintype (A ⧸ D) := Fintype.ofFinite _
  let eqv : {ψ : A →ₗ[ZMod 2] Z // LinearMap.ker ψ = D} ≃
      {L : (A ⧸ D) →ₗ[ZMod 2] Z // Function.Injective L} :=
    { toFun := fun ⟨ψ, hker⟩ =>
        ⟨D.liftQ ψ (le_of_eq hker.symm), by
          rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker]
          simp⟩
      invFun := fun ⟨L, hL⟩ =>
        ⟨L.comp D.mkQ, by
          ext a
          simp only [LinearMap.mem_ker, LinearMap.comp_apply]
          rw [← map_zero L, hL.eq_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]⟩
      left_inv := fun ⟨ψ, _⟩ => by apply Subtype.ext; ext a; simp
      right_inv := fun ⟨L, _⟩ => by
        apply Subtype.ext
        apply LinearMap.ext
        intro q
        rcases Submodule.Quotient.mk_surjective D q with ⟨a, rfl⟩
        simp }
  rw [Fintype.card_congr eqv, card_inj_lin_of_equiv (V := A ⧸ D) j]
  have hdim : Module.finrank (ZMod 2) (A ⧸ D) = m - Module.finrank (ZMod 2) D := by
    have hsum : Module.finrank (ZMod 2) (A ⧸ D) + Module.finrank (ZMod 2) D = m := by
      rw [Submodule.finrank_quotient_add_finrank D]
      exact Module.finrank_fin_fun (ZMod 2)
    omega
  rw [hdim]

private lemma list_prod_take_succ {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Matrix α α ℤ)) (t : ℕ) (ht : t < L.length) :
    (L.take (t + 1)).prod = (L.take t).prod * L[t] := by
  rw [List.take_succ_eq_append_getElem ht, List.prod_append, List.prod_singleton]

private lemma list_prod_drop_take_succ {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Matrix α α ℤ)) (k t : ℕ) (hkt : k ≤ t) (ht : t < L.length) :
    ((L.drop k).take (t + 1 - k)).prod = ((L.drop k).take (t - k)).prod * L[t] := by
  have h1 : t + 1 - k = (t - k) + 1 := by omega
  have hlt : t - k < (L.drop k).length := by simp; omega
  rw [h1, List.take_succ_eq_append_getElem hlt, List.prod_append, List.prod_singleton]
  simp [Nat.add_sub_of_le hkt]

private lemma list_prod_telescoping {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (A : Fin n → Matrix α α ℤ) (E : Matrix α α ℤ) :
    let Q : Matrix α α ℤ := 1 - E
    ∀ t : ℕ, t ≤ n →
    ((List.ofFn A).take t).prod - ((List.ofFn (fun i => Q * A i)).take t).prod =
      ∑ k : Fin t,
        ((List.ofFn (fun i => Q * A i)).take k.val).prod * E *
        (((List.ofFn A).drop k.val).take (t - k.val)).prod := by
  intro Q t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : t < n := by omega
    have hL1 : t < (List.ofFn A).length := by simp [ht']
    have hL2 : t < (List.ofFn (fun i => Q * A i)).length := by simp [ht']
    rw [list_prod_take_succ _ t hL1, list_prod_take_succ _ t hL2]
    simp only [List.getElem_ofFn]
    have hsplit : ((List.ofFn A).take t).prod * A ⟨t, ht'⟩ -
        ((List.ofFn (fun i => Q * A i)).take t).prod * (Q * A ⟨t, ht'⟩) =
        (((List.ofFn A).take t).prod - ((List.ofFn (fun i => Q * A i)).take t).prod) * A ⟨t, ht'⟩ +
        ((List.ofFn (fun i => Q * A i)).take t).prod * E * A ⟨t, ht'⟩ := by
      simp only [Q, sub_mul, one_mul, mul_sub, Matrix.mul_assoc]
      abel
    rw [hsplit, ih (by omega), Fin.sum_univ_castSucc, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.val_castSucc, Matrix.mul_assoc]
      congr 2
      rw [list_prod_drop_take_succ (List.ofFn A) k.val t (by omega) hL1, List.getElem_ofFn]
    · simp only [Fin.val_last]
      have h1 : t + 1 - t = 1 := by omega
      have hdrop : (((List.ofFn A).drop t).take 1).prod = A ⟨t, ht'⟩ := by
        have hlt : 0 < ((List.ofFn A).drop t).length := by simp; omega
        rw [List.take_succ_eq_append_getElem hlt]
        simp
      rw [h1, hdrop]

private lemma trace_rank1_mul {α : Type*} [Fintype α] [DecidableEq α]
    (z₀ : α) (X : Matrix α α ℤ) :
    Matrix.trace (Matrix.of (fun r c : α => if r = z₀ ∧ c = z₀ then (1 : ℤ) else 0) * X) =
      X z₀ z₀ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single z₀]
  · rw [Finset.sum_eq_single z₀]
    · simp
    · intro c _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ z₀) h
  · intro r _ hne
    refine Finset.sum_eq_zero fun c _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ z₀) h

private lemma trace_telescoping {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (A : Fin n → Matrix α α ℤ) (z₀ : α) :
    let E : Matrix α α ℤ := Matrix.of (fun r c => if r = z₀ ∧ c = z₀ then 1 else 0)
    let Q : Matrix α α ℤ := 1 - E
    Matrix.trace (List.ofFn A).prod - Matrix.trace (List.ofFn (fun i => Q * A i)).prod =
      ∑ k : Fin n,
        (((List.ofFn A).drop k.val).prod * ((List.ofFn (fun i => Q * A i)).take k.val).prod) z₀ z₀ := by
  intro E Q
  have h := list_prod_telescoping n A E n (le_refl n)
  rw [List.take_of_length_le (by simp : (List.ofFn A).length ≤ n),
      List.take_of_length_le (by simp : (List.ofFn (fun i => (1 - E) * A i)).length ≤ n)] at h
  have htr : Matrix.trace ((List.ofFn A).prod - (List.ofFn (fun i => Q * A i)).prod) =
      Matrix.trace (∑ k : Fin n,
        ((List.ofFn (fun i => Q * A i)).take k.val).prod * E *
        (((List.ofFn A).drop k.val).take (n - k.val)).prod) := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_sum] at htr
  rw [htr]
  refine Finset.sum_congr rfl fun k _ => ?_
  have htake : ((List.ofFn A).drop k.val).take (n - k.val) = (List.ofFn A).drop k.val := by
    apply List.take_of_length_le
    simp
  rw [htake, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  exact trace_rank1_mul z₀ _

private lemma list_prod_intertwine {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (P : Matrix α β ℤ) (L₁ : List (Matrix α α ℤ)) (L₂ : List (Matrix β β ℤ))
    (hlen : L₁.length = L₂.length)
    (hstep : ∀ i : ℕ, (h1 : i < L₁.length) → (h2 : i < L₂.length) → L₁[i] * P = P * L₂[i]) :
    L₁.prod * P = P * L₂.prod := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons A₁ t₁ ih =>
    cases L₂ with
    | nil => simp at hlen
    | cons A₂ t₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [List.prod_cons, List.prod_cons, Matrix.mul_assoc]
      rw [ih t₂ hlen (fun i h1 h2 => hstep (i + 1) (by simpa using h1) (by simpa using h2))]
      have h0 := hstep 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      rw [← Matrix.mul_assoc, h0, Matrix.mul_assoc]

private lemma list_prod_succ_apply_eq_sum {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (k : ℕ) (M : Fin (k + 1) → Matrix α α ℤ) (s₀ s₁ : α),
    (List.ofFn M).prod s₀ s₁ =
      ∑ traj : Fin k → α,
        M 0 s₀ (if h : 0 < k then traj ⟨0, h⟩ else s₁) *
        ∏ i : Fin k, M i.succ (traj i)
          (if h : i.val + 1 < k then traj ⟨i.val + 1, h⟩ else s₁) := by
  intro k
  induction k with
  | zero =>
    intro M s₀ s₁
    simp
  | succ k ih =>
    intro M s₀ s₁
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih (fun i : Fin (k + 1) => M i.succ) _ s₁]
    let eqv : (Fin (k + 1) → α) ≃ α × (Fin k → α) :=
      { toFun := fun f => (f 0, fun i => f i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun f => by funext i; refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun ⟨a, g⟩ => by ext <;> simp }
    rw [Fintype.sum_equiv eqv _ (fun p =>
      M 0 s₀ p.1 *
      (M (Fin.succ 0) p.1 (if h : 0 < k then p.2 ⟨0, h⟩ else s₁) *
        ∏ i : Fin k, M i.succ.succ (p.2 i)
          (if h : i.val + 1 < k then p.2 ⟨i.val + 1, h⟩ else s₁)))]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
    · intro f
      simp only [eqv, Equiv.coe_fn_mk, Nat.zero_lt_succ, ↓reduceDIte]
      rw [Fin.prod_univ_succ]
      congr 1
      cases k with
      | zero => simp
      | succ k' =>
        simp only [Fin.val_zero, zero_add, Nat.succ_lt_succ_iff, Nat.zero_lt_succ, ↓reduceDIte,
          Fin.val_succ, add_lt_add_iff_right]
        rfl

private lemma trace_list_prod_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 0 < n) (M : Fin n → Matrix α α ℤ) :
    Matrix.trace (List.ofFn M).prod =
      ∑ v : Fin n → α, ∏ i : Fin n,
        M i (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [list_prod_succ_apply_eq_sum k M]
  let eqv : (Fin (k + 1) → α) ≃ α × (Fin k → α) :=
    { toFun := fun f => (f 0, fun i => f i.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun f => by funext i; refine Fin.cases ?_ ?_ i <;> simp
      right_inv := fun ⟨a, g⟩ => by ext <;> simp }
  rw [Fintype.sum_equiv eqv _ (fun p =>
    M 0 p.1 (if h : 0 < k then p.2 ⟨0, h⟩ else p.1) *
    ∏ i : Fin k, M i.succ (p.2 i)
      (if h : i.val + 1 < k then p.2 ⟨i.val + 1, h⟩ else p.1))]
  · rw [Fintype.sum_prod_type]
  · intro v
    simp only [eqv, Equiv.coe_fn_mk]
    rw [Fin.prod_univ_succ]
    congr 1
    · by_cases hk : 0 < k
      · simp only [hk, ↓reduceDIte]
        congr 2; apply Fin.ext; dsimp; exact Nat.mod_eq_of_lt (by omega)
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [lt_self_iff_false, ↓reduceDIte]
        congr 2
    · refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i.val + 1 < k
      · simp only [h, ↓reduceDIte]
        congr 2; apply Fin.ext; dsimp; exact Nat.mod_eq_of_lt (by omega)
      · simp only [h, ↓reduceDIte]
        have heq : i.val + 1 = k := by omega
        congr 2; apply Fin.ext; dsimp
        have h1 : i.val + 1 + 1 = k + 1 := by omega
        rw [h1, Nat.mod_self]

private lemma poly_eq_of_eval_pow2 (P Q : Polynomial ℤ)
    (h : ∀ j : ℕ, P.eval ((2 : ℤ) ^ j) = Q.eval ((2 : ℤ) ^ j)) : P = Q := by
  by_contra hne
  have hsub_ne : P - Q ≠ 0 := sub_ne_zero.mpr hne
  let d := (P - Q).natDegree + 1
  let S : Finset ℤ := (Finset.range d).image (fun j : ℕ => (2 : ℤ) ^ j)
  have hinj : Function.Injective (fun j : ℕ => (2 : ℤ) ^ j) := by
    intro a b hab
    have hnat : (2 : ℕ) ^ a = (2 : ℕ) ^ b := Int.ofNat.inj (by simpa using hab)
    exact Nat.pow_right_injective (by omega : 2 ≤ 2) hnat
  have hScard : S.card = d := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hSsub : S ⊆ (P - Q).roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub_ne, Polynomial.IsRoot,
      Polynomial.eval_sub, h j, sub_self]
  have hle1 : S.card ≤ (P - Q).roots.toFinset.card := Finset.card_le_card hSsub
  have hle2 : (P - Q).roots.toFinset.card ≤ (P - Q).roots.card := Multiset.toFinset_card_le _
  have hle3 : (P - Q).roots.card ≤ (P - Q).natDegree := Polynomial.card_roots' (P - Q)
  omega

open Classical in
private lemma walk_eq_sum_iso_at_pow2 {n m : ℕ} (hn : 0 < n)
    (H : Matrix (Fin m) (Fin n) (ZMod 2)) (j : ℕ)
    (D : Submodule (ZMod 2) (Fin m → ZMod 2))
    (ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2))
    (hker : LinearMap.ker ψ = D) :
    let B := (Fin m → ZMod 2) ⧸ D
    letI : Fintype B := Fintype.ofFinite _
    let next := fun i : Fin n => (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let col := fun (i : Fin n) (a : Fin m) => H a i
    let total : Fin m → ZMod 2 := ∑ i : Fin n, col i
    let symbol := fun i : Fin n => D.mkQ (col i)
    let closeRun := fun b : B => if b = 0 then (2 : ℤ) ^ j - 1 else -1
    let T : Fin n → Matrix (Option B) (Option B) ℤ := fun i before after =>
      before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
        (fun a => after.elim (closeRun a) (fun b => if b = a + symbol i then 1 else 0))
    let Iso := (Finset.univ : Finset (Fin n → Fin j → ZMod 2)).filter
      (fun v => ∀ (r s : Fin j) (i : Fin n), v i r * v (next i) s = v (next i) r * v i s)
    Matrix.trace (List.ofFn T).prod + closeRun (D.mkQ total) -
        (if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0) =
      ∑ v ∈ Iso, ∏ i : Fin n, chi (dot (v i) (ψ (col i))) := by
  intro B
  let : Fintype B := Fintype.ofFinite _
  intro next col total symbol closeRun T Iso
  let ψbar : B →ₗ[ZMod 2] (Fin j → ZMod 2) := D.liftQ ψ (le_of_eq hker.symm)
  have hψbar_inj : Function.Injective ψbar := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker]; simp
  have hψbar_zero : ∀ b : B, ψbar b = 0 ↔ b = 0 := fun b => by
    rw [← map_zero ψbar, hψbar_inj.eq_iff]
  have hψbar_sym : ∀ i : Fin n, ψbar (symbol i) = ψ (col i) := fun i => rfl
  have hclose_eq : ∀ b : B, closeRun b =
      ∑ c ∈ (Finset.univ : Finset (Fin j → ZMod 2)).erase 0, chi (dot c (ψbar b)) := by
    intro b
    rw [sum_chi_dot_nz]
    simp only [closeRun, hψbar_zero]

  let M : Fin n → Matrix (Fin j → ZMod 2) (Fin j → ZMod 2) ℤ := fun i c₁ c₂ =>
    if c₁ = 0 ∨ c₂ = 0 ∨ c₁ = c₂ then chi (dot c₂ (ψ (col i))) else 0
  let P : Matrix (Option B) (Fin j → ZMod 2) ℤ := fun s c =>
    match s with
    | none => if c = 0 then 1 else 0
    | some a => if c = 0 then 0 else chi (dot c (ψbar a))

  have htrM : Matrix.trace (List.ofFn M).prod =
      ∑ v ∈ Iso, ∏ i : Fin n, chi (dot (v i) (ψ (col i))) := by
    rw [trace_list_prod_eq_sum hn M]
    change (∑ v : Fin n → Fin j → ZMod 2, ∏ i : Fin n, M i (v i) (v (next i))) = _

    let nextEquiv : Fin n ≃ Fin n :=
      { toFun := next
        invFun := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩
        left_inv := fun i => by
          ext; dsimp [next]
          have hi := i.isLt
          by_cases h1 : i.val + 1 < n
          · rw [Nat.mod_eq_of_lt h1]
            have : i.val + 1 + n - 1 = i.val + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
          · have heq : i.val + 1 = n := by omega
            rw [heq, Nat.mod_self, zero_add]
            have : n - 1 < n := by omega
            rw [Nat.mod_eq_of_lt this]; omega
        right_inv := fun i => by
          ext; dsimp [next]
          have hi := i.isLt
          by_cases h0 : i.val = 0
          · rw [h0, zero_add]
            have : n - 1 < n := by omega
            rw [Nat.mod_eq_of_lt this]
            have : n - 1 + 1 = n := by omega
            rw [this, Nat.mod_self]
          · have h1 : i.val + n - 1 = (i.val - 1) + n := by omega
            have hlt1 : i.val - 1 < n := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
            have h2 : i.val - 1 + 1 = i.val := by omega
            rw [h2, Nat.mod_eq_of_lt hi] }
    have hshift' : (∑ v : Fin n → Fin j → ZMod 2, ∏ i : Fin n, M i (v i) (v (next i))) =
        ∑ u : Fin n → Fin j → ZMod 2, ∏ i : Fin n, M i (u (nextEquiv.symm i)) (u i) := by
      let eShift : (Fin n → Fin j → ZMod 2) ≃ (Fin n → Fin j → ZMod 2) :=
        { toFun := fun v i => v (next i)
          invFun := fun u i => u (nextEquiv.symm i)
          left_inv := fun v => funext fun i => congrArg v (nextEquiv.apply_symm_apply i)
          right_inv := fun u => funext fun i => congrArg u (nextEquiv.symm_apply_apply i) }
      refine Fintype.sum_equiv eShift _ _ fun v => ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      exact congrArg (fun x => M i (v x) (v (next i))) (nextEquiv.apply_symm_apply i).symm
    rw [hshift']
    rw [← Finset.sum_filter_of_ne (p := fun u => (∏ i : Fin n, M i (u (nextEquiv.symm i)) (u i)) ≠ 0)]
    · rw [Finset.sum_congr (s₂ := Iso)]
      · ext u
        simp only [Iso, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hprod r s i
          have hnz : ∀ k : Fin n, u (nextEquiv.symm k) = 0 ∨ u k = 0 ∨ u (nextEquiv.symm k) = u k := by
            intro k
            by_contra hbad
            apply hprod
            exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [M, hbad])
          have hk := hnz (next i)
          have hinv : nextEquiv.symm (next i) = i := nextEquiv.symm_apply_apply i
          rw [hinv] at hk
          exact (iso_pair_iff (u i) (u (next i))).mpr hk r s
        · intro hiso
          have hne0 : ∀ k : Fin n, M k (u (nextEquiv.symm k)) (u k) ≠ 0 := by
            intro k
            have hcond : u (nextEquiv.symm k) = 0 ∨ u k = 0 ∨ u (nextEquiv.symm k) = u k := by
              have h1 := (iso_pair_iff (u (nextEquiv.symm k)) (u (next (nextEquiv.symm k)))).mp
                (fun r s => hiso r s (nextEquiv.symm k))
              have h2 : next (nextEquiv.symm k) = k := nextEquiv.apply_symm_apply k
              rwa [h2] at h1
            simp only [M, hcond, ↓reduceIte, chi]
            split_ifs <;> decide
          exact Finset.prod_ne_zero_iff.mpr fun k _ => hne0 k
      · intro u hu
        have hiso := (Finset.mem_filter.mp hu).2
        refine Finset.prod_congr rfl fun k _ => ?_
        have hcond : u (nextEquiv.symm k) = 0 ∨ u k = 0 ∨ u (nextEquiv.symm k) = u k := by
          have h1 := (iso_pair_iff (u (nextEquiv.symm k)) (u (next (nextEquiv.symm k)))).mp
            (fun r s => hiso r s (nextEquiv.symm k))
          have h2 : next (nextEquiv.symm k) = k := nextEquiv.apply_symm_apply k
          rwa [h2] at h1
        simp [M, hcond]
    · intro u _ hne; exact hne

  have hinter : ∀ i : Fin n, T i * P = P * M i := by
    intro i
    ext s c'
    simp only [Matrix.mul_apply]
    cases s with
    | none =>

      have hlhs : (∑ s' : Option B, T i none s' * P s' c') =
          P none c' + P (some (symbol i)) c' := by
        rw [Fintype.sum_option]
        simp only [T, Option.elim_none, Option.elim_some, one_mul]
        congr 1
        rw [Finset.sum_eq_single (symbol i)]
        · simp
        · intro b _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ (symbol i)) h
      have hrhs : (∑ c : Fin j → ZMod 2, P none c * M i c c') = M i 0 c' := by
        rw [Finset.sum_eq_single 0]
        · simp [P]
        · intro c _ hne; simp [P, hne]
        · intro h; exact absurd (Finset.mem_univ 0) h
      rw [hlhs, hrhs]
      by_cases hc' : c' = 0
      · subst hc'; simp [P, M, dot_zero_left, chi_zero]
      · simp [P, M, hc', hψbar_sym]
    | some a =>
      have hlhs : (∑ s' : Option B, T i (some a) s' * P s' c') =
          closeRun a * P none c' + P (some (a + symbol i)) c' := by
        rw [Fintype.sum_option]
        simp only [T, Option.elim_some, Option.elim_none]
        congr 1
        rw [Finset.sum_eq_single (a + symbol i)]
        · simp
        · intro b _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ (a + symbol i)) h
      rw [hlhs]
      by_cases hc' : c' = 0
      · subst hc'
        simp only [P, ↓reduceIte, mul_one, add_zero]
        rw [hclose_eq a, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → ZMod 2))]
        simp only [↓reduceIte, zero_mul, zero_add]
        refine Finset.sum_congr rfl fun c hc => ?_
        have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
        simp [M, hc0, dot_zero_left, chi_zero]
      · simp only [P, hc', ↓reduceIte, mul_zero, zero_add]
        rw [Finset.sum_eq_single c']
        · simp only [hc', ↓reduceIte, M, or_true, map_add, hψbar_sym]
          rw [dot_add_right, chi_add]
        · intro c _ hne
          by_cases hc0 : c = 0
          · simp [hc0]
          · simp [hc0, M, hc', hne]
        · intro h; exact absurd (Finset.mem_univ c') h

  let E_Z : Matrix (Fin j → ZMod 2) (Fin j → ZMod 2) ℤ := Matrix.of (fun r c => if r = 0 ∧ c = 0 then 1 else 0)
  let Q_Z : Matrix (Fin j → ZMod 2) (Fin j → ZMod 2) ℤ := 1 - E_Z
  let E_B : Matrix (Option B) (Option B) ℤ :=
    Matrix.of (fun r c => if r = none ∧ c = none then 1 else 0)
  let Q_B : Matrix (Option B) (Option B) ℤ := 1 - E_B
  have hEP : E_B * P = P * E_Z := by
    ext s c
    simp only [Matrix.mul_apply, E_B, E_Z, Matrix.of_apply]
    cases s with
    | none =>
      rw [Finset.sum_eq_single none, Finset.sum_eq_single 0]
      · by_cases hc : c = 0 <;> simp [P, hc]
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ 0) h
      · intro s' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ none) h
    | some a =>
      have hl : (∑ s' : Option B, (if (some a : Option B) = none ∧ s' = none then (1 : ℤ) else 0) * P s' c) = 0 :=
        Finset.sum_eq_zero fun _ _ => by simp
      have hr : (∑ c' : Fin j → ZMod 2, P (some a) c' * (if c' = 0 ∧ c = 0 then (1 : ℤ) else 0)) = 0 :=
        Finset.sum_eq_zero fun c' _ => by
          by_cases hc' : c' = 0 <;> simp [P, hc']
      rw [hl, hr]
  have hQP : Q_B * P = P * Q_Z := by
    dsimp only [Q_B, Q_Z]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hEP]
  have hQM_inter : ∀ i : Fin n, (Q_B * T i) * P = P * (Q_Z * M i) := fun i => by
    rw [Matrix.mul_assoc, hinter i, ← Matrix.mul_assoc, hQP, Matrix.mul_assoc]

  have htel_M : Matrix.trace (List.ofFn M).prod - Matrix.trace (List.ofFn (fun i => Q_Z * M i)).prod =
      ∑ k : Fin n, (((List.ofFn M).drop k.val).prod * ((List.ofFn (fun i => Q_Z * M i)).take k.val).prod) 0 0 :=
    trace_telescoping n M (0 : Fin j → ZMod 2)
  have htel_T : Matrix.trace (List.ofFn T).prod - Matrix.trace (List.ofFn (fun i => Q_B * T i)).prod =
      ∑ k : Fin n, (((List.ofFn T).drop k.val).prod * ((List.ofFn (fun i => Q_B * T i)).take k.val).prod) none none :=
    trace_telescoping n T (none : Option B)
  have htel_eq : Matrix.trace (List.ofFn M).prod - Matrix.trace (List.ofFn (fun i => Q_Z * M i)).prod =
      Matrix.trace (List.ofFn T).prod - Matrix.trace (List.ofFn (fun i => Q_B * T i)).prod := by
    rw [htel_M, htel_T]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdrop : ((List.ofFn T).drop k.val).prod * P = P * ((List.ofFn M).drop k.val).prod := by
      apply list_prod_intertwine P _ _ (by simp)
      intro i h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      exact hinter ⟨k.val + i, by simp at h1; omega⟩
    have htake : ((List.ofFn (fun i => Q_B * T i)).take k.val).prod * P =
        P * ((List.ofFn (fun i => Q_Z * M i)).take k.val).prod := by
      apply list_prod_intertwine P _ _ (by simp)
      intro i h1 h2
      simp only [List.getElem_take, List.getElem_ofFn]
      exact hQM_inter ⟨i, by simp at h1; omega⟩
    have hprod_inter :
        (((List.ofFn T).drop k.val).prod * ((List.ofFn (fun i => Q_B * T i)).take k.val).prod) * P =
        P * (((List.ofFn M).drop k.val).prod * ((List.ofFn (fun i => Q_Z * M i)).take k.val).prod) := by
      rw [Matrix.mul_assoc, htake, ← Matrix.mul_assoc, hdrop, Matrix.mul_assoc]
    have hentry := congrFun (congrFun hprod_inter none) (0 : Fin j → ZMod 2)
    have hl : ((((List.ofFn T).drop k.val).prod * ((List.ofFn (fun i => Q_B * T i)).take k.val).prod) * P) none 0 =
        (((List.ofFn T).drop k.val).prod * ((List.ofFn (fun i => Q_B * T i)).take k.val).prod) none none := by
      rw [Matrix.mul_apply, Finset.sum_eq_single none]
      · simp [P]
      · intro s _ hne; cases s with | none => exact absurd rfl hne | some a => simp [P]
      · intro h; exact absurd (Finset.mem_univ none) h
    have hr : (P * (((List.ofFn M).drop k.val).prod * ((List.ofFn (fun i => Q_Z * M i)).take k.val).prod)) none 0 =
        (((List.ofFn M).drop k.val).prod * ((List.ofFn (fun i => Q_Z * M i)).take k.val).prod) 0 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single 0]
      · simp [P]
      · intro c _ hne; simp [P, hne]
      · intro h; exact absurd (Finset.mem_univ 0) h
    rw [hl, hr] at hentry
    exact hentry.symm

  have hQM_zero : ∀ (i : Fin n) (c₂ : Fin j → ZMod 2), (Q_Z * M i) 0 c₂ = 0 := by
    intro i c₂
    simp only [Q_Z, E_Z, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = 0 <;> simp [hc, Ne.symm]
  have hQM_nz : ∀ (i : Fin n) (c₁ c₂ : Fin j → ZMod 2), c₁ ≠ 0 → (Q_Z * M i) c₁ c₂ = M i c₁ c₂ := by
    intro i c₁ c₂ hc₁
    simp only [Q_Z, E_Z, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single c₁]
    · simp [hc₁]
    · intro c _ hne; simp [hc₁, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ c₁) h
  have htr_QM : Matrix.trace (List.ofFn (fun i => Q_Z * M i)).prod = closeRun (D.mkQ total) := by
    rw [trace_list_prod_eq_sum hn (fun i => Q_Z * M i)]
    change (∑ v : Fin n → Fin j → ZMod 2, ∏ i : Fin n, (Q_Z * M i) (v i) (v (next i))) = _
    let ConstNZ : Finset (Fin n → Fin j → ZMod 2) :=
      ((Finset.univ : Finset (Fin j → ZMod 2)).erase 0).image (fun c => fun _ : Fin n => c)
    have hvan : ∀ v : Fin n → Fin j → ZMod 2, v ∉ ConstNZ →
        (∏ i : Fin n, (Q_Z * M i) (v i) (v (next i))) = 0 := by
      intro v hv
      by_cases h0 : ∃ i : Fin n, v i = 0
      · rcases h0 with ⟨i, hi⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hQM_zero])
      · push Not at h0
        have hne_adj : ∃ i : Fin n, v i ≠ v (next i) := by
          by_contra hall
          push Not at hall
          have hconst : ∀ t : ℕ, (ht : t < n) → v ⟨t, ht⟩ = v ⟨0, hn⟩ := by
            intro t
            induction t with
            | zero => intro _; rfl
            | succ t ih =>
              intro ht
              have h1 := hall ⟨t, by omega⟩
              have hnext : next ⟨t, by omega⟩ = ⟨t + 1, ht⟩ := by
                ext; dsimp [next]; exact Nat.mod_eq_of_lt ht
              rw [hnext] at h1
              exact h1.symm.trans (ih (by omega))
          apply hv
          refine Finset.mem_image.mpr ⟨v ⟨0, hn⟩, Finset.mem_erase.mpr ⟨h0 ⟨0, hn⟩, Finset.mem_univ _⟩, ?_⟩
          funext i; exact (hconst i.val i.isLt).symm
        rcases hne_adj with ⟨i, hi⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by
          rw [hQM_nz i (v i) (v (next i)) (h0 i)]
          simp [M, h0 i, h0 (next i), hi])
    rw [← Finset.sum_subset (Finset.subset_univ ConstNZ) (fun v _ hv => hvan v hv)]
    rw [Finset.sum_image (fun c₁ _ c₂ _ heq => congrFun heq ⟨0, hn⟩)]
    rw [hclose_eq (D.mkQ total)]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    have hprod : (∏ i : Fin n, (Q_Z * M i) c c) = ∏ i : Fin n, chi (dot c (ψ (col i))) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hQM_nz i c c hc0]
      simp [M]
    rw [hprod, ← chi_sum]
    have hdot_sum : (∑ i : Fin n, dot c (ψ (col i))) = dot c (ψbar (D.mkQ total)) := by
      have hψtot : ψbar (D.mkQ total) = ∑ i : Fin n, ψ (col i) := by
        change ψ total = _
        simp [total, map_sum]
      rw [hψtot]
      simp only [dot, Finset.sum_apply, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hdot_sum]

  have hQT_none : ∀ (i : Fin n) (s₂ : Option B), (Q_B * T i) none s₂ = 0 := by
    intro i s₂
    simp only [Q_B, E_B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    cases s <;> simp
  have hQT_some : ∀ (i : Fin n) (a : B) (s₂ : Option B), (Q_B * T i) (some a) s₂ = T i (some a) s₂ := by
    intro i a s₂
    simp only [Q_B, E_B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single (some a)]
    · simp
    · intro s _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ (some a)) h
  have htr_QT : Matrix.trace (List.ofFn (fun i => Q_B * T i)).prod =
      if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0 := by
    rw [trace_list_prod_eq_sum hn (fun i => Q_B * T i)]
    change (∑ v : Fin n → Option B, ∏ i : Fin n, (Q_B * T i) (v i) (v (next i))) = _
    let psum (t : ℕ) : B := ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < t), symbol i
    have hpsum_zero : psum 0 = 0 := by simp [psum]
    have hpsum_succ : ∀ t : ℕ, (ht : t < n) → psum (t + 1) = psum t + symbol ⟨t, ht⟩ := by
      intro t ht
      have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < t + 1) =
          insert ⟨t, ht⟩ ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < t)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨t, ht⟩ : Fin n) ∉ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < t) := by
        simp
      simp only [psum, hfilt, Finset.sum_insert hnotmem, add_comm]
    have hpsum_n : psum n = D.mkQ total := by
      have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n) = Finset.univ := by
        ext i; simp
      simp only [psum, hfilt, total, symbol, map_sum]
    have hchar : ∀ s : Fin n → Option B,
        (∏ i : Fin n, (Q_B * T i) (s i) (s (next i))) ≠ 0 →
        D.mkQ total = 0 ∧ ∃ a₀ : B, ∀ i : Fin n, s i = some (a₀ + psum i.val) := by
      intro s hne
      have hall_ne : ∀ i : Fin n, (Q_B * T i) (s i) (s (next i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hne |> fun h i => h i (Finset.mem_univ i)
      have hall_some : ∀ i : Fin n, ∃ a : B, s i = some a := by
        intro i
        cases hs : s i with
        | none => exfalso; exact hall_ne i (by rw [hs, hQT_none])
        | some a => exact ⟨a, rfl⟩
      rcases hall_some ⟨0, hn⟩ with ⟨a₀, ha₀⟩
      have hstep : ∀ i : Fin n, ∀ a : B, s i = some a → s (next i) = some (a + symbol i) := by
        intro i a hsi
        rcases hall_some (next i) with ⟨b, hsb⟩
        have h1 := hall_ne i
        rw [hsi, hQT_some, hsb] at h1
        simp only [T, Option.elim_some] at h1
        have hbeq : b = a + symbol i := by
          by_contra hnb; simp [hnb] at h1
        rw [hsb, hbeq]
      have hform : ∀ t : ℕ, (ht : t < n) → s ⟨t, ht⟩ = some (a₀ + psum t) := by
        intro t
        induction t with
        | zero => intro _; rw [hpsum_zero, add_zero]; exact ha₀
        | succ t ih =>
          intro ht
          have h1 := hstep ⟨t, by omega⟩ (a₀ + psum t) (ih (by omega))
          have hnext : next ⟨t, by omega⟩ = ⟨t + 1, ht⟩ := by
            ext; dsimp [next]; exact Nat.mod_eq_of_lt ht
          rw [hnext, add_assoc, ← hpsum_succ t (by omega)] at h1
          exact h1
      have hwrap : s (next ⟨n - 1, by omega⟩) = some (a₀ + D.mkQ total) := by
        have h1 := hstep ⟨n - 1, by omega⟩ (a₀ + psum (n - 1)) (hform (n - 1) (by omega))
        have hps : psum (n - 1) + symbol ⟨n - 1, by omega⟩ = D.mkQ total := by
          have := hpsum_succ (n - 1) (by omega)
          have heq : n - 1 + 1 = n := by omega
          rw [heq, hpsum_n] at this
          exact this.symm
        rw [add_assoc, hps] at h1
        exact h1
      have hnext_last : next ⟨n - 1, by omega⟩ = ⟨0, hn⟩ := by
        ext; dsimp [next]
        have : n - 1 + 1 = n := by omega
        rw [this, Nat.mod_self]
      rw [hnext_last, ha₀] at hwrap
      have hadd : a₀ = a₀ + D.mkQ total := Option.some.inj hwrap
      have htot0 : D.mkQ total = 0 := by
        have h1 : a₀ + 0 = a₀ + D.mkQ total := by simpa using hadd
        exact (add_left_cancel h1).symm
      exact ⟨htot0, a₀, fun i => hform i.val i.isLt⟩
    by_cases htot : D.mkQ total = 0
    · simp only [htot, ↓reduceIte]
      let Trajs : Finset (Fin n → Option B) :=
        Finset.univ.image (fun a₀ : B => fun i : Fin n => some (a₀ + psum i.val))
      rw [← Finset.sum_subset (Finset.subset_univ Trajs)]
      · rw [Finset.sum_image]
        · calc (∑ a₀ : B, ∏ i : Fin n,
                  (Q_B * T i) (some (a₀ + psum i.val)) (some (a₀ + psum (next i).val)))
              = ∑ _a₀ : B, (1 : ℤ) := by
                refine Finset.sum_congr rfl fun a₀ _ => Finset.prod_eq_one fun i _ => ?_
                rw [hQT_some]
                simp only [T, Option.elim_some]
                have hnext_eq : a₀ + psum (next i).val = a₀ + psum i.val + symbol i := by
                  by_cases hlt : i.val + 1 < n
                  · have hnv : (next i).val = i.val + 1 := Nat.mod_eq_of_lt hlt
                    rw [hnv, hpsum_succ i.val i.isLt, add_assoc]
                  · have hi : i.val + 1 = n := by omega
                    have hnv : (next i).val = 0 := by dsimp [next]; rw [hi, Nat.mod_self]
                    rw [hnv, hpsum_zero, add_zero, add_assoc]
                    have hps : psum i.val + symbol i = D.mkQ total := by
                      have := hpsum_succ i.val i.isLt
                      rw [hi, hpsum_n] at this
                      exact this.symm
                    rw [hps, htot, add_zero]
                simp [hnext_eq]
            _ = (Fintype.card B : ℤ) := by simp
        · intro a₁ _ a₂ _ heq
          have h0 := congrFun heq ⟨0, hn⟩
          simpa [hpsum_zero] using h0
      · intro s _ hs
        by_contra hne
        rcases hchar s hne with ⟨_, a₀, ha₀⟩
        exact hs (Finset.mem_image.mpr ⟨a₀, Finset.mem_univ _, funext fun i => (ha₀ i).symm⟩)
    · simp only [htot, ↓reduceIte]
      refine Finset.sum_eq_zero fun s _ => ?_
      by_contra hne
      exact htot (hchar s hne).1
  rw [← htrM]
  rw [htr_QM, htr_QT] at htel_eq
  omega

open Classical in
private lemma identity_at_pow2 {n m : ℕ} (hn : 0 < n)
    (H : Matrix (Fin m) (Fin n) (ZMod 2)) (j : ℕ) :
    letI : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
    letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
    let z : ℤ := (2 : ℤ) ^ j
    let used := fun h : ℕ => ∏ r ∈ Finset.range h, (z - (2 : ℤ) ^ r)
    let next := fun i : Fin n => (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let good := (Finset.univ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))).filter (fun U =>
      (∀ x ∈ U, ∀ a, (∑ i, H a i * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i))
    let col := fun (i : Fin n) (a : Fin m) => H a i
    let total : Fin m → ZMod 2 := ∑ i : Fin n, col i
    let walk := fun D : Submodule (ZMod 2) (Fin m → ZMod 2) =>
      let B := (Fin m → ZMod 2) ⧸ D
      letI : Fintype B := Fintype.ofFinite _
      let symbol := fun i : Fin n => D.mkQ (col i)
      let closeRun := fun b : B => if b = 0 then z - 1 else -1
      let T : Fin n → Matrix (Option B) (Option B) ℤ := fun i before after =>
        before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
          (fun a => after.elim (closeRun a) (fun b => if b = a + symbol i then 1 else 0))
      Matrix.trace (List.ofFn T).prod + closeRun (D.mkQ total) -
        (if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0)
    z ^ m * (∑ U ∈ good, used (Module.finrank (ZMod 2) U)) =
      ∑ D : Submodule (ZMod 2) (Fin m → ZMod 2), used (m - Module.finrank (ZMod 2) D) * walk D := by
  let : Fintype (Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  intro z used next good col total walk
  let Iso := (Finset.univ : Finset (Fin n → Fin j → ZMod 2)).filter
    (fun v => ∀ (r s : Fin j) (i : Fin n), v i r * v (next i) s = v (next i) r * v i s)
  let GoodTuples := (Finset.univ : Finset (Fin j → Fin n → ZMod 2)).filter (fun M =>
    (∀ r a, (∑ i : Fin n, H a i * M r i) = 0) ∧
    (∀ r s i, M r i * M s (next i) = M r (next i) * M s i))

  have hspan_good : ∀ M : Fin j → Fin n → ZMod 2,
      M ∈ GoodTuples ↔ Submodule.span (ZMod 2) (Set.range M) ∈ good := by
    intro M
    simp only [GoodTuples, good, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hcheck, hiso⟩
      constructor
      · intro x hx a
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨r, rfl⟩; exact hcheck r a
        · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        · intro u v _ _ hu hv
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          rw [hu, hv, add_zero]
        · intro c u _ hu
          simp only [Pi.smul_apply, smul_eq_mul]
          have hpull : (∑ i : Fin n, H a i * (c * u i)) = c * ∑ i : Fin n, H a i * u i := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
          rw [hpull, hu, mul_zero]
      · intro x hx y hy i
        refine Submodule.span_induction (p := fun x _ => ∀ y ∈ Submodule.span (ZMod 2) (Set.range M),
            x i * y (next i) = x (next i) * y i) ?_ ?_ ?_ ?_ hx y hy
        · rintro _ ⟨r, rfl⟩ y hy
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
          · rintro _ ⟨s, rfl⟩; exact hiso r s i
          · simp only [Pi.zero_apply, mul_zero]
          · intro u v _ _ hu hv
            simp only [Pi.add_apply, mul_add]
            rw [hu, hv]
          · intro c u _ hu
            simp only [Pi.smul_apply, smul_eq_mul]
            calc M r i * (c * u (next i)) = c * (M r i * u (next i)) := by ring
              _ = c * (M r (next i) * u i) := by rw [hu]
              _ = M r (next i) * (c * u i) := by ring
        · intro y _; simp only [Pi.zero_apply, zero_mul]
        · intro u v _ _ hu hv y hy
          simp only [Pi.add_apply, add_mul]
          rw [hu y hy, hv y hy]
        · intro c u _ hu y hy
          simp only [Pi.smul_apply, smul_eq_mul]
          calc c * u i * y (next i) = c * (u i * y (next i)) := by ring
            _ = c * (u (next i) * y i) := by rw [hu y hy]
            _ = c * u (next i) * y i := by ring
    · rintro ⟨hcheck, hiso⟩
      exact ⟨fun r a => hcheck (M r) (Submodule.subset_span ⟨r, rfl⟩) a,
             fun r s i => hiso (M r) (Submodule.subset_span ⟨r, rfl⟩)
               (M s) (Submodule.subset_span ⟨s, rfl⟩) i⟩

  have hLHS_count : (∑ U ∈ good, used (Module.finrank (ZMod 2) U)) = (GoodTuples.card : ℤ) := by
    have hfiber : ∀ U ∈ good, used (Module.finrank (ZMod 2) U) =
        ((GoodTuples.filter (fun M => Submodule.span (ZMod 2) (Set.range M) = U)).card : ℤ) := by
      intro U hU
      have hfilt : GoodTuples.filter (fun M => Submodule.span (ZMod 2) (Set.range M) = U) =
          Finset.univ.filter (fun M => Submodule.span (ZMod 2) (Set.range M) = U) := by
        ext M
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro hsp; exact (hspan_good M).mpr (hsp.symm ▸ hU)
      rw [hfilt, ← Fintype.card_subtype]
      convert (card_spanning_tuples U j).symm using 2
    rw [Finset.sum_congr rfl hfiber]
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.card_biUnion]
    · congr 1
      ext M
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨U, _, hMG, _⟩; exact hMG
      · intro hMG; exact ⟨Submodule.span (ZMod 2) (Set.range M), (hspan_good M).mp hMG, hMG, rfl⟩
    · intro U₁ _ U₂ _ hne
      exact Finset.disjoint_left.mpr fun M h1 h2 =>
        hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

  have hfourier : ∀ v : Fin n → Fin j → ZMod 2,
      (∑ ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2), ∏ i : Fin n, chi (dot (v i) (ψ (col i)))) =
        if (∀ r a, (∑ i : Fin n, H a i * v i r) = 0) then z ^ m else 0 := by
    intro v
    let linEquiv : ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2)) ≃ (Fin m → Fin j → ZMod 2) :=
      { toFun := fun ψ a r => ψ (Pi.single a 1) r
        invFun := fun φ =>
          { toFun := fun w r => ∑ a : Fin m, w a * φ a r
            map_add' := fun w₁ w₂ => by funext r; simp [add_mul, Finset.sum_add_distrib]
            map_smul' := fun c w => by
              funext r; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring }
        left_inv := fun ψ => by
          apply LinearMap.ext
          intro w
          funext r
          have hw : w = ∑ a : Fin m, w a • Pi.single a (1 : ZMod 2) := by
            funext a₀; simp [Finset.sum_apply, Pi.single_apply]
          conv_rhs => rw [hw]
          simp [map_sum, map_smul, Finset.sum_apply]
        right_inv := fun φ => by
          funext a₀ r
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
          rw [Finset.sum_eq_single a₀]
          · simp [Pi.single_eq_same]
          · intro a _ hne; simp [Pi.single_eq_of_ne hne]
          · intro h; exact absurd (Finset.mem_univ a₀) h }
    rw [Fintype.sum_equiv linEquiv _ (fun φ =>
      ∏ a : Fin m, ∏ r : Fin j, chi (φ a r * ∑ i : Fin n, H a i * v i r))]
    · have hprod : ∀ a : Fin m,
          (∑ row : Fin j → ZMod 2, ∏ r : Fin j, chi (row r * ∑ i : Fin n, H a i * v i r)) =
            if (∀ r : Fin j, (∑ i : Fin n, H a i * v i r) = 0) then z else 0 := by
        intro a
        rw [← Fintype.prod_sum (fun r b => chi (b * ∑ i : Fin n, H a i * v i r))]
        simp_rw [sum_chi_mul]
        by_cases ha : ∀ r : Fin j, (∑ i : Fin n, H a i * v i r) = 0
        · simp [ha, z]
        · simp only [ha, ↓reduceIte]
          push Not at ha
          rcases ha with ⟨r₀, hr₀⟩
          exact Finset.prod_eq_zero (Finset.mem_univ r₀) (by simp [hr₀])
      rw [← Fintype.prod_sum (fun (a : Fin m) (row : Fin j → ZMod 2) =>
        ∏ r : Fin j, chi (row r * ∑ i : Fin n, H a i * v i r))]
      simp_rw [hprod]
      by_cases hall : ∀ r a, (∑ i : Fin n, H a i * v i r) = 0
      · simp [hall]
      · simp only [hall, ↓reduceIte]
        push Not at hall
        rcases hall with ⟨r₀, a₀, ha₀⟩
        refine Finset.prod_eq_zero (Finset.mem_univ a₀) ?_
        have hnot : ¬ ∀ r : Fin j, (∑ i : Fin n, H a₀ i * v i r) = 0 := fun h => ha₀ (h r₀)
        simp [hnot]
    · intro ψ
      have hψeq : ∀ i r, ψ (col i) r = ∑ a : Fin m, H a i * linEquiv ψ a r := by
        intro i r
        have hcol : col i = ∑ a : Fin m, H a i • Pi.single a (1 : ZMod 2) := by
          funext a₀; simp [col, Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hcol]
        simp [linEquiv, map_sum, map_smul, Finset.sum_apply]
      rw [← chi_sum]
      have hprod_chi : (∏ a : Fin m, ∏ r : Fin j, chi (linEquiv ψ a r * ∑ i : Fin n, H a i * v i r)) =
          chi (∑ a : Fin m, ∑ r : Fin j, linEquiv ψ a r * ∑ i : Fin n, H a i * v i r) := by
        rw [chi_sum]
        refine Finset.prod_congr rfl fun a _ => (chi_sum Finset.univ _).symm
      rw [hprod_chi]
      congr 1
      calc (∑ i : Fin n, dot (v i) (ψ (col i)))
          = ∑ i : Fin n, ∑ r : Fin j, ∑ a : Fin m, linEquiv ψ a r * (H a i * v i r) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
            rw [hψeq i r, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
        _ = ∑ a : Fin m, ∑ r : Fin j, ∑ i : Fin n, linEquiv ψ a r * (H a i * v i r) := by
            rw [Finset.sum_comm]
            trans (∑ r : Fin j, ∑ a : Fin m, ∑ i : Fin n, linEquiv ψ a r * (H a i * v i r))
            · refine Finset.sum_congr rfl fun r _ => Finset.sum_comm
            · exact Finset.sum_comm
        _ = ∑ a : Fin m, ∑ r : Fin j, linEquiv ψ a r * ∑ i : Fin n, H a i * v i r := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ =>
              (Finset.mul_sum _ _ _).symm

  have htranspose : z ^ m * (GoodTuples.card : ℤ) =
      ∑ v ∈ Iso, if (∀ r a, (∑ i : Fin n, H a i * v i r) = 0) then z ^ m else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    let tr : (Fin j → Fin n → ZMod 2) ≃ (Fin n → Fin j → ZMod 2) := Equiv.piComm (fun _ _ => ZMod 2)
    have hcard : GoodTuples.card =
        (Iso.filter (fun v => ∀ r a, (∑ i : Fin n, H a i * v i r) = 0)).card := by
      refine Finset.card_bij (fun M _ => tr M) ?_ ?_ ?_
      · intro M hM
        simp only [GoodTuples, Iso, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
        exact ⟨fun r s i => hM.2 r s i, hM.1⟩
      · intro M₁ _ M₂ _ heq; exact tr.injective heq
      · intro v hv
        simp only [GoodTuples, Iso, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨tr.symm v, ⟨hv.2, hv.1⟩, tr.apply_symm_apply v⟩
    rw [hcard]

  rw [hLHS_count, htranspose]
  simp_rw [← hfourier]
  rw [Finset.sum_comm]
  have hgroup : (∑ ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2),
        ∑ v ∈ Iso, ∏ i : Fin n, chi (dot (v i) (ψ (col i)))) =
      ∑ D : Submodule (ZMod 2) (Fin m → ZMod 2),
        ∑ ψ ∈ Finset.univ.filter (fun ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) => LinearMap.ker ψ = D),
          ∑ v ∈ Iso, ∏ i : Fin n, chi (dot (v i) (ψ (col i))) := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext ψ
      simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
      exact ⟨LinearMap.ker ψ, rfl⟩
    · intro D₁ _ D₂ _ hne
      exact Finset.disjoint_left.mpr fun ψ h1 h2 =>
        hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hgroup]
  refine Finset.sum_congr rfl fun D _ => ?_
  have hconst_ker : ∀ ψ ∈ Finset.univ.filter (fun ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) => LinearMap.ker ψ = D),
      (∑ v ∈ Iso, ∏ i : Fin n, chi (dot (v i) (ψ (col i)))) = walk D := by
    intro ψ hψ
    exact (walk_eq_sum_iso_at_pow2 hn H j D ψ (Finset.mem_filter.mp hψ).2).symm
  rw [Finset.sum_congr rfl hconst_ker, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Fintype.card_subtype]
  convert card_lin_with_ker D j using 2

private lemma trace_list_prod_inst_indep {α : Type*} (f₁ f₂ : Fintype α) (d₁ d₂ : DecidableEq α)
    (L₁ L₂ : List (Matrix α α ℤ)) (h : L₁ = L₂) :
    (letI := f₁; letI := d₁; Matrix.trace L₁.prod) =
    (letI := f₂; letI := d₂; Matrix.trace L₂.prod) := by
  subst h
  cases Subsingleton.elim f₁ f₂
  cases Subsingleton.elim d₁ d₂
  rfl

private lemma mapMatrix_list_prod {α R S : Type*} [Fintype α] [DecidableEq α]
    [CommRing R] [CommRing S] (f : R →+* S) (L : List (Matrix α α R)) :
    f.mapMatrix L.prod = (L.map f.mapMatrix).prod := by
  induction L with
  | nil => simp
  | cons M t ih =>
    simp only [List.prod_cons, List.map_cons, map_mul, ih]

private lemma prove_791 (n m : ℕ) (hn : 0 < n) (H : Matrix (Fin m) (Fin n) (ZMod 2)) (z : ℤ) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let F := ZMod 2
    let W := Fin n → F
    let A := Fin m → F
    letI : Fintype (Submodule F W) := Fintype.ofFinite _
    letI : Fintype (Submodule F A) := Fintype.ofFinite _
    let used := fun h : ℕ => ∏ r ∈ Finset.range h, (z - (2 : ℤ) ^ r)
    let next := fun i : Fin n => (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let good := (Finset.univ : Finset (Submodule F W)).filter (fun U =>
      (∀ x ∈ U, ∀ a, (∑ i, H a i * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i))
    let col := fun (i : Fin n) (a : Fin m) => H a i
    let total : A := ∑ i : Fin n, col i
    let walk := fun D : Submodule F A =>
      let B := A ⧸ D
      letI : Fintype B := Fintype.ofFinite _
      let symbol := fun i : Fin n => D.mkQ (col i)
      let closeRun := fun b : B => if b = 0 then z - 1 else -1
      let T : Fin n → Matrix (Option B) (Option B) ℤ := fun i before after =>
        before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
          (fun a => after.elim (closeRun a) (fun b => if b = a + symbol i then 1 else 0))
      Matrix.trace (List.ofFn T).prod + closeRun (D.mkQ total) -
        (if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0)
    z ^ m * (∑ U ∈ good, used (Module.finrank F U)) =
      ∑ D : Submodule F A, used (m - Module.finrank F D) * walk D := by
  let : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro F W A
  let : Fintype (Submodule F W) := Fintype.ofFinite _
  let : Fintype (Submodule F A) := Fintype.ofFinite _
  intro used next good col total walk
  let usedP : ℕ → Polynomial ℤ := fun h =>
    ∏ r ∈ Finset.range h, (Polynomial.X - Polynomial.C ((2 : ℤ) ^ r))
  let walkP : Submodule F A → Polynomial ℤ := fun D =>
    let B := A ⧸ D
    letI : Fintype B := Fintype.ofFinite _
    let symbol := fun i : Fin n => D.mkQ (col i)
    let closeRunP := fun b : B => if b = 0 then Polynomial.X - 1 else -1
    let TP : Fin n → Matrix (Option B) (Option B) (Polynomial ℤ) := fun i before after =>
      before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
        (fun a => after.elim (closeRunP a) (fun b => if b = a + symbol i then 1 else 0))
    Matrix.trace (List.ofFn TP).prod + closeRunP (D.mkQ total) -
      (if D.mkQ total = 0 then Polynomial.C (Fintype.card B : ℤ) else 0)
  let P_lhs : Polynomial ℤ := Polynomial.X ^ m * ∑ U ∈ good, usedP (Module.finrank F U)
  let P_rhs : Polynomial ℤ := ∑ D : Submodule F A, usedP (m - Module.finrank F D) * walkP D
  have heval_used : ∀ (t : ℤ) (h : ℕ),
      (usedP h).eval t = ∏ r ∈ Finset.range h, (t - (2 : ℤ) ^ r) := by
    intro t h
    simp [usedP, Polynomial.eval_prod]
  have heval_walk : ∀ (t : ℤ) (D : Submodule F A),
      (walkP D).eval t =
        let B := A ⧸ D
        letI : Fintype B := Fintype.ofFinite _
        let symbol := fun i : Fin n => D.mkQ (col i)
        let closeRun := fun b : B => if b = 0 then t - 1 else -1
        let T : Fin n → Matrix (Option B) (Option B) ℤ := fun i before after =>
          before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
            (fun a => after.elim (closeRun a) (fun b => if b = a + symbol i then 1 else 0))
        Matrix.trace (List.ofFn T).prod + closeRun (D.mkQ total) -
          (if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0) := by
    intro t D
    let B := A ⧸ D
    let : Fintype B := Fintype.ofFinite _
    let symbol := fun i : Fin n => D.mkQ (col i)
    let closeRunP := fun b : B => if b = 0 then Polynomial.X - 1 else (-1 : Polynomial ℤ)
    let closeRunT := fun b : B => if b = 0 then t - 1 else (-1 : ℤ)
    let TP : Fin n → Matrix (Option B) (Option B) (Polynomial ℤ) := fun i before after =>
      before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
        (fun a => after.elim (closeRunP a) (fun b => if b = a + symbol i then 1 else 0))
    let TT : Fin n → Matrix (Option B) (Option B) ℤ := fun i before after =>
      before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
        (fun a => after.elim (closeRunT a) (fun b => if b = a + symbol i then 1 else 0))
    have hclose : ∀ b : B, (closeRunP b).eval t = closeRunT b := fun b => by
      by_cases hb : b = 0 <;> simp [closeRunP, closeRunT, hb]
    have hmapT : ∀ i : Fin n, (Polynomial.evalRingHom t).mapMatrix (TP i) = TT i := by
      intro i
      ext s₁ s₂
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      change (TP i s₁ s₂).eval t = TT i s₁ s₂
      cases s₁ with
      | none =>
        cases s₂ with
        | none => simp [TP, TT]
        | some b =>
          dsimp only [TP, TT, Option.elim_none, Option.elim_some]
          by_cases h : b = symbol i <;> simp [h]
      | some a =>
        cases s₂ with
        | none =>
          dsimp only [TP, TT, Option.elim_some, Option.elim_none]
          exact hclose a
        | some b =>
          dsimp only [TP, TT, Option.elim_some]
          by_cases h : b = a + symbol i <;> simp [h]
    have htr : (Matrix.trace (List.ofFn TP).prod).eval t = Matrix.trace (List.ofFn TT).prod := by
      have h1 : (Matrix.trace (List.ofFn TP).prod).eval t =
          Matrix.trace ((Polynomial.evalRingHom t).mapMatrix (List.ofFn TP).prod) := by
        change Polynomial.evalRingHom t (∑ s : Option B, (List.ofFn TP).prod s s) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun s _ => rfl
      rw [h1, mapMatrix_list_prod, List.map_ofFn]
      congr 1
      apply congrArg List.prod
      apply congrArg List.ofFn
      funext i
      exact hmapT i
    change (Matrix.trace (List.ofFn TP).prod + closeRunP (D.mkQ total) -
      (if D.mkQ total = 0 then Polynomial.C (Fintype.card B : ℤ) else 0)).eval t =
      Matrix.trace (List.ofFn TT).prod + closeRunT (D.mkQ total) -
        (if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0)
    rw [Polynomial.eval_sub, Polynomial.eval_add, htr, hclose]
    by_cases htot : D.mkQ total = 0 <;>
      simp only [htot, ↓reduceIte, Polynomial.eval_C, Polynomial.eval_zero]
  have heval_both : ∀ t : ℤ,
      P_lhs.eval t = t ^ m * ∑ U ∈ good, ∏ r ∈ Finset.range (Module.finrank F U), (t - (2 : ℤ) ^ r) ∧
      P_rhs.eval t = ∑ D : Submodule F A,
        (∏ r ∈ Finset.range (m - Module.finrank F D), (t - (2 : ℤ) ^ r)) * (walkP D).eval t := by
    intro t
    constructor
    · change Polynomial.evalRingHom t (Polynomial.X ^ m * ∑ U ∈ good, usedP (Module.finrank F U)) = _
      rw [map_mul, map_pow, map_sum]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, heval_used]
    · change Polynomial.evalRingHom t (∑ D : Submodule F A, usedP (m - Module.finrank F D) * walkP D) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [map_mul]
      simp only [Polynomial.coe_evalRingHom, heval_used]
  have hpoly_eq : P_lhs = P_rhs := by
    apply poly_eq_of_eval_pow2
    intro j
    rw [(heval_both ((2 : ℤ) ^ j)).1, (heval_both ((2 : ℤ) ^ j)).2]
    simp_rw [heval_walk]
    have hid := identity_at_pow2 hn H j
    dsimp only at hid
    convert hid using 2
    · congr 1
      ext U
      simp only [good, next, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    · rename_i D _
      congr 1
      dsimp only [col, total]
      congr 1
      congr 1
      apply trace_list_prod_inst_indep
      apply congrArg List.ofFn
      funext i
      ext s₁ s₂
      cases s₁ <;> cases s₂ <;> simp
  have heval_z := congrArg (Polynomial.eval z) hpoly_eq
  rw [(heval_both z).1, (heval_both z).2] at heval_z
  simp_rw [heval_walk] at heval_z
  exact heval_z

end PEqualNP.Outside.L_lib_791_aux

theorem PEqualNP.Outside.L_lib_791 : (∀ (n m : ℕ) (hn : 0 < n) (H : Matrix (Fin m) (Fin n) (ZMod 2)) (z : ℤ),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let W := Fin n → F
  let A := Fin m → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  let used := fun h : ℕ => ∏ r ∈ Finset.range h, (z - (2 : ℤ)^r)
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let good := (Finset.univ : Finset (Submodule F W)).filter (fun U =>
    (∀ x ∈ U, ∀ a, (∑ i, H a i * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i))
  let col := fun (i : Fin n) (a : Fin m) => H a i
  let total : A := ∑ i : Fin n, col i
  let walk := fun D : Submodule F A =>
    let B := A ⧸ D
    letI : Fintype B := Fintype.ofFinite _
    let symbol := fun i : Fin n => D.mkQ (col i)
    let closeRun := fun b : B => if b = 0 then z-1 else -1
    let T : Fin n → Matrix (Option B) (Option B) ℤ := fun i before after =>
      before.elim (after.elim 1 (fun b => if b = symbol i then 1 else 0))
        (fun a => after.elim (closeRun a) (fun b => if b = a + symbol i then 1 else 0))
    Matrix.trace (List.ofFn T).prod + closeRun (D.mkQ total) -
      (if D.mkQ total = 0 then (Fintype.card B : ℤ) else 0)
  z^m * (∑ U ∈ good, used (Module.finrank F U)) =
    ∑ D : Submodule F A, used (m - Module.finrank F D) * walk D) := by
  exact PEqualNP.Outside.L_lib_791_aux.prove_791


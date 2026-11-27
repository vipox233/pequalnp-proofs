import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_793_aux

section PolyField

variable {K : Type} [Field K]

abbrev Vec (K : Type) (n : Nat) := Fin n → K
abbrev DualV (K : Type) [Field K] (n : Nat) := (Fin n → K) →ₗ[K] K
abbrev FormV (K : Type) [Field K] (n : Nat) := (Fin n → K) →ₗ[K] ((Fin n → K) →ₗ[K] K)

lemma add_self_of_two (h2 : ∀ a : K, a = 0 ∨ a = 1) (h11 : (1 : K) + 1 = 0) (a : K) :
    a + a = 0 := by
  rcases h2 a with rfl | rfl
  · exact add_zero 0
  · exact h11

lemma eq_of_add_eq_zero_of_two (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {a b : K} (h : a + b = 0) : a = b := by
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl
  · rfl
  · simp at h
  · simp at h
  · rfl

lemma form_symm (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {n : Nat} (M : FormV K n) (halt : ∀ x, M x x = 0) (x y : Vec K n) :
    M x y = M y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  exact (eq_of_add_eq_zero_of_two h2 h).symm

lemma li_sum_zero {M : Type*} [AddCommMonoid M] [Module K M] {s : Nat}
    {B : Fin s → M} (hB : LinearIndependent K B) {c : Fin s → K}
    (h0 : ∑ i : Fin s, c i • B i = 0) (i : Fin s) : c i = 0 := by
  have hf : Finsupp.linearCombination K B (Finsupp.equivFunOnFinite.symm c) = 0 := by
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype (Finsupp.equivFunOnFinite.symm c) (fun i a => a • B i)
        (fun _ => zero_smul K _)]
    exact h0
  have hker : Finsupp.equivFunOnFinite.symm c = 0 := hB (hf.trans (map_zero _).symm)
  exact congrFun (congrArg DFunLike.coe hker) i

lemma rn_gen {M N : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Module.finrank K ↥(LinearMap.range f) + Module.finrank K ↥(LinearMap.ker f) = Module.finrank K M :=
  LinearMap.finrank_range_add_finrank_ker f

lemma finrank_map_subtype_aux {E : Type*} [AddCommGroup E] [Module K E] [Module.Finite K E]
    (R : Submodule K E) (S : Submodule K ↥R) :
    Module.finrank K ↥(S.map R.subtype) = Module.finrank K ↥S := by
  let f : ↥S →ₗ[K] E := R.subtype.comp S.subtype
  have hinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hrng : LinearMap.range f = S.map R.subtype := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_map, f, LinearMap.comp_apply,
      Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨y, hyS⟩, rfl⟩; exact ⟨y, hyS, rfl⟩
    · rintro ⟨y, hyS, rfl⟩; exact ⟨⟨y, hyS⟩, rfl⟩
  rw [← hrng]
  exact (LinearEquiv.ofInjective f hinj).finrank_eq.symm

def radOn {n : Nat} (M : FormV K n) (W : Submodule K (Vec K n)) : Submodule K (Vec K n) :=
  { carrier := {x | x ∈ W ∧ ∀ y ∈ W, M x y = 0}, add_mem' := by
      intro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
      refine ⟨W.add_mem haW hbW, fun y hy => ?_⟩
      simp [ha y hy, hb y hy]
    zero_mem' := ⟨W.zero_mem, fun _ _ => by simp⟩
    smul_mem' := by
      intro c a ⟨haW, ha⟩
      refine ⟨W.smul_mem c haW, fun y hy => ?_⟩
      simp [ha y hy] }

def annOf {A : Type*} [AddCommGroup A] [Module K A]
    (D : Submodule K A) : Submodule K (A →ₗ[K] K) :=
  { carrier := {l | ∀ x ∈ D, l x = 0}, add_mem' := fun ha hb x hx => by simp [ha x hx, hb x hx]
    zero_mem' := fun _ _ => rfl
    smul_mem' := fun c _ ha x hx => by simp [ha x hx] }

lemma radOn_top {n : Nat} (M : FormV K n) : radOn M ⊤ = LinearMap.ker M := by
  ext x
  simp only [radOn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq, Submodule.mem_top, true_and, LinearMap.mem_ker]
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    exact h y trivial
  · intro h y _
    rw [h]
    rfl

lemma finrank_dual_eq {A : Type*} [AddCommGroup A] [Module K A] [Module.Finite K A] :
    Module.finrank K (A →ₗ[K] K) = Module.finrank K A := by
  let b := Module.finBasis K A
  let e : (A →ₗ[K] K) ≃ₗ[K] (Fin (Module.finrank K A) → K) :=
    { toFun := fun φ i => φ (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun w => b.constr K w
      left_inv := fun φ => by
        apply b.ext
        intro i
        simp
      right_inv := fun w => by
        funext i
        simp }
  rw [e.finrank_eq, Module.finrank_fin_fun]

lemma domRestrict_surjective {A : Type*} [AddCommGroup A] [Module K A]
    (S : Submodule K A) :
    Function.Surjective (fun φ : A →ₗ[K] K => φ.domRestrict S) := by
  obtain ⟨T, hST⟩ := Submodule.exists_isCompl S
  let proj : A →ₗ[K] S := Submodule.projectionOnto S T hST
  intro ψ
  refine ⟨ψ.comp proj, ?_⟩
  apply LinearMap.ext
  intro x
  exact congrArg ψ (Submodule.projectionOnto_apply_left hST x)

lemma finrank_range_flip_le {A B : Type*} [AddCommGroup A] [Module K A] [Module.Finite K A]
    [AddCommGroup B] [Module K B] [Module.Finite K B]
    (T : A →ₗ[K] (B →ₗ[K] K)) :
    Module.finrank K (LinearMap.range T.flip) ≤ Module.finrank K (LinearMap.range T) := by
  let res : (A →ₗ[K] K) →ₗ[K] (LinearMap.ker T →ₗ[K] K) :=
    { toFun := fun φ => φ.domRestrict (LinearMap.ker T)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsub : LinearMap.range T.flip ≤ LinearMap.ker res := by
    rintro φ ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro ⟨a, ha⟩
    change T a b = 0
    rw [LinearMap.mem_ker.1 ha]
    rfl
  have hsurj : LinearMap.range res = ⊤ :=
    LinearMap.range_eq_top.2 (domRestrict_surjective (LinearMap.ker T))
  have hrn1 := LinearMap.finrank_range_add_finrank_ker res
  rw [hsurj, finrank_top, finrank_dual_eq, finrank_dual_eq] at hrn1
  have hrn2 := LinearMap.finrank_range_add_finrank_ker T
  have hle := Submodule.finrank_mono hsub
  omega

lemma finrank_range_flip_eq {A B : Type*} [AddCommGroup A] [Module K A] [Module.Finite K A]
    [AddCommGroup B] [Module K B] [Module.Finite K B]
    (T : A →ₗ[K] (B →ₗ[K] K)) :
    Module.finrank K (LinearMap.range T.flip) = Module.finrank K (LinearMap.range T) := by
  apply le_antisymm (finrank_range_flip_le T)
  have h := finrank_range_flip_le T.flip
  rw [LinearMap.flip_flip] at h
  exact h

lemma finrank_domRestrict_on_sub {A : Type*} [AddCommGroup A] [Module K A] [Module.Finite K A]
    (R : Submodule K (A →ₗ[K] K)) (D : Submodule K A) :
    let res : (A →ₗ[K] K) →ₗ[K] (D →ₗ[K] K) :=
      { toFun := fun l => l.domRestrict D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    Module.finrank K ↥(R.map res) + Module.finrank K ↥(R ⊓ annOf D) = Module.finrank K ↥R := by
  intro res
  let resR : ↥R →ₗ[K] (D →ₗ[K] K) := res.comp R.subtype
  have hrng : LinearMap.range resR = R.map res := by
    ext φ
    simp [resR, Submodule.mem_map]
  have hker : (LinearMap.ker resR).map R.subtype = R ⊓ annOf D := by
    ext l
    constructor
    · rintro ⟨⟨l', hl'R⟩, hl'k, rfl⟩
      refine ⟨hl'R, fun x hx => ?_⟩
      have h0 : resR ⟨l', hl'R⟩ ⟨x, hx⟩ = 0 := by rw [LinearMap.mem_ker.1 hl'k]; rfl
      exact h0
    · rintro ⟨hlR, hlAnn⟩
      refine ⟨⟨l, hlR⟩, ?_, rfl⟩
      change resR ⟨l, hlR⟩ = 0
      apply LinearMap.ext
      intro ⟨x, hx⟩
      exact hlAnn x hx
  have hker_dim : Module.finrank K ↥(LinearMap.ker resR) = Module.finrank K ↥(R ⊓ annOf D) := by
    rw [← hker, finrank_map_subtype_aux]
  have hrn := rn_gen (M := ↥R) (N := ↥D →ₗ[K] K) resR
  rw [hrng, hker_dim] at hrn
  exact hrn

lemma symplectic_decomp (h2 : ∀ a : K, a = 0 ∨ a = 1) (h11 : (1 : K) + 1 = 0)
    {n : Nat} (M : FormV K n) (halt : ∀ x, M x x = 0) :
    ∀ k (W : Submodule K (Vec K n)), Module.finrank K W = k →
      ∃ a : Nat,
        Module.finrank K W = Module.finrank K (radOn M W) + 2 * a ∧
        ∃ L : Submodule K (Vec K n),
          L ≤ W ∧ (∀ x ∈ L, ∀ y ∈ L, M x y = 0) ∧
          Module.finrank K L = Module.finrank K (radOn M W) + a := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hWk
    have hsym := form_symm h2 M halt
    by_cases hzero : ∀ x ∈ W, ∀ y ∈ W, M x y = 0
    · have hrad : radOn M W = W := by
        ext x
        simp only [radOn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_ofPred_eq, and_iff_left_iff_imp]
        exact fun hx => hzero x hx
      refine ⟨0, by rw [hrad]; omega, W, le_rfl, hzero, by rw [hrad]; omega⟩
    · push Not at hzero
      obtain ⟨u, huW, v, hvW, huv_ne⟩ := hzero
      have huv : M u v = 1 := by
        rcases h2 (M u v) with h | h
        · exact (huv_ne h).elim
        · exact h
      have hvu : M v u = 1 := by rw [hsym, huv]
      let W' : Submodule K (Vec K n) :=
        { carrier := {w | w ∈ W ∧ M u w = 0 ∧ M v w = 0}, add_mem' := fun ⟨haW, hau, hav⟩ ⟨hbW, hbu, hbv⟩ =>
            ⟨W.add_mem haW hbW, by simp [hau, hbu], by simp [hav, hbv]⟩
          zero_mem' := ⟨W.zero_mem, by simp, by simp⟩
          smul_mem' := fun c _ ⟨haW, hau, hav⟩ =>
            ⟨W.smul_mem c haW, by simp [hau], by simp [hav]⟩ }
      have hW'_le : W' ≤ W := fun _ hw => hw.1
      let P : Submodule K (Vec K n) := (K ∙ u) ⊔ (K ∙ v)
      have hP_le : P ≤ W := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 huW)
        ((Submodule.span_singleton_le_iff_mem _ _).2 hvW)
      have hmemP : ∀ z ∈ P, ∃ c₁ c₂ : K, z = c₁ • u + c₂ • v := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
        obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.1 ha
        obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.1 hb
        exact ⟨c₁, c₂, rfl⟩
      have hinf : W' ⊓ P = ⊥ := by
        rw [eq_bot_iff]
        intro z ⟨hzW', hzP⟩
        obtain ⟨c₁, c₂, rfl⟩ := hmemP z hzP
        have h1 : M u (c₁ • u + c₂ • v) = 0 := hzW'.2.1
        have h2' : M v (c₁ • u + c₂ • v) = 0 := hzW'.2.2
        simp only [map_add, map_smul, smul_eq_mul, halt, huv, hvu, mul_zero, mul_one, zero_add, add_zero] at h1 h2'
        simp [h1, h2']
      have hsup : W' ⊔ P = W := by
        apply le_antisymm (sup_le hW'_le hP_le)
        intro w hwW
        let w' : Vec K n := w + M v w • u + M u w • v
        have hw'W' : w' ∈ W' := by
          refine ⟨W.add_mem (W.add_mem hwW (W.smul_mem _ huW)) (W.smul_mem _ hvW), ?_, ?_⟩
          · simp only [w', map_add, map_smul, smul_eq_mul, halt, huv, mul_zero, mul_one, add_zero]
            exact add_self_of_two h2 h11 _
          · simp only [w', map_add, map_smul, smul_eq_mul, halt, hvu, mul_zero, mul_one, add_zero]
            exact add_self_of_two h2 h11 _
        have hcombP : M v w • u + M u w • v ∈ P :=
          Submodule.add_mem _
            (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
            (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        have hw_eq : w = w' + (M v w • u + M u w • v) := by
          funext j
          simp only [w', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1 : M v w * u j + M v w * u j = 0 := add_self_of_two h2 h11 _
          have h2' : M u w * v j + M u w * v j = 0 := add_self_of_two h2 h11 _
          calc
            w j = w j + 0 + 0 := by ring
            _ = w j + (M v w * u j + M v w * u j) + (M u w * v j + M u w * v j) := by rw [h1, h2']
            _ = w j + M v w * u j + M u w * v j + (M v w * u j + M u w * v j) := by ring
        rw [hw_eq]
        exact Submodule.add_mem_sup hw'W' hcombP
      have hu_ne : u ≠ 0 := fun h => by rw [h, map_zero] at huv; exact one_ne_zero huv.symm
      have hv_ne : v ≠ 0 := fun h => by rw [h, map_zero] at hvu; exact one_ne_zero hvu.symm
      have huv_inf : (K ∙ u) ⊓ (K ∙ v) = ⊥ := by
        rw [eq_bot_iff]
        intro z ⟨hzu, hzv⟩
        obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.1 hzu
        obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.1 hzv
        have h1 : M u (c₁ • u) = M u (c₂ • v) := congrArg (M u) hc₂.symm
        simp only [map_smul, smul_eq_mul, halt, huv, mul_zero, mul_one] at h1
        rw [← hc₂, ← h1, zero_smul]
        exact Submodule.zero_mem _
      have hP_dim : Module.finrank K P = 2 := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ u) (K ∙ v)
        rw [huv_inf, finrank_bot, add_zero, finrank_span_singleton hu_ne,
          finrank_span_singleton hv_ne] at h1
        exact h1
      have hW'_dim : Module.finrank K W' + 2 = k := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq W' P
        rw [hsup, hinf, finrank_bot, add_zero, hP_dim, hWk] at h1
        exact h1.symm
      have hrad_eq : radOn M W' = radOn M W := by
        ext z
        simp only [radOn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hzW', hz0⟩
          refine ⟨hzW'.1, fun y hyW => ?_⟩
          rw [← hsup] at hyW
          obtain ⟨y', hy'W', q, hqP, rfl⟩ := Submodule.mem_sup.1 hyW
          obtain ⟨c₁, c₂, rfl⟩ := hmemP q hqP
          simp only [map_add, map_smul, smul_eq_mul, hz0 y' hy'W', zero_add]
          rw [hsym z u, hzW'.2.1, hsym z v, hzW'.2.2]
          simp
        · rintro ⟨hzW, hz0⟩
          refine ⟨⟨hzW, ?_, ?_⟩, fun y hyW' => hz0 y hyW'.1⟩
          · rw [hsym]; exact hz0 u huW
          · rw [hsym]; exact hz0 v hvW
      obtain ⟨a', ha'dim, L', hL'W', hL'iso, hL'dim⟩ :=
        ih (Module.finrank K W') (by omega) W' rfl
      refine ⟨a' + 1, by rw [← hrad_eq]; omega, L' ⊔ (K ∙ u), ?_, ?_, ?_⟩
      · exact sup_le (le_trans hL'W' hW'_le) ((Submodule.span_singleton_le_iff_mem _ _).2 huW)
      · intro x hx y hy
        obtain ⟨x', hx', a, ha, rfl⟩ := Submodule.mem_sup.1 hx
        obtain ⟨y', hy', b, hb, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.1 ha
        obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.1 hb
        have hx'u : M x' u = 0 := by rw [hsym]; exact (hL'W' hx').2.1
        have huy' : M u y' = 0 := (hL'W' hy').2.1
        simp [hL'iso x' hx' y' hy', hx'u, huy', halt]
      · have hL'u_inf : L' ⊓ (K ∙ u) = ⊥ := by
          rw [eq_bot_iff]
          intro z ⟨hzL', hzu⟩
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hzu
          have h1 : M v (c • u) = 0 := (hL'W' hzL').2.2
          simp only [map_smul, smul_eq_mul, hvu, mul_one] at h1
          simp [h1]
        have hdim := Submodule.finrank_sup_add_finrank_inf_eq L' (K ∙ u)
        rw [hL'u_inf, finrank_bot, add_zero, finrank_span_singleton hu_ne] at hdim
        rw [← hrad_eq]
        omega

lemma exists_subspace_cuts [Fintype K] (hcard : Fintype.card K = 2)
    {E : Type*} [AddCommGroup E] [Module K E] [Module.Finite K E]
    (R : Submodule K E) (k : Nat) (hk : k ≤ Module.finrank K ↥R) :
    ∃ (S : Submodule K E) (cuts : Finset E),
      S ≤ R ∧ Module.finrank K ↥S = k ∧
      (0 : E) ∉ cuts ∧
      cuts.card ≤ 2 ^ k - 1 ∧
      (∀ l ∈ cuts, l ∈ S) ∧
      (∀ l ∈ S, l ≠ 0 → l ∈ cuts) := by
  classical
  have : Module.Free K ↥R := Module.Free.of_divisionRing K ↥R
  let b := Module.finBasis K ↥R
  let emb : Fin k → Fin (Module.finrank K ↥R) := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hk⟩
  have hemb_inj : Function.Injective emb := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin (Module.finrank K ↥R) => x.val) h)
  let v : Fin k → E := fun j => (b (emb j)).val
  have hv_mem : ∀ j, v j ∈ R := fun j => (b (emb j)).property
  have hv_ind : LinearIndependent K v := by
    have h1 : LinearIndependent K (fun j => b (emb j)) := b.linearIndependent.comp emb hemb_inj
    exact h1.map' R.subtype (Submodule.ker_subtype R)
  let S : Submodule K E := Submodule.span K (Set.range v)
  have hS_le : S ≤ R := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hv_mem j
  have hS_dim : Module.finrank K ↥S = k := by
    rw [finrank_span_eq_card hv_ind, Fintype.card_fin]
  let comb : (Fin k → K) → E := fun w => ∑ j : Fin k, w j • v j
  let cuts : Finset E := ((Finset.univ : Finset (Fin k → K)).erase 0).image comb
  refine ⟨S, cuts, hS_le, hS_dim, ?_, ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw, hcomb0⟩ := Finset.mem_image.1 h0
    have hw_ne : w ≠ 0 := (Finset.mem_erase.1 hw).1
    have hw_zero : w = 0 := by
      funext j
      exact li_sum_zero hv_ind hcomb0 j
    exact hw_ne hw_zero
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, hcard]
  · intro l hl
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hl
    exact Submodule.sum_mem S (fun j _ =>
      Submodule.smul_mem S (w j) (Submodule.subset_span ⟨j, rfl⟩))
  · intro l hlS hl_ne
    have hmem : l ∈ Submodule.span K (Set.range v) := hlS
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
    obtain ⟨c, hc⟩ := hmem
    let w : Fin k → K := fun j => c j
    have hw_eq : comb w = l := by
      dsimp only [comb, w]
      rw [← hc, Finsupp.sum_fintype c (fun i a => a • v i) (fun _ => zero_smul K _)]
    refine Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨?_, Finset.mem_univ w⟩, hw_eq⟩
    intro hw0
    apply hl_ne
    rw [← hw_eq, hw0]
    simp [comb]

lemma isotropic_annihilator_bounds (h2 : ∀ a : K, a = 0 ∨ a = 1) (h11 : (1 : K) + 1 = 0)
    {n p : Nat} (M : FormV K n) (halt : ∀ x, M x x = 0)
    (D : Submodule K (Vec K n)) (hcodim : n - Module.finrank K ↥D ≤ p)
    (hiso : ∀ x ∈ D, ∀ y ∈ D, M x y = 0) :
    Module.finrank K ↥(LinearMap.range M) ≤ 2 * p ∧
    Module.finrank K ↥(LinearMap.range M) / 2 ≤
      Module.finrank K ↥(LinearMap.range M ⊓ annOf D) := by
  have hsym := form_symm h2 M halt
  obtain ⟨a, hadim, _⟩ := symplectic_decomp h2 h11 M halt
    (Module.finrank K (⊤ : Submodule K (Vec K n))) ⊤ rfl
  rw [radOn_top, finrank_top] at hadim
  have hrnM := LinearMap.finrank_range_add_finrank_ker M
  have hVn : Module.finrank K (Vec K n) = n := Module.finrank_fin_fun K
  have hadim' : n = Module.finrank K ↥(LinearMap.ker M) + 2 * a := hVn.symm.trans hadim
  have hrnM' : Module.finrank K ↥(LinearMap.range M) + Module.finrank K ↥(LinearMap.ker M) = n :=
    hrnM.trans hVn
  have hrk : Module.finrank K ↥(LinearMap.range M) = 2 * a := by omega
  let f1 : ↥D →ₗ[K] (Vec K n →ₗ[K] K) := M.comp D.subtype
  let f2 : Vec K n →ₗ[K] (↥D →ₗ[K] K) := f1.flip
  have hf2_eq : ∀ v : Vec K n, ∀ x : ↥D, f2 v x = M v x.val := fun v x => hsym x.val v
  let res : (Vec K n →ₗ[K] K) →ₗ[K] (↥D →ₗ[K] K) :=
    { toFun := fun l => l.domRestrict D, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hmap_eq : (LinearMap.range M).map res = LinearMap.range f2 := by
    ext φ
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨l, ⟨v, rfl⟩, rfl⟩
      refine ⟨v, ?_⟩
      apply LinearMap.ext
      intro x
      exact hf2_eq v x
    · rintro ⟨v, rfl⟩
      refine ⟨M v, ⟨v, rfl⟩, ?_⟩
      apply LinearMap.ext
      intro x
      exact (hf2_eq v x).symm
  have hrn_res := finrank_domRestrict_on_sub (LinearMap.range M) D
  dsimp only at hrn_res
  change Module.finrank K ↥((LinearMap.range M).map res) +
      Module.finrank K ↥(LinearMap.range M ⊓ annOf D) =
      Module.finrank K ↥(LinearMap.range M) at hrn_res
  rw [hmap_eq, finrank_range_flip_eq f1] at hrn_res
  have hrn_res' : Module.finrank K ↥(LinearMap.range f1) +
      Module.finrank K ↥(LinearMap.range M ⊓ annOf D) = 2 * a :=
    hrn_res.trans hrk
  have hmap_le : LinearMap.range f1 ≤ LinearMap.range M ⊓ annOf D := by
    rintro l ⟨⟨x, hxD⟩, rfl⟩
    exact ⟨⟨x, rfl⟩, fun y hyD => hiso x hxD y hyD⟩
  have hmap_le_ann : Module.finrank K ↥(LinearMap.range f1) ≤
      Module.finrank K ↥(LinearMap.range M ⊓ annOf D) := Submodule.finrank_mono hmap_le
  have hker_f1_le : (LinearMap.ker f1).map D.subtype ≤ LinearMap.ker M := by
    rintro x ⟨⟨x', hx'D⟩, hx'k, rfl⟩
    exact LinearMap.mem_ker.1 hx'k
  have hker_f1_dim : Module.finrank K ↥(LinearMap.ker f1) ≤ Module.finrank K ↥(LinearMap.ker M) := by
    rw [← finrank_map_subtype_aux D (LinearMap.ker f1)]
    exact Submodule.finrank_mono hker_f1_le
  have hrn_f1 : Module.finrank K ↥(LinearMap.range f1) + Module.finrank K ↥(LinearMap.ker f1) =
      Module.finrank K ↥D := LinearMap.finrank_range_add_finrank_ker f1
  have hD_le_n : Module.finrank K ↥D ≤ n := le_trans (Submodule.finrank_le D) (le_of_eq hVn)
  constructor <;> omega

lemma form_sum_apply {n s : Nat} (c : Fin s → K) (B : Fin s → FormV K n) (x y : Vec K n) :
    (∑ i : Fin s, c i • B i) x y = ∑ i : Fin s, c i * B i x y := by
  have h1 : ∀ S : Finset (Fin s), (∑ i ∈ S, c i • B i) x y = ∑ i ∈ S, c i * B i x y := by
    intro S
    induction S using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => simp
  exact h1 Finset.univ

lemma shrinks_iff_exists_nonzero_isotropic {n s : Nat} (B : Fin s → FormV K n)
    (D : Submodule K (Vec K n)) :
    (Module.finrank K ↥(Submodule.span K
      (Set.range (fun i : Fin s => fun z : ↥D × ↥D => B i z.1.val z.2.val))) < s) ↔
    ∃ c : Fin s → K, c ≠ 0 ∧ ∀ x ∈ D, ∀ y ∈ D, (∑ i : Fin s, c i • B i) x y = 0 := by
  let row : Fin s → (↥D × ↥D → K) := fun i z => B i z.1.val z.2.val
  let T : (Fin s → K) →ₗ[K] (↥D × ↥D → K) :=
    { toFun := fun c z => ∑ i : Fin s, c i * row i z
      map_add' := fun c₁ c₂ => by
        funext z
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
  have hrange : LinearMap.range T = Submodule.span K (Set.range row) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hEq : T c = ∑ i : Fin s, c i • row i := by
        funext z
        simp [T, Finset.sum_apply, smul_eq_mul]
      rw [hEq]
      exact Submodule.sum_mem _ (fun i _ =>
        Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ?_⟩
      funext z
      simp [T, Pi.single_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [Module.finrank_fin_fun, hrange] at hrn
  dsimp only [row] at hrn
  have hker_iff : ∀ c : Fin s → K,
      c ∈ LinearMap.ker T ↔ ∀ x ∈ D, ∀ y ∈ D, (∑ i : Fin s, c i • B i) x y = 0 := by
    intro c
    rw [LinearMap.mem_ker]
    constructor
    · intro h x hx y hy
      rw [form_sum_apply]
      exact congrFun h (⟨x, hx⟩, ⟨y, hy⟩)
    · intro h
      funext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      change ∑ i : Fin s, c i * B i x y = 0
      rw [← form_sum_apply]
      exact h x hx y hy
  constructor
  · intro hlt
    have hpos : 0 < Module.finrank K ↥(LinearMap.ker T) := by omega
    have hne : LinearMap.ker T ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hpos
      omega
    obtain ⟨c, hcK, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨c, hc0, (hker_iff c).1 hcK⟩
  · rintro ⟨c, hc0, hiso⟩
    have hcK : c ∈ LinearMap.ker T := (hker_iff c).2 hiso
    have hpos : 0 < Module.finrank K ↥(LinearMap.ker T) := by
      have h1 : Module.finrank K ↥(K ∙ c) ≤ Module.finrank K ↥(LinearMap.ker T) :=
        Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).2 hcK)
      rw [finrank_span_singleton hc0] at h1
      omega
    omega

theorem main_poly [Fintype K] [DecidableEq K]
    (h2 : ∀ a : K, a = 0 ∨ a = 1) (h11 : (1 : K) + 1 = 0) (hcard : Fintype.card K = 2)
    (n s p : Nat) (B : Fin s → FormV K n)
    (hBind : LinearIndependent K B) (haltB : ∀ i x, B i x x = 0) :
    let mix := fun c : Fin s → K => ∑ i : Fin s, c i • B i
    let rk := fun c : Fin s → K => Module.finrank K (LinearMap.range (mix c))
    let small := (Finset.univ : Finset (Fin s → K)).filter (fun c => c ≠ 0 ∧ rk c ≤ 2 * p)
    let shrinks := fun D : Submodule K (Vec K n) =>
      let row := fun i : Fin s => fun z : D × D => B i z.1.val z.2.val
      Module.finrank K (Submodule.span K (Set.range row)) < s
    let admissible := fun D : Submodule K (Vec K n) => n - Module.finrank K D ≤ p ∧ shrinks D
    ((∃ D : Submodule K (Vec K n), admissible D) ↔ small.Nonempty) ∧
      (∃ cuts : Finset (DualV K n), (0 : DualV K n) ∉ cuts ∧
        cuts.card ≤ ∑ c ∈ small, ((2 : Nat) ^ (rk c / 2 + 1) - 1) ∧
        (∀ l ∈ cuts, ∃ c ∈ small, l ∈ LinearMap.range (mix c)) ∧
        (∀ D : Submodule K (Vec K n), admissible D → ∃ l ∈ cuts, ∀ x ∈ D, l x = 0)) := by
  classical
  intro mix rk small shrinks admissible
  have halt_mix : ∀ c : Fin s → K, ∀ x : Vec K n, mix c x x = 0 := by
    intro c x
    dsimp only [mix]
    rw [form_sum_apply]
    simp [haltB]
  have hmix_ne : ∀ c : Fin s → K, c ≠ 0 → mix c ≠ 0 := by
    intro c hc h0
    apply hc
    funext i
    exact li_sum_zero hBind h0 i
  have hrk_even : ∀ c : Fin s → K, ∃ a : Nat, rk c = 2 * a := by
    intro c
    obtain ⟨a, hadim, _⟩ := symplectic_decomp h2 h11 (mix c) (halt_mix c)
      (Module.finrank K (⊤ : Submodule K (Vec K n))) ⊤ rfl
    rw [radOn_top, finrank_top] at hadim
    have hrn := LinearMap.finrank_range_add_finrank_ker (mix c)
    have hVn : Module.finrank K (Vec K n) = n := Module.finrank_fin_fun K
    have hadim' : n = Module.finrank K ↥(LinearMap.ker (mix c)) + 2 * a := hVn.symm.trans hadim
    have hrn' : rk c + Module.finrank K ↥(LinearMap.ker (mix c)) = n := hrn.trans hVn
    exact ⟨a, by omega⟩
  constructor
  · constructor
    · rintro ⟨D, hcodim, hshr⟩
      obtain ⟨c, hc0, hiso⟩ := (shrinks_iff_exists_nonzero_isotropic B D).1 hshr
      have hbound := (isotropic_annihilator_bounds h2 h11 (mix c) (halt_mix c) D hcodim hiso).1
      exact ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ c, hc0, hbound⟩⟩
    · rintro ⟨c, hc_small⟩
      obtain ⟨_, hc0, hrk_le⟩ := Finset.mem_filter.1 hc_small
      obtain ⟨a, hadim, L, _, hLiso, hLdim⟩ := symplectic_decomp h2 h11 (mix c) (halt_mix c)
        (Module.finrank K (⊤ : Submodule K (Vec K n))) ⊤ rfl
      rw [radOn_top, finrank_top] at hadim
      rw [radOn_top] at hLdim
      have hrn := LinearMap.finrank_range_add_finrank_ker (mix c)
      have hVn : Module.finrank K (Vec K n) = n := Module.finrank_fin_fun K
      have hadim' : n = Module.finrank K ↥(LinearMap.ker (mix c)) + 2 * a := hVn.symm.trans hadim
      have hrn' : rk c + Module.finrank K ↥(LinearMap.ker (mix c)) = n := hrn.trans hVn
      refine ⟨L, by omega, ?_⟩
      exact (shrinks_iff_exists_nonzero_isotropic B L).2 ⟨c, hc0, hLiso⟩
  · have hchoose : ∀ c : Fin s → K, c ∈ small →
        ∃ (S : Submodule K (DualV K n)) (cs : Finset (DualV K n)),
          S ≤ LinearMap.range (mix c) ∧
          Module.finrank K ↥S = rk c / 2 + 1 ∧
          (0 : DualV K n) ∉ cs ∧
          cs.card ≤ 2 ^ (rk c / 2 + 1) - 1 ∧
          (∀ l ∈ cs, l ∈ S) ∧
          (∀ l ∈ S, l ≠ 0 → l ∈ cs) := by
      intro c hc_small
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc_small).2.1
      have hne : mix c ≠ 0 := hmix_ne c hc0
      have hrk_pos : 0 < rk c := by
        by_contra h0
        have hrk0 : Module.finrank K ↥(LinearMap.range (mix c)) = 0 := by
          change rk c = 0; omega
        have hbot : LinearMap.range (mix c) = ⊥ :=
          Submodule.finrank_eq_zero.1 hrk0
        apply hne
        apply LinearMap.ext
        intro x
        have hx : mix c x ∈ LinearMap.range (mix c) := ⟨x, rfl⟩
        rw [hbot, Submodule.mem_bot] at hx
        exact hx
      obtain ⟨a, ha⟩ := hrk_even c
      have hk : rk c / 2 + 1 ≤ Module.finrank K ↥(LinearMap.range (mix c)) := by
        change rk c / 2 + 1 ≤ rk c
        omega
      exact exists_subspace_cuts hcard (LinearMap.range (mix c)) (rk c / 2 + 1) hk
    let Sc : (Fin s → K) → Submodule K (DualV K n) := fun c =>
      if hc : c ∈ small then Classical.choose (hchoose c hc) else ⊥
    let Csc : (Fin s → K) → Finset (DualV K n) := fun c =>
      if hc : c ∈ small then Classical.choose (Classical.choose_spec (hchoose c hc)) else ∅
    have hSpec : ∀ c (hc : c ∈ small),
        Sc c ≤ LinearMap.range (mix c) ∧
        Module.finrank K ↥(Sc c) = rk c / 2 + 1 ∧
        (0 : DualV K n) ∉ Csc c ∧
        (Csc c).card ≤ 2 ^ (rk c / 2 + 1) - 1 ∧
        (∀ l ∈ Csc c, l ∈ Sc c) ∧
        (∀ l ∈ Sc c, l ≠ 0 → l ∈ Csc c) := by
      intro c hc
      have hSc : Sc c = Classical.choose (hchoose c hc) := by
        dsimp only [Sc]; simp only [hc, ↓reduceDIte]
      have hCsc : Csc c = Classical.choose (Classical.choose_spec (hchoose c hc)) := by
        dsimp only [Csc]; simp only [hc, ↓reduceDIte]
      rw [hSc, hCsc]
      exact Classical.choose_spec (Classical.choose_spec (hchoose c hc))
    let cuts : Finset (DualV K n) := small.biUnion Csc
    refine ⟨cuts, ?_, ?_, ?_, ?_⟩
    · intro h0
      obtain ⟨c, hc, h0c⟩ := Finset.mem_biUnion.1 h0
      exact (hSpec c hc).2.2.1 h0c
    · refine le_trans Finset.card_biUnion_le ?_
      exact Finset.sum_le_sum (fun c hc => (hSpec c hc).2.2.2.1)
    · intro l hl
      obtain ⟨c, hc, hlc⟩ := Finset.mem_biUnion.1 hl
      exact ⟨c, hc, (hSpec c hc).1 ((hSpec c hc).2.2.2.2.1 l hlc)⟩
    · intro D ⟨hcodim, hshr⟩
      obtain ⟨c, hc0, hiso⟩ := (shrinks_iff_exists_nonzero_isotropic B D).1 hshr
      obtain ⟨hrk_le, hann_ge⟩ := isotropic_annihilator_bounds h2 h11 (mix c) (halt_mix c) D hcodim hiso
      have hc_small : c ∈ small := Finset.mem_filter.2 ⟨Finset.mem_univ c, hc0, hrk_le⟩
      obtain ⟨hSc_le, hSc_dim, _, _, _, hSc_mem⟩ := hSpec c hc_small
      let A : Submodule K (DualV K n) := LinearMap.range (mix c) ⊓ annOf D
      have hsup_le : Sc c ⊔ A ≤ LinearMap.range (mix c) := sup_le hSc_le inf_le_left
      have hsup_dim : Module.finrank K ↥(Sc c ⊔ A) ≤ rk c := Submodule.finrank_mono hsup_le
      have hgrass := Submodule.finrank_sup_add_finrank_inf_eq (Sc c) A
      obtain ⟨a, ha⟩ := hrk_even c
      have hinf_pos : 0 < Module.finrank K ↥(Sc c ⊓ A) := by
        have h1 : rk c / 2 ≤ Module.finrank K ↥A := hann_ge
        omega
      have hinf_ne : Sc c ⊓ A ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hinf_pos
        omega
      obtain ⟨l, ⟨hlS, _, hlAnn⟩, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf_ne
      exact ⟨l, Finset.mem_biUnion.2 ⟨c, hc_small, hSc_mem l hlS hl0⟩, hlAnn⟩

end PolyField

end PEqualNP.Outside.L_lib_793_aux

theorem PEqualNP.Outside.L_lib_793 : (∀ (n s p : Nat),
  let F := ZMod 2
  let V := Fin n → F
  let Dual := V →ₗ[F] F
  let Form := V →ₗ[F] Dual
  ∀ B : Fin s → Form, LinearIndependent F B → (∀ i x, B i x x = 0) →
    let mix := fun c : Fin s → F => ∑ i : Fin s, c i • B i
    let rk := fun c : Fin s → F => Module.finrank F (LinearMap.range (mix c))
    let small := (Finset.univ : Finset (Fin s → F)).filter (fun c => c ≠ 0 ∧ rk c ≤ 2*p)
    let shrinks := fun D : Submodule F V =>
      let row := fun i : Fin s => fun z : D × D => B i z.1.val z.2.val
      Module.finrank F (Submodule.span F (Set.range row)) < s
    let admissible := fun D : Submodule F V => n - Module.finrank F D ≤ p ∧ shrinks D
    ((∃ D : Submodule F V, admissible D) ↔ small.Nonempty) ∧
      (∃ cuts : Finset Dual, (0 : Dual) ∉ cuts ∧
        cuts.card ≤ ∑ c ∈ small, ((2 : Nat)^(rk c/2+1)-1) ∧
        (∀ l ∈ cuts, ∃ c ∈ small, l ∈ LinearMap.range (mix c)) ∧
        (∀ D : Submodule F V, admissible D → ∃ l ∈ cuts, ∀ x ∈ D, l x = 0))) := by
  intro n s p F V Dual Form B hBind haltB
  exact PEqualNP.Outside.L_lib_793_aux.main_poly (K := ZMod 2)
    (fun a => by revert a; decide) (by decide) (ZMod.card 2) n s p B hBind haltB

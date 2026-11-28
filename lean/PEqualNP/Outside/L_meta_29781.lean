import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29781

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

/-! ## Section 1: Basic `ZMod 2`, Characters, and Linear Algebra -/

def chi (a : F) : ℤ := if a = 1 then -1 else 1
def sg (b : Bool) : ℤ := if b then -1 else 1
def b2f (b : Bool) : F := if b then 1 else 0

lemma zmod2_add_self (a : F) : a + a = 0 := by fin_cases a <;> decide
lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by fin_cases a <;> fin_cases b <;> decide
lemma zmod2_mul_self (a : F) : a * a = a := by revert a; decide
lemma zmod2_eq_one_of_ne_zero (a : F) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl
lemma zmod2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma chi_zero : chi 0 = 1 := by decide
lemma chi_one : chi 1 = -1 := by decide
lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by fin_cases a <;> fin_cases b <;> decide
lemma chi_sub (a b : F) : chi (a - b) = chi a * chi b := by fin_cases a <;> fin_cases b <;> decide
lemma chi_abs (a : F) : (chi a).natAbs = 1 := by fin_cases a <;> decide
lemma sg_xor (b : Bool) (a : F) : sg (xor b (decide (a = 1))) = sg b * chi a := by
  cases b <;> fin_cases a <;> decide
lemma agree_eq_sg_chi (b : Bool) (a : F) :
    (if b = decide (a = 1) then (1 : ℤ) else -1) = sg b * chi a := by
  cases b <;> fin_cases a <;> decide
lemma sg_eq_chi_b2f (b : Bool) : sg b = chi (b2f b) := by cases b <;> decide
lemma b2f_decide (a : F) : b2f (decide (a = 1)) = a := by revert a; decide
lemma decide_b2f (b : Bool) : decide (b2f b = 1) = b := by cases b <;> decide
lemma dec_add (a b : F) : decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
lemma dec_mul (a b : F) : decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by cases a <;> cases b <;> decide
lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by cases a <;> cases b <;> decide
lemma vec_sub_eq_add {n : ℕ} (x y : Fin n → F) : x - y = x + y := by
  funext j; exact zmod2_sub_eq_add (x j) (y j)
lemma vec_add_self {n : ℕ} (x : Fin n → F) : x + x = 0 := by
  funext j; exact zmod2_add_self (x j)

lemma card_fin_fun (n : ℕ) : Fintype.card (Fin n → F) = 2 ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma card_submodule {n : ℕ} (U : Submodule F (Fin n → F)) [Fintype U] :
    Fintype.card U = 2 ^ (Module.finrank F U) := by
  classical
  let e : (Fin (Module.finrank F U) → F) ≃ₗ[F] U :=
    LinearEquiv.ofFinrankEq (R := F) (M := Fin (Module.finrank F U) → F) (M' := U)
      (by rw [Module.finrank_fin_fun])
  rw [← Fintype.card_congr e.toEquiv, card_fin_fun]

def dotLin {n : ℕ} (v : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun := fun x => dotProduct v x
  map_add' := fun x y => dotProduct_add v x y
  map_smul' := fun c x => by simp [dotProduct_smul]

def dualMap {n : ℕ} (U : Submodule F (Fin n → F)) : (Fin n → F) →ₗ[F] (U →ₗ[F] F) where
  toFun := fun x => (dotLin x).comp U.subtype
  map_add' := fun x y => by
    ext u; simp [dotLin, add_dotProduct]
  map_smul' := fun c x => by
    ext u; simp [dotLin, smul_dotProduct]

def perp {n : ℕ} (U : Submodule F (Fin n → F)) : Submodule F (Fin n → F) :=
  LinearMap.ker (dualMap U)

lemma mem_perp {n : ℕ} (U : Submodule F (Fin n → F)) (x : Fin n → F) :
    x ∈ perp U ↔ ∀ u ∈ U, dotProduct x u = 0 := by
  simp only [perp, LinearMap.mem_ker, LinearMap.ext_iff, dualMap, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.comp_apply, Submodule.coe_subtype, dotLin, LinearMap.zero_apply,
    Subtype.forall]

lemma proj_of_isCompl {V : Type*} [AddCommGroup V] [Module F V]
    (U W : Submodule F V) (hUW : IsCompl U W) :
    ∃ π : V →ₗ[F] U, ∀ u : U, π u.1 = u := by
  classical
  have huniq : ∀ x : V, ∃! p : U × W, (p.1 : V) + (p.2 : V) = x := by
    intro x
    obtain ⟨u, w, hxw, hu⟩ := Submodule.existsUnique_add_of_isCompl hUW x
    refine ⟨(u, w), hxw, fun p hp => ?_⟩
    have h := hu p.1 p.2 hp
    exact Prod.ext h.1 h.2
  choose f hf1 hf2 using huniq
  refine ⟨{
    toFun := fun x => (f x).1
    map_add' := fun x y => by
      have hsum : (((f x).1 + (f y).1 : U) : V) + (((f x).2 + (f y).2 : W) : V) = x + y := by
        have hx : ((f x).1 : V) + ((f x).2 : V) = x := hf1 x
        have hy : ((f y).1 : V) + ((f y).2 : V) = y := hf1 y
        calc (((f x).1 + (f y).1 : U) : V) + (((f x).2 + (f y).2 : W) : V)
            = (((f x).1 : V) + ((f y).1 : V)) + (((f x).2 : V) + ((f y).2 : V)) := by simp
          _ = (((f x).1 : V) + ((f x).2 : V)) + (((f y).1 : V) + ((f y).2 : V)) := by abel
          _ = x + y := by rw [hx, hy]
      have heq := hf2 (x + y) ((f x).1 + (f y).1, (f x).2 + (f y).2) hsum
      exact congrArg Prod.fst heq.symm
    map_smul' := fun c x => by
      have hsm : ((c • (f x).1 : U) : V) + ((c • (f x).2 : W) : V) = c • x := by
        simp only [SetLike.val_smul, ← smul_add, hf1 x]
      have heq := hf2 (c • x) (c • (f x).1, c • (f x).2) hsm
      exact congrArg Prod.fst heq.symm
  }, fun u => by
    have h0 : ((u : U) : V) + ((0 : W) : V) = u.1 := by simp
    exact congrArg Prod.fst (hf2 u.1 (u, 0) h0).symm⟩

lemma dualMap_surjective {n : ℕ} (U : Submodule F (Fin n → F)) :
    Function.Surjective (dualMap U) := by
  intro φ
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  obtain ⟨π, hπ⟩ := proj_of_isCompl U W hUW
  let ψ : (Fin n → F) →ₗ[F] F := φ.comp π
  refine ⟨fun j => ψ (Pi.single j 1), ?_⟩
  ext u
  simp only [dualMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    Submodule.coe_subtype, dotLin]
  have hrep : u.1 = ∑ j : Fin n, u.1 j • Pi.single j (1 : F) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hdot : dotProduct (fun j => ψ (Pi.single j 1)) u.1 = ψ u.1 := by
    conv_rhs => rw [hrep, map_sum]
    simp only [dotProduct, map_smul, smul_eq_mul, mul_comm]
  rw [hdot]
  show φ (π u.1) = φ u
  rw [hπ u]

lemma finrank_perp {n : ℕ} (U : Submodule F (Fin n → F)) :
    Module.finrank F (perp U) + Module.finrank F U = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (dualMap U)
  have hr : LinearMap.range (dualMap U) = ⊤ :=
    LinearMap.range_eq_top.mpr (dualMap_surjective U)
  rw [hr, finrank_top, Subspace.dual_finrank_eq, Module.finrank_fin_fun] at h1
  change Module.finrank F U + Module.finrank F (perp U) = n at h1
  omega

lemma perp_perp {n : ℕ} (U : Submodule F (Fin n → F)) : perp (perp U) = U := by
  have hle : U ≤ perp (perp U) := by
    intro u hu
    rw [mem_perp]
    intro v hv
    rw [dotProduct_comm]
    exact (mem_perp U v).mp hv u hu
  have hfr : Module.finrank F U = Module.finrank F (perp (perp U)) := by
    have h1 := finrank_perp U
    have h2 := finrank_perp (perp U)
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfr).symm

lemma exists_left_inv {s k : ℕ} (B : (Fin s → F) →ₗ[F] (Fin k → F))
    (hB : Function.Injective B) :
    ∃ P : (Fin k → F) →ₗ[F] (Fin s → F), ∀ t, P (B t) = t := by
  obtain ⟨W, hBW⟩ := Submodule.exists_isCompl (LinearMap.range B)
  obtain ⟨π, hπ⟩ := proj_of_isCompl (LinearMap.range B) W hBW
  let e : (Fin s → F) ≃ₗ[F] LinearMap.range B := LinearEquiv.ofInjective B hB
  refine ⟨e.symm.toLinearMap.comp π, fun t => ?_⟩
  have hmem : B t ∈ LinearMap.range B := ⟨t, rfl⟩
  change e.symm (π (⟨B t, hmem⟩ : LinearMap.range B).1) = t
  rw [hπ ⟨B t, hmem⟩]
  exact e.symm_apply_apply t

lemma sum_chi_dot_subspace {n : ℕ} (U : Submodule F (Fin n → F)) [Fintype U] (v : Fin n → F)
    [Decidable (v ∈ perp U)] :
    (∑ u : U, chi (dotProduct v u.1)) = if v ∈ perp U then (Fintype.card U : ℤ) else 0 := by
  by_cases hv : v ∈ perp U
  · rw [if_pos hv]
    have h1 : ∀ u : U, chi (dotProduct v u.1) = 1 := fun u => by
      rw [(mem_perp U v).mp hv u.1 u.2, chi_zero]
    simp [h1]
  · rw [if_neg hv]
    rw [mem_perp] at hv
    push Not at hv
    obtain ⟨u0, hu0, hne⟩ := hv
    have h1 : dotProduct v u0 = 1 := zmod2_eq_one_of_ne_zero _ hne
    let S : ℤ := ∑ u : U, chi (dotProduct v u.1)
    have hshift : S = -S := by
      change (∑ u : U, chi (dotProduct v u.1)) = -(∑ u : U, chi (dotProduct v u.1))
      rw [← Finset.sum_neg_distrib]
      refine Fintype.sum_equiv (Equiv.addRight (⟨u0, hu0⟩ : U)) _ _ (fun u => ?_)
      change chi (dotProduct v u.1) = -chi (dotProduct v (u.1 + u0))
      rw [dotProduct_add, h1, chi_add, chi_one]
      ring
    omega

lemma sum_chi_dot_univ {n : ℕ} (v : Fin n → F) :
    (∑ x : Fin n → F, chi (dotProduct x v)) = if v = 0 then (2 ^ n : ℤ) else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [chi_zero, card_fin_fun]
  · rw [if_neg hv]
    have hex : ∃ j : Fin n, v j = 1 := by
      by_contra h
      push Not at h
      apply hv
      funext j
      rcases zmod2_eq_zero_or_one (v j) with hj | hj
      · exact hj
      · exact absurd hj (h j)
    obtain ⟨j, hj⟩ := hex
    let S : ℤ := ∑ x : Fin n → F, chi (dotProduct x v)
    have hshift : S = -S := by
      change (∑ x : Fin n → F, chi (dotProduct x v)) = -(∑ x : Fin n → F, chi (dotProduct x v))
      rw [← Finset.sum_neg_distrib]
      let σ : (Fin n → F) ≃ (Fin n → F) :=
        { toFun := fun x => x + Pi.single j (1 : F)
          invFun := fun x => x + Pi.single j (1 : F)
          left_inv := fun x => by dsimp only; rw [add_assoc, vec_add_self, add_zero]
          right_inv := fun x => by dsimp only; rw [add_assoc, vec_add_self, add_zero] }
      refine Fintype.sum_equiv σ
        (fun x => chi (dotProduct x v)) (fun x => -chi (dotProduct x v)) (fun x => ?_)
      dsimp only [σ, Equiv.coe_fn_mk]
      rw [add_dotProduct, single_dotProduct, one_mul, hj, chi_add, chi_one]
      ring
    omega

lemma perp_basis_three {s : ℕ} (W : Submodule F (Fin s → F))
    (hW : Module.finrank F W + 3 = s) :
    ∃ a b c : Fin s → F, ∀ u : Fin s → F,
      u ∈ W ↔ dotProduct a u = 0 ∧ dotProduct b u = 0 ∧ dotProduct c u = 0 := by
  have hfr : Module.finrank F (perp W) = 3 := by
    have := finrank_perp W; omega
  let e : (Fin 3 → F) ≃ₗ[F] perp W :=
    LinearEquiv.ofFinrankEq (R := F) (M := Fin 3 → F) (M' := perp W)
      (by rw [Module.finrank_fin_fun, hfr])
  let a : Fin s → F := (e (Pi.single 0 1)).1
  let b : Fin s → F := (e (Pi.single 1 1)).1
  let c : Fin s → F := (e (Pi.single 2 1)).1
  refine ⟨a, b, c, fun u => ?_⟩
  constructor
  · intro hu
    exact ⟨(mem_perp W a).mp (e (Pi.single 0 1)).2 u hu,
      (mem_perp W b).mp (e (Pi.single 1 1)).2 u hu,
      (mem_perp W c).mp (e (Pi.single 2 1)).2 u hu⟩
  · rintro ⟨ha, hb, hc⟩
    rw [← perp_perp W, mem_perp]
    intro v hv
    let lam : Fin 3 → F := e.symm ⟨v, hv⟩
    have hv_eq : v = lam 0 • a + lam 1 • b + lam 2 • c := by
      have hlam : lam = lam 0 • Pi.single 0 1 + lam 1 • Pi.single 1 1 + lam 2 • Pi.single 2 1 := by
        funext i; fin_cases i <;> simp [Pi.single_apply]
      have he : (e lam).1 = v := congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
      conv_lhs => rw [← he, hlam, map_add, map_add, map_smul, map_smul, map_smul]
      simp only [Submodule.coe_add, SetLike.val_smul]
      rfl
    rw [dotProduct_comm, hv_eq, add_dotProduct, add_dotProduct, smul_dotProduct,
      smul_dotProduct, smul_dotProduct, ha, hb, hc]
    simp

/-! ## Section 2: Finite Differences, `HasDeg`, Reed-Muller Min Weight, and Quadratics -/

def dd {n : ℕ} (f : (Fin n → F) → F) (u x : Fin n → F) : F := f (x + u) - f x

lemma dd_eq_add {n : ℕ} (f : (Fin n → F) → F) (u x : Fin n → F) :
    dd f u x = f (x + u) + f x := zmod2_sub_eq_add _ _

lemma dd_const {n : ℕ} (c : F) (u x : Fin n → F) : dd (fun _ => c) u x = 0 := by
  simp [dd]

lemma dd_add {n : ℕ} (f₁ f₂ : (Fin n → F) → F) (u x : Fin n → F) :
    dd (fun t => f₁ t + f₂ t) u x = dd f₁ u x + dd f₂ u x := by
  simp only [dd_eq_add]; ring

lemma dd_smul {n : ℕ} (c : F) (f : (Fin n → F) → F) (u x : Fin n → F) :
    dd (fun t => c * f t) u x = c * dd f u x := by
  simp only [dd_eq_add]; ring

lemma dd_comp_aff {s k : ℕ} (g : (Fin k → F) → F) (B : (Fin s → F) →ₗ[F] (Fin k → F))
    (a : Fin k → F) (u x : Fin s → F) :
    dd (fun t => g (a + B t)) u x = dd g (B u) (a + B x) := by
  simp only [dd, map_add]
  rw [add_assoc]

lemma dd_mul {n : ℕ} (f₁ f₂ : (Fin n → F) → F) (u x : Fin n → F) :
    dd (fun t => f₁ t * f₂ t) u x = dd f₁ u x * f₂ (x + u) + f₁ x * dd f₂ u x := by
  simp only [dd_eq_add]
  have h : ∀ a b c d : F, a * c + b * d = (a + b) * c + b * (c + d) := by decide
  exact h _ _ _ _

def HasDeg {n : ℕ} : ℕ → ((Fin n → F) → F) → Prop
  | 0, f => ∀ u x, dd f u x = 0
  | d + 1, f => ∀ u, HasDeg d (dd f u)

lemma hasDeg_zero_iff {n : ℕ} (f : (Fin n → F) → F) :
    HasDeg 0 f ↔ ∀ x y, f x = f y := by
  constructor
  · intro h x y
    have h1 := h (y - x) x
    simp only [dd, add_sub_cancel] at h1
    exact (sub_eq_zero.mp h1).symm
  · intro h u x
    simp only [dd, h (x + u) x, sub_self]

lemma hasDeg_const {n : ℕ} (d : ℕ) (c : F) : HasDeg d (fun _ : Fin n → F => c) := by
  induction d generalizing c with
  | zero => intro u x; exact dd_const c u x
  | succ d ih =>
    intro u
    have : dd (fun _ : Fin n → F => c) u = fun _ => 0 := by funext x; exact dd_const c u x
    rw [this]
    exact ih 0

lemma hasDeg_zero_fn {n : ℕ} (d : ℕ) : HasDeg d (fun _ : Fin n → F => (0 : F)) :=
  hasDeg_const d 0

lemma hasDeg_mono {n d : ℕ} {f : (Fin n → F) → F} (h : HasDeg d f) : HasDeg (d + 1) f := by
  induction d generalizing f with
  | zero =>
    intro u v x
    have h0 : dd f u = fun _ => 0 := by funext t; exact h u t
    rw [h0]
    exact dd_const 0 v x
  | succ d ih =>
    intro u
    exact ih (h u)

lemma hasDeg_add {n d : ℕ} {f₁ f₂ : (Fin n → F) → F}
    (h1 : HasDeg d f₁) (h2 : HasDeg d f₂) : HasDeg d (fun t => f₁ t + f₂ t) := by
  induction d generalizing f₁ f₂ with
  | zero =>
    intro u x
    rw [dd_add, h1 u x, h2 u x, zero_add]
  | succ d ih =>
    intro u
    have heq : dd (fun t => f₁ t + f₂ t) u = fun t => dd f₁ u t + dd f₂ u t := by
      funext t; exact dd_add f₁ f₂ u t
    rw [heq]
    exact ih (h1 u) (h2 u)

lemma hasDeg_smul {n d : ℕ} (c : F) {f : (Fin n → F) → F} (h : HasDeg d f) :
    HasDeg d (fun t => c * f t) := by
  induction d generalizing f with
  | zero =>
    intro u x
    rw [dd_smul, h u x, mul_zero]
  | succ d ih =>
    intro u
    have heq : dd (fun t => c * f t) u = fun t => c * dd f u t := by
      funext t; exact dd_smul c f u t
    rw [heq]
    exact ih (h u)

lemma hasDeg_sum {n d : ℕ} {ι : Type*} (S : Finset ι) (f : ι → (Fin n → F) → F)
    (hf : ∀ i ∈ S, HasDeg d (f i)) :
    HasDeg d (fun t => ∑ i ∈ S, f i t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using hasDeg_zero_fn (n := n) d
  | insert a S ha ih =>
    have heq : (fun t => ∑ i ∈ insert a S, f i t) = fun t => f a t + ∑ i ∈ S, f i t := by
      funext t; exact Finset.sum_insert ha
    rw [heq]
    exact hasDeg_add (hf a (Finset.mem_insert_self a S))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma hasDeg_translate {n d : ℕ} (a : Fin n → F) {f : (Fin n → F) → F} (h : HasDeg d f) :
    HasDeg d (fun t => f (a + t)) := by
  induction d generalizing f with
  | zero =>
    intro u x
    have : dd (fun t => f (a + t)) u x = dd f u (a + x) := by
      simp only [dd, add_assoc]
    rw [this, h u (a + x)]
  | succ d ih =>
    intro u
    have : dd (fun t => f (a + t)) u = fun t => dd f u (a + t) := by
      funext t; simp only [dd, add_assoc]
    rw [this]
    exact ih (h u)

lemma hasDeg_comp_aff {s k d : ℕ} (B : (Fin s → F) →ₗ[F] (Fin k → F)) (a : Fin k → F)
    {g : (Fin k → F) → F} (hg : HasDeg d g) :
    HasDeg d (fun t => g (a + B t)) := by
  induction d generalizing g with
  | zero =>
    intro u x
    rw [dd_comp_aff, hg (B u) (a + B x)]
  | succ d ih =>
    intro u
    have : dd (fun t => g (a + B t)) u = fun t => dd g (B u) (a + B t) := by
      funext t; exact dd_comp_aff g B a u t
    rw [this]
    exact ih (hg (B u))

lemma hasDeg_dot {n : ℕ} (v : Fin n → F) (c : F) :
    HasDeg 1 (fun t : Fin n → F => dotProduct v t + c) := by
  intro u w x
  have h1 : dd (fun t => dotProduct v t + c) u = fun _ => dotProduct v u := by
    funext t
    simp only [dd_eq_add, dotProduct_add]
    have h2 : dotProduct v t + dotProduct v t = 0 := zmod2_add_self _
    have h3 : c + c = 0 := zmod2_add_self _
    calc dotProduct v t + dotProduct v u + c + (dotProduct v t + c)
        = (dotProduct v t + dotProduct v t) + (c + c) + dotProduct v u := by ring
      _ = dotProduct v u := by rw [h2, h3]; ring
  rw [h1]
  exact dd_const _ w x

lemma hasDeg_mul_aff {n d : ℕ} {f₁ f₂ : (Fin n → F) → F}
    (h1 : HasDeg 1 f₁) (h2 : HasDeg d f₂) :
    HasDeg (d + 1) (fun t => f₁ t * f₂ t) := by
  induction d generalizing f₂ with
  | zero =>
    have hc : ∀ x, f₂ x = f₂ 0 := fun x => (hasDeg_zero_iff f₂).mp h2 x 0
    have heq : (fun t => f₁ t * f₂ t) = fun t => f₂ 0 * f₁ t := by
      funext t; rw [hc t, mul_comm]
    rw [heq]
    exact hasDeg_smul (f₂ 0) h1
  | succ d ih =>
    intro u
    have hconst : ∀ x, dd f₁ u x = dd f₁ u 0 := fun x => (hasDeg_zero_iff (dd f₁ u)).mp (h1 u) x 0
    have heq : dd (fun t => f₁ t * f₂ t) u =
        fun t => dd f₁ u 0 * f₂ (u + t) + f₁ t * dd f₂ u t := by
      funext t
      rw [dd_mul, hconst t, add_comm t u]
    rw [heq]
    exact hasDeg_add (hasDeg_smul _ (hasDeg_translate u h2)) (ih (h2 u))

lemma dd3_eq_zero_of_hasDeg2 {n : ℕ} {f : (Fin n → F) → F} (h : HasDeg 2 f) (u v w x : Fin n → F) :
    dd (dd (dd f u) v) w x = 0 := h u v w x

lemma dd3_const_in_x {n : ℕ} {f : (Fin n → F) → F} (h : HasDeg 3 f) (u v w x : Fin n → F) :
    dd (dd (dd f u) v) w x = dd (dd (dd f u) v) w 0 :=
  (hasDeg_zero_iff (dd (dd (dd f u) v) w)).mp (h u v w) x 0

lemma dd3_add {n : ℕ} (f₁ f₂ : (Fin n → F) → F) (u v w x : Fin n → F) :
    dd (dd (dd (fun t => f₁ t + f₂ t) u) v) w x =
      dd (dd (dd f₁ u) v) w x + dd (dd (dd f₂ u) v) w x := by
  have h1 : dd (fun t => f₁ t + f₂ t) u = fun t => dd f₁ u t + dd f₂ u t := by
    funext t; exact dd_add f₁ f₂ u t
  have h2 : dd (fun t => dd f₁ u t + dd f₂ u t) v = fun t => dd (dd f₁ u) v t + dd (dd f₂ u) v t := by
    funext t; exact dd_add _ _ v t
  rw [h1, h2, dd_add]

lemma dd3_comp_aff {s k : ℕ} {g : (Fin k → F) → F} (hg : HasDeg 3 g)
    (B : (Fin s → F) →ₗ[F] (Fin k → F)) (a : Fin k → F) (u v w x : Fin s → F) :
    dd (dd (dd (fun t => g (a + B t)) u) v) w x = dd (dd (dd g (B u)) (B v)) (B w) 0 := by
  have h1 : dd (fun t => g (a + B t)) u = fun t => dd g (B u) (a + B t) := by
    funext t; exact dd_comp_aff g B a u t
  have h2 : dd (fun t => dd g (B u) (a + B t)) v = fun t => dd (dd g (B u)) (B v) (a + B t) := by
    funext t; exact dd_comp_aff (dd g (B u)) B a v t
  rw [h1, h2, dd_comp_aff]
  exact dd3_const_in_x hg (B u) (B v) (B w) (a + B x)

/-! ### Hamming Weight, Reed-Muller Minimum Weight, and Coset Classification -/

def wt {n : ℕ} (f : (Fin n → F) → F) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → F => f x = 1)).card

lemma wt_add_one {n : ℕ} (f : (Fin n → F) → F) :
    wt f + wt (fun x => f x + 1) = 2 ^ n := by
  have hunion : Finset.univ.filter (fun x : Fin n → F => f x = 1) ∪
      Finset.univ.filter (fun x : Fin n → F => f x + 1 = 1) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have h : ∀ a : F, a = 1 ∨ a + 1 = 1 := by decide
    exact h (f x)
  have hdisj : Disjoint (Finset.univ.filter (fun x : Fin n → F => f x = 1))
      (Finset.univ.filter (fun x : Fin n → F => f x + 1 = 1)) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  unfold wt
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, card_fin_fun]

lemma sum_chi_eq_wt {n : ℕ} (f : (Fin n → F) → F) :
    (∑ x : Fin n → F, chi (f x)) = (2 ^ n : ℤ) - 2 * (wt f : ℤ) := by
  classical
  have h1 : ∀ x : Fin n → F, chi (f x) = (1 : ℤ) - if f x = 1 then 2 else 0 := by
    intro x
    have h : ∀ a : F, chi a = (1 : ℤ) - if a = 1 then 2 else 0 := by decide
    exact h (f x)
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_fin_fun]
  simp only [nsmul_eq_mul, mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  unfold wt
  push_cast
  ring

lemma exists_low_wt_shift {n : ℕ} (f : (Fin n → F) → F) :
    ∃ f₀ : (Fin n → F) → F, (f₀ = f ∨ f₀ = fun x => f x + 1) ∧
      2 * wt f₀ ≤ 2 ^ n ∧
      (∑ x : Fin n → F, chi (f x)).natAbs + 2 * wt f₀ = 2 ^ n := by
  have hsum := sum_chi_eq_wt f
  by_cases hle : 2 * wt f ≤ 2 ^ n
  · refine ⟨f, Or.inl rfl, hle, ?_⟩
    have hleZ : 2 * (wt f : ℤ) ≤ (2 ^ n : ℤ) := by exact_mod_cast hle
    have hnn : (0 : ℤ) ≤ (2 ^ n : ℤ) - 2 * (wt f : ℤ) := by linarith
    zify
    rw [hsum, abs_of_nonneg hnn]
    ring
  · refine ⟨fun x => f x + 1, Or.inr rfl, ?_, ?_⟩
    · have hcomp := wt_add_one f; omega
    · have hcomp := wt_add_one f
      have hgtZ : (2 ^ n : ℤ) < 2 * (wt f : ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hle)
      have hneg : (2 ^ n : ℤ) - 2 * (wt f : ℤ) ≤ 0 := by linarith
      have h2 : (wt f : ℤ) + (wt (fun x => f x + 1) : ℤ) = (2 ^ n : ℤ) := by exact_mod_cast hcomp
      zify
      rw [hsum, abs_of_nonpos hneg]
      linarith

lemma wt_dd_add_inter {n : ℕ} (f : (Fin n → F) → F) (u : Fin n → F) :
    wt (dd f u) + 2 * (Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1)).card =
      2 * wt f := by
  classical
  let A := Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 0)
  let B := Finset.univ.filter (fun x : Fin n → F => f x = 0 ∧ f (x + u) = 1)
  let C := Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1)
  have hdd : Finset.univ.filter (fun x : Fin n → F => dd f u x = 1) = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, dd_eq_add]
    rcases zmod2_eq_zero_or_one (f x) with h1 | h1 <;>
      rcases zmod2_eq_zero_or_one (f (x + u)) with h2 | h2 <;> simp [h1, h2]
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1.1] at h2; exact absurd h2.1 (by decide)
  have hAC : Finset.univ.filter (fun x : Fin n → F => f x = 1) = A ∪ C := by
    ext x
    simp only [A, C, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rcases zmod2_eq_zero_or_one (f (x + u)) with h2 | h2 <;> simp [h2]
  have hdisjAC : Disjoint A C := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)
  have hBC : Finset.univ.filter (fun x : Fin n → F => f (x + u) = 1) = B ∪ C := by
    ext x
    simp only [B, C, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rcases zmod2_eq_zero_or_one (f x) with h1 | h1 <;> simp [h1]
  have hdisjBC : Disjoint B C := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1.1] at h2; exact absurd h2.1 (by decide)
  have hshift : (Finset.univ.filter (fun x : Fin n → F => f (x + u) = 1)).card = wt f := by
    unfold wt
    refine Finset.card_nbij (fun x => x + u) ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
    · intro x _ y _ hxy; exact add_right_cancel hxy
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact ⟨y - u, by simp [hy], sub_add_cancel y u⟩
  have c1 : wt (dd f u) = A.card + B.card := by
    unfold wt; rw [hdd, Finset.card_union_of_disjoint hdisjAB]
  have c2 : wt f = A.card + C.card := by
    unfold wt; rw [hAC, Finset.card_union_of_disjoint hdisjAC]
  have c3 : wt f = B.card + C.card := by
    rw [← hshift, hBC, Finset.card_union_of_disjoint hdisjBC]
  change wt (dd f u) + 2 * C.card = 2 * wt f
  omega

lemma rm_min_wt {n d : ℕ} (f : (Fin n → F) → F) (hd : HasDeg d f) (hne : ∃ x, f x = 1) :
    2 ^ n ≤ 2 ^ d * wt f := by
  induction d generalizing f with
  | zero =>
    obtain ⟨x0, hx0⟩ := hne
    have hall : ∀ x, f x = 1 := fun x => ((hasDeg_zero_iff f).mp hd x x0).trans hx0
    have hwt : wt f = 2 ^ n := by
      unfold wt
      simp [hall, card_fin_fun]
    rw [hwt]; simp
  | succ d ih =>
    obtain ⟨x0, hx0⟩ := hne
    by_cases hall : ∀ x, f x = 1
    · have hwt : wt f = 2 ^ n := by
        unfold wt; simp [hall, card_fin_fun]
      rw [hwt]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    · push Not at hall
      obtain ⟨x1, hx1⟩ := hall
      have hx10 : f x1 = 0 := by
        rcases zmod2_eq_zero_or_one (f x1) with h | h
        · exact h
        · exact absurd h hx1
      let u := x1 - x0
      have hdd1 : dd f u x0 = 1 := by
        simp only [dd, u, add_sub_cancel, hx10, hx0]; decide
      have hih := ih (dd f u) (hd u) ⟨x0, hdd1⟩
      have hle : wt (dd f u) ≤ 2 * wt f := by
        have := wt_dd_add_inter f u; omega
      calc 2 ^ n ≤ 2 ^ d * wt (dd f u) := hih
        _ ≤ 2 ^ d * (2 * wt f) := Nat.mul_le_mul_left _ hle
        _ = 2 ^ (d + 1) * wt f := by ring

lemma rm_min_wt_coset {n d : ℕ} (hd1 : 1 ≤ d) (f : (Fin n → F) → F)
    (hd : HasDeg d f) (hne : ∃ x, f x = 1) (heq : 2 ^ d * wt f = 2 ^ n) :
    ∃ (x₀ : Fin n → F) (W : Submodule F (Fin n → F)),
      Module.finrank F W + d = n ∧ ∀ x, f x = 1 ↔ x - x₀ ∈ W := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hdich : ∀ u : Fin n → F,
      (∀ x, f (x + u) = f x) ∨ (∀ x, ¬ (f x = 1 ∧ f (x + u) = 1)) := by
    intro u
    by_cases h0 : ∃ x, dd f u x = 1
    · right
      have hd_prev : HasDeg (d - 1) (dd f u) := by
        rcases d with _ | d'
        · omega
        · exact hd u
      have hmin := rm_min_wt (dd f u) hd_prev h0
      have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
        rcases d with _ | d'
        · omega
        · simp [pow_succ]
      have hwt_ge : 2 * wt f ≤ wt (dd f u) := by
        have hmul : 2 ^ (d - 1) * (2 * wt f) ≤ 2 ^ (d - 1) * wt (dd f u) := by
          calc 2 ^ (d - 1) * (2 * wt f) = 2 ^ d * wt f := by rw [hpow]; ring
            _ = 2 ^ n := heq
            _ ≤ 2 ^ (d - 1) * wt (dd f u) := hmin
        exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos _)
      have hint0 : (Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1)).card = 0 := by
        have := wt_dd_add_inter f u; omega
      intro x hx
      have hmem : x ∈ Finset.univ.filter (fun x : Fin n → F => f x = 1 ∧ f (x + u) = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      rw [Finset.card_eq_zero] at hint0
      rw [hint0] at hmem
      exact Finset.notMem_empty x hmem
    · left
      push Not at h0
      intro x
      have hzx : dd f u x = 0 := by
        rcases zmod2_eq_zero_or_one (dd f u x) with h | h
        · exact h
        · exact absurd h (h0 x)
      exact sub_eq_zero.mp hzx
  let W : Submodule F (Fin n → F) :=
    { carrier := { u : Fin n → F | f (x₀ + u) = 1 }
      zero_mem' := by simp [hx₀], add_mem' := by
        intro u v hu hv
        change f (x₀ + u) = 1 at hu
        change f (x₀ + v) = 1 at hv
        change f (x₀ + (u + v)) = 1
        rcases hdich u with hco | hdisj
        · rw [add_comm u v, ← add_assoc, hco (x₀ + v), hv]
        · exact absurd ⟨hx₀, hu⟩ (hdisj x₀)
      smul_mem' := by
        intro c u hu
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp [hx₀]
        · simpa using hu }
  have hmemW : ∀ x, f x = 1 ↔ x - x₀ ∈ W := by
    intro x
    show f x = 1 ↔ f (x₀ + (x - x₀)) = 1
    rw [add_sub_cancel]
  have hcardW : wt f = Fintype.card W := by
    unfold wt
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x hx => (⟨x - x₀, (hmemW x).mp (Finset.mem_filter.mp hx).2⟩ : W)) ?_ ?_ ?_
    · intro x _; exact Finset.mem_univ _
    · intro x _ y _ hxy
      have h1 : x - x₀ = y - x₀ := congrArg Subtype.val hxy
      exact sub_left_inj.mp h1
    · intro w _
      refine ⟨x₀ + w.1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact w.2
      · ext j; simp
  rw [hcardW, card_submodule, ← pow_add] at heq
  have hdim : d + Module.finrank F W = n := Nat.pow_right_injective (by norm_num) heq
  exact ⟨x₀, W, by omega, hmemW⟩

lemma rm3_coset_wedge {s : ℕ} (f : (Fin s → F) → F) (hd : HasDeg 3 f)
    (hne : ∃ x, f x = 1) (heq : 8 * wt f = 2 ^ s) :
    ∃ a b c : Fin s → F, ∀ u v w,
      dd (dd (dd f u) v) w 0 =
        dd (dd (dd (fun t => dotProduct a t * dotProduct b t * dotProduct c t) u) v) w 0 := by
  have heq' : 2 ^ 3 * wt f = 2 ^ s := by simpa using heq
  obtain ⟨x₀, W, hWdim, hWmem⟩ := rm_min_wt_coset (by omega) f hd hne heq'
  obtain ⟨a, b, c, habc⟩ := perp_basis_three W hWdim
  let α : F := dotProduct a x₀ + 1
  let β : F := dotProduct b x₀ + 1
  let γ : F := dotProduct c x₀ + 1
  have hf_eq : ∀ t : Fin s → F,
      f t = (dotProduct a t + α) * (dotProduct b t + β) * (dotProduct c t + γ) := by
    intro t
    have hiff : f t = 1 ↔
        dotProduct a t + α = 1 ∧ dotProduct b t + β = 1 ∧ dotProduct c t + γ = 1 := by
      rw [hWmem t, habc (t - x₀)]
      simp only [dotProduct_sub, α, β, γ]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have e1 : dotProduct a t = dotProduct a x₀ := sub_eq_zero.mp h1
        have e2 : dotProduct b t = dotProduct b x₀ := sub_eq_zero.mp h2
        have e3 : dotProduct c t = dotProduct c x₀ := sub_eq_zero.mp h3
        rw [e1, e2, e3, ← add_assoc, zmod2_add_self, zero_add,
          ← add_assoc, zmod2_add_self, zero_add, ← add_assoc, zmod2_add_self, zero_add]
        exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨h1, h2, h3⟩
        have k : ∀ p q : F, p + (q + 1) = 1 → p - q = 0 := by
          intro p q; fin_cases p <;> fin_cases q <;> decide
        exact ⟨k _ _ h1, k _ _ h2, k _ _ h3⟩
    have hprod : (dotProduct a t + α) * (dotProduct b t + β) * (dotProduct c t + γ) = 1 ↔
        dotProduct a t + α = 1 ∧ dotProduct b t + β = 1 ∧ dotProduct c t + γ = 1 := by
      rcases zmod2_eq_zero_or_one (dotProduct a t + α) with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (dotProduct b t + β) with h2 | h2 <;>
        rcases zmod2_eq_zero_or_one (dotProduct c t + γ) with h3 | h3 <;> simp [h1, h2, h3]
    rcases zmod2_eq_zero_or_one (f t) with hft | hft <;>
      rcases zmod2_eq_zero_or_one ((dotProduct a t + α) * (dotProduct b t + β) * (dotProduct c t + γ)) with hp | hp
    · rw [hft, hp]
    · exfalso; have := hiff.mpr (hprod.mp hp); rw [hft] at this; exact absurd this (by decide)
    · exfalso; have := hprod.mpr (hiff.mp hft); rw [hp] at this; exact absurd this (by decide)
    · rw [hft, hp]
  let h : (Fin s → F) → F := fun t => dotProduct a t * dotProduct b t * dotProduct c t
  let q : (Fin s → F) → F := fun t =>
    γ * (dotProduct a t * dotProduct b t) +
    β * (dotProduct a t * dotProduct c t) +
    α * (dotProduct b t * dotProduct c t) +
    (β * γ) * dotProduct a t +
    (α * γ) * dotProduct b t +
    (α * β) * dotProduct c t +
    α * β * γ
  have hfq : f = fun t => h t + q t := by
    funext t
    rw [hf_eq t]
    simp only [h, q]
    ring
  have hq2 : HasDeg 2 q := by
    have hL : ∀ v : Fin s → F, HasDeg 1 (fun t => dotProduct v t) := fun v => by
      simpa using hasDeg_dot v 0
    have hQ : ∀ v w : Fin s → F, HasDeg 2 (fun t => dotProduct v t * dotProduct w t) := fun v w =>
      hasDeg_mul_aff (hL v) (hL w)
    exact hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add
      (hasDeg_smul γ (hQ a b))
      (hasDeg_smul β (hQ a c)))
      (hasDeg_smul α (hQ b c)))
      (hasDeg_smul (β * γ) (hasDeg_mono (hL a))))
      (hasDeg_smul (α * γ) (hasDeg_mono (hL b))))
      (hasDeg_smul (α * β) (hasDeg_mono (hL c))))
      (hasDeg_const 2 (α * β * γ))
  refine ⟨a, b, c, fun u v w => ?_⟩
  rw [hfq, dd3_add, dd3_eq_zero_of_hasDeg2 hq2 u v w 0, add_zero]

lemma triple_hasDeg3 {s : ℕ} (a b c : Fin s → F) :
    HasDeg 3 (fun t : Fin s → F => dotProduct a t * dotProduct b t * dotProduct c t) := by
  have hL : ∀ v : Fin s → F, HasDeg 1 (fun t => dotProduct v t) := fun v => by
    simpa using hasDeg_dot v 0
  have h2 : HasDeg 2 (fun t => dotProduct a t * dotProduct b t) := hasDeg_mul_aff (hL a) (hL b)
  have heq : (fun t => dotProduct a t * dotProduct b t * dotProduct c t) =
      fun t => dotProduct c t * (dotProduct a t * dotProduct b t) := by
    funext t; ring
  rw [heq]
  exact hasDeg_mul_aff (hL c) h2

lemma triple_wt_or_zero {s : ℕ} (a b c : Fin s → F) :
    (∀ u v w, dd (dd (dd (fun t => dotProduct a t * dotProduct b t * dotProduct c t) u) v) w 0 = 0) ∨
    8 * wt (fun t => dotProduct a t * dotProduct b t * dotProduct c t) = 2 ^ s := by
  classical
  let h : (Fin s → F) → F := fun t => dotProduct a t * dotProduct b t * dotProduct c t
  let Φ : (Fin s → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fun t => ![dotProduct a t, dotProduct b t, dotProduct c t]
      map_add' := fun x y => by
        funext i; fin_cases i <;> simp [dotProduct_add]
      map_smul' := fun r x => by
        funext i; fin_cases i <;> simp [dotProduct_smul] }
  by_cases hsurj : LinearMap.range Φ = ⊤
  · right
    have hfr := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hfr
    have hex : ∃ t1 : Fin s → F, Φ t1 = ![1, 1, 1] := by
      have : (![1, 1, 1] : Fin 3 → F) ∈ LinearMap.range Φ := by rw [hsurj]; trivial
      exact this
    obtain ⟨t1, ht1⟩ := hex
    have hiff : ∀ t : Fin s → F, h t = 1 ↔ t - t1 ∈ LinearMap.ker Φ := by
      intro t
      have h1 : h t = 1 ↔ Φ t = ![1, 1, 1] := by
        simp only [h, Φ, LinearMap.coe_mk, AddHom.coe_mk]
        constructor
        · intro ht
          have ha : dotProduct a t = 1 := by
            rcases zmod2_eq_zero_or_one (dotProduct a t) with h0 | h0
            · rw [h0] at ht; simp at ht
            · exact h0
          have hb : dotProduct b t = 1 := by
            rcases zmod2_eq_zero_or_one (dotProduct b t) with h0 | h0
            · rw [h0] at ht; simp at ht
            · exact h0
          have hc : dotProduct c t = 1 := by
            rcases zmod2_eq_zero_or_one (dotProduct c t) with h0 | h0
            · rw [h0] at ht; simp at ht
            · exact h0
          funext i; fin_cases i <;> simp [ha, hb, hc]
        · intro hφ
          have ha : dotProduct a t = 1 := by simpa using congrFun hφ 0
          have hb : dotProduct b t = 1 := by simpa using congrFun hφ 1
          have hc : dotProduct c t = 1 := by simpa using congrFun hφ 2
          rw [ha, hb, hc]; decide
      rw [h1, LinearMap.mem_ker, map_sub, ht1, sub_eq_zero]
    have hcard : wt h = Fintype.card (LinearMap.ker Φ) := by
      unfold wt
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun t ht => (⟨t - t1, (hiff t).mp (Finset.mem_filter.mp ht).2⟩ : LinearMap.ker Φ)) ?_ ?_ ?_
      · intro t _; exact Finset.mem_univ _
      · intro t _ t' _ htt'
        exact sub_left_inj.mp (congrArg Subtype.val htt')
      · intro w _
        refine ⟨t1 + w.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hiff]; simpa using w.2
        · ext j; simp
    rw [hcard, card_submodule]
    calc 8 * 2 ^ Module.finrank F (LinearMap.ker Φ)
        = 2 ^ (3 + Module.finrank F (LinearMap.ker Φ)) := by rw [pow_add]; norm_num
      _ = 2 ^ s := by rw [hfr]
  · left
    have hlt : Module.finrank F (LinearMap.range Φ) < 3 := by
      have hle : Module.finrank F (LinearMap.range Φ) ≤ 3 := by
        have := Submodule.finrank_le (LinearMap.range Φ)
        rw [Module.finrank_fin_fun] at this
        exact this
      by_contra hge
      have heq : Module.finrank F (LinearMap.range Φ) = 3 := by omega
      apply hsurj
      exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact heq)
    have hppos : 0 < Module.finrank F (perp (LinearMap.range Φ)) := by
      have := finrank_perp (LinearMap.range Φ); omega
    have : Nontrivial (perp (LinearMap.range Φ)) := Module.finrank_pos_iff.mp hppos
    obtain ⟨⟨lam, hlam_mem⟩, hlam_ne⟩ := exists_ne (0 : perp (LinearMap.range Φ))
    have hlam0 : lam ≠ 0 := fun h => hlam_ne (Subtype.ext h)
    have hcomb : lam 0 • a + lam 1 • b + lam 2 • c = 0 := by
      funext j
      have h0 := (mem_perp (LinearMap.range Φ) lam).mp hlam_mem (Φ (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
      rw [dotProduct, Fin.sum_univ_three] at h0
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, dotProduct_single, mul_one] at h0
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h0
    have hdeg2 : HasDeg 2 h := by
      have hL : ∀ v : Fin s → F, HasDeg 1 (fun t => dotProduct v t) := fun v => by
        simpa using hasDeg_dot v 0
      have hQ : ∀ v w : Fin s → F, HasDeg 2 (fun t => dotProduct v t * dotProduct w t) := fun v w =>
        hasDeg_mul_aff (hL v) (hL w)
      rcases zmod2_eq_zero_or_one (lam 0) with l0 | l0 <;>
        rcases zmod2_eq_zero_or_one (lam 1) with l1 | l1 <;>
        rcases zmod2_eq_zero_or_one (lam 2) with l2 | l2
      · exfalso; apply hlam0; funext i; fin_cases i <;> assumption
      · have hc0 : c = 0 := by simpa [l0, l1, l2] using hcomb
        have : h = fun _ => 0 := by funext t; simp [h, hc0]
        rw [this]; exact hasDeg_zero_fn 2
      · have hb0 : b = 0 := by simpa [l0, l1, l2] using hcomb
        have : h = fun _ => 0 := by funext t; simp [h, hb0]
        rw [this]; exact hasDeg_zero_fn 2
      · have hbc : b = c := by
          have : b + c = 0 := by simpa [l0, l1, l2] using hcomb
          calc b = b + (b + c) := by rw [this, add_zero]
            _ = (b + b) + c := by rw [add_assoc]
            _ = c := by rw [vec_add_self, zero_add]
        have : h = fun t => dotProduct a t * dotProduct b t := by
          funext t; simp only [h, hbc, mul_assoc, zmod2_mul_self]
        rw [this]; exact hQ a b
      · have ha0 : a = 0 := by simpa [l0, l1, l2] using hcomb
        have : h = fun _ => 0 := by funext t; simp [h, ha0]
        rw [this]; exact hasDeg_zero_fn 2
      · have hac : a = c := by
          have : a + c = 0 := by simpa [l0, l1, l2] using hcomb
          calc a = a + (a + c) := by rw [this, add_zero]
            _ = (a + a) + c := by rw [add_assoc]
            _ = c := by rw [vec_add_self, zero_add]
        have : h = fun t => dotProduct a t * dotProduct b t := by
          funext t
          simp only [h, hac]
          rw [mul_comm (dotProduct c t * dotProduct b t), ← mul_assoc, zmod2_mul_self]
        rw [this]; exact hQ a b
      · have hab : a = b := by
          have : a + b = 0 := by simpa [l0, l1, l2] using hcomb
          calc a = a + (a + b) := by rw [this, add_zero]
            _ = (a + a) + b := by rw [add_assoc]
            _ = b := by rw [vec_add_self, zero_add]
        have : h = fun t => dotProduct a t * dotProduct c t := by
          funext t; simp only [h, hab, zmod2_mul_self]
        rw [this]; exact hQ a c
      · have hcab : c = a + b := by
          have : a + b + c = 0 := by simpa [l0, l1, l2] using hcomb
          calc c = c + (a + b + c) := by rw [this, add_zero]
            _ = (a + b) + (c + c) := by abel
            _ = a + b := by rw [vec_add_self, add_zero]
        have : h = fun _ => 0 := by
          funext t
          simp only [h, hcab, add_dotProduct]
          generalize dotProduct a t = A
          generalize dotProduct b t = B
          fin_cases A <;> fin_cases B <;> decide
        rw [this]; exact hasDeg_zero_fn 2
    intro u v w
    exact dd3_eq_zero_of_hasDeg2 hdeg2 u v w 0

/-! ### Quadratic Representation of `HasDeg 2` Functions -/

def suppCard {s : ℕ} (t : Fin s → F) : ℕ :=
  (Finset.univ.filter (fun i : Fin s => t i = 1)).card

lemma quad_repr {s : ℕ} (f : (Fin s → F) → F) (hf : HasDeg 2 f) :
    ∃ (Q : Fin s → Fin s → F) (ℓ : Fin s → F) (c₀ : F),
      ∀ t : Fin s → F, f t = c₀ + ∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i) := by
  let c₀ : F := f 0
  let ℓ : Fin s → F := fun j => f (Pi.single j 1) + f 0
  let Q : Fin s → Fin s → F := fun i j =>
    if i < j then f (Pi.single i 1 + Pi.single j 1) + f (Pi.single i 1) + f (Pi.single j 1) + f 0
    else 0
  let q : (Fin s → F) → F := fun t =>
    c₀ + ∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i)
  have hq2 : HasDeg 2 q := by
    have hcoord : ∀ j : Fin s, HasDeg 1 (fun t : Fin s → F => t j) := fun j => by
      have : (fun t : Fin s → F => t j) = fun t => dotProduct (Pi.single j 1) t + 0 := by
        funext t; simp [single_dotProduct]
      rw [this]; exact hasDeg_dot _ 0
    refine hasDeg_add (hasDeg_const 2 c₀) (hasDeg_sum Finset.univ _ fun j _ => ?_)
    have hinner : HasDeg 1 (fun t : Fin s → F => ℓ j + ∑ i : Fin s, Q i j * t i) :=
      hasDeg_add (hasDeg_const 1 (ℓ j))
        (hasDeg_sum Finset.univ _ fun i _ => hasDeg_smul (Q i j) (hcoord i))
    exact hasDeg_mul_aff (hcoord j) hinner
  let r : (Fin s → F) → F := fun t => f t + q t
  have hr2 : HasDeg 2 r := hasDeg_add hf hq2
  have hq0 : q 0 = f 0 := by simp [q, c₀]
  have hq1 : ∀ a : Fin s, q (Pi.single a 1) = f (Pi.single a 1) := by
    intro a
    simp only [q, c₀, ℓ, Q]
    let ea : Fin s → F := Pi.single a 1
    have hs1 : (∑ j : Fin s, ea j *
        (f (Pi.single j 1) + f 0 + ∑ i : Fin s,
          (if i < j then f (Pi.single i 1 + Pi.single j 1) + f (Pi.single i 1) + f (Pi.single j 1) + f 0 else 0) *
          ea i)) = f (Pi.single a 1) + f 0 := by
      rw [Finset.sum_eq_single a]
      · simp only [ea, Pi.single_eq_same, one_mul]
        have hs2 : (∑ i : Fin s,
            (if i < a then f (Pi.single i 1 + Pi.single a 1) + f (Pi.single i 1) + f (Pi.single a 1) + f 0 else 0) *
            ((Pi.single a (1 : F) : Fin s → F) i)) = 0 := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro i _ hia; simp [Pi.single_eq_of_ne hia]
          · intro h; exact absurd (Finset.mem_univ a) h
        rw [hs2, add_zero]
      · intro j _ hja; simp [ea, Pi.single_eq_of_ne hja]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [hs1, ← add_assoc, add_comm (f 0) (f (Pi.single a 1)), add_assoc, zmod2_add_self, add_zero]
  have hq2pt : ∀ a b : Fin s, a < b → q (Pi.single a 1 + Pi.single b 1) = f (Pi.single a 1 + Pi.single b 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    have hne' : b ≠ a := ne_of_gt hab
    let t : Fin s → F := Pi.single a 1 + Pi.single b 1
    have ht_a : t a = 1 := by simp [t, Pi.single_eq_same, Pi.single_eq_of_ne hne]
    have ht_b : t b = 1 := by simp [t, Pi.single_eq_same, Pi.single_eq_of_ne hne']
    have ht_o : ∀ k, k ≠ a → k ≠ b → t k = 0 := fun k hka hkb => by
      simp [t, Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb]
    have hinner_a : (∑ i : Fin s, Q i a * t i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hia : i = a
      · subst hia; simp [Q]
      · by_cases hib : i = b
        · rw [hib]; have hnot : ¬ b < a := not_lt_of_gt hab; simp only [Q, hnot, ↓reduceIte, zero_mul]
        · rw [ht_o i hia hib, mul_zero]
    have hinner_b : (∑ i : Fin s, Q i b * t i) = Q a b := by
      rw [Finset.sum_eq_single a]
      · rw [ht_a, mul_one]
      · intro i _ hia
        by_cases hib : i = b
        · subst hib; simp [Q]
        · rw [ht_o i hia hib, mul_zero]
      · intro h; exact absurd (Finset.mem_univ a) h
    have houter : (∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i)) =
        (ℓ a + 0) + (ℓ b + Q a b) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ b⟩)]
      have hrest : (∑ j ∈ (Finset.univ.erase a).erase b, t j * (ℓ j + ∑ i : Fin s, Q i j * t i)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
        have hja : j ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        rw [ht_o j hja hjb, zero_mul]
      rw [hrest, add_zero, ht_a, ht_b, one_mul, one_mul, hinner_a, hinner_b]
    show c₀ + ∑ j : Fin s, t j * (ℓ j + ∑ i : Fin s, Q i j * t i) = f t
    rw [houter]
    simp only [c₀, ℓ, Q, hab, if_true, t]
    have e1 := zmod2_add_self (f 0)
    have e2 := zmod2_add_self (f (Pi.single a 1))
    have e3 := zmod2_add_self (f (Pi.single b 1))
    calc f 0 + (f (Pi.single a 1) + f 0 + 0 +
          (f (Pi.single b 1) + f 0 + (f (Pi.single a 1 + Pi.single b 1) + f (Pi.single a 1) + f (Pi.single b 1) + f 0)))
        = f (Pi.single a 1 + Pi.single b 1) + (f 0 + f 0) + (f 0 + f 0) +
          (f (Pi.single a 1) + f (Pi.single a 1)) + (f (Pi.single b 1) + f (Pi.single b 1)) := by ring
      _ = f (Pi.single a 1 + Pi.single b 1) := by rw [e1, e2, e3]; ring
  have hr_zero : ∀ m : ℕ, ∀ t : Fin s → F, suppCard t = m → r t = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro t hm
      let S := Finset.univ.filter (fun i : Fin s => t i = 1)
      have hScard : S.card = m := hm
      by_cases h0 : m = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
        have ht0 : t = 0 := by
          funext i
          rcases zmod2_eq_zero_or_one (t i) with hi | hi
          · exact hi
          · exfalso
            have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
            rw [hS0] at this; exact Finset.notMem_empty i this
        subst ht0; simp only [r, hq0, zmod2_add_self]
      · by_cases h1 : m = 1
        · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
          have hta : t = Pi.single a 1 := by
            funext i
            by_cases hia : i = a
            · subst hia
              have : i ∈ S := by rw [ha]; simp
              simp only [Pi.single_eq_same]
              exact (Finset.mem_filter.mp this).2
            · simp only [Pi.single_eq_of_ne hia]
              rcases zmod2_eq_zero_or_one (t i) with hi | hi
              · exact hi
              · exfalso
                have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
                rw [ha] at this; exact hia (Finset.mem_singleton.mp this)
          subst hta; simp only [r, hq1 a, zmod2_add_self]
        · by_cases h2 : m = 2
          · obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp (show S.card = 2 by omega)
            have htab : t = Pi.single a 1 + Pi.single b 1 := by
              funext i
              by_cases hia : i = a
              · subst hia
                have : i ∈ S := by rw [hSab]; simp
                simp [Pi.single_eq_same, Pi.single_eq_of_ne hab, (Finset.mem_filter.mp this).2]
              · by_cases hib : i = b
                · subst hib
                  have : i ∈ S := by rw [hSab]; simp
                  simp [Pi.single_eq_same, Pi.single_eq_of_ne hia, (Finset.mem_filter.mp this).2]
                · simp only [Pi.add_apply, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, add_zero]
                  rcases zmod2_eq_zero_or_one (t i) with hi | hi
                  · exact hi
                  · exfalso
                    have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
                    rw [hSab] at this
                    rcases Finset.mem_insert.mp this with rfl | hmem
                    · exact hia rfl
                    · exact hib (Finset.mem_singleton.mp hmem)
            subst htab
            rcases lt_or_gt_of_ne hab with hlt | hgt
            · simp only [r, hq2pt a b hlt, zmod2_add_self]
            · rw [add_comm (Pi.single a 1) (Pi.single b 1)]
              simp only [r, hq2pt b a hgt, zmod2_add_self]
          · have hm3 : 3 ≤ m := by omega
            have hSpos1 : 0 < S.card := by omega
            obtain ⟨a, ha⟩ := Finset.card_pos.mp hSpos1
            have hSpos2 : 0 < (S.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
            obtain ⟨b, hb'⟩ := Finset.card_pos.mp hSpos2
            have hba : b ≠ a := (Finset.mem_erase.mp hb').1
            have hb : b ∈ S := (Finset.mem_erase.mp hb').2
            have hSpos3 : 0 < ((S.erase a).erase b).card := by
              rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
            obtain ⟨c, hc'⟩ := Finset.card_pos.mp hSpos3
            have hcb : c ≠ b := (Finset.mem_erase.mp hc').1
            have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc').2).1
            have hc : c ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hc').2).2
            let ea : Fin s → F := Pi.single a 1
            let eb : Fin s → F := Pi.single b 1
            let ec : Fin s → F := Pi.single c 1
            let t' : Fin s → F := t + ea + eb + ec
            have hdd0 : dd (dd (dd r ea) eb) ec t' = 0 := hr2 ea eb ec t'
            have hexp : dd (dd (dd r ea) eb) ec t' =
                r (t' + ec + eb + ea) + r (t' + ec + eb) + r (t' + ec + ea) + r (t' + ec) +
                r (t' + eb + ea) + r (t' + eb) + r (t' + ea) + r t' := by
              simp only [dd_eq_add]; ring
            have htop : t' + ec + eb + ea = t := by
              simp only [t']
              calc t + ea + eb + ec + ec + eb + ea
                  = t + (ea + ea) + (eb + eb) + (ec + ec) := by abel
                _ = t := by rw [vec_add_self, vec_add_self, vec_add_self, add_zero, add_zero, add_zero]
            have hsub : ∀ p q w : F, (p = 0 ∨ q = 0 ∨ w = 0) →
                suppCard (t' + p • ea + q • eb + w • ec) < m := by
              intro p q w h0
              let z := t' + p • ea + q • eb + w • ec
              have hta1 : t a = 1 := (Finset.mem_filter.mp ha).2
              have htb1 : t b = 1 := (Finset.mem_filter.mp hb).2
              have htc1 : t c = 1 := (Finset.mem_filter.mp hc).2
              have hss : Finset.univ.filter (fun i : Fin s => z i = 1) ⊂ S := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨?_, ?_⟩
                · intro i hi
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                  by_cases hia : i = a
                  · subst hia; exact ha
                  · by_cases hib : i = b
                    · subst hib; exact hb
                    · by_cases hic : i = c
                      · subst hic; exact hc
                      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
                        have hzi : z i = t i := by
                          simp [z, t', ea, eb, ec, Pi.single_eq_of_ne hia,
                            Pi.single_eq_of_ne hib, Pi.single_eq_of_ne hic]
                        rwa [← hzi]
                · intro heqS
                  rcases h0 with rfl | rfl | rfl
                  · have hmem : a ∈ Finset.univ.filter (fun i : Fin s => z i = 1) := heqS ▸ ha
                    have hza : z a = 0 := by
                      simp [z, t', ea, eb, ec, hta1, Pi.single_eq_same,
                        Pi.single_eq_of_ne hba.symm, Pi.single_eq_of_ne hca.symm, zmod2_add_self]
                    have := (Finset.mem_filter.mp hmem).2
                    rw [hza] at this; exact absurd this (by decide)
                  · have hmem : b ∈ Finset.univ.filter (fun i : Fin s => z i = 1) := heqS ▸ hb
                    have hzb : z b = 0 := by
                      simp [z, t', ea, eb, ec, htb1, Pi.single_eq_same,
                        Pi.single_eq_of_ne hba, Pi.single_eq_of_ne hcb.symm, zmod2_add_self]
                    have := (Finset.mem_filter.mp hmem).2
                    rw [hzb] at this; exact absurd this (by decide)
                  · have hmem : c ∈ Finset.univ.filter (fun i : Fin s => z i = 1) := heqS ▸ hc
                    have hzc : z c = 0 := by
                      simp [z, t', ea, eb, ec, htc1, Pi.single_eq_same,
                        Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb, zmod2_add_self]
                    have := (Finset.mem_filter.mp hmem).2
                    rw [hzc] at this; exact absurd this (by decide)
              exact lt_of_lt_of_eq (Finset.card_lt_card hss) hScard
            have hzero_pt : ∀ p q w : F, (p = 0 ∨ q = 0 ∨ w = 0) →
                r (t' + p • ea + q • eb + w • ec) = 0 := fun p q w h0 =>
              ih _ (hsub p q w h0) _ rfl
            have r1 : r (t' + ec + eb) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 1 1 (Or.inl rfl)
            have r2 : r (t' + ec + ea) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 1 0 1 (Or.inr (Or.inl rfl))
            have r3 : r (t' + ec) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 0 1 (Or.inl rfl)
            have r4 : r (t' + eb + ea) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 1 1 0 (Or.inr (Or.inr rfl))
            have r5 : r (t' + eb) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 1 0 (Or.inl rfl)
            have r6 : r (t' + ea) = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 1 0 0 (Or.inr (Or.inl rfl))
            have r7 : r t' = 0 := by
              simpa [add_comm, add_left_comm, add_assoc] using hzero_pt 0 0 0 (Or.inl rfl)
            rw [hexp, htop, r1, r2, r3, r4, r5, r6, r7] at hdd0
            simpa using hdd0
  refine ⟨Q, ℓ, c₀, fun t => ?_⟩
  have hrt : f t + q t = 0 := hr_zero (suppCard t) t rfl
  calc f t = f t + (f t + q t) := by rw [hrt, add_zero]
    _ = (f t + f t) + q t := by rw [add_assoc]
    _ = q t := by rw [zmod2_add_self, zero_add]

/-! ## Section 3: Circuit Partition Decomposition (Simplified `L_lib_835` with `IsAff`) -/

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_length (gs : List Gate) :
    ∀ x : List Bool, (gs.foldl step x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x; simp only [List.foldl_cons, ih, step]; simp; omega

lemma foldl_step_getD (gs : List Gate) :
    ∀ (x : List Bool) (i : ℕ), i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro x i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp only [step, List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma foldl_step_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl step x = step (gs.foldl step x) g := by simp [List.foldl_append]

lemma step_getD_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

lemma step_getD_old (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ hi

def bitsN (n : ℕ) (v : Fin n → F) : List Bool := List.ofFn (fun j : Fin n => decide (v j = 1))

lemma bitsN_length (n : ℕ) (v : Fin n → F) : (bitsN n v).length = n := by simp [bitsN]

lemma bitsN_getD (n : ℕ) (v : Fin n → F) (j : ℕ) (hj : j < n) :
    (bitsN n v).getD j false = decide (v ⟨j, hj⟩ = 1) := by
  simp [bitsN, List.getD_eq_getElem?_getD, hj]

def GOk (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧ (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.mod 2 ∨
    (h.op = GateOp.not ∧ h.inputs.length = 1))

def LegalG (n : ℕ) (ds : List Gate) : Prop :=
  (∀ j < ds.length, ∀ i ∈ (ds.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧ ∀ h ∈ ds, GOk h

noncomputable def costG (ds : List Gate) : ℕ :=
  ds.countP (fun h => @decide ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2)
    (Classical.propDecidable _))

lemma costG_snoc_zero (ds : List Gate) (g : Gate)
    (h : ¬((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) :
    costG (ds ++ [g]) = costG ds := by
  unfold costG; rw [List.countP_append]; simp [h]

lemma costG_snoc_one (ds : List Gate) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    costG (ds ++ [g]) = costG ds + 1 := by
  unfold costG; rw [List.countP_append]; simp [h]

def lin {k : ℕ} (s u : Fin k → F) : Bool := decide (dotProduct s u = 1)

lemma lin_add_right {k : ℕ} (s u v : Fin k → F) : lin s (u + v) = xor (lin s u) (lin s v) := by
  simp only [lin, dotProduct_add, dec_add]

lemma lin_add_left {k : ℕ} (s s' u : Fin k → F) : lin (s + s') u = xor (lin s u) (lin s' u) := by
  simp only [lin, add_dotProduct, dec_add]

lemma lin_zero_left {k : ℕ} (u : Fin k → F) : lin (0 : Fin k → F) u = false := by simp [lin]

lemma lin_bit_smul {k : ℕ} (s d : Fin k → F) (b : Bool) :
    lin s ((if b then (1 : F) else 0) • d) = (b && lin s d) := by cases b <;> simp [lin]

lemma lin_single {k : ℕ} (j : Fin k) (u : Fin k → F) :
    lin (Pi.single j 1) u = decide (u j = 1) := by simp [lin, single_dotProduct]

lemma lin_sum {k : ℕ} (ins : List ℕ) (s : ℕ → Fin k → F) (u : Fin k → F) :
    lin (ins.map s).sum u = ins.foldr (fun i acc => xor (lin (s i) u) acc) false := by
  induction ins with
  | nil => simp [lin_zero_left]
  | cons a l ih => simp [List.sum_cons, lin_add_left, ih]

lemma aff_eval (op : GateOp) (ins : List ℕ) (hok : GOk ⟨op, ins⟩)
    (hn : ¬((op = GateOp.and ∨ op = GateOp.or) ∧ ins.length = 2)) (cs ls : ℕ → Bool) :
    op.eval (ins.map fun i => xor (cs i) (ls i)) =
      xor (op.eval (ins.map cs)) (ins.foldr (fun i acc => xor (ls i) acc) false) := by
  obtain ⟨hl, hop⟩ := hok
  simp only at hl hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩ <;> simp [GateOp.eval]
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    generalize cs a = A; generalize ls a = B
    rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩ <;> cases A <;> cases B <;> decide
  · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩
    · exact absurd ⟨Or.inl rfl, rfl⟩ hn
    · exact absurd ⟨Or.inr rfl, rfl⟩ hn
    · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      generalize cs a = A; generalize ls a = B; generalize cs b = C; generalize ls b = D
      cases A <;> cases B <;> cases C <;> cases D <;> decide
    · simp at h
  · simp at hl

def IsAff {t : ℕ} (f : (Fin t → F) → Bool) : Prop :=
  ∃ (v : Fin t → F) (b : Bool), ∀ z, f z = xor b (lin v z)

lemma isAff_const {t : ℕ} (b : Bool) : IsAff (fun _ : Fin t → F => b) :=
  ⟨0, b, fun z => by simp [lin_zero_left]⟩

lemma isAff_coord {t : ℕ} (j : Fin t) : IsAff (fun z : Fin t → F => decide (z j = 1)) :=
  ⟨Pi.single j 1, false, fun z => by simp [lin_single]⟩

lemma isAff_xor {t : ℕ} {f₁ f₂ : (Fin t → F) → Bool} (h1 : IsAff f₁) (h2 : IsAff f₂) :
    IsAff (fun z => xor (f₁ z) (f₂ z)) := by
  obtain ⟨v1, b1, h1⟩ := h1
  obtain ⟨v2, b2, h2⟩ := h2
  refine ⟨v1 + v2, xor b1 b2, fun z => ?_⟩
  dsimp only
  rw [h1 z, h2 z, lin_add_left]
  cases b1 <;> cases b2 <;> cases lin v1 z <;> cases lin v2 z <;> rfl

lemma isAff_congr {t : ℕ} {f₁ f₂ : (Fin t → F) → Bool} (h1 : IsAff f₁) (heq : ∀ z, f₁ z = f₂ z) :
    IsAff f₂ := by
  obtain ⟨v, b, hv⟩ := h1; exact ⟨v, b, fun z => (heq z).symm.trans (hv z)⟩

lemma isAff_gate {t : ℕ} (g : Gate) (hg : GOk g)
    (hnb : ¬((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2))
    (cs : ℕ → (Fin t → F) → Bool) (hcs : ∀ i ∈ g.inputs, IsAff (cs i)) :
    IsAff (fun z => g.op.eval (g.inputs.map fun i => cs i z)) := by
  classical
  have hpick : ∀ i : ℕ, ∃ p : (Fin t → F) × Bool, i ∈ g.inputs → ∀ z, cs i z = xor p.2 (lin p.1 z) := by
    intro i
    by_cases hi : i ∈ g.inputs
    · obtain ⟨v, b, hv⟩ := hcs i hi
      exact ⟨(v, b), fun _ => hv⟩
    · exact ⟨(0, false), fun h => absurd h hi⟩
  choose p hp using hpick
  refine ⟨(g.inputs.map fun i => (p i).1).sum, g.op.eval (g.inputs.map fun i => (p i).2), fun z => ?_⟩
  have hmap : (g.inputs.map fun i => cs i z) = g.inputs.map (fun i => xor (p i).2 (lin (p i).1 z)) :=
    List.map_congr_left (fun i hi => hp i hi z)
  dsimp only
  rw [hmap, aff_eval g.op g.inputs hg hnb (fun i => (p i).2) (fun i => lin (p i).1 z), lin_sum]

lemma isAff_hasDeg1 {t : ℕ} {f : (Fin t → F) → Bool} (hf : IsAff f) :
    HasDeg 1 (fun z => b2f (f z)) := by
  obtain ⟨v, b, hv⟩ := hf
  have heq : (fun z => b2f (f z)) = fun z => dotProduct v z + b2f b := by
    funext z
    rw [hv z, b2f_xor, lin, b2f_decide, add_comm]
  rw [heq]
  exact hasDeg_dot v (b2f b)

structure Piece (k t : ℕ) where
  U : Submodule F (Fin k → F)
  r : ℕ
  e : ℕ
  p : (Fin t → F) → (Fin k → F)
  c : ℕ → (Fin t → F) → Bool
  s : ℕ → (Fin k → F)

def PInv (k t : ℕ) (gs : List Gate) (P : Piece k t) : Prop :=
  Module.finrank F P.U + P.r = k ∧ P.e + P.r ≤ costG gs ∧
  (P.e = 0 → (∀ w < k + t + gs.length, IsAff (P.c w)) ∧
    ∀ j : Fin k, IsAff (fun z => decide (P.p z j = 1))) ∧
  ∀ z, ∀ u ∈ P.U, ∀ w < k + t + gs.length,
    (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD w false = xor (P.c w z) (lin (P.s w) u)

noncomputable def cnt {k t : ℕ} (L : List (Piece k t)) (z : Fin t → F) (x : Fin k → F) : ℕ :=
  L.countP (fun Q => @decide (x - Q.p z ∈ Q.U) (Classical.propDecidable _))

lemma xin_length (k t : ℕ) (v : Fin k → F) (z : Fin t → F) :
    (bitsN k v ++ bitsN t z).length = k + t := by simp [bitsN_length]

lemma cw_old (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ [g]).foldl step x).getD w false = (gs.foldl step x).getD w false := by
  rw [foldl_step_snoc, step_getD_old _ _ _ (by rw [foldl_step_length]; exact hw)]

lemma cw_new (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl step x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false) := by
  rw [foldl_step_snoc, ← foldl_step_length, step_getD_new]

lemma split_dim {k : ℕ} (U : Submodule F (Fin k → F)) (s d : Fin k → F) (hd : d ∈ U)
    (hsd : dotProduct s d = 1) :
    ∃ U' : Submodule F (Fin k → F), Module.finrank F U' + 1 = Module.finrank F U ∧
      ∀ v, v ∈ U' ↔ v ∈ U ∧ dotProduct s v = 0 := by
  let ψ := (dotLin s).comp U.subtype
  refine ⟨(LinearMap.ker ψ).map U.subtype, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have hr : LinearMap.range ψ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨y • ⟨d, hd⟩, ?_⟩
      simp [ψ, dotLin, dotProduct_smul, hsd]
    rw [hr, finrank_top, Module.finrank_self] at h1
    rw [Submodule.finrank_map_subtype_eq]
    omega
  · intro v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, ψ,
      LinearMap.comp_apply, dotLin, LinearMap.coe_mk, AddHom.coe_mk]
    exact ⟨fun ⟨y, hy, h⟩ => h ▸ ⟨y.2, hy⟩, fun ⟨hv, h0⟩ => ⟨⟨v, hv⟩, h0, rfl⟩⟩

lemma bit_cases (a : F) (b : Bool) : a - (if b then 1 else 0) = 0 ↔ decide (a = 1) = b := by
  fin_cases a <;> cases b <;> decide

lemma pbit_shift {k : ℕ} (v d : Fin k → F) (b : Bool) (j : Fin k) :
    decide ((v + (if b then (1 : F) else 0) • d) j = 1) =
      xor (decide (v j = 1)) (b && decide (d j = 1)) := by cases b <;> simp [dec_add]

lemma init_piece (k t : ℕ) : ∃ P : Piece k t, PInv k t [] P ∧ ∀ z x, x - P.p z ∈ P.U := by
  let P : Piece k t :=
    { U := ⊤, r := 0, e := 0, p := fun _ => 0,
      c := fun w z => if w < k then false else
        if h : w - k < t then decide (z ⟨w - k, h⟩ = 1) else false,
      s := fun w => if h : w < k then Pi.single ⟨w, h⟩ 1 else 0 }
  refine ⟨P, ⟨by simp [P], by simp [P, costG], ?_, ?_⟩, fun _ _ => Submodule.mem_top⟩
  · intro _
    refine ⟨fun w hw => ?_, fun j => isAff_congr (isAff_const false) (fun z => by simp [P])⟩
    by_cases hwk : w < k
    · exact isAff_congr (isAff_const false) (fun z => by simp [P, hwk])
    · have hwt : w - k < t := by simp at hw; omega
      exact isAff_congr (isAff_coord ⟨w - k, hwt⟩) (fun z => by simp [P, hwk, hwt])
  · intro z u _ w hw
    simp only [List.length_nil, add_zero] at hw
    simp only [List.foldl_nil, P, zero_add]
    by_cases hwk : w < k
    · rw [List.getD_append _ _ _ _ (by rw [bitsN_length]; exact hwk), bitsN_getD _ _ _ hwk]
      simp [hwk, lin_single]
    · have hwt : w - k < t := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [bitsN_length]; omega), bitsN_length,
        bitsN_getD _ _ _ hwt]
      simp [hwk, hwt, lin_zero_left]

lemma cnt_single_mem {k t : ℕ} (Q : Piece k t) (z : Fin t → F) (x : Fin k → F)
    (h : x - Q.p z ∈ Q.U) : cnt [Q] z x = 1 := by simp [cnt, h]

lemma cnt_single_not {k t : ℕ} (Q : Piece k t) (z : Fin t → F) (x : Fin k → F)
    (h : x - Q.p z ∉ Q.U) : cnt [Q] z x = 0 := by simp [cnt, h]

lemma step_piece {k t : ℕ} (gs : List Gate) (g : Gate) (hg : GOk g)
    (hin : ∀ i ∈ g.inputs, i < k + t + gs.length) (P : Piece k t) (hP : PInv k t gs P) :
    ∃ L : List (Piece k t), (∀ Q ∈ L, PInv k t (gs ++ [g]) Q) ∧
      ∀ z x, (x - P.p z ∈ P.U → cnt L z x = 1) ∧ (x - P.p z ∉ P.U → cnt L z x = 0) := by
  classical
  obtain ⟨hrank, hcost, haff, hval⟩ := hP
  set m := k + t + gs.length with hm
  have hlen1 : k + t + (gs ++ [g]).length = m + 1 := by simp [hm]; omega
  have Cold : ∀ v z w, w < m → ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD w false =
      (gs.foldl step (bitsN k v ++ bitsN t z)).getD w false := fun v z w hw =>
    cw_old gs g _ w (by rw [xin_length]; omega)
  have Cnew : ∀ v z, ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD m false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step (bitsN k v ++ bitsN t z)).getD i false) := by
    intro v z; have h := cw_new gs g (bitsN k v ++ bitsN t z); rw [xin_length] at h; exact h
  by_cases hbin : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  · obtain ⟨hop, hl2⟩ := hbin
    obtain ⟨i1, i2, hgi⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs, hl2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hi1 : i1 < m := hin i1 (by rw [hgi]; simp)
    have hi2 : i2 < m := hin i2 (by rw [hgi]; simp)
    have hcostC : costG (gs ++ [g]) = costG gs + 1 := costG_snoc_one _ _ ⟨hop, hl2⟩
    obtain ⟨A, hA⟩ : ∃ A : Bool, ∀ X Y : Bool,
        g.op.eval [X, Y] = (if A then (X && Y) else (X || Y)) := by
      rcases hop with h | h
      · exact ⟨true, fun X Y => by rw [h]; cases X <;> cases Y <;> rfl⟩
      · exact ⟨false, fun X Y => by rw [h]; cases X <;> cases Y <;> rfl⟩
    by_cases hz : ∀ u ∈ P.U, lin (P.s i1) u = false ∧ lin (P.s i2) u = false
    · let Q : Piece k t :=
        { U := P.U, r := P.r, e := P.e + 1, p := P.p,
          c := fun w => if w = m then (fun z => g.op.eval [P.c i1 z, P.c i2 z]) else P.c w,
          s := fun w => if w = m then 0 else P.s w }
      refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
        fun h => cnt_single_not Q z x h⟩⟩
      intro Q' hQ'
      simp only [List.mem_singleton] at hQ'
      subst hQ'
      refine ⟨hrank, by simp only [Q]; rw [hcostC]; omega, by intro h; simp only [Q] at h; omega, ?_⟩
      intro z u hu w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        simp only [Q, if_true]
        rw [Cnew, hgi]
        simp only [List.map_cons, List.map_nil]
        rw [hval z u hu i1 hi1, hval z u hu i2 hi2, (hz u hu).1, (hz u hu).2, lin_zero_left]
        simp
      · simp only [Q, hwm, if_false]
        rw [Cold _ _ _ (by omega), hval z u hu w (by omega)]
    · push Not at hz
      obtain ⟨u0, hu0, hne⟩ := hz
      have key : ∀ ia ib, ia < m → ib < m →
          (∀ v z, ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD m false =
            (if A then ((gs.foldl step (bitsN k v ++ bitsN t z)).getD ia false &&
              (gs.foldl step (bitsN k v ++ bitsN t z)).getD ib false)
             else ((gs.foldl step (bitsN k v ++ bitsN t z)).getD ia false ||
              (gs.foldl step (bitsN k v ++ bitsN t z)).getD ib false))) →
          ∀ d ∈ P.U, lin (P.s ia) d = true →
          ∃ L : List (Piece k t), (∀ Q ∈ L, PInv k t (gs ++ [g]) Q) ∧
            ∀ z x, (x - P.p z ∈ P.U → cnt L z x = 1) ∧ (x - P.p z ∉ P.U → cnt L z x = 0) := by
        intro ia ib hia hib hCval d hd hdl
        have hsd : dotProduct (P.s ia) d = 1 := of_decide_eq_true hdl
        obtain ⟨U', hU'rank, hU'mem⟩ := split_dim P.U (P.s ia) d hd hsd
        have hU'U : ∀ v, v ∈ U' → v ∈ P.U := fun v hv => ((hU'mem v).1 hv).1
        have hU'lin : ∀ v, v ∈ U' → lin (P.s ia) v = false := fun v hv => by
          simp [lin, ((hU'mem v).1 hv).2]
        let bf : Bool → (Fin t → F) → Bool := fun β z => xor β (P.c ia z)
        let pass : Bool → Bool := fun β => if A then β else !β
        let child : Bool → Piece k t := fun β =>
          { U := U', r := P.r + 1, e := P.e,
            p := fun z => P.p z + (if bf β z then (1 : F) else 0) • d,
            c := fun w z => if w = m then
                (if pass β then xor (P.c ib z) (bf β z && lin (P.s ib) d) else β)
              else xor (P.c w z) (bf β z && lin (P.s w) d),
            s := fun w => if w = m then (if pass β then P.s ib else 0) else P.s w }
        have hmem : ∀ β z x, (x - (child β).p z ∈ (child β).U ↔
            (x - P.p z ∈ P.U ∧ lin (P.s ia) (x - P.p z) = bf β z)) := by
          intro β z x
          show x - (P.p z + (if bf β z then (1 : F) else 0) • d) ∈ U' ↔ _
          rw [hU'mem, sub_add_eq_sub_sub]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨by simpa using P.U.add_mem h1 (P.U.smul_mem (if bf β z then (1 : F) else 0) hd), ?_⟩
            rw [dotProduct_sub, dotProduct_smul, hsd, smul_eq_mul, mul_one] at h2
            exact (bit_cases _ _).1 h2
          · rintro ⟨h1, h2⟩
            refine ⟨P.U.sub_mem h1 (P.U.smul_mem _ hd), ?_⟩
            rw [dotProduct_sub, dotProduct_smul, hsd, smul_eq_mul, mul_one]
            exact (bit_cases _ _).2 h2
        have hchild : ∀ β, PInv k t (gs ++ [g]) (child β) := by
          intro β
          refine ⟨by show Module.finrank F U' + (P.r + 1) = k; omega,
            by show P.e + (P.r + 1) ≤ costG (gs ++ [g]); rw [hcostC]; omega, ?_, ?_⟩
          · intro he0
            obtain ⟨hcw, hpb⟩ := haff he0
            have hbf : IsAff (bf β) := isAff_xor (isAff_const β) (hcw ia hia)
            have hold : ∀ w, w < m → IsAff (fun z => xor (P.c w z) (bf β z && lin (P.s w) d)) := by
              intro w hw
              cases hlw : lin (P.s w) d
              · exact isAff_congr (hcw w hw) (fun z => by simp)
              · exact isAff_congr (isAff_xor (hcw w hw) hbf) (fun z => by simp)
            refine ⟨fun w hw => ?_, fun j => ?_⟩
            · rw [hlen1] at hw
              by_cases hwm : w = m
              · subst hwm
                cases hp : pass β
                · exact isAff_congr (isAff_const β) (fun z => by simp [child, hp])
                · exact isAff_congr (hold ib hib) (fun z => by simp [child, hp])
              · exact isAff_congr (hold w (by omega)) (fun z => by simp [child, hwm])
            · cases hdj : decide (d j = 1)
              · exact isAff_congr (hpb j) (fun z => by dsimp only [child]; rw [pbit_shift, hdj]; simp)
              · exact isAff_congr (isAff_xor (hpb j) hbf) (fun z => by dsimp only [child]; rw [pbit_shift, hdj]; simp)
          · intro z u' hu' w hw
            rw [hlen1] at hw
            have hu : (if bf β z then (1 : F) else 0) • d + u' ∈ P.U :=
              P.U.add_mem (P.U.smul_mem _ hd) (hU'U u' hu')
            have hpt : (child β).p z + u' = P.p z + ((if bf β z then (1 : F) else 0) • d + u') := by
              show P.p z + _ + u' = _; rw [add_assoc]
            have hold : ∀ w, w < m →
                (gs.foldl step (bitsN k ((child β).p z + u') ++ bitsN t z)).getD w false
                  = xor (xor (P.c w z) (bf β z && lin (P.s w) d)) (lin (P.s w) u') := fun w hw => by
              rw [hpt, hval z _ hu w hw, lin_add_right, lin_bit_smul, Bool.xor_assoc]
            by_cases hwm : w = m
            · subst hwm
              rw [hCval, hold ia hia, hold ib hib, hdl, hU'lin u' hu']
              show _ = xor (if m = m then (if pass β then _ else β) else _)
                (lin (if m = m then (if pass β then P.s ib else 0) else P.s m) u')
              simp only [if_true]
              have hli : lin (if pass β then P.s ib else 0) u' = (pass β && lin (P.s ib) u') := by
                cases pass β <;> simp [lin_zero_left]
              rw [hli]
              simp only [pass, bf]
              generalize P.c ia z = C1; generalize P.c ib z = C2
              generalize lin (P.s ib) d = L1; generalize lin (P.s ib) u' = L2
              cases A <;> cases β <;> cases C1 <;> cases C2 <;> cases L1 <;> cases L2 <;>
                simp [lin_zero_left]
            · rw [Cold _ _ _ (by omega), hold w (by omega)]
              show _ = xor (if w = m then _ else _) (lin (if w = m then _ else P.s w) u')
              simp [hwm]
        refine ⟨[child false, child true], ?_, fun z x => ⟨fun h => ?_, fun h => ?_⟩⟩
        · intro Q hQ
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
          rcases hQ with rfl | rfl <;> exact hchild _
        · by_cases hl : lin (P.s ia) (x - P.p z) = bf false z
          · have m0 : x - (child false).p z ∈ (child false).U := (hmem false z x).2 ⟨h, hl⟩
            have m1 : x - (child true).p z ∉ (child true).U := by
              rw [hmem]; rintro ⟨_, h2⟩; rw [hl] at h2; simp [bf] at h2
            simp [cnt, List.countP_cons, m0, m1]
          · have m0 : x - (child false).p z ∉ (child false).U := by
              rw [hmem]; exact fun hh => hl hh.2
            have m1 : x - (child true).p z ∈ (child true).U := by
              rw [hmem]
              refine ⟨h, ?_⟩
              revert hl; simp only [bf]
              cases lin (P.s ia) (x - P.p z) <;> cases P.c ia z <;> simp
            simp [cnt, List.countP_cons, m0, m1]
        · have m0 : x - (child false).p z ∉ (child false).U := by rw [hmem]; exact fun hh => h hh.1
          have m1 : x - (child true).p z ∉ (child true).U := by rw [hmem]; exact fun hh => h hh.1
          simp [cnt, List.countP_cons, m0, m1]
      by_cases h1 : lin (P.s i1) u0 = true
      · refine key i1 i2 hi1 hi2 (fun v z => ?_) u0 hu0 h1
        rw [Cnew, hgi]; exact hA _ _
      · have h2 : lin (P.s i2) u0 = true := by
          cases hb : lin (P.s i1) u0
          · exact Bool.eq_true_of_not_eq_false (hne hb)
          · exact absurd hb h1
        refine key i2 i1 hi2 hi1 (fun v z => ?_) u0 hu0 h2
        rw [Cnew, hgi]; simp only [List.map_cons, List.map_nil]
        rw [hA]; cases A <;> simp [Bool.and_comm, Bool.or_comm]
  · let Q : Piece k t :=
      { U := P.U, r := P.r, e := P.e, p := P.p,
        c := fun w => if w = m then (fun z => g.op.eval (g.inputs.map fun i => P.c i z)) else P.c w,
        s := fun w => if w = m then (g.inputs.map P.s).sum else P.s w }
    refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
      fun h => cnt_single_not Q z x h⟩⟩
    intro Q' hQ'
    simp only [List.mem_singleton] at hQ'
    subst hQ'
    refine ⟨hrank, by simp only [Q]; rw [costG_snoc_zero _ _ hbin]; exact hcost, ?_, ?_⟩
    · intro he0
      obtain ⟨hcw, hpb⟩ := haff he0
      refine ⟨fun w hw => ?_, hpb⟩
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        have hg_aff := isAff_gate g hg hbin P.c (fun i hi => hcw i (hin i hi))
        exact isAff_congr hg_aff (fun z => by simp [Q])
      · exact isAff_congr (hcw w (by omega)) (fun z => by simp [Q, hwm])
    · intro z u hu w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        simp only [Q, if_true]
        rw [Cnew]
        have e1 : (g.inputs.map fun i => (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD i false)
            = g.inputs.map fun i => xor (P.c i z) (lin (P.s i) u) :=
          List.map_congr_left (fun i hi => hval z u hu i (hin i hi))
        rw [e1, aff_eval g.op g.inputs hg hbin (fun i => P.c i z) (fun i => lin (P.s i) u), lin_sum]
      · simp only [Q, hwm, if_false]
        rw [Cold _ _ _ (by omega), hval z u hu w (by omega)]

lemma step_list {k t : ℕ} (gs : List Gate) (g : Gate) (hg : GOk g)
    (hin : ∀ i ∈ g.inputs, i < k + t + gs.length) :
    ∀ L : List (Piece k t), (∀ P ∈ L, PInv k t gs P) →
      ∃ L' : List (Piece k t), (∀ Q ∈ L', PInv k t (gs ++ [g]) Q) ∧
        ∀ z x, cnt L' z x = cnt L z x := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, fun _ _ => rfl⟩
  | cons P L ih =>
    intro hL
    obtain ⟨LP, hLP, hcP⟩ := step_piece gs g hg hin P (hL P (List.mem_cons_self ..))
    obtain ⟨L', hL', hc'⟩ := ih (fun Q hQ => hL Q (List.mem_cons_of_mem _ hQ))
    refine ⟨LP ++ L', fun Q hQ => (List.mem_append.1 hQ).elim (hLP Q) (hL' Q), fun z x => ?_⟩
    have e1 : cnt (LP ++ L') z x = cnt LP z x + cnt L' z x := by simp only [cnt, List.countP_append]
    rw [e1, hc' z x]
    by_cases hm : x - P.p z ∈ P.U
    · rw [(hcP z x).1 hm]; simp only [cnt, List.countP_cons, hm, decide_true, ↓reduceIte]; omega
    · rw [(hcP z x).2 hm]; simp only [cnt, List.countP_cons, hm, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

lemma all_gates {k t : ℕ} (C : Circuit) (hC : ∀ h ∈ C.gates, GOk h)
    (hRB : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < k + t + j) :
    ∀ n, n ≤ C.gates.length → ∃ L : List (Piece k t),
      (∀ P ∈ L, PInv k t (C.gates.take n) P) ∧ ∀ z x, cnt L z x = 1 := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨P, hP, hm⟩ := init_piece k t
    exact ⟨[P], by simpa using hP, fun z x => cnt_single_mem P z x (hm z x)⟩
  | succ n ih =>
    intro hn
    obtain ⟨L, hL, hc⟩ := ih (by omega)
    have hlt : n < C.gates.length := by omega
    have htake : C.gates.take (n + 1) = C.gates.take n ++ [C.gates[n]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]; rfl
    have e : C.gates.getD n ⟨GateOp.or, []⟩ = C.gates[n] := by
      simp [List.getD_eq_getElem?_getD, hlt]
    obtain ⟨L', hL', hc'⟩ := step_list (C.gates.take n) (C.gates[n]) (hC _ (List.getElem_mem hlt))
      (fun i hi => by have h := hRB n hlt i (by rw [e]; exact hi); rw [List.length_take]; omega) L hL
    exact ⟨L', by rw [htake]; exact hL', fun z x => (hc' z x).trans (hc z x)⟩

lemma exists_unique_of_count {α : Type*} (q : α → Prop) :
    ∀ l : List α, l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 1 →
      ∃! i : Fin l.length, q (l.get i) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    rw [List.countP_cons] at h
    by_cases ha : q a
    · have h0 : l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 0 := by
        have e : (@decide (q a) (Classical.propDecidable _)) = true :=
          @decide_eq_true _ (Classical.propDecidable _) ha
        rw [e, if_pos rfl] at h; omega
      rw [List.countP_eq_zero] at h0
      refine ⟨⟨0, by simp⟩, by simpa using ha, ?_⟩
      intro j hj
      rcases j with ⟨_ | j, hjl⟩
      · rfl
      · exfalso
        have hj' : q (l.get ⟨j, by simpa using hjl⟩) := by simpa using hj
        have := h0 (l.get ⟨j, by simpa using hjl⟩) (List.get_mem _ _)
        simp only [decide_eq_true_eq] at this
        exact this hj'
    · have h1 : l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 1 := by
        have e : (@decide (q a) (Classical.propDecidable _)) = false :=
          @decide_eq_false _ (Classical.propDecidable _) ha
        rw [e, if_neg Bool.false_ne_true] at h; omega
      obtain ⟨i, hi, huniq⟩ := ih h1
      refine ⟨i.succ, by simpa using hi, ?_⟩
      intro j hj
      rcases j with ⟨_ | j, hjl⟩
      · exfalso; exact ha (by simpa using hj)
      · have := huniq ⟨j, by simpa using hjl⟩ (by simpa using hj)
        exact Fin.ext (by simp [← this])

lemma circuit_decomp (k s : ℕ) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * k) C)
    (hG : ∀ h ∈ C.gates, GOk h) (hcost : costG C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F (Fin k → F))
      (a : Fin N → (Fin k → F)) (p : Fin N → (Fin k → F) → (Fin k → F))
      (c : Fin N → (Fin k → F) → Bool),
      0 < N ∧
      (∀ i, Module.finrank F (U i) + r i = k ∧ r i ≤ s) ∧
      (∀ i, r i = s → IsAff (c i) ∧ ∀ j : Fin k, IsAff (fun z => decide (p i z j = 1))) ∧
      (∀ y x, ∃! i : Fin N, x - p i y ∈ U i) ∧
      (∀ i y u, u ∈ U i →
        C.eval (bitsN k (p i y + u) ++ bitsN k y) = xor (c i y) (lin (a i) u)) := by
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < k + k + j := by
    intro j hj i hi
    have h := hRB j hj i hi
    omega
  obtain ⟨L, hL, hc⟩ := all_gates (k := k) (t := k) C hG hRB' C.gates.length le_rfl
  rw [List.take_length] at hL
  set M := k + k + C.gates.length with hM
  refine ⟨L.length, fun i => (L.get i).r, fun i => (L.get i).U,
    fun i => if C.output < M then (L.get i).s C.output else 0,
    fun i => (L.get i).p,
    fun i y => if C.output < M then (L.get i).c C.output y else false,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := hc 0 0
    rcases L with _ | ⟨P, L⟩
    · simp [cnt] at h
    · simp
  · intro i
    obtain ⟨hrank, hce, _, _⟩ := hL (L.get i) (List.get_mem _ _)
    dsimp only
    exact ⟨hrank, by omega⟩
  · intro i hris
    dsimp only at hris ⊢
    obtain ⟨_, hce, haff, _⟩ := hL (L.get i) (List.get_mem _ _)
    have he0 : (L.get i).e = 0 := by omega
    obtain ⟨hcw, hpb⟩ := haff he0
    refine ⟨?_, hpb⟩
    by_cases ho : C.output < M
    · exact isAff_congr (hcw C.output ho) (fun y => by simp [ho])
    · exact isAff_congr (isAff_const false) (fun y => by simp [ho])
  · intro y x
    exact exists_unique_of_count (fun Q : Piece k k => x - Q.p y ∈ Q.U) L (hc y x)
  · intro i y u hu
    obtain ⟨_, _, _, hval⟩ := hL (L.get i) (List.get_mem _ _)
    dsimp only
    show (C.gates.foldl step (bitsN k ((L.get i).p y + u) ++ bitsN k y)).getD C.output false = _
    by_cases ho : C.output < M
    · rw [hval y u hu C.output ho]
      simp only [ho, ↓reduceIte]
    · simp only [ho, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by rw [foldl_step_length, xin_length]; omega)]
      simp [lin_zero_left]

/-! ## Section 4: Fourier Upper Bound & High-Bias Quadratic Fit -/

lemma natAbs_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

def rawScore {k : ℕ} (g : (Fin k → F) → F) (C : Circuit) : ℕ :=
  (∑ x : Fin k → F, ∑ y : Fin k → F,
    if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1).natAbs

lemma high_bias_quad_fit (k s : ℕ) (g : (Fin k → F) → F) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * k) C)
    (hG : ∀ h ∈ C.gates, GOk h) (hcost : costG C.gates ≤ s) :
    4 * rawScore g C ≤ 4 * 2 ^ (k + s) ∧
    (3 * 2 ^ (k + s) ≤ 4 * rawScore g C →
      ∃ (B : (Fin s → F) →ₗ[F] (Fin k → F)) (a : Fin k → F) (q : (Fin s → F) → F),
        Function.Injective B ∧ HasDeg 2 q ∧
        4 * rawScore g C ≤
          2 ^ k * (4 * (∑ t : Fin s → F, chi (g (a + B t) + q t)).natAbs)) := by
  classical
  obtain ⟨N, r, U, a, p, c, hNpos, hrk, haff, hpart, heval⟩ := circuit_decomp k s C hRB hG hcost
  -- For each y, (i, u) ↦ p i y + u is a bijection (Σ i : Fin N, U i) ≃ (Fin k → F)
  have hbij : ∀ y : Fin k → F, Function.Bijective (fun z : Σ i : Fin N, U i => p z.1 y + z.2.1) := by
    intro y
    constructor
    · rintro ⟨i1, u1⟩ ⟨i2, u2⟩ hEq
      dsimp only at hEq
      let x := p i1 y + u1.1
      have h1 : x - p i1 y ∈ U i1 := by simp [x, u1.2]
      have h2 : x - p i2 y ∈ U i2 := by rw [show x = p i2 y + u2.1 from hEq]; simp [u2.2]
      obtain ⟨i0, _, huniq⟩ := hpart y x
      have hi : i1 = i2 := (huniq i1 h1).trans (huniq i2 h2).symm
      subst hi
      have hu : u1.1 = u2.1 := add_left_cancel hEq
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hu))
    · intro x
      obtain ⟨i, hi, _⟩ := hpart y x
      exact ⟨⟨i, ⟨x - p i y, hi⟩⟩, add_sub_cancel (p i y) x⟩
  -- Cardinality sum: ∑ i : Fin N, 2 ^ (k - r i) = 2 ^ k
  have hcardU : ∀ i : Fin N, Fintype.card (U i) = 2 ^ (k - r i) := fun i => by
    rw [card_submodule]; have := (hrk i).1; congr 1; omega
  have hsum_card : (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k := by
    have h1 := Fintype.card_congr (Equiv.ofBijective _ (hbij 0))
    rw [Fintype.card_sigma, card_fin_fun] at h1
    simp_rw [hcardU] at h1
    exact h1
  -- Evaluate the signed correlation sum
  let T : Fin N → ℕ := fun i =>
    (∑ z : perp (U i),
      chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1))).natAbs
  have hS_eq :
      (∑ x : Fin k → F, ∑ y : Fin k → F,
        if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
      ∑ i : Fin N, (2 ^ (k - r i) : ℤ) *
        (∑ z : perp (U i),
          chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1))) := by
    rw [Finset.sum_comm]
    have hinner : ∀ y : Fin k → F,
        (∑ x : Fin k → F,
          if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1) =
        ∑ i : Fin N,
          chi (b2f (c i y) + dotProduct (p i y) y + g y) *
            (if y + a i ∈ perp (U i) then (2 ^ (k - r i) : ℤ) else 0) := by
      intro y
      rw [← Fintype.sum_equiv (Equiv.ofBijective _ (hbij y))
        (fun z => if C.eval (bitsN k (p z.1 y + z.2.1) ++ bitsN k y) =
            decide (dotProduct (p z.1 y + z.2.1) y + g y = 1)
          then (1 : ℤ) else -1) _ (fun _ => rfl)]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : ∀ u : U i,
          (if C.eval (bitsN k (p i y + u.1) ++ bitsN k y) =
              decide (dotProduct (p i y + u.1) y + g y = 1)
            then (1 : ℤ) else -1) =
          chi (b2f (c i y) + dotProduct (p i y) y + g y) * chi (dotProduct (y + a i) u.1) := by
        intro u
        rw [agree_eq_sg_chi, heval i y u.1 u.2, lin, sg_xor, sg_eq_chi_b2f, add_dotProduct,
          dotProduct_comm u.1 y, add_dotProduct]
        simp only [chi_add]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum, sum_chi_dot_subspace, hcardU i]
      push_cast; rfl
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfilt : (∑ y : Fin k → F,
        chi (b2f (c i y) + dotProduct (p i y) y + g y) *
          (if y + a i ∈ perp (U i) then (2 ^ (k - r i) : ℤ) else 0)) =
      (2 ^ (k - r i) : ℤ) *
        ∑ z : perp (U i),
          chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1)) := by
      rw [Finset.mul_sum]
      have hsplit : (∑ y : Fin k → F,
          chi (b2f (c i y) + dotProduct (p i y) y + g y) *
            (if y + a i ∈ perp (U i) then (2 ^ (k - r i) : ℤ) else 0)) =
        ∑ y ∈ Finset.univ.filter (fun y : Fin k → F => y + a i ∈ perp (U i)),
          (2 ^ (k - r i) : ℤ) * chi (b2f (c i y) + dotProduct (p i y) y + g y) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
      rw [hsplit]
      refine Finset.sum_bij (fun y hy => (⟨y + a i, (Finset.mem_filter.mp hy).2⟩ : perp (U i))) ?_ ?_ ?_ ?_
      · intro y _; exact Finset.mem_univ _
      · intro y1 _ y2 _ hEq
        exact add_right_cancel (congrArg Subtype.val hEq)
      · intro z _
        refine ⟨a i + z.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have : a i + z.1 + a i = z.1 := by
            rw [add_comm (a i) z.1, add_assoc, vec_add_self, add_zero]
          rw [this]; exact z.2
        · ext j
          simp only [Pi.add_apply]
          rw [add_comm (a i j) (z.1 j), add_assoc, zmod2_add_self, add_zero]
      · intro y hy
        have heq : a i + (y + a i) = y := by
          rw [add_comm y (a i), ← add_assoc, vec_add_self, zero_add]
        simp only [heq]
    exact hfilt
  -- Triangle inequality on rawScore
  have hraw_le : rawScore g C ≤ ∑ i : Fin N, 2 ^ (k - r i) * T i := by
    unfold rawScore
    rw [hS_eq]
    have htri : (∑ i : Fin N, (2 ^ (k - r i) : ℤ) *
        (∑ z : perp (U i),
          chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1)))).natAbs ≤
      ∑ i : Fin N, ((2 ^ (k - r i) : ℤ) *
        (∑ z : perp (U i),
          chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1)))).natAbs :=
      natAbs_sum_le _ _
    refine le_trans htri (Finset.sum_le_sum fun i _ => ?_)
    rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
  -- Trivial bound T i ≤ 2 ^ (r i)
  have hT_le : ∀ i : Fin N, T i ≤ 2 ^ (r i) := by
    intro i
    have hcardP : Fintype.card (perp (U i)) = 2 ^ (r i) := by
      rw [card_submodule]
      have h1 := finrank_perp (U i)
      have h2 := (hrk i).1
      congr 1; omega
    have h1 := natAbs_sum_le (Finset.univ : Finset (perp (U i)))
      (fun z => chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1)))
    have h2 : (∑ z : perp (U i),
        (chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1))).natAbs) =
        2 ^ (r i) := by
      simp_rw [chi_abs]
      rw [Finset.sum_const, Finset.card_univ, hcardP, smul_eq_mul, mul_one]
    exact h1.trans_eq h2
  constructor
  · -- Universal upper bound 4 * rawScore g C ≤ 4 * 2 ^ (k + s)
    have h1 : rawScore g C ≤ 2 ^ (k + s) := by
      calc rawScore g C ≤ ∑ i : Fin N, 2 ^ (k - r i) * T i := hraw_le
        _ ≤ ∑ i : Fin N, 2 ^ (k - r i) * 2 ^ s := Finset.sum_le_sum fun i _ =>
            Nat.mul_le_mul_left _ ((hT_le i).trans (Nat.pow_le_pow_right (by norm_num) (hrk i).2))
        _ = (∑ i : Fin N, 2 ^ (k - r i)) * 2 ^ s := (Finset.sum_mul _ _ _).symm
        _ = 2 ^ k * 2 ^ s := by rw [hsum_card]
        _ = 2 ^ (k + s) := (pow_add 2 k s).symm
    omega
  · -- High-bias quadratic fit when 3 * 2 ^ (k + s) ≤ 4 * rawScore g C
    intro hhigh
    have hex_i : ∃ i : Fin N, 4 * rawScore g C ≤ 2 ^ k * (4 * T i) := by
      by_contra hlt
      push Not at hlt
      have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
        ⟨⟨0, hNpos⟩, Finset.mem_univ _⟩
      have hstrict :
          (∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * (4 * T i))) <
            ∑ i : Fin N, 2 ^ (k - r i) * (4 * rawScore g C) :=
        Finset.sum_lt_sum_of_nonempty hne fun i _ =>
          Nat.mul_lt_mul_of_pos_left (hlt i) (Nat.two_pow_pos _)
      have hlhs : 2 ^ k * (4 * rawScore g C) ≤ ∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * (4 * T i)) := by
        calc 2 ^ k * (4 * rawScore g C)
            ≤ 2 ^ k * (4 * ∑ i : Fin N, 2 ^ (k - r i) * T i) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hraw_le)
          _ = ∑ i : Fin N, 2 ^ k * (4 * (2 ^ (k - r i) * T i)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
          _ = ∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * (4 * T i)) :=
              Finset.sum_congr rfl fun i _ => by ring
      have hrhs : (∑ i : Fin N, 2 ^ (k - r i) * (4 * rawScore g C)) = 2 ^ k * (4 * rawScore g C) := by
        rw [← Finset.sum_mul, hsum_card]
      omega
    obtain ⟨i, hi_bound⟩ := hex_i
    have hTi_ge : 3 * 2 ^ s ≤ 4 * T i := by
      have h1 : 2 ^ k * (3 * 2 ^ s) ≤ 2 ^ k * (4 * T i) := by
        calc 2 ^ k * (3 * 2 ^ s) = 3 * 2 ^ (k + s) := by rw [pow_add]; ring
          _ ≤ 4 * rawScore g C := hhigh
          _ ≤ 2 ^ k * (4 * T i) := hi_bound
      exact Nat.le_of_mul_le_mul_left h1 (Nat.two_pow_pos _)
    have hris : r i = s := by
      have hle := (hrk i).2
      by_contra hne
      have hlt : r i + 1 ≤ s := by omega
      have hpow : 2 ^ (r i) * 2 ≤ 2 ^ s := by
        calc 2 ^ (r i) * 2 = 2 ^ (r i + 1) := (pow_succ 2 (r i)).symm
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hlt
      have hTi := hT_le i
      have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
      omega
    obtain ⟨hc_aff, hp_aff⟩ := haff i hris
    have hfrP : Module.finrank F (perp (U i)) = s := by
      have h1 := finrank_perp (U i)
      have h2 := (hrk i).1
      omega
    let e : (Fin s → F) ≃ₗ[F] perp (U i) :=
      LinearEquiv.ofFinrankEq (R := F) (M := Fin s → F) (M' := perp (U i))
        (by rw [Module.finrank_fin_fun, hfrP])
    let B : (Fin s → F) →ₗ[F] (Fin k → F) := (perp (U i)).subtype.comp e.toLinearMap
    have hBinj : Function.Injective B := Subtype.val_injective.comp e.injective
    let q : (Fin s → F) → F := fun t =>
      b2f (c i (a i + B t)) + dotProduct (p i (a i + B t)) (a i + B t)
    have hq2 : HasDeg 2 q := by
      have h1 : HasDeg 2 (fun t => b2f (c i (a i + B t))) :=
        hasDeg_mono (hasDeg_comp_aff B (a i) (isAff_hasDeg1 hc_aff))
      have h2 : HasDeg 2 (fun t => dotProduct (p i (a i + B t)) (a i + B t)) := by
        simp only [dotProduct]
        refine hasDeg_sum Finset.univ _ fun j _ => ?_
        have hpa : HasDeg 1 (fun t => p i (a i + B t) j) := by
          have heq : (fun y : Fin k → F => p i y j) = fun y => b2f (decide (p i y j = 1)) := by
            funext y; exact (b2f_decide _).symm
          have h1y : HasDeg 1 (fun y : Fin k → F => p i y j) := by
            rw [heq]; exact isAff_hasDeg1 (hp_aff j)
          exact hasDeg_comp_aff B (a i) h1y
        have hya : HasDeg 1 (fun t => (a i + B t) j) := by
          have h1y : HasDeg 1 (fun y : Fin k → F => y j) := by
            have : (fun y : Fin k → F => y j) = fun y => dotProduct (Pi.single j 1) y + 0 := by
              funext y; simp [single_dotProduct]
            rw [this]; exact hasDeg_dot _ 0
          exact hasDeg_comp_aff B (a i) h1y
        exact hasDeg_mul_aff hpa hya
      exact hasDeg_add h1 h2
    have hsum_eq :
        (∑ t : Fin s → F, chi (g (a i + B t) + q t)) =
        ∑ z : perp (U i),
          chi (b2f (c i (a i + z.1)) + dotProduct (p i (a i + z.1)) (a i + z.1) + g (a i + z.1)) := by
      refine Fintype.sum_equiv e.toEquiv _ _ fun t => ?_
      dsimp only [B, q, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.coe_subtype,
        LinearEquiv.coe_toEquiv]
      congr 1; ring
    refine ⟨B, a i, q, hBinj, hq2, ?_⟩
    rw [hsum_eq]
    exact hi_bound

/-! ## Section 5: Circuit Construction for Any Injective `B` and Quadratic `q` -/

def Real (n : ℕ) (ds : List Gate) (f : (Fin n → F) → Bool) : Prop :=
  ∃ w, w < n + ds.length ∧ ∀ z, (ds.foldl step (bitsN n z)).getD w false = f z

lemma real_mono {n : ℕ} {ds : List Gate} {f : (Fin n → F) → Bool} (more : List Gate)
    (h : Real n ds f) : Real n (ds ++ more) f := by
  obtain ⟨w, hw, hv⟩ := h
  refine ⟨w, by simp; omega, fun z => ?_⟩
  rw [List.foldl_append, foldl_step_getD more _ w (by rw [foldl_step_length, bitsN_length]; exact hw), hv]

lemma real_congr {n : ℕ} {ds : List Gate} {f f' : (Fin n → F) → Bool} (h : Real n ds f)
    (heq : ∀ z, f z = f' z) : Real n ds f' := by
  obtain ⟨w, hw, hv⟩ := h; exact ⟨w, hw, fun z => (hv z).trans (heq z)⟩

lemma real_input {n : ℕ} (ds : List Gate) (j : Fin n) :
    Real n ds (fun z => decide (z j = 1)) := by
  refine ⟨j.val, by omega, fun z => ?_⟩
  rw [foldl_step_getD ds _ j.val (by rw [bitsN_length]; exact j.isLt), bitsN_getD n z j.val j.isLt]

lemma real_gate {n : ℕ} {ds : List Gate} (hL : LegalG n ds) (op : GateOp)
    (fs : List ((Fin n → F) → Bool)) (hfs : ∀ f ∈ fs, Real n ds f)
    (hok : ∀ ins : List ℕ, ins.length = fs.length → GOk ⟨op, ins⟩) :
    ∃ g : Gate, g.op = op ∧ g.inputs.length = fs.length ∧ LegalG n (ds ++ [g]) ∧
      Real n (ds ++ [g]) (fun z => op.eval (fs.map fun f => f z)) := by
  classical
  have hc : ∀ f, ∃ w, f ∈ fs → w < n + ds.length ∧
      ∀ z, (ds.foldl step (bitsN n z)).getD w false = f z := by
    intro f
    by_cases hf : f ∈ fs
    · obtain ⟨w, hw, hv⟩ := hfs f hf; exact ⟨w, fun _ => ⟨hw, hv⟩⟩
    · exact ⟨0, fun h => absurd h hf⟩
  choose τ hτ using hc
  refine ⟨Gate.mk op (fs.map τ), rfl, by simp, ⟨fun j hj i hi => ?_, fun h hh => ?_⟩, ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j ds.length with hj' | hj'
    · rw [List.getD_append _ _ _ _ hj'] at hi; exact hL.1 j hj' i hi
    · have hjeq : j = ds.length := by omega
      subst hjeq
      have e : (ds ++ [Gate.mk op (fs.map τ)]).getD ds.length (Gate.mk GateOp.or []) =
          Gate.mk op (fs.map τ) := by rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
      rw [e] at hi
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hi
      exact (hτ f hf).1
  · rcases List.mem_append.mp hh with hh | hh
    · exact hL.2 h hh
    · rw [List.mem_singleton.mp hh]; exact hok _ (by simp)
  · refine ⟨n + ds.length, by simp, fun z => ?_⟩
    rw [foldl_step_snoc]
    have hlen : (ds.foldl step (bitsN n z)).length = n + ds.length := by
      rw [foldl_step_length, bitsN_length]
    rw [← hlen, step_getD_new]
    congr 1; rw [List.map_map]
    exact List.map_congr_left fun f hf => (hτ f hf).2 z

lemma real_const {n : ℕ} {ds : List Gate} (hL : LegalG n ds) (β : Bool) :
    ∃ ds', LegalG n ds' ∧ costG ds' = costG ds ∧ (∀ h, Real n ds h → Real n ds' h) ∧
      Real n ds' (fun _ => β) := by
  obtain ⟨g1, _, hl1, hL1, hr1⟩ := real_gate hL (if β then GateOp.and else GateOp.or) []
    (by simp) (fun ins hins => ⟨show ins.length ≤ 2 by rw [List.length_nil] at hins; omega, by cases β <;> simp⟩)
  refine ⟨ds ++ [g1], hL1, costG_snoc_zero _ _ (by simp at hl1; simp [hl1]),
    fun _ hh => real_mono _ hh, real_congr hr1 (fun _ => by cases β <;> rfl)⟩

lemma real_xor {n : ℕ} {ds : List Gate} (hL : LegalG n ds) (f b : (Fin n → F) → Bool)
    (hf : Real n ds f) (hb : Real n ds b) :
    ∃ ds', LegalG n ds' ∧ costG ds' = costG ds ∧ (∀ h, Real n ds h → Real n ds' h) ∧
      Real n ds' (fun z => xor (f z) (b z)) := by
  obtain ⟨g1, hg1, _, hL1, hr1⟩ := real_gate hL (GateOp.mod 2) [f, b]
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
    (fun ins hins => ⟨show ins.length ≤ 2 by simp at hins; omega, Or.inr (Or.inr (Or.inl rfl))⟩)
  obtain ⟨g2, hg2, _, hL2, hr2⟩ := real_gate hL1 GateOp.not [_] (by simpa using hr1)
    (fun ins hins => ⟨show ins.length ≤ 2 by simp at hins; omega,
      Or.inr (Or.inr (Or.inr ⟨rfl, show ins.length = 1 by simpa using hins⟩))⟩)
  refine ⟨ds ++ [g1] ++ [g2], hL2, ?_, fun _ hh => real_mono _ (real_mono _ hh), ?_⟩
  · rw [costG_snoc_zero _ _ (by rw [hg2]; simp), costG_snoc_zero _ _ (by rw [hg1]; simp)]
  · obtain ⟨w, hw, hv⟩ := hr2
    refine ⟨w, hw, fun z => ?_⟩
    rw [hv z]
    show GateOp.not.eval [(GateOp.mod 2).eval [f z, b z]] = xor (f z) (b z)
    generalize f z = A; generalize b z = B; cases A <;> cases B <;> decide

lemma real_and {n : ℕ} {ds : List Gate} (hL : LegalG n ds) (f b : (Fin n → F) → Bool)
    (hf : Real n ds f) (hb : Real n ds b) :
    ∃ ds', LegalG n ds' ∧ costG ds' = costG ds + 1 ∧ (∀ h, Real n ds h → Real n ds' h) ∧
      Real n ds' (fun z => f z && b z) := by
  obtain ⟨g1, hg1, hl1, hL1, hr1⟩ := real_gate hL GateOp.and [f, b]
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
    (fun ins hins => ⟨show ins.length ≤ 2 by simp at hins; omega, Or.inl rfl⟩)
  refine ⟨ds ++ [g1], hL1, costG_snoc_one _ _ ⟨hg1 ▸ Or.inl rfl, by simpa using hl1⟩,
    fun _ hh => real_mono _ hh, real_congr hr1 (fun z => by
      show GateOp.and.eval [f z, b z] = (f z && b z)
      cases f z <;> cases b z <;> rfl)⟩

lemma real_list_sum_aff {n : ℕ} (v : Fin n → F) :
    ∀ (l : List (Fin n)) (ds : List Gate), LegalG n ds →
      ∃ ds', LegalG n ds' ∧ costG ds' = costG ds ∧ (∀ h, Real n ds h → Real n ds' h) ∧
        Real n ds' (fun z => decide ((l.map fun i => v i * z i).sum = 1)) := by
  intro l
  induction l with
  | nil =>
    intro ds hL
    obtain ⟨ds', hL', hc', hm', hr'⟩ := real_const hL false
    exact ⟨ds', hL', hc', hm', real_congr hr' (fun _ => by simp)⟩
  | cons i l ih =>
    intro ds hL
    obtain ⟨ds1, hL1, hc1, hm1, hr1⟩ := ih ds hL
    rcases zmod2_eq_zero_or_one (v i) with hvi | hvi
    · exact ⟨ds1, hL1, hc1, hm1, real_congr hr1 (fun z => by simp [hvi])⟩
    · obtain ⟨ds2, hL2, hc2, hm2, hr2⟩ := real_xor hL1 (fun z => decide (z i = 1))
        (fun z => decide ((l.map fun j => v j * z j).sum = 1)) (real_input ds1 i) hr1
      refine ⟨ds2, hL2, hc2.trans hc1, fun h hh => hm2 h (hm1 h hh),
        real_congr hr2 (fun z => by simp [hvi, dec_add])⟩

lemma real_aff {n : ℕ} (v : Fin n → F) (c : F) (ds : List Gate) (hL : LegalG n ds) :
    ∃ ds', LegalG n ds' ∧ costG ds' = costG ds ∧ (∀ h, Real n ds h → Real n ds' h) ∧
      Real n ds' (fun z => decide (dotProduct v z + c = 1)) := by
  obtain ⟨ds1, hL1, hc1, hm1, hr1⟩ := real_list_sum_aff v (List.finRange n) ds hL
  obtain ⟨ds2, hL2, hc2, hm2, hr2⟩ := real_const hL1 (decide (c = 1))
  obtain ⟨ds3, hL3, hc3, hm3, hr3⟩ := real_xor hL2 _ _ (hm2 _ hr1) hr2
  refine ⟨ds3, hL3, by omega, fun h hh => hm3 h (hm2 h (hm1 h hh)), real_congr hr3 (fun z => ?_)⟩
  have hsum : ((List.finRange n).map fun i => v i * z i).sum = dotProduct v z := by
    simp only [dotProduct, ← Fin.sum_univ_def]
  rw [hsum, dec_add]

lemma real_quad_list {n : ℕ} :
    ∀ (l : List ((Fin n → F) × (Fin n → F) × F)) (c₀ : F) (ds : List Gate), LegalG n ds →
      ∃ ds', LegalG n ds' ∧ costG ds' = costG ds + l.length ∧
        Real n ds' (fun z => decide (c₀ + (l.map fun p => dotProduct p.1 z * (dotProduct p.2.1 z + p.2.2)).sum = 1)) := by
  intro l
  induction l with
  | nil =>
    intro c₀ ds hL
    obtain ⟨ds', hL', hc', _, hr'⟩ := real_const hL (decide (c₀ = 1))
    exact ⟨ds', hL', by simp [hc'], real_congr hr' (fun _ => by simp)⟩
  | cons p l ih =>
    intro c₀ ds hL
    obtain ⟨ds1, hL1, hc1, hr1⟩ := ih c₀ ds hL
    obtain ⟨ds2, hL2, hc2, hm2, hr2⟩ := real_aff p.1 0 ds1 hL1
    obtain ⟨ds3, hL3, hc3, hm3, hr3⟩ := real_aff p.2.1 p.2.2 ds2 hL2
    obtain ⟨ds4, hL4, hc4, hm4, hr4⟩ := real_and hL3 _ _ (hm3 _ hr2) hr3
    obtain ⟨ds5, hL5, hc5, _, hr5⟩ := real_xor hL4 _ _ (hm4 _ (hm3 _ (hm2 _ hr1))) hr4
    refine ⟨ds5, hL5, by simp only [List.length_cons]; omega, real_congr hr5 (fun z => ?_)⟩
    simp only [List.map_cons, List.sum_cons, add_zero]
    rw [← dec_mul, ← dec_add]
    congr 1; ring

def appendVec {k : ℕ} (x y : Fin k → F) : Fin (2 * k) → F :=
  fun i => if h : i.val < k then x ⟨i.val, h⟩ else y ⟨i.val - k, by omega⟩

lemma bitsN_appendVec {k : ℕ} (x y : Fin k → F) :
    bitsN (2 * k) (appendVec x y) = bitsN k x ++ bitsN k y := by
  apply List.ext_getElem
  · simp [bitsN_length]; omega
  · intro i h1 h2
    simp only [bitsN, List.length_ofFn] at h1
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp [bitsN_length]; exact hik)]
      simp [bitsN, appendVec, hik]
    · rw [List.getElem_append_right (by simp [bitsN_length]; omega)]
      simp [bitsN, appendVec, hik]

def leftVec {k : ℕ} (u : Fin k → F) : Fin (2 * k) → F :=
  fun i => if h : i.val < k then u ⟨i.val, h⟩ else 0

def rightVec {k : ℕ} (v : Fin k → F) : Fin (2 * k) → F :=
  fun i => if h : i.val < k then 0 else v ⟨i.val - k, by omega⟩

lemma dot_leftVec {k : ℕ} (u x y : Fin k → F) :
    dotProduct (leftVec u) (appendVec x y) = dotProduct u x := by
  unfold dotProduct
  have h1 : (∑ i : Fin (2 * k), leftVec u i * appendVec x y i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * k) => i.val < k), leftVec u i * appendVec x y i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i.val < k <;> simp [leftVec, h]
  rw [h1]
  refine Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k)) ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro i1 _ i2 _ hEq; exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) hEq)
  · intro j _
    refine ⟨⟨j.val, by omega⟩, ?_, Fin.ext rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact j.isLt
  · intro i hi
    have hlt : i.val < k := (Finset.mem_filter.mp hi).2
    simp [leftVec, appendVec, hlt]

lemma dot_rightVec {k : ℕ} (v x y : Fin k → F) :
    dotProduct (rightVec v) (appendVec x y) = dotProduct v y := by
  unfold dotProduct
  have h1 : (∑ i : Fin (2 * k), rightVec v i * appendVec x y i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * k) => ¬ i.val < k), rightVec v i * appendVec x y i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i.val < k <;> simp [rightVec, h]
  rw [h1]
  refine Finset.sum_bij (fun i hi => (⟨i.val - k, by have := (Finset.mem_filter.mp hi).2; omega⟩ : Fin k)) ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro i1 hi1 i2 hi2 hEq
    have h1 : ¬ i1.val < k := (Finset.mem_filter.mp hi1).2
    have h2 : ¬ i2.val < k := (Finset.mem_filter.mp hi2).2
    have hv : i1.val - k = i2.val - k := congrArg Fin.val hEq
    exact Fin.ext (by omega)
  · intro j _
    refine ⟨⟨k + j.val, by omega⟩, ?_, Fin.ext (by simp)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro i hi
    have hge : ¬ i.val < k := (Finset.mem_filter.mp hi).2
    simp [rightVec, appendVec, hge]

lemma build_quad_circuit (k s : ℕ) (g : (Fin k → F) → F)
    (B : (Fin s → F) →ₗ[F] (Fin k → F)) (hB : Function.Injective B)
    (q : (Fin s → F) → F) (hq : HasDeg 2 q) :
    ∃ C : Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * k) C ∧
      (∀ h ∈ C.gates, GOk h) ∧
      costG C.gates ≤ s ∧
      rawScore g C = 2 ^ k * (∑ t : Fin s → F, chi (g (B t) + q t)).natAbs := by
  obtain ⟨Q, ℓ, c₀, hq_eq⟩ := quad_repr q hq
  obtain ⟨P, hPB⟩ := exists_left_inv B hB
  let v : Fin s → (Fin k → F) := fun j => B (Pi.single j 1)
  let w : Fin s → (Fin k → F) := fun j m => P (Pi.single m 1) j
  have hP_dot : ∀ (j : Fin s) (y : Fin k → F), P y j = dotProduct (w j) y := by
    intro j y
    have hy : y = ∑ m : Fin k, y m • Pi.single m (1 : F) := by
      funext m; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, dotProduct, w, mul_comm]
  have hB_sum : ∀ (t : Fin s → F), B t = ∑ j : Fin s, t j • v j := by
    intro t
    have ht : t = ∑ j : Fin s, t j • Pi.single j (1 : F) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ht, map_sum]
    simp only [map_smul, v]
  let pairs : List ((Fin (2 * k) → F) × (Fin (2 * k) → F) × F) :=
    (List.finRange s).map fun j =>
      (rightVec (w j), leftVec (v j) + rightVec (∑ i : Fin s, Q i j • w i), ℓ j)
  have hL0 : LegalG (2 * k) [] := ⟨fun j hj => by simp at hj, by simp⟩
  obtain ⟨ds, hLds, hcds, out, hout, hev⟩ := real_quad_list pairs c₀ [] hL0
  let C : Circuit := ⟨ds, out⟩
  have hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * k) C := fun j hj i hi => hLds.1 j hj i hi
  have hG : ∀ h ∈ C.gates, GOk h := hLds.2
  have hcost : costG C.gates ≤ s := by
    change costG ds ≤ s
    rw [hcds]
    simp [costG, pairs]
  have hC_eval : ∀ x y : Fin k → F,
      C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x (B (P y)) + q (P y) = 1) := by
    intro x y
    rw [← bitsN_appendVec x y]
    show (ds.foldl step (bitsN (2 * k) (appendVec x y))).getD out false = _
    rw [hev (appendVec x y)]
    congr 1
    have hmap : (pairs.map fun p => dotProduct p.1 (appendVec x y) *
        (dotProduct p.2.1 (appendVec x y) + p.2.2)).sum =
      ∑ j : Fin s, P y j * (dotProduct (v j) x + (ℓ j + ∑ i : Fin s, Q i j * P y i)) := by
      simp only [pairs, List.map_map, Function.comp_def, dot_rightVec, add_dotProduct,
        dot_leftVec, ← hP_dot]
      have hsum_w : ∀ j : Fin s,
          dotProduct (∑ i : Fin s, Q i j • w i) y = ∑ i : Fin s, Q i j * P y i := fun j => by
        rw [sum_dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_dotProduct, smul_eq_mul, hP_dot i y]
      simp_rw [hsum_w]
      have hlist : ∀ f : Fin s → F, ((List.finRange s).map f).sum = ∑ j : Fin s, f j := fun f => by
        simp only [← Fin.sum_univ_def]
      rw [hlist]
      refine Finset.sum_congr rfl fun j _ => by ring
    dsimp only
    rw [hmap, hq_eq (P y)]
    have hdotBP : dotProduct x (B (P y)) = ∑ j : Fin s, P y j * dotProduct (v j) x := by
      rw [hB_sum (P y), dotProduct_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x (v j)]
    rw [hdotBP]
    have hsplit : (∑ j : Fin s, P y j * (dotProduct (v j) x + (ℓ j + ∑ i : Fin s, Q i j * P y i))) =
        (∑ j : Fin s, P y j * dotProduct (v j) x) +
        (∑ j : Fin s, P y j * (ℓ j + ∑ i : Fin s, Q i j * P y i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit]; ring
  have hraw : rawScore g C = 2 ^ k * (∑ t : Fin s → F, chi (g (B t) + q t)).natAbs := by
    unfold rawScore
    have hsum :
        (∑ x : Fin k → F, ∑ y : Fin k → F,
          if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1) =
        (2 ^ k : ℤ) * ∑ t : Fin s → F, chi (g (B t) + q t) := by
      rw [Finset.sum_comm]
      have hinner : ∀ y : Fin k → F,
          (∑ x : Fin k → F,
            if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) =
          chi (q (P y) + g y) * (if y + B (P y) = 0 then (2 ^ k : ℤ) else 0) := by
        intro y
        have ht : ∀ x : Fin k → F,
            (if C.eval (bitsN k x ++ bitsN k y) = decide (dotProduct x y + g y = 1)
              then (1 : ℤ) else -1) =
            chi (q (P y) + g y) * chi (dotProduct x (y + B (P y))) := by
          intro x
          rw [agree_eq_sg_chi, hC_eval x y, sg_eq_chi_b2f, b2f_decide, dotProduct_add]
          simp only [chi_add]; ring
        simp_rw [ht]
        rw [← Finset.mul_sum, sum_chi_dot_univ]
      simp_rw [hinner]
      have hfilt :
          (∑ y : Fin k → F, chi (q (P y) + g y) * (if y + B (P y) = 0 then (2 ^ k : ℤ) else 0)) =
          ∑ y ∈ Finset.univ.filter (fun y : Fin k → F => y + B (P y) = 0),
            (2 ^ k : ℤ) * chi (q (P y) + g y) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
      rw [hfilt, Finset.mul_sum]
      refine (Finset.sum_nbij B ?_ ?_ ?_ ?_).symm
      · intro t _
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hPB t, vec_add_self]
      · intro t1 _ t2 _ hEq; exact hB hEq
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨P y, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        calc B (P y) = B (P y) + (y + B (P y)) := by rw [hy, add_zero]
          _ = y + (B (P y) + B (P y)) := by abel
          _ = y := by rw [vec_add_self, add_zero]
      · intro t _
        rw [hPB t, add_comm (g (B t)) (q t)]
    rw [hsum, Int.natAbs_mul, Int.natAbs_pow]; rfl
  exact ⟨C, hRB, hG, hcost, hraw⟩

end PEqualNP.Outside.L_meta_29781

theorem PEqualNP.Outside.L_meta_29781 :
    ∀ (k s : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin k → F
  let raw := fun (g : V → F) (C : Circ) => (∑ x : V, ∑ y : V,
    if C.eval (bits k x ++ bits k y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1).natAbs
  let E := Fin s → F
  let diff := fun (g : V → F) (u x : V) => g (x+u) - g x
  let third := fun (g : V → F) (u v w : V) => diff (diff (diff g u) v) w 0
  let deriv := fun (f : E → F) (u x : E) => f (x+u) - f x
  s ≤ k → ∀ g : V → F,
    (∀ a b c d x, diff (diff (diff (diff g a) b) c) d x = 0) →
    let zeroOn := ∃ B : E →ₗ[F] V, Function.Injective B ∧ ∀ u v w, third g (B u) (B v) (B w) = 0
    let wedge := ∃ (B : E →ₗ[F] V) (a b c : E), Function.Injective B ∧
      ∀ u v w, third g (B u) (B v) (B w) =
        let h := fun t : E => dotProduct a t * dotProduct b t * dotProduct c t
        deriv (deriv (deriv h u) v) w 0
    let opt := fun (n : ℕ) =>
      (∀ C : Circ, legal (2*k) C → cost C ≤ s → 4 * raw g C ≤ n) ∧
      (∃ C : Circ, legal (2*k) C ∧ cost C ≤ s ∧ 4 * raw g C = n)
    (opt (4 * 2^(k+s)) ↔ zeroOn) ∧
    (¬ zeroOn → (∀ C : Circ, legal (2*k) C → cost C ≤ s → 4 * raw g C ≤ 3 * 2^(k+s))) ∧
    (opt (3 * 2^(k+s)) ↔ ¬ zeroOn ∧ wedge) := by
  intro k s Circ F legal cost bits V raw E diff third deriv _ g hg3 zeroOn wedge opt
  have hgDeg3 : PEqualNP.Outside.L_meta_29781.HasDeg 3 g := hg3
  have hnot_zero_bound :
      ¬ zeroOn → ∀ C : Circ, legal (2 * k) C → cost C ≤ s → 4 * raw g C ≤ 3 * 2 ^ (k + s) := by
    intro hnz C hleg hcost
    by_contra hgt
    push Not at hgt
    have hfit := (PEqualNP.Outside.L_meta_29781.high_bias_quad_fit k s g C hleg.1 hleg.2 hcost).2 (le_of_lt hgt)
    obtain ⟨B, a, q, hBinj, hq2, hbound⟩ := hfit
    let f : E → F := fun t => g (a + B t) + q t
    obtain ⟨f₀, hf₀_or, _, hf₀_sum⟩ := PEqualNP.Outside.L_meta_29781.exists_low_wt_shift f
    have hT_gt : 3 * 2 ^ s < 4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs := by
      have h1 : 2 ^ k * (3 * 2 ^ s) < 2 ^ k * (4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs) := by
        calc 2 ^ k * (3 * 2 ^ s) = 3 * 2 ^ (k + s) := by rw [pow_add]; ring
          _ < 4 * raw g C := hgt
          _ ≤ 2 ^ k * (4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs) := hbound
      exact Nat.lt_of_mul_lt_mul_left h1
    have hsum_eq : (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs +
        2 * PEqualNP.Outside.L_meta_29781.wt f₀ = 2 ^ s := hf₀_sum
    have hwt_lt : 8 * PEqualNP.Outside.L_meta_29781.wt f₀ < 2 ^ s := by omega
    have hfDeg3 : PEqualNP.Outside.L_meta_29781.HasDeg 3 f :=
      PEqualNP.Outside.L_meta_29781.hasDeg_add
        (PEqualNP.Outside.L_meta_29781.hasDeg_comp_aff B a hgDeg3)
        (PEqualNP.Outside.L_meta_29781.hasDeg_mono hq2)
    have hf₀Deg3 : PEqualNP.Outside.L_meta_29781.HasDeg 3 f₀ := by
      rcases hf₀_or with rfl | rfl
      · exact hfDeg3
      · exact PEqualNP.Outside.L_meta_29781.hasDeg_add hfDeg3 (PEqualNP.Outside.L_meta_29781.hasDeg_const 3 1)
    have hf₀_zero : ∀ t, f₀ t = 0 := by
      intro t
      by_contra hne
      have h1 : f₀ t = 1 := PEqualNP.Outside.L_meta_29781.zmod2_eq_one_of_ne_zero _ hne
      have hmin := PEqualNP.Outside.L_meta_29781.rm_min_wt f₀ hf₀Deg3 ⟨t, h1⟩
      have h8 : 2 ^ 3 = 8 := by norm_num
      rw [h8] at hmin
      omega
    have hf_const : PEqualNP.Outside.L_meta_29781.HasDeg 2 f := by
      rcases hf₀_or with h | h
      · have : f = fun _ => 0 := by funext t; rw [← h]; exact hf₀_zero t
        rw [this]; exact PEqualNP.Outside.L_meta_29781.hasDeg_zero_fn 2
      · have : f = fun _ => 1 := by
          funext t
          have h0 : f t + 1 = 0 := by rw [← congrFun h t]; exact hf₀_zero t
          rcases PEqualNP.Outside.L_meta_29781.zmod2_eq_zero_or_one (f t) with ht | ht
          · rw [ht] at h0; exact absurd h0 (by decide)
          · exact ht
        rw [this]; exact PEqualNP.Outside.L_meta_29781.hasDeg_const 2 1
    apply hnz
    refine ⟨B, hBinj, fun u v w => ?_⟩
    have h0 := PEqualNP.Outside.L_meta_29781.dd3_eq_zero_of_hasDeg2 hf_const u v w 0
    have h1 : PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd f u) v) w 0 =
        third g (B u) (B v) (B w) := by
      dsimp only [f]
      rw [PEqualNP.Outside.L_meta_29781.dd3_add,
        PEqualNP.Outside.L_meta_29781.dd3_comp_aff hgDeg3 B a u v w 0,
        PEqualNP.Outside.L_meta_29781.dd3_eq_zero_of_hasDeg2 hq2 u v w 0, add_zero]
      rfl
    rw [← h1]
    exact h0
  have hzero_imp_opt : zeroOn → opt (4 * 2 ^ (k + s)) := by
    rintro ⟨B, hBinj, hB0⟩
    refine ⟨fun C hleg hcost =>
      (PEqualNP.Outside.L_meta_29781.high_bias_quad_fit k s g C hleg.1 hleg.2 hcost).1, ?_⟩
    have hgB2 : PEqualNP.Outside.L_meta_29781.HasDeg 2 (fun t => g (B t)) := by
      intro u v w x
      have h1 : (fun t => g (B t)) = fun t => g (0 + B t) := by funext t; simp
      rw [h1, PEqualNP.Outside.L_meta_29781.dd3_comp_aff hgDeg3 B 0 u v w x]
      exact hB0 u v w
    obtain ⟨C, hRB, hG, hcost, hraw⟩ :=
      PEqualNP.Outside.L_meta_29781.build_quad_circuit k s g B hBinj (fun t => g (B t)) hgB2
    refine ⟨C, ⟨hRB, hG⟩, hcost, ?_⟩
    have hsum : (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (g (B t) + g (B t))) = (2 ^ s : ℤ) := by
      have h1 : ∀ t : E, PEqualNP.Outside.L_meta_29781.chi (g (B t) + g (B t)) = 1 := fun t => by
        rw [PEqualNP.Outside.L_meta_29781.zmod2_add_self (g (B t)), PEqualNP.Outside.L_meta_29781.chi_zero]
      simp_rw [h1]
      rw [Finset.sum_const, Finset.card_univ, PEqualNP.Outside.L_meta_29781.card_fin_fun]
      simp only [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    show 4 * PEqualNP.Outside.L_meta_29781.rawScore g C = 4 * 2 ^ (k + s)
    rw [hraw, hsum, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl, ← pow_add]
  refine ⟨⟨?_, hzero_imp_opt⟩, hnot_zero_bound, ⟨?_, ?_⟩⟩
  · intro hopt
    by_contra hnz
    obtain ⟨C, hleg, hcost, hraw⟩ := hopt.2
    have hle := hnot_zero_bound hnz C hleg hcost
    have hpos : 0 < 2 ^ (k + s) := Nat.two_pow_pos _
    omega
  · intro hopt
    have hnz : ¬ zeroOn := by
      intro hz
      obtain ⟨C, hleg, hcost, hraw⟩ := (hzero_imp_opt hz).2
      have hle := hopt.1 C hleg hcost
      have hpos : 0 < 2 ^ (k + s) := Nat.two_pow_pos _
      omega
    refine ⟨hnz, ?_⟩
    obtain ⟨C, hleg, hcost, hraw⟩ := hopt.2
    have hfit := (PEqualNP.Outside.L_meta_29781.high_bias_quad_fit k s g C hleg.1 hleg.2 hcost).2 (le_of_eq hraw.symm)
    obtain ⟨B, a, q, hBinj, hq2, hbound⟩ := hfit
    let f : E → F := fun t => g (a + B t) + q t
    obtain ⟨f₀, hf₀_or, _, hf₀_sum⟩ := PEqualNP.Outside.L_meta_29781.exists_low_wt_shift f
    have hT_ge : 3 * 2 ^ s ≤ 4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs := by
      have h1 : 2 ^ k * (3 * 2 ^ s) ≤ 2 ^ k * (4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs) := by
        calc 2 ^ k * (3 * 2 ^ s) = 3 * 2 ^ (k + s) := by rw [pow_add]; ring
          _ = 4 * raw g C := hraw.symm
          _ ≤ 2 ^ k * (4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs) := hbound
      exact Nat.le_of_mul_le_mul_left h1 (Nat.two_pow_pos _)
    have hsum_eq : (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (f t)).natAbs +
        2 * PEqualNP.Outside.L_meta_29781.wt f₀ = 2 ^ s := hf₀_sum
    have hwt_le : 8 * PEqualNP.Outside.L_meta_29781.wt f₀ ≤ 2 ^ s := by omega
    have hfDeg3 : PEqualNP.Outside.L_meta_29781.HasDeg 3 f :=
      PEqualNP.Outside.L_meta_29781.hasDeg_add
        (PEqualNP.Outside.L_meta_29781.hasDeg_comp_aff B a hgDeg3)
        (PEqualNP.Outside.L_meta_29781.hasDeg_mono hq2)
    have hf₀Deg3 : PEqualNP.Outside.L_meta_29781.HasDeg 3 f₀ := by
      rcases hf₀_or with rfl | rfl
      · exact hfDeg3
      · exact PEqualNP.Outside.L_meta_29781.hasDeg_add hfDeg3 (PEqualNP.Outside.L_meta_29781.hasDeg_const 3 1)
    have hdd3_f₀ : ∀ u v w,
        PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd f₀ u) v) w 0 =
        third g (B u) (B v) (B w) := by
      intro u v w
      have hdd3_f : PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd f u) v) w 0 =
          third g (B u) (B v) (B w) := by
        dsimp only [f]
        rw [PEqualNP.Outside.L_meta_29781.dd3_add,
          PEqualNP.Outside.L_meta_29781.dd3_comp_aff hgDeg3 B a u v w 0,
          PEqualNP.Outside.L_meta_29781.dd3_eq_zero_of_hasDeg2 hq2 u v w 0, add_zero]
        rfl
      rcases hf₀_or with rfl | rfl
      · exact hdd3_f
      · rw [PEqualNP.Outside.L_meta_29781.dd3_add,
          PEqualNP.Outside.L_meta_29781.dd3_eq_zero_of_hasDeg2 (PEqualNP.Outside.L_meta_29781.hasDeg_const 2 1) u v w 0, add_zero, hdd3_f]
    have hne : ∃ t, f₀ t = 1 := by
      by_contra h0
      push Not at h0
      have hf₀z : f₀ = fun _ => 0 := by
        funext t
        rcases PEqualNP.Outside.L_meta_29781.zmod2_eq_zero_or_one (f₀ t) with ht | ht
        · exact ht
        · exact absurd ht (h0 t)
      apply hnz
      refine ⟨B, hBinj, fun u v w => ?_⟩
      rw [← hdd3_f₀ u v w, hf₀z]
      exact PEqualNP.Outside.L_meta_29781.dd3_eq_zero_of_hasDeg2 (PEqualNP.Outside.L_meta_29781.hasDeg_zero_fn 2) u v w 0
    have hmin := PEqualNP.Outside.L_meta_29781.rm_min_wt f₀ hf₀Deg3 hne
    have h8 : 2 ^ 3 = 8 := by norm_num
    rw [h8] at hmin
    have hwt_eq : 8 * PEqualNP.Outside.L_meta_29781.wt f₀ = 2 ^ s := by omega
    obtain ⟨a', b', c', habc⟩ := PEqualNP.Outside.L_meta_29781.rm3_coset_wedge f₀ hf₀Deg3 hne hwt_eq
    refine ⟨B, a', b', c', hBinj, fun u v w => ?_⟩
    rw [← hdd3_f₀ u v w, habc u v w]
    rfl
  · rintro ⟨hnz, B, a, b, c, hBinj, hBw⟩
    refine ⟨hnot_zero_bound hnz, ?_⟩
    let h : E → F := fun t => dotProduct a t * dotProduct b t * dotProduct c t
    have hwt : 8 * PEqualNP.Outside.L_meta_29781.wt h = 2 ^ s := by
      rcases PEqualNP.Outside.L_meta_29781.triple_wt_or_zero a b c with hz | h8
      · exfalso
        apply hnz
        refine ⟨B, hBinj, fun u v w => ?_⟩
        rw [hBw u v w]
        exact hz u v w
      · exact h8
    let r : E → F := fun t => g (B t) + h t
    have hr2 : PEqualNP.Outside.L_meta_29781.HasDeg 2 r := by
      intro u v w x
      dsimp only [r]
      rw [PEqualNP.Outside.L_meta_29781.dd3_add]
      have h1 : (fun t => g (B t)) = fun t => g (0 + B t) := by funext t; simp
      rw [h1, PEqualNP.Outside.L_meta_29781.dd3_comp_aff hgDeg3 B 0 u v w x,
        PEqualNP.Outside.L_meta_29781.dd3_const_in_x (PEqualNP.Outside.L_meta_29781.triple_hasDeg3 a b c) u v w x]
      have heq : PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd g (B u)) (B v)) (B w) 0 =
          PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd (PEqualNP.Outside.L_meta_29781.dd h u) v) w 0 :=
        hBw u v w
      rw [heq, PEqualNP.Outside.L_meta_29781.zmod2_add_self]
    obtain ⟨C, hRB, hG, hcost, hraw⟩ :=
      PEqualNP.Outside.L_meta_29781.build_quad_circuit k s g B hBinj r hr2
    refine ⟨C, ⟨hRB, hG⟩, hcost, ?_⟩
    have hcancel : ∀ t : E, g (B t) + r t = h t := fun t => by
      dsimp only [r]
      rw [← add_assoc, PEqualNP.Outside.L_meta_29781.zmod2_add_self, zero_add]
    have hsum : 4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (g (B t) + r t)).natAbs = 3 * 2 ^ s := by
      simp_rw [hcancel]
      rw [PEqualNP.Outside.L_meta_29781.sum_chi_eq_wt h]
      have hle : 2 * PEqualNP.Outside.L_meta_29781.wt h ≤ 2 ^ s := by omega
      have hleZ : 2 * (PEqualNP.Outside.L_meta_29781.wt h : ℤ) ≤ (2 ^ s : ℤ) := by exact_mod_cast hle
      have hnn : (0 : ℤ) ≤ (2 ^ s : ℤ) - 2 * (PEqualNP.Outside.L_meta_29781.wt h : ℤ) := by linarith
      have habs : ((2 ^ s : ℤ) - 2 * (PEqualNP.Outside.L_meta_29781.wt h : ℤ)).natAbs +
          2 * PEqualNP.Outside.L_meta_29781.wt h = 2 ^ s := by
        zify; rw [abs_of_nonneg hnn]; ring
      omega
    show 4 * PEqualNP.Outside.L_meta_29781.rawScore g C = 3 * 2 ^ (k + s)
    rw [hraw]
    calc 4 * (2 ^ k * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (g (B t) + r t)).natAbs)
        = 2 ^ k * (4 * (∑ t : E, PEqualNP.Outside.L_meta_29781.chi (g (B t) + r t)).natAbs) := by ring
      _ = 2 ^ k * (3 * 2 ^ s) := by rw [hsum]
      _ = 3 * 2 ^ (k + s) := by rw [pow_add]; ring

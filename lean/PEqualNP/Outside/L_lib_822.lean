import Mathlib.LinearAlgebra.Matrix.Trace
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_822_aux

open scoped BigOperators Matrix

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

lemma zmod2_vec_add_self {n : ℕ} (a : Fin n → ZMod 2) : a + a = 0 := by
  funext i
  exact zmod2_add_self (a i)

def chi (b : ZMod 2) : ℚ := if b = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [chi, h10]

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [chi, h10, h11]

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma chi_mul_self (a : ZMod 2) : chi a * chi a = 1 := by
  rw [← chi_add, zmod2_add_self, chi_zero]

lemma sum_chi_mul (t : ZMod 2) :
    (∑ b : ZMod 2, chi (b * t)) = if t = 0 then 2 else 0 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [huniv, Finset.sum_pair h01]
  rcases zmod2_eq_zero_or_one t with rfl | rfl
  · simp [chi]; norm_num
  · simp [chi, h10]

def dot {n : ℕ} (u v : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i : Fin n, u i * v i

lemma dot_comm {n : ℕ} (u v : Fin n → ZMod 2) : dot u v = dot v u := by
  dsimp only [dot]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dot_zero_left {n : ℕ} (v : Fin n → ZMod 2) : dot 0 v = 0 := by
  simp [dot]

lemma dot_zero_right {n : ℕ} (u : Fin n → ZMod 2) : dot u 0 = 0 := by
  simp [dot]

lemma dot_add_left {n : ℕ} (u₁ u₂ v : Fin n → ZMod 2) :
    dot (u₁ + u₂) v = dot u₁ v + dot u₂ v := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (u v₁ v₂ : Fin n → ZMod 2) :
    dot u (v₁ + v₂) = dot u v₁ + dot u v₂ := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_smul_left {n : ℕ} (c : ZMod 2) (u v : Fin n → ZMod 2) :
    dot (c • u) v = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma dot_smul_right {n : ℕ} (c : ZMod 2) (u v : Fin n → ZMod 2) :
    dot u (c • v) = c * dot u v := by
  rw [dot_comm, dot_smul_left, dot_comm]

def char {n : ℕ} (u v : Fin n → ZMod 2) : ℚ := chi (dot u v)

lemma char_comm {n : ℕ} (u v : Fin n → ZMod 2) : char u v = char v u := by
  simp only [char, dot_comm]

lemma char_zero_left {n : ℕ} (v : Fin n → ZMod 2) : char 0 v = 1 := by
  simp [char, dot_zero_left, chi_zero]

lemma char_zero_right {n : ℕ} (u : Fin n → ZMod 2) : char u 0 = 1 := by
  simp [char, dot_zero_right, chi_zero]

lemma char_add_left {n : ℕ} (u₁ u₂ v : Fin n → ZMod 2) :
    char (u₁ + u₂) v = char u₁ v * char u₂ v := by
  simp only [char, dot_add_left, chi_add]

lemma char_add_right {n : ℕ} (u v₁ v₂ : Fin n → ZMod 2) :
    char u (v₁ + v₂) = char u v₁ * char u v₂ := by
  simp only [char, dot_add_right, chi_add]

lemma char_mul_self {n : ℕ} (u v : Fin n → ZMod 2) : char u v * char u v = 1 := by
  rw [← char_add_right, zmod2_vec_add_self, char_zero_right]

lemma char_list_sum {n : ℕ} (u : Fin n → ZMod 2) (w : List (Fin n → ZMod 2)) :
    char u w.sum = (w.map (char u)).prod := by
  induction w with
  | nil => simp [char_zero_right]
  | cons h t ih => simp [char_add_right, ih]

lemma sum_char_right {n : ℕ} (u : Fin n → ZMod 2) :
    (∑ v : Fin n → ZMod 2, char u v) = if u = 0 then ((2 ^ n : ℕ) : ℚ) else 0 := by
  have hrew : ∀ v : Fin n → ZMod 2, char u v = ∏ i : Fin n, chi (v i * u i) := fun v => by
    dsimp only [char, dot]
    rw [chi_sum]
    refine Finset.prod_congr rfl fun i _ => by rw [mul_comm]
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun i b => chi (b * u i))]
  simp_rw [sum_chi_mul]
  by_cases hu : u = 0
  · subst hu
    simp
  · simp only [hu, ite_false]
    have hex : ∃ i : Fin n, u i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu (funext hall)
    rcases hex with ⟨i₀, hi₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])

lemma sum_char_left {n : ℕ} (v : Fin n → ZMod 2) :
    (∑ u : Fin n → ZMod 2, char u v) = if v = 0 then ((2 ^ n : ℕ) : ℚ) else 0 := by
  have h : (∑ u : Fin n → ZMod 2, char u v) = ∑ u : Fin n → ZMod 2, char v u :=
    Finset.sum_congr rfl fun u _ => char_comm u v
  rw [h, sum_char_right]

def perp {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {v | ∀ u ∈ U, dot u v = 0}
    zero_mem' := fun u _ => dot_zero_right u
    smul_mem' := fun c x hx u hu => by rw [dot_smul_right, hx u hu, mul_zero]
    , add_mem' := fun ha hb u hu => by rw [dot_add_right, ha u hu, hb u hu, add_zero] }

lemma mem_perp_iff {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    v ∈ perp U ↔ ∀ u ∈ U, dot u v = 0 := Iff.rfl

lemma card_subspace {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype U] :
    Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
  let e := (Module.finBasis (ZMod 2) U).equivFun
  rw [Fintype.card_congr e.toEquiv]
  simp [Fintype.card_pi]

open Classical in
lemma sum_char_subspace {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    letI : Fintype U := Fintype.ofFinite _
    (∑ u : U, char u.1 v) = if v ∈ perp U then ((2 ^ Module.finrank (ZMod 2) U : ℕ) : ℚ) else 0 := by
  let : Fintype U := Fintype.ofFinite _
  by_cases hv : v ∈ perp U
  · simp only [hv, ite_true]
    have h1 : ∀ u : U, char u.1 v = 1 := fun u => by
      simp [char, hv u.1 u.2, chi_zero]
    simp_rw [h1, Finset.sum_const, Finset.card_univ, card_subspace, nsmul_eq_mul, mul_one]
  · simp only [hv, ite_false]
    have hex : ∃ u₀ : U, dot u₀.1 v = 1 := by
      rw [mem_perp_iff] at hv
      push Not at hv
      rcases hv with ⟨u₀, hu₀, hne⟩
      rcases zmod2_eq_zero_or_one (dot u₀ v) with h0 | h1
      · exact absurd h0 hne
      · exact ⟨⟨u₀, hu₀⟩, h1⟩
    rcases hex with ⟨u₀, hu₀⟩
    have hneg : (∑ u : U, char u.1 v) = -(∑ u : U, char u.1 v) := by
      calc (∑ u : U, char u.1 v)
          = ∑ u : U, char (u + u₀).1 v := by
            exact (Fintype.sum_equiv (Equiv.addRight u₀) (fun u => char (u + u₀).1 v)
              (fun u => char u.1 v) (fun _ => rfl)).symm
        _ = ∑ u : U, -(char u.1 v) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            change char (u.1 + u₀.1) v = -(char u.1 v)
            rw [char_add_left]
            have hc : char u₀.1 v = -1 := by simp [char, hu₀, chi_one]
            rw [hc, mul_neg_one]
        _ = -(∑ u : U, char u.1 v) := Finset.sum_neg_distrib _
    linarith

open Classical in
lemma finrank_perp {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) (perp U) + Module.finrank (ZMod 2) U = n := by
  let d := Module.finrank (ZMod 2) U
  let b := Module.finBasis (ZMod 2) U
  let φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := fun v i => dot (b i).1 v
      map_add' := fun v₁ v₂ => by funext i; exact dot_add_right _ _ _
      map_smul' := fun c v => by funext i; exact dot_smul_right c _ _ }
  have hker : LinearMap.ker φ = perp U := by
    ext v
    simp only [LinearMap.mem_ker, mem_perp_iff]
    constructor
    · intro hv u hu
      have hdecomp : (⟨u, hu⟩ : U) = ∑ i : Fin d, b.repr ⟨u, hu⟩ i • b i :=
        (b.sum_repr ⟨u, hu⟩).symm
      have hval : u = ∑ i : Fin d, b.repr ⟨u, hu⟩ i • (b i).1 := by
        have h1 := congrArg Subtype.val hdecomp
        rw [Submodule.coe_sum] at h1
        exact h1
      rw [hval]
      have hdot_sum : ∀ (s : Finset (Fin d)) (f : Fin d → (Fin n → ZMod 2)),
          dot (∑ i ∈ s, f i) v = ∑ i ∈ s, dot (f i) v := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp [dot_zero_left]
        | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add_left, ih]
      rw [hdot_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dot_smul_left]
      have hi : dot (b i).1 v = 0 := congrFun hv i
      rw [hi, mul_zero]
    · intro hv
      funext i
      exact hv (b i).1 (b i).2
  have hsurj : Function.Surjective φ := by
    let ψ : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      { toFun := fun c => ∑ i : Fin d, c i • (b i).1
        map_add' := fun c₁ c₂ => by
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun a c => by
          simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }
    have hψ_inj : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have hsub : (∑ i : Fin d, c i • b i) = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact hc
      have hli := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      funext i
      exact hli c hsub i
    have hdual : ∀ w : Fin d → ZMod 2, (∀ v : Fin n → ZMod 2, dot w (φ v) = 0) → w = 0 := by
      intro w hw
      have hψw : ψ w = 0 := by
        funext a
        have h1 := hw (Pi.single a 1)
        have hcalc : dot w (φ (Pi.single a 1)) = ψ w a := by
          change (∑ i : Fin d, w i * dot (b i).1 (Pi.single a 1)) =
            (∑ i : Fin d, w i • (b i).1) a
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          dsimp only [dot]
          rw [Finset.sum_eq_single a]
          · simp [Pi.single_eq_same]
          · intro x _ hne; simp [Pi.single_eq_of_ne hne]
          · intro h; exact absurd (Finset.mem_univ a) h
        rw [hcalc] at h1
        exact h1
      exact (injective_iff_map_eq_zero ψ).mp hψ_inj w hψw
    have hperp_range : perp (LinearMap.range φ) = ⊥ := by
      ext w
      simp only [mem_perp_iff, Submodule.mem_bot]
      constructor
      · intro hw
        exact hdual w fun v => by rw [dot_comm]; exact hw (φ v) ⟨v, rfl⟩
      · rintro rfl u _
        exact dot_zero_right u
    have hcard_perp : (∑ w : Fin d → ZMod 2, if w ∈ perp (LinearMap.range φ) then (1 : ℚ) else 0) = 1 := by
      rw [hperp_range]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro w _ hne; simp [Submodule.mem_bot, hne]
      · intro h; exact absurd (Finset.mem_univ 0) h
    let : Fintype (LinearMap.range φ) := Fintype.ofFinite _
    have hsum : (∑ w : Fin d → ZMod 2, ∑ u : LinearMap.range φ, char u.1 w) =
        ((2 ^ Module.finrank (ZMod 2) (LinearMap.range φ) : ℕ) : ℚ) := by
      calc (∑ w : Fin d → ZMod 2, ∑ u : LinearMap.range φ, char u.1 w)
          = ∑ w : Fin d → ZMod 2,
              if w ∈ perp (LinearMap.range φ) then ((2 ^ Module.finrank (ZMod 2) (LinearMap.range φ) : ℕ) : ℚ) else 0 :=
            Finset.sum_congr rfl fun w _ => sum_char_subspace (LinearMap.range φ) w
        _ = ((2 ^ Module.finrank (ZMod 2) (LinearMap.range φ) : ℕ) : ℚ) *
              ∑ w : Fin d → ZMod 2, if w ∈ perp (LinearMap.range φ) then (1 : ℚ) else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
        _ = ((2 ^ Module.finrank (ZMod 2) (LinearMap.range φ) : ℕ) : ℚ) := by rw [hcard_perp, mul_one]
    have hsum2 : (∑ w : Fin d → ZMod 2, ∑ u : LinearMap.range φ, char u.1 w) = ((2 ^ d : ℕ) : ℚ) := by
      rw [Finset.sum_comm]
      calc (∑ u : LinearMap.range φ, ∑ w : Fin d → ZMod 2, char u.1 w)
          = ∑ u : LinearMap.range φ, if u.1 = 0 then ((2 ^ d : ℕ) : ℚ) else 0 :=
            Finset.sum_congr rfl fun u _ => sum_char_right u.1
        _ = ((2 ^ d : ℕ) : ℚ) := by
            rw [Finset.sum_eq_single (0 : LinearMap.range φ)]
            · simp
            · intro u _ hne
              have : u.1 ≠ 0 := fun h => hne (Subtype.ext h)
              simp [this]
            · intro h; exact absurd (Finset.mem_univ 0) h
    have hpow : (2 : ℕ) ^ Module.finrank (ZMod 2) (LinearMap.range φ) = 2 ^ d := by
      exact_mod_cast hsum.symm.trans hsum2
    have hfr : Module.finrank (ZMod 2) (LinearMap.range φ) = d :=
      Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
    have htop : LinearMap.range φ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hfr, Module.finrank_fin_fun])
    intro y
    have hy : y ∈ LinearMap.range φ := by rw [htop]; trivial
    exact hy
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun, hker] at hrn
  omega

lemma perp_perp {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    perp (perp U) = U := by
  have hle : U ≤ perp (perp U) := fun u hu v hv => by rw [dot_comm]; exact hv u hu
  have hfr : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) (perp (perp U)) := by
    have h1 := finrank_perp U
    have h2 := finrank_perp (perp U)
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfr).symm

lemma perp_antitone {n : ℕ} {U V : Submodule (ZMod 2) (Fin n → ZMod 2)} (h : U ≤ V) :
    perp V ≤ perp U := fun _ hx u hu => hx u (h hu)

lemma perp_le_iff {n : ℕ} {U V : Submodule (ZMod 2) (Fin n → ZMod 2)} :
    perp V ≤ perp U ↔ U ≤ V := by
  constructor
  · intro h
    have h1 := perp_antitone h
    rwa [perp_perp, perp_perp] at h1
  · exact perp_antitone

lemma perp_inj {n : ℕ} {U V : Submodule (ZMod 2) (Fin n → ZMod 2)} (h : perp U = perp V) :
    U = V := by
  have := congrArg perp h
  rwa [perp_perp, perp_perp] at this

lemma perp_top {n : ℕ} : perp (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) = ⊥ := by
  ext v
  simp only [mem_perp_iff, Submodule.mem_top, forall_true_left, Submodule.mem_bot]
  constructor
  · intro hv
    funext i
    have h := hv (Pi.single i 1)
    dsimp only [dot] at h
    rw [Finset.sum_eq_single i] at h
    · simpa [Pi.single_eq_same] using h
    · intro x _ hne; simp [Pi.single_eq_of_ne hne]
    · intro h0; exact absurd (Finset.mem_univ i) h0
  · rintro rfl u; exact dot_zero_right u

def linOf {m j : ℕ} (Λ : Fin j → (Fin m → ZMod 2)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin j → ZMod 2) where
  toFun v b := dot (Λ b) v
  map_add' v₁ v₂ := by funext b; exact dot_add_right _ _ _
  map_smul' c v := by funext b; exact dot_smul_right c _ _

lemma ker_linOf {m j : ℕ} (Λ : Fin j → (Fin m → ZMod 2)) :
    LinearMap.ker (linOf Λ) = perp (Submodule.span (ZMod 2) (Set.range Λ)) := by
  ext v
  simp only [LinearMap.mem_ker, mem_perp_iff]
  constructor
  · intro hv u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨b, rfl⟩
      exact congrFun hv b
    · exact dot_zero_left v
    · intro x y _ _ hx hy; rw [dot_add_left, hx, hy, add_zero]
    · intro c x _ hx; rw [dot_smul_left, hx, mul_zero]
  · intro hv
    funext b
    exact hv (Λ b) (Submodule.subset_span ⟨b, rfl⟩)

lemma perp_ker_linOf {m j : ℕ} (Λ : Fin j → (Fin m → ZMod 2)) :
    perp (LinearMap.ker (linOf Λ)) = Submodule.span (ZMod 2) (Set.range Λ) := by
  rw [ker_linOf, perp_perp]

lemma codim_ker_linOf {m j : ℕ} (Λ : Fin j → (Fin m → ZMod 2)) :
    m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ)) =
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) := by
  have h := finrank_perp (Submodule.span (ZMod 2) (Set.range Λ))
  rw [← ker_linOf Λ] at h
  omega

def matChar {m j : ℕ} (Λ Y : Fin j → (Fin m → ZMod 2)) : ℚ :=
  ∏ b : Fin j, char (Λ b) (Y b)

lemma sum_matChar_left {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2)) :
    (∑ Λ : Fin j → (Fin m → ZMod 2), matChar Λ Y) =
    if Y = 0 then ((2 ^ (m * j) : ℕ) : ℚ) else 0 := by
  dsimp only [matChar]
  rw [← Fintype.prod_sum (fun b v => char v (Y b))]
  simp_rw [sum_char_left]
  by_cases hY : Y = 0
  · subst hY
    simp [pow_mul]
  · simp only [hY, ite_false]
    have hex : ∃ b : Fin j, Y b ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hY (funext hall)
    rcases hex with ⟨b₀, hb₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ b₀) (by simp [hb₀])

open Classical in
lemma card_indep_ext (n d r : ℕ) (hd : d ≤ r)
    (R₀ : Fin d → (Fin n → ZMod 2)) (hR₀ : LinearIndependent (ZMod 2) R₀) :
    (Fintype.card {R : Fin r → (Fin n → ZMod 2) //
      LinearIndependent (ZMod 2) R ∧ ∀ i : Fin d, R (Fin.castLE hd i) = R₀ i} : ℚ) =
    ∏ i ∈ Finset.Ico d r, ((2 : ℚ) ^ n - (2 : ℚ) ^ i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction k with
  | zero =>
    have hcard : Fintype.card {R : Fin (d + 0) → (Fin n → ZMod 2) //
        LinearIndependent (ZMod 2) R ∧ ∀ i : Fin d, R (Fin.castLE hd i) = R₀ i} = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨R₀, hR₀, fun _ => rfl⟩, ?_⟩
      rintro ⟨R, _, hR⟩
      apply Subtype.ext
      funext i
      exact hR i
    rw [hcard]
    simp
  | succ k ih =>
    let r' := d + k
    have hdr' : d ≤ r' := by omega
    let S_big := {R : Fin (r' + 1) → (Fin n → ZMod 2) //
      LinearIndependent (ZMod 2) R ∧ ∀ i : Fin d, R (Fin.castLE hd i) = R₀ i}
    let S_small := {R : Fin r' → (Fin n → ZMod 2) //
      LinearIndependent (ZMod 2) R ∧ ∀ i : Fin d, R (Fin.castLE hdr' i) = R₀ i}
    let Sig := Σ R : S_small, {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)}
    let heqv : S_big ≃ Sig :=
      { toFun := fun ⟨R, hli, heq⟩ =>
          have hinit_li : LinearIndependent (ZMod 2) (Fin.init R) := by
            have hfeq : Fin.init R = R ∘ Fin.castSucc := funext fun _ => rfl
            rw [hfeq]
            exact hli.comp Fin.castSucc (Fin.castSucc_injective _)
          have hinit_eq : ∀ i : Fin d, Fin.init R (Fin.castLE hdr' i) = R₀ i := fun i => by
            simpa [Fin.init] using heq i
          have hv : R (Fin.last r') ∉ Submodule.span (ZMod 2) (Set.range (Fin.init R)) := by
            intro hmem
            rw [Submodule.mem_span_range_iff_exists_fun] at hmem
            rcases hmem with ⟨c, hc⟩
            let c' : Fin (r' + 1) → ZMod 2 := Fin.snoc c 1
            have hsum0 : ∑ i : Fin (r' + 1), c' i • R i = 0 := by
              rw [Fin.sum_univ_castSucc]
              simp only [c', Fin.snoc_castSucc, Fin.snoc_last, one_smul]
              change (∑ i : Fin r', c i • Fin.init R i) + R (Fin.last r') = 0
              rw [hc, zmod2_vec_add_self]
            have hzero := (Fintype.linearIndependent_iff.mp hli) c' hsum0 (Fin.last r')
            simp [c'] at hzero
          ⟨⟨Fin.init R, hinit_li, hinit_eq⟩, ⟨R (Fin.last r'), hv⟩⟩
        invFun := fun ⟨⟨R, hli, heq⟩, ⟨v, hv⟩⟩ =>
          have hsnoc_li : LinearIndependent (ZMod 2) (Fin.snoc (α := fun _ => Fin n → ZMod 2) R v) := by
            rw [Fintype.linearIndependent_iff]
            intro c hc
            rw [Fin.sum_univ_castSucc] at hc
            simp only [Fin.snoc_castSucc, Fin.snoc_last] at hc
            have hclast : c (Fin.last r') = 0 := by
              rcases zmod2_eq_zero_or_one (c (Fin.last r')) with h0 | h1
              · exact h0
              · exfalso
                rw [h1, one_smul] at hc
                apply hv
                rw [Submodule.mem_span_range_iff_exists_fun]
                refine ⟨fun i => c i.castSucc, ?_⟩
                have h2 := congrArg (· + v) hc
                simp only [add_assoc, zmod2_vec_add_self, add_zero, zero_add] at h2
                exact h2
            rw [hclast, zero_smul, add_zero] at hc
            have hrest := (Fintype.linearIndependent_iff.mp hli) (fun i => c i.castSucc) hc
            intro i
            refine Fin.lastCases hclast hrest i
          have hsnoc_eq : ∀ i : Fin d,
              Fin.snoc (α := fun _ => Fin n → ZMod 2) R v (Fin.castLE hd i) = R₀ i := fun i => by
            have hcast : Fin.castLE hd i = (Fin.castLE hdr' i).castSucc := rfl
            rw [hcast, Fin.snoc_castSucc]
            exact heq i
          ⟨Fin.snoc R v, hsnoc_li, hsnoc_eq⟩
        left_inv := fun ⟨R, _, _⟩ => by
          apply Subtype.ext
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp
          · intro j; simp [Fin.init]
        right_inv := fun ⟨⟨R, hli, heq⟩, ⟨v, hv⟩⟩ => by
          have hinit_eq : Fin.init (Fin.snoc (α := fun _ => Fin n → ZMod 2) R v) = R :=
            funext fun i => by simp [Fin.init]
          have h1 : (⟨Fin.init (Fin.snoc (α := fun _ => Fin n → ZMod 2) R v),
              by rw [hinit_eq]; exact hli, by rw [hinit_eq]; exact heq⟩ : S_small) = ⟨R, hli, heq⟩ :=
            Subtype.ext hinit_eq
          refine Sigma.ext h1 ?_
          refine (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr (by simp)
          simp only [hinit_eq] }
    have hcard_eq : Fintype.card S_big =
        ∑ R : S_small, Fintype.card {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)} := by
      rw [Fintype.card_congr heqv, Fintype.card_sigma]
    have hfiber : ∀ R : S_small,
        (Fintype.card {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)} : ℚ) =
        (2 : ℚ) ^ n - (2 : ℚ) ^ r' := by
      intro R
      let U := Submodule.span (ZMod 2) (Set.range R.1)
      have hfrU : Module.finrank (ZMod 2) U = r' := by
        rw [finrank_span_eq_card R.2.1, Fintype.card_fin]
      have hcardU : Fintype.card U = 2 ^ r' := by rw [card_subspace, hfrU]
      have hle : 2 ^ r' ≤ 2 ^ n := by
        have h1 : Fintype.card U ≤ Fintype.card (Fin n → ZMod 2) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        simpa [hcardU, Fintype.card_pi] using h1
      have hcompl := Fintype.card_subtype_compl (fun v : Fin n → ZMod 2 => v ∈ U)
      change (Fintype.card {v : Fin n → ZMod 2 // v ∉ U} : ℚ) = _
      rw [hcompl]
      have hcardV : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp [Fintype.card_pi]
      rw [hcardV]
      have hcardU' : Fintype.card {v : Fin n → ZMod 2 // v ∈ U} = 2 ^ r' := hcardU
      rw [hcardU', Nat.cast_sub hle]
      push_cast
      rfl
    have hico : Finset.Ico d (d + (k + 1)) = insert r' (Finset.Ico d r') := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot : r' ∉ Finset.Ico d r' := by simp
    rw [hico, Finset.prod_insert hnot, mul_comm]
    change (Fintype.card S_big : ℚ) = _
    rw [hcard_eq]
    push_cast
    calc (∑ R : S_small, (Fintype.card {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)} : ℚ))
        = ∑ _R : S_small, ((2 : ℚ) ^ n - (2 : ℚ) ^ r') := Finset.sum_congr rfl fun R _ => hfiber R
      _ = (Fintype.card S_small : ℚ) * ((2 : ℚ) ^ n - (2 : ℚ) ^ r') := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (∏ i ∈ Finset.Ico d r', ((2 : ℚ) ^ n - (2 : ℚ) ^ i)) * ((2 : ℚ) ^ n - (2 : ℚ) ^ r') := by
          rw [ih hdr']

open Classical in
lemma sum_indep_char (n t : ℕ) :
    ∀ (u : Fin t → (Fin n → ZMod 2)), LinearIndependent (ZMod 2) u →
    (∑ R : {f : Fin t → (Fin n → ZMod 2) // LinearIndependent (ZMod 2) f},
      ∏ p : Fin t, char (R.1 p) (u p)) =
    (-1 : ℚ) ^ t * (2 : ℚ) ^ (t * (t - 1) / 2) := by
  induction t with
  | zero =>
    intro u _
    have hcard : Fintype.card {f : Fin 0 → (Fin n → ZMod 2) // LinearIndependent (ZMod 2) f} = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨Fin.elim0, linearIndependent_empty_type⟩, ?_⟩
      rintro ⟨f, _⟩
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    simp [Finset.sum_const, Finset.card_univ]
  | succ t ih =>
    intro u hu
    let S_big := {f : Fin (t + 1) → (Fin n → ZMod 2) // LinearIndependent (ZMod 2) f}
    let S_small := {f : Fin t → (Fin n → ZMod 2) // LinearIndependent (ZMod 2) f}
    let Sig := Σ R : S_small, {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)}
    let heqv : S_big ≃ Sig :=
      { toFun := fun ⟨R, hli⟩ =>
          have hinit_li : LinearIndependent (ZMod 2) (Fin.init R) := by
            have hfeq : Fin.init R = R ∘ Fin.castSucc := funext fun _ => rfl
            rw [hfeq]
            exact hli.comp Fin.castSucc (Fin.castSucc_injective _)
          have hv : R (Fin.last t) ∉ Submodule.span (ZMod 2) (Set.range (Fin.init R)) := by
            intro hmem
            rw [Submodule.mem_span_range_iff_exists_fun] at hmem
            rcases hmem with ⟨c, hc⟩
            let c' : Fin (t + 1) → ZMod 2 := Fin.snoc c 1
            have hsum0 : ∑ i : Fin (t + 1), c' i • R i = 0 := by
              rw [Fin.sum_univ_castSucc]
              simp only [c', Fin.snoc_castSucc, Fin.snoc_last, one_smul]
              change (∑ i : Fin t, c i • Fin.init R i) + R (Fin.last t) = 0
              rw [hc, zmod2_vec_add_self]
            have hzero := (Fintype.linearIndependent_iff.mp hli) c' hsum0 (Fin.last t)
            simp [c'] at hzero
          ⟨⟨Fin.init R, hinit_li⟩, ⟨R (Fin.last t), hv⟩⟩
        invFun := fun ⟨⟨R, hli⟩, ⟨v, hv⟩⟩ =>
          have hsnoc_li : LinearIndependent (ZMod 2) (Fin.snoc (α := fun _ => Fin n → ZMod 2) R v) := by
            rw [Fintype.linearIndependent_iff]
            intro c hc
            rw [Fin.sum_univ_castSucc] at hc
            simp only [Fin.snoc_castSucc, Fin.snoc_last] at hc
            have hclast : c (Fin.last t) = 0 := by
              rcases zmod2_eq_zero_or_one (c (Fin.last t)) with h0 | h1
              · exact h0
              · exfalso
                rw [h1, one_smul] at hc
                apply hv
                rw [Submodule.mem_span_range_iff_exists_fun]
                refine ⟨fun i => c i.castSucc, ?_⟩
                have h2 := congrArg (· + v) hc
                simp only [add_assoc, zmod2_vec_add_self, add_zero, zero_add] at h2
                exact h2
            rw [hclast, zero_smul, add_zero] at hc
            have hrest := (Fintype.linearIndependent_iff.mp hli) (fun i => c i.castSucc) hc
            intro i
            refine Fin.lastCases hclast hrest i
          ⟨Fin.snoc R v, hsnoc_li⟩
        left_inv := fun ⟨R, _⟩ => by
          apply Subtype.ext
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp
          · intro j; simp [Fin.init]
        right_inv := fun ⟨⟨R, hli⟩, ⟨v, hv⟩⟩ => by
          have hinit_eq : Fin.init (Fin.snoc (α := fun _ => Fin n → ZMod 2) R v) = R :=
            funext fun i => by simp [Fin.init]
          have h1 : (⟨Fin.init (Fin.snoc (α := fun _ => Fin n → ZMod 2) R v),
              by rw [hinit_eq]; exact hli⟩ : S_small) = ⟨R, hli⟩ :=
            Subtype.ext hinit_eq
          refine Sigma.ext h1 ?_
          refine (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr (by simp)
          simp only [hinit_eq] }
    have hu_last : u (Fin.last t) ≠ 0 := hu.ne_zero (Fin.last t)
    have hinner : ∀ R : S_small,
        (∑ v : {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)},
          char v.1 (u (Fin.last t))) =
        -(∑ c : Fin t → ZMod 2, ∏ p : Fin t, char (R.1 p) (c p • u (Fin.last t))) := by
      intro R
      let U := Submodule.span (ZMod 2) (Set.range R.1)
      have htot : (∑ v : Fin n → ZMod 2, char v (u (Fin.last t))) = 0 := by
        rw [sum_char_left]; simp [hu_last]
      have hsplit : (∑ v : Fin n → ZMod 2, char v (u (Fin.last t))) =
          (∑ v ∈ Finset.univ.filter (fun v => v ∈ U), char v (u (Fin.last t))) +
          (∑ v ∈ Finset.univ.filter (fun v => v ∉ U), char v (u (Fin.last t))) :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => v ∈ U) _).symm
      have hsub1 : (∑ v : {v : Fin n → ZMod 2 // v ∉ U}, char v.1 (u (Fin.last t))) =
          ∑ v ∈ Finset.univ.filter (fun v => v ∉ U), char v (u (Fin.last t)) :=
        (Finset.sum_subtype (Finset.univ.filter (fun v => v ∉ U))
          (fun v => by simp) (fun v => char v (u (Fin.last t)))).symm
      have hsub2 : (∑ v ∈ Finset.univ.filter (fun v => v ∈ U), char v (u (Fin.last t))) =
          ∑ c : Fin t → ZMod 2, ∏ p : Fin t, char (R.1 p) (c p • u (Fin.last t)) := by
        let φ : (Fin t → ZMod 2) → (Fin n → ZMod 2) := fun c => ∑ p : Fin t, c p • R.1 p
        have hφ_inj : Function.Injective φ := by
          intro c₁ c₂ heq
          have hsub : ∑ p : Fin t, (c₁ p + c₂ p) • R.1 p = 0 := by
            simp only [add_smul, Finset.sum_add_distrib]
            change φ c₁ + φ c₂ = 0
            rw [heq, zmod2_vec_add_self]
          have h0 := (Fintype.linearIndependent_iff.mp R.2) (fun p => c₁ p + c₂ p) hsub
          funext p
          have hp := h0 p
          have h2 := congrArg (· + c₂ p) hp
          simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
          exact h2
        have hfilt : Finset.univ.filter (fun v => v ∈ U) = Finset.univ.image φ := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, U,
            Submodule.mem_span_range_iff_exists_fun]
          rfl
        rw [hfilt, Finset.sum_image (fun c₁ _ c₂ _ h => hφ_inj h)]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hdot : dot (φ c) (u (Fin.last t)) = ∑ p : Fin t, dot (R.1 p) (c p • u (Fin.last t)) := by
          dsimp only [φ]
          have hlin : ∀ (s : Finset (Fin t)) (f : Fin t → (Fin n → ZMod 2)),
              dot (∑ p ∈ s, f p) (u (Fin.last t)) = ∑ p ∈ s, dot (f p) (u (Fin.last t)) := by
            intro s f
            induction s using Finset.induction_on with
            | empty => simp [dot_zero_left]
            | insert a s' ha ihs => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add_left, ihs]
          rw [hlin]
          refine Finset.sum_congr rfl fun p _ => by rw [dot_smul_left, dot_smul_right]
        dsimp only [char]
        rw [hdot, chi_sum]
      linarith
    have hstep1 : (∑ R : S_big, ∏ p : Fin (t + 1), char (R.1 p) (u p)) =
        ∑ R : S_small, (∏ p : Fin t, char (R.1 p) (u p.castSucc)) *
          ∑ v : {v : Fin n → ZMod 2 // v ∉ Submodule.span (ZMod 2) (Set.range R.1)},
            char v.1 (u (Fin.last t)) := by
      rw [Fintype.sum_equiv heqv _ (fun s =>
        (∏ p : Fin t, char (s.1.1 p) (u p.castSucc)) * char s.2.1 (u (Fin.last t)))]
      · rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun R _ => by
          dsimp only
          rw [Finset.mul_sum]
      · rintro ⟨R, hli⟩
        rw [Fin.prod_univ_castSucc]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun p _ => rfl) rfl
    rw [hstep1]
    simp_rw [hinner, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ c : Fin t → ZMod 2,
        (∑ R : S_small, (∏ p : Fin t, char (R.1 p) (u p.castSucc)) *
          ∏ p : Fin t, char (R.1 p) (c p • u (Fin.last t))) =
        (-1 : ℚ) ^ t * (2 : ℚ) ^ (t * (t - 1) / 2) := by
      intro c
      let u' : Fin t → (Fin n → ZMod 2) := fun p => u p.castSucc + c p • u (Fin.last t)
      have hu' : LinearIndependent (ZMod 2) u' := by
        rw [Fintype.linearIndependent_iff]
        intro a ha
        let a' : Fin (t + 1) → ZMod 2 := Fin.snoc a (∑ p : Fin t, a p * c p)
        have hsum : ∑ i : Fin (t + 1), a' i • u i = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [a', Fin.snoc_castSucc, Fin.snoc_last]
          have hrew : (∑ p : Fin t, a p • u' p) =
              (∑ p : Fin t, a p • u p.castSucc) + (∑ p : Fin t, a p * c p) • u (Fin.last t) := by
            simp only [u', smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]
          rw [← hrew]
          exact ha
        have h0 := (Fintype.linearIndependent_iff.mp hu) a' hsum
        intro p
        have hp := h0 p.castSucc
        simpa [a'] using hp
      calc (∑ R : S_small, (∏ p : Fin t, char (R.1 p) (u p.castSucc)) *
              ∏ p : Fin t, char (R.1 p) (c p • u (Fin.last t)))
          = ∑ R : S_small, ∏ p : Fin t, char (R.1 p) (u' p) := by
            refine Finset.sum_congr rfl fun R _ => ?_
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun p _ => (char_add_right _ _ _).symm
        _ = (-1 : ℚ) ^ t * (2 : ℚ) ^ (t * (t - 1) / 2) := ih u' hu'
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ]
    have hcardC : Fintype.card (Fin t → ZMod 2) = 2 ^ t := by simp [Fintype.card_pi]
    rw [hcardC, nsmul_eq_mul]
    have hexp : t + t * (t - 1) / 2 = (t + 1) * t / 2 := by
      have hdiv : 2 ∣ t * (t - 1) := by
        rcases Nat.even_or_odd t with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨k * (k + k - 1), by ring⟩
        · refine ⟨(2 * k + 1) * k, ?_⟩
          have hsub : 2 * k + 1 - 1 = 2 * k := by omega
          rw [hsub]; ring
      have hmul : (t + 1) * t = 2 * t + t * (t - 1) := by
        cases t with
        | zero => simp
        | succ t' =>
          have hsub : t' + 1 - 1 = t' := by omega
          rw [hsub]; ring
      rcases hdiv with ⟨q, hq⟩
      rw [hmul, hq]
      omega
    push_cast
    rw [pow_succ, ← hexp, pow_add]
    ring

open Classical in
noncomputable def coeffD {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2))
    (D : Submodule (ZMod 2) (Fin m → ZMod 2)) : ℚ :=
  ∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → (Fin m → ZMod 2) => LinearMap.ker (linOf Λ) = D),
    matChar Λ Y

open Classical in
lemma coeffD_eq_zero_of_lt {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2))
    (D : Submodule (ZMod 2) (Fin m → ZMod 2))
    (hlt : j < m - Module.finrank (ZMod 2) D) :
    coeffD Y D = 0 := by
  dsimp only [coeffD]
  refine Finset.sum_eq_zero fun Λ hΛ => ?_
  exfalso
  have hker : LinearMap.ker (linOf Λ) = D := (Finset.mem_filter.mp hΛ).2
  have h1 := codim_ker_linOf Λ
  rw [hker] at h1
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) ≤ j := by
    calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ))
        ≤ Fintype.card (Fin j) := finrank_span_le_card (Set.range Λ) |> le_trans <| by
          have := Set.toFinset_range Λ
          simpa using Finset.card_image_le (s := Finset.univ) (f := Λ)
      _ = j := Fintype.card_fin j
  omega

open Classical in
lemma coeffD_ne_zero {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2))
    (D : Submodule (ZMod 2) (Fin m → ZMod 2))
    (hle : m - Module.finrank (ZMod 2) D ≤ j) :
    coeffD Y D ≠ 0 := by
  let A := Fin m → ZMod 2
  let C := Fin j → ZMod 2
  let W := perp D
  let r := m - Module.finrank (ZMod 2) D
  have hfrW : Module.finrank (ZMod 2) W = r := by
    have h := finrank_perp D
    dsimp only [W, r]
    omega
  by_cases hr0 : r = 0
  · have hWbot : W = ⊥ := Submodule.finrank_eq_zero.mp (hfrW.trans hr0)
    have hDtop : D = ⊤ := by
      have h1 : perp D = perp (⊤ : Submodule (ZMod 2) A) := hWbot.trans perp_top.symm
      exact perp_inj h1
    have hfilt : Finset.univ.filter (fun Λ : Fin j → A => LinearMap.ker (linOf Λ) = D) = {0} := by
      ext Λ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hker
        have hsp : Submodule.span (ZMod 2) (Set.range Λ) = ⊥ := by
          rw [← perp_ker_linOf Λ, hker]; exact hWbot
        funext b
        have hb : Λ b ∈ (⊥ : Submodule (ZMod 2) A) := hsp ▸ Submodule.subset_span ⟨b, rfl⟩
        have hb0 : Λ b = 0 := by simpa using hb
        rw [hb0]; rfl
      · rintro rfl
        rw [ker_linOf, hDtop]
        have hsp : Submodule.span (ZMod 2) (Set.range (0 : Fin j → A)) = ⊥ := by
          rw [Submodule.span_eq_bot]; rintro _ ⟨b, rfl⟩; rfl
        rw [hsp]
        ext v; simp [mem_perp_iff, dot_zero_left]
    dsimp only [coeffD]
    rw [hfilt, Finset.sum_singleton]
    have hmc0 : matChar (0 : Fin j → A) Y = 1 := by
      dsimp only [matChar]; exact Finset.prod_eq_one fun b _ => char_zero_left (Y b)
    rw [hmc0]
    norm_num
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  let : Nonempty (Fin r) := ⟨⟨0, hr_pos⟩⟩
  let η : W →ₗ[ZMod 2] C :=
    { toFun := fun w b => dot w.1 (Y b)
      map_add' := fun w₁ w₂ => by funext b; exact dot_add_left _ _ _
      map_smul' := fun c w => by funext b; exact dot_smul_left c _ _ }
  let eW : W ≃ₗ[ZMod 2] (Fin r → ZMod 2) :=
    ((Module.finBasis (ZMod 2) W).reindex (finCongr hfrW)).equivFun
  let η' : (Fin r → ZMod 2) →ₗ[ZMod 2] C := η.comp eW.symm.toLinearMap
  let K := LinearMap.ker η'
  let s := Module.finrank (ZMod 2) K
  let d := Module.finrank (ZMod 2) (LinearMap.range η')
  have hds : d + s = r := by
    have h := LinearMap.finrank_range_add_finrank_ker η'
    rw [Module.finrank_fin_fun] at h
    exact h
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl K
  have hfrQ : Module.finrank (ZMod 2) Q = d := by
    have h := Submodule.finrank_add_eq_of_isCompl hQ
    rw [Module.finrank_fin_fun] at h
    omega
  let bQ : Module.Basis (Fin d) (ZMod 2) Q :=
    (Module.finBasis (ZMod 2) Q).reindex (finCongr hfrQ)
  let bK : Module.Basis (Fin s) (ZMod 2) K := Module.finBasis (ZMod 2) K
  let eIdx : Fin r ≃ Fin d ⊕ Fin s := (finCongr hds.symm).trans finSumFinEquiv.symm
  let wVec : Fin r → W := fun p =>
    eW.symm (match eIdx p with | Sum.inl i => (bQ i).1 | Sum.inr k => (bK k).1)
  have hw_li : LinearIndependent (ZMod 2) wVec := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : (∑ p : Fin r, c p • (match eIdx p with | Sum.inl i => (bQ i).1 | Sum.inr k => (bK k).1)) = 0 := by
      apply eW.symm.injective
      rw [map_sum, map_zero]
      simpa only [map_smul, wVec] using hc
    have hsplit : (∑ p : Fin r, c p • (match eIdx p with | Sum.inl i => (bQ i).1 | Sum.inr k => (bK k).1)) =
        (∑ i : Fin d, c (eIdx.symm (Sum.inl i)) • (bQ i).1) +
        (∑ k : Fin s, c (eIdx.symm (Sum.inr k)) • (bK k).1) := by
      rw [Fintype.sum_equiv eIdx _ (fun x => c (eIdx.symm x) • match x with | Sum.inl i => (bQ i).1 | Sum.inr k => (bK k).1)]
      · rw [Fintype.sum_sum_type]
      · intro p; simp
    rw [hsplit] at hc'
    have hmemQ : (∑ i : Fin d, c (eIdx.symm (Sum.inl i)) • (bQ i).1) ∈ Q :=
      Submodule.sum_mem Q fun i _ => Submodule.smul_mem Q _ (bQ i).2
    have hmemK : (∑ k : Fin s, c (eIdx.symm (Sum.inr k)) • (bK k).1) ∈ K :=
      Submodule.sum_mem K fun k _ => Submodule.smul_mem K _ (bK k).2
    have hQ0 : (∑ i : Fin d, c (eIdx.symm (Sum.inl i)) • (bQ i).1) = 0 := by
      have hneg := eq_neg_of_add_eq_zero_left hc'
      have hmemK' : (∑ i : Fin d, c (eIdx.symm (Sum.inl i)) • (bQ i).1) ∈ K := by
        rw [hneg]; exact Submodule.neg_mem K hmemK
      have hbot : (∑ i : Fin d, c (eIdx.symm (Sum.inl i)) • (bQ i).1) ∈ K ⊓ Q := ⟨hmemK', hmemQ⟩
      rw [hQ.inf_eq_bot] at hbot
      exact hbot
    have hK0 : (∑ k : Fin s, c (eIdx.symm (Sum.inr k)) • (bK k).1) = 0 := by
      rw [hQ0, zero_add] at hc'; exact hc'
    have hcQ : ∀ i : Fin d, c (eIdx.symm (Sum.inl i)) = 0 := by
      have hsub : (∑ i : Fin d, c (eIdx.symm (Sum.inl i)) • bQ i) = 0 := by
        apply Subtype.ext; rw [Submodule.coe_sum]; exact hQ0
      exact (Fintype.linearIndependent_iff.mp bQ.linearIndependent) _ hsub
    have hcK : ∀ k : Fin s, c (eIdx.symm (Sum.inr k)) = 0 := by
      have hsub : (∑ k : Fin s, c (eIdx.symm (Sum.inr k)) • bK k) = 0 := by
        apply Subtype.ext; rw [Submodule.coe_sum]; exact hK0
      exact (Fintype.linearIndependent_iff.mp bK.linearIndependent) _ hsub
    intro p
    cases h : eIdx p with
    | inl i =>
      have hp : p = eIdx.symm (Sum.inl i) := by rw [← h, Equiv.symm_apply_apply]
      rw [hp]; exact hcQ i
    | inr k =>
      have hp : p = eIdx.symm (Sum.inr k) := by rw [← h, Equiv.symm_apply_apply]
      rw [hp]; exact hcK k
  let bW : Module.Basis (Fin r) (ZMod 2) W :=
    basisOfLinearIndependentOfCardEqFinrank hw_li (by rw [Fintype.card_fin, hfrW])
  have hbW_apply : ∀ p : Fin r, bW p = wVec p := fun p => by
    simp [bW]
  have hd_le_r : d ≤ r := by omega
  have heIdx_cast : ∀ i : Fin d, eIdx (Fin.castLE hd_le_r i) = Sum.inl i := fun i => by
    dsimp only [eIdx]
    apply Equiv.injective finSumFinEquiv
    ext
    simp [finSumFinEquiv_apply_left]
  have hη_zero : ∀ p : Fin r, d ≤ p.val → η (bW p) = 0 := by
    intro p hp
    rw [hbW_apply]
    cases h : eIdx p with
    | inl i =>
      exfalso
      have h1 : p = Fin.castLE hd_le_r i := eIdx.injective (h.trans (heIdx_cast i).symm)
      have h2 : p.val = i.val := congrArg Fin.val h1
      omega
    | inr k =>
      simp only [wVec, h]
      exact LinearMap.mem_ker.mp (bK k).2
  let u : Fin d → C := fun i => η (bW (Fin.castLE hd_le_r i))
  have hu_li : LinearIndependent (ZMod 2) u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmap : η' (∑ i : Fin d, c i • (bQ i).1) = 0 := by
      rw [map_sum]
      have hrew : ∀ i : Fin d, η' (c i • (bQ i).1) = c i • u i := fun i => by
        rw [map_smul]; congr 1
        dsimp only [u, η']; rw [hbW_apply]; simp [wVec, heIdx_cast i]
      simp_rw [hrew]; exact hc
    have hmemK : (∑ i : Fin d, c i • (bQ i).1) ∈ K := LinearMap.mem_ker.mpr hmap
    have hmemQ : (∑ i : Fin d, c i • (bQ i).1) ∈ Q :=
      Submodule.sum_mem Q fun i _ => Submodule.smul_mem Q _ (bQ i).2
    have h0 : (∑ i : Fin d, c i • (bQ i).1) = 0 := by
      have hbot : (∑ i : Fin d, c i • (bQ i).1) ∈ K ⊓ Q := ⟨hmemK, hmemQ⟩
      rw [hQ.inf_eq_bot] at hbot; exact hbot
    have hsub : (∑ i : Fin d, c i • bQ i) = 0 := by apply Subtype.ext; rw [Submodule.coe_sum]; exact h0
    exact (Fintype.linearIndependent_iff.mp bQ.linearIndependent) c hsub
  let S_Λ := {Λ : Fin j → A // LinearMap.ker (linOf Λ) = D}
  let S_R := {R : Fin r → C // LinearIndependent (ZMod 2) R}
  have hker_iff : ∀ Λ : Fin j → A, LinearMap.ker (linOf Λ) = D ↔
      Submodule.span (ZMod 2) (Set.range Λ) = W := fun Λ => by
    constructor
    · intro h; rw [← perp_ker_linOf Λ, h]
    · intro h; rw [ker_linOf Λ, h, perp_perp]
  let toR : S_Λ → S_R := fun ⟨Λ, hΛ⟩ =>
    have hspan : Submodule.span (ZMod 2) (Set.range Λ) = W := (hker_iff Λ).mp hΛ
    have hmemW : ∀ b : Fin j, Λ b ∈ W := fun b => by rw [← hspan]; exact Submodule.subset_span ⟨b, rfl⟩
    let R : Fin r → C := fun p b => bW.repr ⟨Λ b, hmemW b⟩ p
    have hR_li : LinearIndependent (ZMod 2) R := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      let ψ : W →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun w => ∑ p : Fin r, c p * bW.repr w p
          map_add' := fun w₁ w₂ => by simp [map_add, mul_add, Finset.sum_add_distrib]
          map_smul' := fun a w => by
            simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by ring }
      have hψ_zero : ∀ w : W, ψ w = 0 := by
        intro w
        have hw : w.1 ∈ Submodule.span (ZMod 2) (Set.range Λ) := by rw [hspan]; exact w.2
        have hmem_sub : w ∈ Submodule.span (ZMod 2) (Set.range fun b : Fin j => (⟨Λ b, hmemW b⟩ : W)) := by
          rw [Submodule.mem_span_range_iff_exists_fun] at hw ⊢
          rcases hw with ⟨g, hg⟩
          exact ⟨g, by apply Subtype.ext; simpa using hg⟩
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem_sub
        · rintro _ ⟨b, rfl⟩
          have hb := congrFun hc b
          dsimp only [C] at hb
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hb
          exact hb
        · exact map_zero ψ
        · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
        · intro a x _ hx; rw [map_smul, hx, smul_zero]
      intro p
      have hp := hψ_zero (bW p)
      change (∑ q : Fin r, c q * bW.repr (bW p) q) = 0 at hp
      rw [Finset.sum_eq_single p] at hp
      · simpa using hp
      · intro q _ hne; rw [bW.repr_self, Finsupp.single_eq_of_ne hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ p) h
    ⟨R, hR_li⟩
  let ofR : S_R → S_Λ := fun ⟨R, hR⟩ =>
    let Λ : Fin j → A := fun b => ∑ p : Fin r, R p b • (bW p).1
    have hΛ_mem : ∀ b : Fin j, Λ b ∈ W := fun b =>
      Submodule.sum_mem W fun p _ => Submodule.smul_mem W _ (bW p).2
    have hspan : Submodule.span (ZMod 2) (Set.range Λ) = W := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        exact hΛ_mem b
      · let M : C →ₗ[ZMod 2] (Fin r → ZMod 2) :=
          { toFun := fun x p => dot (R p) x
            map_add' := fun x₁ x₂ => by funext p; exact dot_add_right _ _ _
            map_smul' := fun a x => by funext p; exact dot_smul_right a _ _ }
        have hM_surj : Function.Surjective M := by
          have hker_dual : perp (LinearMap.range M) = ⊥ := by
            ext c
            simp only [mem_perp_iff, Submodule.mem_bot]
            constructor
            · intro hc
              have hsum : ∑ p : Fin r, c p • R p = 0 := by
                funext b
                have hb := hc (M (Pi.single b 1)) ⟨Pi.single b 1, rfl⟩
                have hcalc : dot (M (Pi.single b 1)) c = (∑ p : Fin r, c p • R p) b := by
                  change (∑ p : Fin r, dot (R p) (Pi.single b 1) * c p) =
                    (∑ p : Fin r, c p • R p) b
                  dsimp only [C]
                  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [mul_comm]
                  congr 1
                  dsimp only [dot]
                  rw [Finset.sum_eq_single b]
                  · simp [Pi.single_eq_same]
                  · intro x _ hne; simp [Pi.single_eq_of_ne hne]
                  · intro h; exact absurd (Finset.mem_univ b) h
                rw [hcalc] at hb; exact hb
              funext p
              exact (Fintype.linearIndependent_iff.mp hR) c hsum p
            · rintro rfl _ _; exact dot_zero_right _
          have h1 := finrank_perp (LinearMap.range M)
          rw [hker_dual, finrank_bot, zero_add] at h1
          have htop : LinearMap.range M = ⊤ :=
            Submodule.eq_top_of_finrank_eq (by rw [h1, Module.finrank_fin_fun])
          intro y
          have hy : y ∈ LinearMap.range M := by rw [htop]; trivial
          exact hy
        have hrange_eq : Submodule.span (ZMod 2) (Set.range Λ) = W := by
          apply le_antisymm
          · rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact hΛ_mem b
          · intro w hw
            rcases hM_surj (fun p => bW.repr ⟨w, hw⟩ p) with ⟨x, hx⟩
            rw [Submodule.mem_span_range_iff_exists_fun]
            refine ⟨x, ?_⟩
            have hdecomp : (⟨w, hw⟩ : W) = ∑ p : Fin r, bW.repr ⟨w, hw⟩ p • bW p :=
              (bW.sum_repr ⟨w, hw⟩).symm
            have hw_eq : w = ∑ p : Fin r, bW.repr ⟨w, hw⟩ p • (bW p).1 := by
              have h1 := congrArg Subtype.val hdecomp
              rw [Submodule.coe_sum] at h1
              exact h1
            rw [hw_eq]
            calc (∑ b : Fin j, x b • Λ b)
                = ∑ b : Fin j, ∑ p : Fin r, (x b * R p b) • (bW p).1 := by
                  refine Finset.sum_congr rfl fun b _ => ?_
                  simp only [Λ, Finset.smul_sum, smul_smul]
              _ = ∑ p : Fin r, (∑ b : Fin j, R p b * x b) • (bW p).1 := by
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [Finset.sum_smul]
                  refine Finset.sum_congr rfl fun b _ => by rw [mul_comm]
              _ = ∑ p : Fin r, bW.repr ⟨w, hw⟩ p • (bW p).1 := by
                  refine Finset.sum_congr rfl fun p _ => ?_
                  have hp := congrFun hx p
                  exact congrArg (· • (bW p).1) hp
        rw [hrange_eq]
    ⟨Λ, (hker_iff Λ).mpr hspan⟩
  let heqv : S_Λ ≃ S_R :=
    { toFun := toR
      invFun := ofR
      left_inv := fun ⟨Λ, hΛ⟩ => by
        apply Subtype.ext
        funext b
        have hspan : Submodule.span (ZMod 2) (Set.range Λ) = W := (hker_iff Λ).mp hΛ
        have hmemW : Λ b ∈ W := by rw [← hspan]; exact Submodule.subset_span ⟨b, rfl⟩
        have hdecomp := bW.sum_repr ⟨Λ b, hmemW⟩
        have h1 := congrArg Subtype.val hdecomp
        rw [Submodule.coe_sum] at h1
        exact h1
      right_inv := fun ⟨R, hR⟩ => by
        apply Subtype.ext
        funext p b
        have hmem : (ofR ⟨R, hR⟩).1 b ∈ W := by
          have := (hker_iff _).mp (ofR ⟨R, hR⟩).2
          rw [← this]; exact Submodule.subset_span ⟨b, rfl⟩
        have heqW : (⟨(ofR ⟨R, hR⟩).1 b, hmem⟩ : W) = ∑ q : Fin r, R q b • bW q := by
          apply Subtype.ext; rw [Submodule.coe_sum]; rfl
        change bW.repr ⟨(ofR ⟨R, hR⟩).1 b, hmem⟩ p = R p b
        have hfsum : ∀ (s : Finset (Fin r)) (f : Fin r → (Fin r →₀ ZMod 2)),
            (∑ q ∈ s, f q) p = ∑ q ∈ s, f q p := by
          intro s f
          induction s using Finset.induction_on with
          | empty => simp
          | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]
        rw [heqW, map_sum, hfsum]
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single p]
        · simp [bW.repr_self]
        · intro q _ hne; simp [bW.repr_self, Finsupp.single_eq_of_ne (Ne.symm hne)]
        · intro h; exact absurd (Finset.mem_univ p) h }
  have hmatChar_eq : ∀ R : S_R, matChar (ofR R).1 Y =
      ∏ i : Fin d, char (R.1 (Fin.castLE hd_le_r i)) (u i) := by
    intro R
    dsimp only [matChar, char]
    rw [← chi_sum, ← chi_sum]
    congr 1
    calc (∑ b : Fin j, dot ((ofR R).1 b) (Y b))
        = ∑ b : Fin j, ∑ p : Fin r, R.1 p b * dot (bW p).1 (Y b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          dsimp only [ofR]
          have hlin : ∀ (s : Finset (Fin r)) (f : Fin r → A),
              dot (∑ p ∈ s, f p) (Y b) = ∑ p ∈ s, dot (f p) (Y b) := by
            intro s f
            induction s using Finset.induction_on with
            | empty => simp [dot_zero_left]
            | insert a s' ha ihs => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add_left, ihs]
          rw [hlin]
          refine Finset.sum_congr rfl fun p _ => dot_smul_left _ _ _
      _ = ∑ p : Fin r, dot (R.1 p) (η (bW p)) := by
          rw [Finset.sum_comm]
          rfl
      _ = ∑ i : Fin d, dot (R.1 (Fin.castLE hd_le_r i)) (u i) := by
          rw [← Finset.sum_subset (s₁ := Finset.univ.image (Fin.castLE hd_le_r)) (Finset.subset_univ _)]
          · rw [Finset.sum_image (fun i₁ _ i₂ _ h => Fin.castLE_injective hd_le_r h)]
          · intro p _ hp
            have hge : d ≤ p.val := by
              by_contra hlt
              push Not at hlt
              exact hp (Finset.mem_image.mpr ⟨⟨p.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
            rw [hη_zero p hge, dot_zero_right]
  have hcoeff_rew : coeffD Y D = ∑ R : S_R, ∏ i : Fin d, char (R.1 (Fin.castLE hd_le_r i)) (u i) := by
    dsimp only [coeffD]
    rw [Finset.sum_subtype (p := fun Λ : Fin j → A => LinearMap.ker (linOf Λ) = D)
      (Finset.univ.filter (fun Λ : Fin j → A => LinearMap.ker (linOf Λ) = D))
      (fun Λ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun Λ => matChar Λ Y)]
    rw [Fintype.sum_equiv heqv (fun Λ => matChar Λ.1 Y) (fun R => matChar (ofR R).1 Y)
      (fun Λ => by rw [show ofR (heqv Λ) = Λ from heqv.left_inv Λ])]
    refine Finset.sum_congr rfl fun R _ => hmatChar_eq R
  rw [hcoeff_rew]
  let S_head := {R₀ : Fin d → C // LinearIndependent (ZMod 2) R₀}
  let restrictHead : S_R → S_head := fun ⟨R, hR⟩ =>
    ⟨fun i => R (Fin.castLE hd_le_r i), hR.comp (Fin.castLE hd_le_r) (Fin.castLE_injective hd_le_r)⟩
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset S_head))
    (g := restrictHead) (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ R₀ : S_head,
      (∑ R ∈ Finset.univ.filter (fun R : S_R => restrictHead R = R₀),
        ∏ i : Fin d, char (R.1 (Fin.castLE hd_le_r i)) (u i)) =
      (∏ i : Fin d, char (R₀.1 i) (u i)) * ∏ i ∈ Finset.Ico d r, ((2 : ℚ) ^ j - (2 : ℚ) ^ i) := by
    intro R₀
    have hconst : ∀ R ∈ Finset.univ.filter (fun R : S_R => restrictHead R = R₀),
        (∏ i : Fin d, char (R.1 (Fin.castLE hd_le_r i)) (u i)) = ∏ i : Fin d, char (R₀.1 i) (u i) := by
      intro R hR
      have heq := (Finset.mem_filter.mp hR).2
      refine Finset.prod_congr rfl fun i _ => ?_
      have hi : R.1 (Fin.castLE hd_le_r i) = R₀.1 i := congrFun (congrArg Subtype.val heq) i
      rw [hi]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    let FibTy := {R : Fin r → C // LinearIndependent (ZMod 2) R ∧ ∀ i : Fin d, R (Fin.castLE hd_le_r i) = R₀.1 i}
    have hcard_eq : (Finset.univ.filter (fun R : S_R => restrictHead R = R₀)).card = Fintype.card FibTy := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun ⟨⟨R, hR⟩, hmem⟩ =>
            ⟨R, hR, fun i => congrFun (congrArg Subtype.val (Finset.mem_filter.mp hmem).2) i⟩
          invFun := fun ⟨R, hR, hEq⟩ =>
            ⟨⟨R, hR⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext (funext hEq)⟩⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
    rw [hcard_eq]
    exact card_indep_ext j d r hd_le_r R₀.1 R₀.2
  simp_rw [hfib, ← Finset.sum_mul]
  dsimp only [S_head, C]
  rw [sum_indep_char j d u hu_li]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hir : i < j := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hle
  have hlt : (2 : ℚ) ^ i < (2 : ℚ) ^ j := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) hir
  linarith

open Classical in
noncomputable def kappa0_num {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2)) : ℚ :=
  ∑ Λ : Fin j → (Fin m → ZMod 2), matChar Λ Y *
    let r := m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ))
    if r < j then (2 : ℚ) ^ (j - r) - 2 else 0

open Classical in
lemma kappa0_num_eq_zero_iff {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2)) (hY : Y ≠ 0) :
    kappa0_num Y = 0 ↔ m < j ∧ 2 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y)) := by
  let A := Fin m → ZMod 2
  let C := Fin j → ZMod 2
  let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
  have hrankY_pos : 1 ≤ rankY := by
    by_contra h0
    have hr0 : rankY = 0 := by omega
    have hbot : Submodule.span (ZMod 2) (Set.range Y) = ⊥ := Submodule.finrank_eq_zero.mp hr0
    apply hY
    funext b
    have hb : Y b ∈ (⊥ : Submodule (ZMod 2) A) := hbot ▸ Submodule.subset_span ⟨b, rfl⟩
    have hb0 : Y b = 0 := by simpa using hb
    rw [hb0]; rfl
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm' : m = 0 := by omega
    subst hm'
    apply hY
    funext b a
    exact Fin.elim0 a
  have hweight : ∀ Λ : Fin j → A,
      let r := m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ))
      (if r < j then (2 : ℚ) ^ (j - r) - 2 else 0) =
      ((Finset.univ.filter (fun c : C => c ≠ 0 ∧ ∑ b : Fin j, c b • Λ b = 0)).card : ℚ) +
      (if r = j then (1 : ℚ) else 0) - 1 := by
    intro Λ
    let r := m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ))
    let T : C →ₗ[ZMod 2] A :=
      { toFun := fun c => ∑ b : Fin j, c b • Λ b
        map_add' := fun c₁ c₂ => by
          change (∑ b : Fin j, (c₁ b + c₂ b) • Λ b) = _
          simp only [add_smul, Finset.sum_add_distrib]
        map_smul' := fun a c => by
          change (∑ b : Fin j, (a * c b) • Λ b) = a • ∑ b : Fin j, c b • Λ b
          simp only [Finset.smul_sum, smul_smul] }
    have hrangeT : LinearMap.range T = Submodule.span (ZMod 2) (Set.range Λ) := by
      ext v
      simp only [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
      rfl
    have hfr_range : Module.finrank (ZMod 2) (LinearMap.range T) = r := by
      rw [hrangeT, ← codim_ker_linOf Λ]
    have hfr_ker : Module.finrank (ZMod 2) (LinearMap.ker T) = j - r := by
      have h := LinearMap.finrank_range_add_finrank_ker T
      rw [hfr_range, Module.finrank_fin_fun] at h
      omega
    have hr_le_j : r ≤ j := by
      have h := LinearMap.finrank_range_add_finrank_ker T
      rw [hfr_range, Module.finrank_fin_fun] at h
      omega
    have hcard_ker : (Finset.univ.filter (fun c : C => ∑ b : Fin j, c b • Λ b = 0)).card = 2 ^ (j - r) := by
      let : Fintype (LinearMap.ker T) := Fintype.ofFinite _
      have h1 : (Finset.univ.filter (fun c : C => ∑ b : Fin j, c b • Λ b = 0)).card = Fintype.card (LinearMap.ker T) := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr
          { toFun := fun ⟨c, hc⟩ => ⟨c, (Finset.mem_filter.mp hc).2⟩
            invFun := fun ⟨c, hc⟩ => ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [h1, card_subspace, hfr_ker]
    have h0mem : (0 : C) ∈ Finset.univ.filter (fun c : C => ∑ b : Fin j, c b • Λ b = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change (∑ b : Fin j, (0 : ZMod 2) • Λ b) = 0; simp⟩
    have herase : Finset.univ.filter (fun c : C => c ≠ 0 ∧ ∑ b : Fin j, c b • Λ b = 0) =
        (Finset.univ.filter (fun c : C => ∑ b : Fin j, c b • Λ b = 0)).erase 0 := by
      ext c; simp [and_comm]
    have hcard_nz : ((Finset.univ.filter (fun c : C => c ≠ 0 ∧ ∑ b : Fin j, c b • Λ b = 0)).card : ℚ) =
        (2 : ℚ) ^ (j - r) - 1 := by
      rw [herase, Finset.card_erase_of_mem h0mem, hcard_ker]
      have hpos : 1 ≤ 2 ^ (j - r) := Nat.one_le_pow _ _ (by decide)
      rw [Nat.cast_sub hpos]
      push_cast
      rfl
    change (if r < j then (2 : ℚ) ^ (j - r) - 2 else 0) =
      ((Finset.univ.filter (fun c : C => c ≠ 0 ∧ ∑ b : Fin j, c b • Λ b = 0)).card : ℚ) +
      (if r = j then (1 : ℚ) else 0) - 1
    rw [hcard_nz]
    by_cases hlt : r < j
    · have hne : r ≠ j := by omega
      simp only [hlt, ite_true, hne, ite_false]; ring
    · have heq : r = j := by omega
      have hsub : j - r = 0 := by omega
      simp [heq]
  have hdecomp : kappa0_num Y =
      (∑ c ∈ (Finset.univ : Finset C).erase 0,
        ∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0), matChar Λ Y) +
      (∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ)) = j),
        matChar Λ Y) := by
    dsimp only [kappa0_num]
    simp_rw [hweight, mul_sub, mul_add, mul_one, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hsum0 : (∑ Λ : Fin j → A, matChar Λ Y) = 0 := by rw [sum_matChar_left]; simp [hY]
    rw [hsum0, sub_zero]
    congr 1
    · calc (∑ Λ : Fin j → A, matChar Λ Y * ((Finset.univ.filter (fun c : C => c ≠ 0 ∧ ∑ b : Fin j, c b • Λ b = 0)).card : ℚ))
          = ∑ Λ : Fin j → A, ∑ c ∈ (Finset.univ : Finset C).erase 0,
              if ∑ b : Fin j, c b • Λ b = 0 then matChar Λ Y else 0 := by
            refine Finset.sum_congr rfl fun Λ _ => ?_
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
            have hf : ((Finset.univ : Finset C).erase 0).filter (fun c : C => ∑ b : Fin j, c b • Λ b = 0) =
                Finset.univ.filter (fun c : C => c ≠ 0 ∧ ∑ b : Fin j, c b • Λ b = 0) := by
              ext c; simp [and_comm]
            rw [hf]
        _ = ∑ c ∈ (Finset.univ : Finset C).erase 0, ∑ Λ : Fin j → A,
              if ∑ b : Fin j, c b • Λ b = 0 then matChar Λ Y else 0 := Finset.sum_comm
        _ = ∑ c ∈ (Finset.univ : Finset C).erase 0,
              ∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0), matChar Λ Y := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.sum_filter]
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun Λ _ => by split_ifs <;> simp
  have hterm1_c : ∀ c : C, c ≠ 0 →
      (∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0), matChar Λ Y) =
      if ∃ v : A, ∀ b : Fin j, Y b = c b • v then (2 : ℚ) ^ (m * (j - 1)) else 0 := by
    intro c hc
    have hex_b : ∃ b₀ : Fin j, c b₀ = 1 := by
      by_contra hall
      push Not at hall
      apply hc
      funext b
      rcases zmod2_eq_zero_or_one (c b) with h0 | h1
      · exact h0
      · exact absurd h1 (hall b)
    rcases hex_b with ⟨b₀, hb₀⟩
    let Rest := {b : Fin j // b ≠ b₀}
    let S_Λ := {Λ : Fin j → A // ∑ b : Fin j, c b • Λ b = 0}
    let eqv : S_Λ ≃ (Rest → A) :=
      { toFun := fun ⟨Λ, _⟩ b => Λ b.1
        invFun := fun f =>
          let Λ : Fin j → A := fun b =>
            if hb : b = b₀ then ∑ x : Rest, c x.1 • f x else f ⟨b, hb⟩
          have hsum : ∑ b : Fin j, c b • Λ b = 0 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)]
            have h1 : c b₀ • Λ b₀ = ∑ x : Rest, c x.1 • f x := by
              simp [Λ, hb₀]
            have h2 : (∑ b ∈ Finset.univ.erase b₀, c b • Λ b) = ∑ x : Rest, c x.1 • f x := by
              rw [Finset.sum_subtype (p := fun b : Fin j => b ≠ b₀) (Finset.univ.erase b₀)
                (fun b => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
                (fun b => c b • Λ b)]
              refine Finset.sum_congr rfl fun x _ => by simp [Λ, x.2]
            rw [h1, h2, zmod2_vec_add_self]
          ⟨Λ, hsum⟩
        left_inv := fun ⟨Λ, hΛ⟩ => by
          apply Subtype.ext
          funext b
          by_cases hb : b = b₀
          · subst hb
            simp only [↓reduceDIte]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at hΛ
            rw [hb₀, one_smul] at hΛ
            have h2 := congrArg (· + Λ b) hΛ
            rw [add_comm (Λ b), add_assoc, zmod2_vec_add_self, add_zero, zero_add] at h2
            rw [Finset.sum_subtype (p := fun x : Fin j => x ≠ b) (Finset.univ.erase b)
              (fun x => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
              (fun x => c x • Λ x)] at h2
            exact h2
          · simp [hb]
        right_inv := fun f => by funext x; simp [x.2] }
    rw [Finset.sum_subtype (p := fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0)
      (Finset.univ.filter (fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0))
      (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun Λ => matChar Λ Y)]
    rw [Fintype.sum_equiv eqv (fun Λ => matChar Λ.1 Y) (fun f => matChar (eqv.symm f).1 Y)
      (fun Λ => by rw [Equiv.symm_apply_apply])]
    have hprod_eq : ∀ f : Rest → A, matChar (eqv.symm f).1 Y =
        ∏ x : Rest, char (f x) (Y x.1 + c x.1 • Y b₀) := by
      intro f
      dsimp only [matChar]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀)]
      have hb0_val : (eqv.symm f).1 b₀ = ∑ x : Rest, c x.1 • f x := by simp [eqv]
      have hchar_b0 : char ((eqv.symm f).1 b₀) (Y b₀) = ∏ x : Rest, char (f x) (c x.1 • Y b₀) := by
        rw [hb0_val]
        dsimp only [char]
        have hlin : ∀ (s : Finset Rest) (g : Rest → A),
            dot (∑ x ∈ s, g x) (Y b₀) = ∑ x ∈ s, dot (g x) (Y b₀) := by
          intro s g
          induction s using Finset.induction_on with
          | empty => simp [dot_zero_left]
          | insert a s' ha ihs => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add_left, ihs]
        rw [hlin, chi_sum]
        refine Finset.prod_congr rfl fun x _ => by rw [dot_smul_left, dot_smul_right]
      have hrest_prod : (∏ b ∈ Finset.univ.erase b₀, char ((eqv.symm f).1 b) (Y b)) =
          ∏ x : Rest, char (f x) (Y x.1) := by
        rw [Finset.prod_subtype (p := fun b : Fin j => b ≠ b₀) (Finset.univ.erase b₀)
          (fun b => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
          (fun b => char ((eqv.symm f).1 b) (Y b))]
        refine Finset.prod_congr rfl fun x _ => by simp [eqv, x.2]
      rw [hchar_b0, hrest_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => by rw [mul_comm, ← char_add_right]
    simp_rw [hprod_eq]
    rw [← Fintype.prod_sum (fun (x : Rest) (v : A) => char v (Y x.1 + c x.1 • Y b₀))]
    dsimp only [A]
    simp_rw [sum_char_left]
    have hcond : (∀ x : Rest, Y x.1 + c x.1 • Y b₀ = 0) ↔ ∃ v : A, ∀ b : Fin j, Y b = c b • v := by
      constructor
      · intro hall
        refine ⟨Y b₀, fun b => ?_⟩
        by_cases hb : b = b₀
        · subst hb; simp [hb₀]
        · have hx := hall ⟨b, hb⟩
          have h2 := congrArg (· + c b • Y b₀) hx
          simpa [add_assoc, zmod2_vec_add_self] using h2
      · rintro ⟨v, hv⟩ ⟨b, hb⟩
        have hv0 : Y b₀ = v := by simpa [hb₀] using hv b₀
        rw [hv b, hv0, zmod2_vec_add_self]
    by_cases hall : ∀ x : Rest, Y x.1 + c x.1 • Y b₀ = 0
    · have hex_v : ∃ v : Fin m → ZMod 2, ∀ b : Fin j, Y b = c b • v := hcond.mp hall
      simp only [hex_v, ite_true]
      have hcardR : Fintype.card Rest = j - 1 := by
        have h1 : Fintype.card Rest = (Finset.univ.erase b₀).card := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun ⟨b, hb⟩ => ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩⟩
              invFun := fun ⟨b, hb⟩ => ⟨b, (Finset.mem_erase.mp hb).1⟩
              left_inv := fun ⟨_, _⟩ => rfl
              right_inv := fun ⟨_, _⟩ => rfl }
        rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      simp [hall, hcardR, pow_mul]
    · have hnex_v : ¬ ∃ v : Fin m → ZMod 2, ∀ b : Fin j, Y b = c b • v := fun h => hall (hcond.mpr h)
      simp only [hnex_v, ite_false]
      push Not at hall
      rcases hall with ⟨x₀, hx₀⟩
      exact Finset.prod_eq_zero (Finset.mem_univ x₀) (by simp [hx₀])
  have hterm1 : (∑ c ∈ (Finset.univ : Finset C).erase 0,
      ∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0), matChar Λ Y) =
      if rankY = 1 then (2 : ℚ) ^ (m * (j - 1)) else 0 := by
    have hrew : ∀ c ∈ (Finset.univ : Finset C).erase 0,
        (∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => ∑ b : Fin j, c b • Λ b = 0), matChar Λ Y) =
        if ∃ v : A, ∀ b : Fin j, Y b = c b • v then (2 : ℚ) ^ (m * (j - 1)) else 0 :=
      fun c hc => hterm1_c c (Finset.mem_erase.mp hc).1
    rw [Finset.sum_congr rfl hrew]
    by_cases hr1 : rankY = 1
    · simp only [hr1, ite_true]
      have hex_v : ∃ v : A, v ≠ 0 ∧ Submodule.span (ZMod 2) (Set.range Y) = Submodule.span (ZMod 2) {v} := by
        let b1 := (Module.finBasis (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))).reindex (finCongr hr1)
        refine ⟨(b1 0).1, fun h0 => b1.ne_zero 0 (Subtype.ext h0), ?_⟩
        apply le_antisymm
        · intro x hx
          have hdecomp := b1.sum_repr ⟨x, hx⟩
          have hx' : x = b1.repr ⟨x, hx⟩ 0 • (b1 0).1 := by
            have h1 := congrArg Subtype.val hdecomp.symm
            simpa using h1
          rw [hx', Submodule.mem_span_singleton]
          exact ⟨b1.repr ⟨x, hx⟩ 0, rfl⟩
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (b1 0).2)
      rcases hex_v with ⟨v, hv0, hvspan⟩
      have hcoord : ∀ b : Fin j, ∃ cb : ZMod 2, Y b = cb • v := fun b => by
        have hb : Y b ∈ Submodule.span (ZMod 2) {v} := hvspan ▸ Submodule.subset_span ⟨b, rfl⟩
        rcases Submodule.mem_span_singleton.mp hb with ⟨cb, hcb⟩
        exact ⟨cb, hcb.symm⟩
      choose c₀ hc₀ using hcoord
      have hc₀_ne : c₀ ≠ 0 := by
        intro h0
        apply hY
        funext b
        rw [hc₀ b, h0]
        simp
      rw [Finset.sum_eq_single c₀]
      · simp only [show ∃ v : A, ∀ b : Fin j, Y b = c₀ b • v from ⟨v, hc₀⟩, ite_true]
      · intro c _ hne
        have hnot_ex : ¬ ∃ v' : A, ∀ b : Fin j, Y b = c b • v' := by
          rintro ⟨v', hv'⟩
          apply hne
          have hex_b : ∃ b : Fin j, Y b ≠ 0 := by
            by_contra hall; push Not at hall; exact hY (funext hall)
          rcases hex_b with ⟨b₁, hb₁⟩
          have hvv' : v' = v := by
            have h1 := hc₀ b₁
            have h2 := hv' b₁
            rcases zmod2_eq_zero_or_one (c₀ b₁) with hc0 | hc1
            · rw [hc0, zero_smul] at h1; exact absurd h1 hb₁
            · rcases zmod2_eq_zero_or_one (c b₁) with hd0 | hd1
              · rw [hd0, zero_smul] at h2; exact absurd h2 hb₁
              · rw [hc1, one_smul] at h1; rw [hd1, one_smul] at h2; exact h2.symm.trans h1
          funext b
          have h1 : c b • v = c₀ b • v := by
            calc c b • v = c b • v' := by rw [hvv']
              _ = Y b := (hv' b).symm
              _ = c₀ b • v := hc₀ b
          rcases zmod2_eq_zero_or_one (c b) with hcb | hcb <;>
          rcases zmod2_eq_zero_or_one (c₀ b) with hc0b | hc0b
          · rw [hcb, hc0b]
          · rw [hcb, hc0b, zero_smul, one_smul] at h1; exact absurd h1.symm hv0
          · rw [hcb, hc0b, one_smul, zero_smul] at h1; exact absurd h1 hv0
          · rw [hcb, hc0b]
        simp only [hnot_ex, ite_false]
      · intro hnot; exact absurd (Finset.mem_erase.mpr ⟨hc₀_ne, Finset.mem_univ _⟩) hnot
    · simp only [hr1, ite_false]
      refine Finset.sum_eq_zero fun c _ => ?_
      have hnot_ex : ¬ ∃ v : A, ∀ b : Fin j, Y b = c b • v := by
        rintro ⟨v, hv⟩
        have hle : Submodule.span (ZMod 2) (Set.range Y) ≤ Submodule.span (ZMod 2) {v} := by
          rw [Submodule.span_le]
          rintro _ ⟨b, rfl⟩
          rw [hv b]
          exact Submodule.mem_span_singleton.mpr ⟨c b, rfl⟩
        have hfr_le : rankY ≤ 1 := by
          calc rankY ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v} : Set A)) :=
                Submodule.finrank_mono hle
            _ ≤ 1 := le_trans (finrank_span_le_card ({v} : Set A)) (by simp)
        omega
      simp only [hnot_ex, ite_false]
  have hterm2_iff : ∀ Λ : Fin j → A,
      (m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ)) = j) ↔ LinearIndependent (ZMod 2) Λ := fun Λ => by
    rw [codim_ker_linOf Λ]
    constructor
    · intro hfr
      have hle : Fintype.card (Fin j) ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) := by
        rw [hfr, Fintype.card_fin]
      let bsub : Fin j → Submodule.span (ZMod 2) (Set.range Λ) :=
        fun i => ⟨Λ i, Submodule.subset_span ⟨i, rfl⟩⟩
      have hspan_top : (⊤ : Submodule (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ))) ≤
          Submodule.span (ZMod 2) (Set.range bsub) := by
        rintro ⟨x, hx⟩ _
        rw [Submodule.mem_span_range_iff_exists_fun] at hx ⊢
        rcases hx with ⟨c, hc⟩
        exact ⟨c, by apply Subtype.ext; rw [Submodule.coe_sum]; exact hc⟩
      have hli := linearIndependent_of_top_le_span_of_card_le_finrank hspan_top hle
      rw [Fintype.linearIndependent_iff] at hli ⊢
      intro c hc
      exact hli c (by apply Subtype.ext; rw [Submodule.coe_sum]; exact hc)
    · intro hli
      rw [finrank_span_eq_card hli, Fintype.card_fin]
  by_cases hmj : m < j
  · have hterm2_zero : (∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A =>
        m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ)) = j), matChar Λ Y) = 0 := by
      refine Finset.sum_eq_zero fun Λ hΛ => ?_
      exfalso
      have hli := (hterm2_iff Λ).mp (Finset.mem_filter.mp hΛ).2
      have hcard := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, Module.finrank_fin_fun] at hcard
      omega
    rw [hdecomp, hterm1, hterm2_zero, add_zero]
    simp only [hmj, true_and]
    change (if rankY = 1 then (2 : ℚ) ^ (m * (j - 1)) else 0) = 0 ↔ 2 ≤ rankY
    by_cases hr1 : rankY = 1
    · simp only [hr1, ite_true]
      have hne : (2 : ℚ) ^ (m * (j - 1)) ≠ 0 := by positivity
      have hnot2 : ¬ (2 ≤ rankY) := by omega
      simp [hne]
    · simp only [hr1, ite_false]
      have hge2 : 2 ≤ rankY := by omega
      simp [hge2]
  · have hjm : j ≤ m := by omega
    have hnot_mj : ¬ (m < j ∧ 2 ≤ rankY) := fun h => hmj h.1
    change kappa0_num Y = 0 ↔ m < j ∧ 2 ≤ rankY
    simp only [hnot_mj, iff_false]
    let T_Y : C →ₗ[ZMod 2] A :=
      { toFun := fun c => ∑ b : Fin j, c b • Y b
        map_add' := fun c₁ c₂ => by
          change (∑ b : Fin j, (c₁ b + c₂ b) • Y b) = _
          simp only [add_smul, Finset.sum_add_distrib]
        map_smul' := fun a c => by
          change (∑ b : Fin j, (a * c b) • Y b) = a • ∑ b : Fin j, c b • Y b
          simp only [Finset.smul_sum, smul_smul] }
    have hrangeTY : LinearMap.range T_Y = Submodule.span (ZMod 2) (Set.range Y) := by
      ext v; simp only [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]; rfl
    let KY := LinearMap.ker T_Y
    let sY := Module.finrank (ZMod 2) KY
    have hts : rankY + sY = j := by
      have h := LinearMap.finrank_range_add_finrank_ker T_Y
      rw [hrangeTY, Module.finrank_fin_fun] at h
      exact h
    obtain ⟨QY, hQY⟩ := Submodule.exists_isCompl KY
    have hfrQY : Module.finrank (ZMod 2) QY = rankY := by
      have h := Submodule.finrank_add_eq_of_isCompl hQY
      rw [Module.finrank_fin_fun] at h
      omega
    let bQY : Module.Basis (Fin rankY) (ZMod 2) QY :=
      (Module.finBasis (ZMod 2) QY).reindex (finCongr hfrQY)
    let bKY : Module.Basis (Fin sY) (ZMod 2) KY := Module.finBasis (ZMod 2) KY
    let eJ : Fin j ≃ Fin rankY ⊕ Fin sY := (finCongr hts.symm).trans finSumFinEquiv.symm
    let cVec : Fin j → C := fun p =>
      match eJ p with
      | Sum.inl i => (bQY i).1
      | Sum.inr k => (bKY k).1
    have hcVec_li : LinearIndependent (ZMod 2) cVec := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hsplit : (∑ p : Fin j, c p • cVec p) =
          (∑ i : Fin rankY, c (eJ.symm (Sum.inl i)) • (bQY i).1) +
          (∑ k : Fin sY, c (eJ.symm (Sum.inr k)) • (bKY k).1) := by
        rw [Fintype.sum_equiv eJ _ (fun x => c (eJ.symm x) • match x with | Sum.inl i => (bQY i).1 | Sum.inr k => (bKY k).1)]
        · rw [Fintype.sum_sum_type]
        · intro p; simp [cVec]
      rw [hsplit] at hc
      have hmemQ : (∑ i : Fin rankY, c (eJ.symm (Sum.inl i)) • (bQY i).1) ∈ QY :=
        Submodule.sum_mem QY fun i _ => Submodule.smul_mem QY _ (bQY i).2
      have hmemK : (∑ k : Fin sY, c (eJ.symm (Sum.inr k)) • (bKY k).1) ∈ KY :=
        Submodule.sum_mem KY fun k _ => Submodule.smul_mem KY _ (bKY k).2
      have hQ0 : (∑ i : Fin rankY, c (eJ.symm (Sum.inl i)) • (bQY i).1) = 0 := by
        have hneg := eq_neg_of_add_eq_zero_left hc
        have hmemK' : (∑ i : Fin rankY, c (eJ.symm (Sum.inl i)) • (bQY i).1) ∈ KY := by
          rw [hneg]; exact Submodule.neg_mem KY hmemK
        have hbot : (∑ i : Fin rankY, c (eJ.symm (Sum.inl i)) • (bQY i).1) ∈ KY ⊓ QY := ⟨hmemK', hmemQ⟩
        rw [hQY.inf_eq_bot] at hbot; exact hbot
      have hK0 : (∑ k : Fin sY, c (eJ.symm (Sum.inr k)) • (bKY k).1) = 0 := by
        rw [hQ0, zero_add] at hc; exact hc
      have hcQ : ∀ i : Fin rankY, c (eJ.symm (Sum.inl i)) = 0 :=
        (Fintype.linearIndependent_iff.mp bQY.linearIndependent) _ (by apply Subtype.ext; rw [Submodule.coe_sum]; exact hQ0)
      have hcK : ∀ k : Fin sY, c (eJ.symm (Sum.inr k)) = 0 :=
        (Fintype.linearIndependent_iff.mp bKY.linearIndependent) _ (by apply Subtype.ext; rw [Submodule.coe_sum]; exact hK0)
      intro p
      cases h : eJ p with
      | inl i =>
        have hp : p = eJ.symm (Sum.inl i) := by rw [← h, Equiv.symm_apply_apply]
        rw [hp]; exact hcQ i
      | inr k =>
        have hp : p = eJ.symm (Sum.inr k) := by rw [← h, Equiv.symm_apply_apply]
        rw [hp]; exact hcK k
    let : Nonempty (Fin j) := ⟨⟨0, by omega⟩⟩
    let bC : Module.Basis (Fin j) (ZMod 2) C :=
      basisOfLinearIndependentOfCardEqFinrank hcVec_li (by rw [Fintype.card_fin, Module.finrank_fin_fun])
    have hbC_apply : ∀ p : Fin j, bC p = cVec p := fun p => by simp [bC]
    have ht_le_j : rankY ≤ j := by omega
    have heJ_cast : ∀ i : Fin rankY, eJ (Fin.castLE ht_le_j i) = Sum.inl i := fun i => by
      dsimp only [eJ]
      apply Equiv.injective finSumFinEquiv
      ext
      simp [finSumFinEquiv_apply_left]
    let Y' : Fin j → A := fun p => T_Y (bC p)
    have hY'_zero : ∀ p : Fin j, rankY ≤ p.val → Y' p = 0 := by
      intro p hp
      dsimp only [Y']; rw [hbC_apply]
      cases h : eJ p with
      | inl i =>
        exfalso
        have h1 : p = Fin.castLE ht_le_j i := eJ.injective (h.trans (heJ_cast i).symm)
        have h2 : p.val = i.val := congrArg Fin.val h1
        omega
      | inr k =>
        simp only [cVec, h]
        exact LinearMap.mem_ker.mp (bKY k).2
    let uY : Fin rankY → A := fun i => Y' (Fin.castLE ht_le_j i)
    have huY_li : LinearIndependent (ZMod 2) uY := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hmap : T_Y (∑ i : Fin rankY, c i • (bQY i).1) = 0 := by
        rw [map_sum]
        have hrew : ∀ i : Fin rankY, T_Y (c i • (bQY i).1) = c i • uY i := fun i => by
          rw [map_smul]; congr 1
          dsimp only [uY, Y']; rw [hbC_apply]; simp [cVec, heJ_cast i]
        simp_rw [hrew]; exact hc
      have hmemK : (∑ i : Fin rankY, c i • (bQY i).1) ∈ KY := LinearMap.mem_ker.mpr hmap
      have hmemQ : (∑ i : Fin rankY, c i • (bQY i).1) ∈ QY :=
        Submodule.sum_mem QY fun i _ => Submodule.smul_mem QY _ (bQY i).2
      have h0 : (∑ i : Fin rankY, c i • (bQY i).1) = 0 := by
        have hbot : (∑ i : Fin rankY, c i • (bQY i).1) ∈ KY ⊓ QY := ⟨hmemK, hmemQ⟩
        rw [hQY.inf_eq_bot] at hbot; exact hbot
      exact (Fintype.linearIndependent_iff.mp bQY.linearIndependent) c (by apply Subtype.ext; rw [Submodule.coe_sum]; exact h0)
    let Mmat : Matrix (Fin j) (Fin j) (ZMod 2) := fun p b => bC p b
    let M_inv : Matrix (Fin j) (Fin j) (ZMod 2) := fun b p => bC.repr (Pi.single b 1) p
    have hM_mul : ∀ b₁ b₂ : Fin j, (∑ p : Fin j, M_inv b₁ p * Mmat p b₂) = if b₁ = b₂ then 1 else 0 := by
      intro b₁ b₂
      have hdecomp : (∑ p : Fin j, bC.repr (Pi.single b₁ (1 : ZMod 2)) p • bC p) = Pi.single b₁ 1 :=
        bC.sum_repr (Pi.single b₁ (1 : ZMod 2))
      have hb2 := congrFun hdecomp b₂
      dsimp only [C] at hb2
      rw [Finset.sum_apply] at hb2
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hb2
      by_cases h : b₁ = b₂
      · subst h
        simp only [ite_true] at hb2 ⊢
        exact hb2
      · have h' : b₂ ≠ b₁ := Ne.symm h
        simp only [h, h', ite_false] at hb2 ⊢
        exact hb2
    have hM_mul2 : ∀ p₁ p₂ : Fin j, (∑ b : Fin j, Mmat p₁ b * M_inv b p₂) = if p₁ = p₂ then 1 else 0 := by
      intro p₁ p₂
      have hdecomp : bC p₁ = ∑ b : Fin j, bC p₁ b • Pi.single b (1 : ZMod 2) := by
        funext x; simp [Finset.sum_apply, Pi.single_apply]
      have hfsum : ∀ (s : Finset (Fin j)) (f : Fin j → (Fin j →₀ ZMod 2)),
          (∑ b ∈ s, f b) p₂ = ∑ b ∈ s, f b p₂ := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]
      have hrepr := congrArg (fun v => bC.repr v p₂) hdecomp
      rw [bC.repr_self, map_sum, hfsum] at hrepr
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply] at hrepr
      exact hrepr.symm
    let S_ind := {Λ : Fin j → A // LinearIndependent (ZMod 2) Λ}
    let chg : S_ind ≃ S_ind :=
      { toFun := fun ⟨Λ, hΛ⟩ =>
          let Λ' : Fin j → A := fun p => ∑ b : Fin j, M_inv b p • Λ b
          have hli : LinearIndependent (ZMod 2) Λ' := by
            rw [Fintype.linearIndependent_iff]
            intro c hc
            have hsum : ∑ b : Fin j, (∑ p : Fin j, c p * M_inv b p) • Λ b = 0 := by
              calc (∑ b : Fin j, (∑ p : Fin j, c p * M_inv b p) • Λ b)
                  = ∑ b : Fin j, ∑ p : Fin j, (c p * M_inv b p) • Λ b := by
                    refine Finset.sum_congr rfl fun b _ => Finset.sum_smul ..
                _ = ∑ p : Fin j, c p • Λ' p := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun p _ => by simp [Λ', Finset.smul_sum, smul_smul]
                _ = 0 := hc
            have h0 := (Fintype.linearIndependent_iff.mp hΛ) _ hsum
            intro p₁
            calc c p₁ = ∑ p : Fin j, c p * (if p₁ = p then 1 else 0) := by
                  rw [Finset.sum_eq_single p₁] <;> simp (config := { contextual := true }) [Ne.symm]
              _ = ∑ p : Fin j, c p * ∑ b : Fin j, Mmat p₁ b * M_inv b p := by
                  refine Finset.sum_congr rfl fun p _ => by rw [hM_mul2]
              _ = ∑ b : Fin j, Mmat p₁ b * ∑ p : Fin j, c p * M_inv b p := by
                  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => by ring
              _ = 0 := Finset.sum_eq_zero fun b _ => by rw [h0 b, mul_zero]
          ⟨Λ', hli⟩
        invFun := fun ⟨Λ', hΛ'⟩ =>
          let Λ : Fin j → A := fun b => ∑ p : Fin j, Mmat p b • Λ' p
          have hli : LinearIndependent (ZMod 2) Λ := by
            rw [Fintype.linearIndependent_iff]
            intro c hc
            have hsum : ∑ p : Fin j, (∑ b : Fin j, c b * Mmat p b) • Λ' p = 0 := by
              calc (∑ p : Fin j, (∑ b : Fin j, c b * Mmat p b) • Λ' p)
                  = ∑ p : Fin j, ∑ b : Fin j, (c b * Mmat p b) • Λ' p := by
                    refine Finset.sum_congr rfl fun p _ => Finset.sum_smul ..
                _ = ∑ b : Fin j, c b • Λ b := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun b _ => by simp [Λ, Finset.smul_sum, smul_smul]
                _ = 0 := hc
            have h0 := (Fintype.linearIndependent_iff.mp hΛ') _ hsum
            intro b₁
            calc c b₁ = ∑ b : Fin j, c b * (if b₁ = b then 1 else 0) := by
                  rw [Finset.sum_eq_single b₁] <;> simp (config := { contextual := true }) [Ne.symm]
              _ = ∑ b : Fin j, c b * ∑ p : Fin j, M_inv b₁ p * Mmat p b := by
                  refine Finset.sum_congr rfl fun b _ => by rw [hM_mul]
              _ = ∑ p : Fin j, M_inv b₁ p * ∑ b : Fin j, c b * Mmat p b := by
                  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun b _ => by ring
              _ = 0 := Finset.sum_eq_zero fun p _ => by rw [h0 p, mul_zero]
          ⟨Λ, hli⟩
        left_inv := fun ⟨Λ, _⟩ => by
          apply Subtype.ext; funext b
          calc (∑ p : Fin j, Mmat p b • ∑ b' : Fin j, M_inv b' p • Λ b')
              = ∑ b' : Fin j, (∑ p : Fin j, M_inv b' p * Mmat p b) • Λ b' := by
                simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun b' _ => by
                  rw [Finset.sum_smul]; refine Finset.sum_congr rfl fun p _ => by rw [mul_comm]
            _ = ∑ b' : Fin j, (if b' = b then (1 : ZMod 2) else 0) • Λ b' := by
                refine Finset.sum_congr rfl fun b' _ => by rw [hM_mul]
            _ = Λ b := by
                rw [Finset.sum_eq_single b] <;> simp (config := { contextual := true })
        right_inv := fun ⟨Λ', _⟩ => by
          apply Subtype.ext; funext p
          calc (∑ b : Fin j, M_inv b p • ∑ p' : Fin j, Mmat p' b • Λ' p')
              = ∑ p' : Fin j, (∑ b : Fin j, Mmat p' b * M_inv b p) • Λ' p' := by
                simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun p' _ => by
                  rw [Finset.sum_smul]; refine Finset.sum_congr rfl fun b _ => by rw [mul_comm]
            _ = ∑ p' : Fin j, (if p' = p then (1 : ZMod 2) else 0) • Λ' p' := by
                refine Finset.sum_congr rfl fun p' _ => by rw [hM_mul2]
            _ = Λ' p := by
                rw [Finset.sum_eq_single p] <;> simp (config := { contextual := true }) }
    have hmc_chg : ∀ R : S_ind, matChar (chg.symm R).1 Y = ∏ i : Fin rankY, char (R.1 (Fin.castLE ht_le_j i)) (uY i) := by
      intro R
      dsimp only [matChar, char]
      rw [← chi_sum, ← chi_sum]
      congr 1
      calc (∑ b : Fin j, dot ((chg.symm R).1 b) (Y b))
          = ∑ b : Fin j, ∑ p : Fin j, Mmat p b * dot (R.1 p) (Y b) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            have hlin : ∀ (s : Finset (Fin j)) (f : Fin j → A),
                dot (∑ p ∈ s, f p) (Y b) = ∑ p ∈ s, dot (f p) (Y b) := by
              intro s f
              induction s using Finset.induction_on with
              | empty => simp [dot_zero_left]
              | insert a s' ha ihs => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add_left, ihs]
            change dot (∑ p : Fin j, Mmat p b • R.1 p) (Y b) = _
            rw [hlin]
            refine Finset.sum_congr rfl fun p _ => dot_smul_left _ _ _
        _ = ∑ p : Fin j, dot (R.1 p) (Y' p) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            have hlin : ∀ (s : Finset (Fin j)) (f : Fin j → A),
                dot (R.1 p) (∑ b ∈ s, f b) = ∑ b ∈ s, dot (R.1 p) (f b) := by
              intro s f
              induction s using Finset.induction_on with
              | empty => simp [dot_zero_right]
              | insert a s' ha ihs => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add_right, ihs]
            change _ = dot (R.1 p) (∑ b : Fin j, Mmat p b • Y b)
            rw [hlin]
            refine Finset.sum_congr rfl fun b _ => (dot_smul_right _ _ _).symm
        _ = ∑ i : Fin rankY, dot (R.1 (Fin.castLE ht_le_j i)) (uY i) := by
            rw [← Finset.sum_subset (s₁ := Finset.univ.image (Fin.castLE ht_le_j)) (Finset.subset_univ _)]
            · rw [Finset.sum_image (fun i₁ _ i₂ _ h => Fin.castLE_injective ht_le_j h)]
            · intro p _ hp
              have hge : rankY ≤ p.val := by
                by_contra hlt; push Not at hlt
                exact hp (Finset.mem_image.mpr ⟨⟨p.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
              rw [hY'_zero p hge, dot_zero_right]
    have hterm2 : (∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A =>
        m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ)) = j), matChar Λ Y) =
        (-1 : ℚ) ^ rankY * (2 : ℚ) ^ (rankY * (rankY - 1) / 2) *
        ∏ i ∈ Finset.Ico rankY j, ((2 : ℚ) ^ m - (2 : ℚ) ^ i) := by
      have hfilt_eq : Finset.univ.filter (fun Λ : Fin j → A =>
          m - Module.finrank (ZMod 2) (LinearMap.ker (linOf Λ)) = j) =
          Finset.univ.filter (fun Λ : Fin j → A => LinearIndependent (ZMod 2) Λ) := by
        ext Λ; simp [hterm2_iff]
      rw [hfilt_eq, Finset.sum_subtype (p := fun Λ : Fin j → A => LinearIndependent (ZMod 2) Λ) _
        (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun Λ => matChar Λ Y)]
      rw [Fintype.sum_equiv chg (fun Λ => matChar Λ.1 Y) (fun R => matChar (chg.symm R).1 Y)
        (fun Λ => by rw [Equiv.symm_apply_apply])]
      simp_rw [hmc_chg]
      let S_head := {R₀ : Fin rankY → A // LinearIndependent (ZMod 2) R₀}
      let restrictHead : S_ind → S_head := fun ⟨R, hR⟩ =>
        ⟨fun i => R (Fin.castLE ht_le_j i), hR.comp (Fin.castLE ht_le_j) (Fin.castLE_injective ht_le_j)⟩
      rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset S_head))
        (g := restrictHead) (fun _ _ => Finset.mem_univ _)]
      have hfib : ∀ R₀ : S_head,
          (∑ R ∈ Finset.univ.filter (fun R : S_ind => restrictHead R = R₀),
            ∏ i : Fin rankY, char (R.1 (Fin.castLE ht_le_j i)) (uY i)) =
          (∏ i : Fin rankY, char (R₀.1 i) (uY i)) *
          ∏ i ∈ Finset.Ico rankY j, ((2 : ℚ) ^ m - (2 : ℚ) ^ i) := by
        intro R₀
        have hconst : ∀ R ∈ Finset.univ.filter (fun R : S_ind => restrictHead R = R₀),
            (∏ i : Fin rankY, char (R.1 (Fin.castLE ht_le_j i)) (uY i)) = ∏ i : Fin rankY, char (R₀.1 i) (uY i) := by
          intro R hR
          have heq := (Finset.mem_filter.mp hR).2
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [congrFun (congrArg Subtype.val heq) i]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 1
        let FibTy := {R : Fin j → A // LinearIndependent (ZMod 2) R ∧ ∀ i : Fin rankY, R (Fin.castLE ht_le_j i) = R₀.1 i}
        have hcard_eq : (Finset.univ.filter (fun R : S_ind => restrictHead R = R₀)).card = Fintype.card FibTy := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun ⟨⟨R, hR⟩, hmem⟩ =>
                ⟨R, hR, fun i => congrFun (congrArg Subtype.val (Finset.mem_filter.mp hmem).2) i⟩
              invFun := fun ⟨R, hR, hEq⟩ =>
                ⟨⟨R, hR⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext (funext hEq)⟩⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
              right_inv := fun ⟨_, _, _⟩ => rfl }
        rw [hcard_eq]
        exact card_indep_ext m rankY j ht_le_j R₀.1 R₀.2
      simp_rw [hfib, ← Finset.sum_mul]
      dsimp only [S_head, A]
      rw [sum_indep_char m rankY uY huY_li]
    rw [hdecomp, hterm1, hterm2]
    by_cases hr1 : rankY = 1
    · simp only [hr1, ite_true]
      simp only [pow_one, Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, mul_one, neg_one_mul]
      have hprod_lt : (∏ i ∈ Finset.Ico 1 j, ((2 : ℚ) ^ m - (2 : ℚ) ^ i)) < (2 : ℚ) ^ (m * (j - 1)) := by
        have hcard : (Finset.Ico 1 j).card = j - 1 := by simp
        have hpow_eq : (2 : ℚ) ^ (m * (j - 1)) = ∏ _i ∈ Finset.Ico 1 j, (2 : ℚ) ^ m := by
          rw [Finset.prod_const, hcard, pow_mul]
        rw [hpow_eq]
        have hlt_gen : ∀ s : Finset ℕ, s.Nonempty → (∀ i ∈ s, i < m) →
            (∏ i ∈ s, ((2 : ℚ) ^ m - (2 : ℚ) ^ i)) < ∏ _i ∈ s, (2 : ℚ) ^ m := by
          intro s
          induction s using Finset.induction_on with
          | empty => intro hne; exact absurd hne (by simp)
          | insert a t ha ih =>
            intro _ hall
            have ham : a < m := hall a (Finset.mem_insert_self a t)
            have ha_pos : (0 : ℚ) < (2 : ℚ) ^ m - (2 : ℚ) ^ a := by
              have hlt : (2 : ℚ) ^ a < (2 : ℚ) ^ m := by
                exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) ham
              linarith
            have ha_lt : (2 : ℚ) ^ m - (2 : ℚ) ^ a < (2 : ℚ) ^ m := by
              have hpos : (0 : ℚ) < (2 : ℚ) ^ a := by positivity
              linarith
            rw [Finset.prod_insert ha, Finset.prod_insert ha]
            by_cases ht : t = ∅
            · subst ht; simp [ha_lt]
            · have hne_t : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
              have iht := ih hne_t fun i hi => hall i (Finset.mem_insert_of_mem hi)
              have ht_pos : (0 : ℚ) < ∏ i ∈ t, ((2 : ℚ) ^ m - (2 : ℚ) ^ i) :=
                Finset.prod_pos fun i hi => by
                  have him := hall i (Finset.mem_insert_of_mem hi)
                  have hlt : (2 : ℚ) ^ i < (2 : ℚ) ^ m := by
                    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) him
                  linarith
              have hm_pos : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
              nlinarith
        exact hlt_gen (Finset.Ico 1 j) ⟨1, Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩⟩
          fun i hi => lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hjm
      linarith
    · simp only [hr1, ite_false, zero_add]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) ?_
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have him : i < m := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hjm
      have hlt : (2 : ℚ) ^ i < (2 : ℚ) ^ m := by
        exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) him
      linarith

open Classical in
noncomputable def kappa_nz_num {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2)) (α : Fin m → ZMod 2) : ℚ :=
  ∑ Λ : Fin j → (Fin m → ZMod 2), matChar Λ Y *
    let W := Submodule.span (ZMod 2) (Set.range Λ)
    if α ∈ W then (2 : ℚ) ^ (j - Module.finrank (ZMod 2) W) - 1 else 0

open Classical in
lemma kappa_nz_num_ne_zero {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2))
    (α : Fin m → ZMod 2) (hα : α ≠ 0) :
    kappa_nz_num Y α ≠ 0 := by
  let A := Fin m → ZMod 2
  let chiZ : ZMod 2 → ℤ := fun b => if b = 0 then 1 else -1
  let matCharZ : (Fin j → A) → ℤ := fun Λ => ∏ b : Fin j, chiZ (dot (Λ b) (Y b))
  have hmc_cast : ∀ Λ : Fin j → A, (matCharZ Λ : ℚ) = matChar Λ Y := fun Λ => by
    dsimp only [matCharZ, matChar, char, chi, chiZ]
    push_cast
    refine Finset.prod_congr rfl fun b _ => by split_ifs <;> simp
  have hmc_odd : ∀ Λ : Fin j → A, Odd (matCharZ Λ) := fun Λ => by
    dsimp only [matCharZ]
    have hprod_odd : ∀ (s : Finset (Fin j)), Odd (∏ b ∈ s, chiZ (dot (Λ b) (Y b))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0, by norm_num⟩
      | insert a t ha ih =>
        rw [Finset.prod_insert ha]
        refine Odd.mul ?_ ih
        dsimp only [chiZ]
        split_ifs
        · exact ⟨0, by omega⟩
        · exact ⟨-1, by omega⟩
    exact hprod_odd Finset.univ
  let wZ : (Fin j → A) → ℤ := fun Λ =>
    let W := Submodule.span (ZMod 2) (Set.range Λ)
    if α ∈ W then (2 : ℤ) ^ (j - Module.finrank (ZMod 2) W) - 1 else 0
  have hw_cast : ∀ Λ : Fin j → A, (wZ Λ : ℚ) =
      (let W := Submodule.span (ZMod 2) (Set.range Λ)
       if α ∈ W then (2 : ℚ) ^ (j - Module.finrank (ZMod 2) W) - 1 else 0) := fun Λ => by
    dsimp only [wZ]
    split_ifs <;> push_cast <;> rfl
  let totalZ : ℤ := ∑ Λ : Fin j → A, matCharZ Λ * wZ Λ
  have htot_cast : (totalZ : ℚ) = kappa_nz_num Y α := by
    dsimp only [totalZ, kappa_nz_num]
    push_cast
    refine Finset.sum_congr rfl fun Λ _ => by rw [hmc_cast, hw_cast]
  rw [← htot_cast]
  suffices hodd : Odd totalZ by
    intro h0
    have h0z : totalZ = 0 := by exact_mod_cast h0
    rcases hodd with ⟨k, hk⟩
    omega
  let S_hi : Finset (Fin j → A) :=
    Finset.univ.filter (fun Λ => 2 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)))
  let S_lo : Finset (Fin j → A) :=
    Finset.univ.filter (fun Λ => ¬ 2 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)))
  have hsplit : totalZ = (∑ Λ ∈ S_hi, matCharZ Λ * wZ Λ) + (∑ Λ ∈ S_lo, matCharZ Λ * wZ Λ) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have heven_hi : Even (∑ Λ ∈ S_hi, matCharZ Λ * wZ Λ) := by
    have hmod : ∀ Λ ∈ S_hi, Even (matCharZ Λ * wZ Λ - wZ Λ) := fun Λ _ => by
      rcases hmc_odd Λ with ⟨k, hk⟩
      exact ⟨k * wZ Λ, by rw [hk]; ring⟩
    have hdiff_even : Even ((∑ Λ ∈ S_hi, matCharZ Λ * wZ Λ) - ∑ Λ ∈ S_hi, wZ Λ) := by
      rw [← Finset.sum_sub_distrib]
      have hsum_even : ∀ (s : Finset (Fin j → A)), (∀ Λ ∈ s, Even (matCharZ Λ * wZ Λ - wZ Λ)) →
          Even (∑ Λ ∈ s, (matCharZ Λ * wZ Λ - wZ Λ)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => intro _; exact ⟨0, by norm_num⟩
        | insert a t ha ih =>
          intro h
          rw [Finset.sum_insert ha]
          exact Even.add (h a (Finset.mem_insert_self a t))
            (ih fun x hx => h x (Finset.mem_insert_of_mem hx))
      exact hsum_even S_hi hmod
    suffices hw_even : Even (∑ Λ ∈ S_hi, wZ Λ) by
      rcases hdiff_even with ⟨a, ha⟩
      rcases hw_even with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
    let b0Of (Λ : Fin j → A) : WithTop (Fin j) :=
      (Finset.univ.filter (fun b : Fin j => Λ b ≠ 0)).min
    let b1Of (Λ : Fin j → A) : WithTop (Fin j) :=
      match b0Of Λ with
      | ⊤ => ⊤
      | (b0 : Fin j) => (Finset.univ.filter (fun b : Fin j => Λ b ≠ 0 ∧ Λ b ≠ Λ b0)).min
    let τ (Λ : Fin j → A) : Fin j → A :=
      match b0Of Λ, b1Of Λ with
      | (b0 : Fin j), (b1 : Fin j) => Function.update Λ b1 (Λ b1 + Λ b0)
      | _, _ => Λ
    have hhi_b01 : ∀ Λ ∈ S_hi, ∃ b0 b1 : Fin j, b0Of Λ = (b0 : WithTop (Fin j)) ∧
        b1Of Λ = (b1 : WithTop (Fin j)) ∧ Λ b0 ≠ 0 ∧ Λ b1 ≠ 0 ∧ Λ b1 ≠ Λ b0 ∧ b0 < b1 := by
      intro Λ hΛ
      have hfr : 2 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) :=
        (Finset.mem_filter.mp hΛ).2
      have hne0 : (Finset.univ.filter (fun b : Fin j => Λ b ≠ 0)).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hΛ0 : Λ = 0 := funext fun b => by
          by_contra hne
          have hmem : b ∈ Finset.univ.filter (fun b : Fin j => Λ b ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
        have hspan0 : Submodule.span (ZMod 2) (Set.range Λ) = ⊥ := by
          rw [hΛ0, Submodule.span_eq_bot]; rintro _ ⟨b, rfl⟩; rfl
        rw [hspan0, finrank_bot] at hfr; omega
      rcases Finset.min_of_nonempty hne0 with ⟨b0, hb0⟩
      have hb0_mem : Λ b0 ≠ 0 := (Finset.mem_filter.mp (Finset.mem_of_min hb0)).2
      have hne1 : (Finset.univ.filter (fun b : Fin j => Λ b ≠ 0 ∧ Λ b ≠ Λ b0)).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hle : Submodule.span (ZMod 2) (Set.range Λ) ≤ Submodule.span (ZMod 2) {Λ b0} := by
          rw [Submodule.span_le]
          rintro _ ⟨b, rfl⟩
          by_cases h1 : Λ b = 0
          · rw [h1]; exact Submodule.zero_mem _
          · have h2 : Λ b = Λ b0 := by
              by_contra hne
              have hmem : b ∈ Finset.univ.filter (fun b : Fin j => Λ b ≠ 0 ∧ Λ b ≠ Λ b0) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, hne⟩
              rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
            rw [h2]; exact Submodule.subset_span (Set.mem_singleton _)
        have hfr1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) ≤ 1 := by
          calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ))
              ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({Λ b0} : Set A)) := Submodule.finrank_mono hle
            _ ≤ 1 := le_trans (finrank_span_le_card ({Λ b0} : Set A)) (by simp)
        omega
      rcases Finset.min_of_nonempty hne1 with ⟨b1, hb1⟩
      have hb1_mem := (Finset.mem_filter.mp (Finset.mem_of_min hb1)).2
      have hb0_le : b0 ≤ b1 := Finset.min_le_of_eq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb1_mem.1⟩) hb0
      have hb0_ne_b1 : b0 ≠ b1 := fun heq => hb1_mem.2 (heq ▸ rfl)
      have hb0_lt : b0 < b1 := lt_of_le_of_ne hb0_le hb0_ne_b1
      refine ⟨b0, b1, hb0, ?_, hb0_mem, hb1_mem.1, hb1_mem.2, hb0_lt⟩
      have hb0_eq : b0Of Λ = (b0 : WithTop (Fin j)) := hb0
      change (match b0Of Λ with | none => ⊤ | some b => (Finset.univ.filter (fun x : Fin j => Λ x ≠ 0 ∧ Λ x ≠ Λ b)).min) = _
      rw [hb0_eq]; exact hb1
    have hτ_b01 : ∀ Λ ∈ S_hi, b0Of (τ Λ) = b0Of Λ ∧ b1Of (τ Λ) = b1Of Λ := by
      intro Λ hΛ
      rcases hhi_b01 Λ hΛ with ⟨b0, b1, hb0, hb1, hΛ0, hΛ1, hΛ10, hlt⟩
      have hτ_eq : τ Λ = Function.update Λ b1 (Λ b1 + Λ b0) := by dsimp only [τ]; rw [hb0, hb1]
      have hsum_ne0 : Λ b1 + Λ b0 ≠ 0 := by
        intro h0
        apply hΛ10
        have h2 := congrArg (· + Λ b0) h0
        rw [add_assoc, zmod2_vec_add_self, add_zero, zero_add] at h2
        exact h2
      have hsum_ne0' : Λ b1 + Λ b0 ≠ Λ b0 := by
        intro h0
        apply hΛ1
        have h2 := congrArg (· + Λ b0) h0
        rw [add_assoc, zmod2_vec_add_self, add_zero] at h2
        exact h2
      have hf0 : Finset.univ.filter (fun b : Fin j => τ Λ b ≠ 0) =
          Finset.univ.filter (fun b : Fin j => Λ b ≠ 0) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hτ_eq]
        by_cases hb : b = b1
        · subst hb; simp [hsum_ne0, hΛ1]
        · simp [Function.update_of_ne hb]
      have hb0' : b0Of (τ Λ) = (b0 : WithTop (Fin j)) := by dsimp only [b0Of]; rw [hf0]; exact hb0
      have hf1 : Finset.univ.filter (fun b : Fin j => τ Λ b ≠ 0 ∧ τ Λ b ≠ τ Λ b0) =
          Finset.univ.filter (fun b : Fin j => Λ b ≠ 0 ∧ Λ b ≠ Λ b0) := by
        have hτb0 : τ Λ b0 = Λ b0 := by rw [hτ_eq, Function.update_of_ne (ne_of_lt hlt)]
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hτb0, hτ_eq]
        by_cases hb : b = b1
        · subst hb; simp [hsum_ne0, hsum_ne0', hΛ1, hΛ10]
        · simp [Function.update_of_ne hb]
      have hb1' : b1Of (τ Λ) = (b1 : WithTop (Fin j)) := by
        change (match b0Of (τ Λ) with | none => ⊤ | some b => (Finset.univ.filter (fun x : Fin j => τ Λ x ≠ 0 ∧ τ Λ x ≠ τ Λ b)).min) = _
        rw [hb0']
        change (Finset.univ.filter (fun x : Fin j => τ Λ x ≠ 0 ∧ τ Λ x ≠ τ Λ b0)).min = _
        rw [hf1]
        change (match b0Of Λ with | none => ⊤ | some b => (Finset.univ.filter (fun x : Fin j => Λ x ≠ 0 ∧ Λ x ≠ Λ b)).min) = _ at hb1
        rw [hb0] at hb1
        exact hb1
      exact ⟨hb0'.trans hb0.symm, hb1'.trans hb1.symm⟩
    have hτ_span : ∀ Λ ∈ S_hi, Submodule.span (ZMod 2) (Set.range (τ Λ)) =
        Submodule.span (ZMod 2) (Set.range Λ) := by
      intro Λ hΛ
      rcases hhi_b01 Λ hΛ with ⟨b0, b1, hb0, hb1, _, _, _, hlt⟩
      have hτ_eq : τ Λ = Function.update Λ b1 (Λ b1 + Λ b0) := by dsimp only [τ]; rw [hb0, hb1]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        rw [hτ_eq]
        by_cases hb : b = b1
        · subst hb; rw [Function.update_self]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩) (Submodule.subset_span ⟨b0, rfl⟩)
        · rw [Function.update_of_ne hb]; exact Submodule.subset_span ⟨b, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        by_cases hb : b = b1
        · subst hb
          have h1 : τ Λ b = Λ b + Λ b0 := by rw [hτ_eq, Function.update_self]
          have h2 : τ Λ b0 = Λ b0 := by rw [hτ_eq, Function.update_of_ne (ne_of_lt hlt)]
          have h3 : Λ b = τ Λ b + τ Λ b0 := by rw [h1, h2, add_assoc, zmod2_vec_add_self, add_zero]
          rw [h3]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩) (Submodule.subset_span ⟨b0, rfl⟩)
        · have h2 : τ Λ b = Λ b := by rw [hτ_eq, Function.update_of_ne hb]
          rw [← h2]; exact Submodule.subset_span ⟨b, rfl⟩
    have hτ_mem : ∀ Λ ∈ S_hi, τ Λ ∈ S_hi := fun Λ hΛ => by
      have hsp := hτ_span Λ hΛ
      simp only [S_hi, Finset.mem_filter, Finset.mem_univ, true_and] at hΛ ⊢
      rw [hsp]; exact hΛ
    have hτ_inv : ∀ Λ ∈ S_hi, τ (τ Λ) = Λ := fun Λ hΛ => by
      rcases hhi_b01 Λ hΛ with ⟨b0, b1, hb0, hb1, _, _, _, hlt⟩
      have ⟨hb0', hb1'⟩ := hτ_b01 Λ hΛ
      have hτ_eq : τ Λ = Function.update Λ b1 (Λ b1 + Λ b0) := by dsimp only [τ]; rw [hb0, hb1]
      have hτ2_eq : τ (τ Λ) = Function.update (τ Λ) b1 (τ Λ b1 + τ Λ b0) := by
        dsimp only [τ]; rw [hb0', hb1', hb0, hb1]
      rw [hτ2_eq, hτ_eq]
      funext b
      by_cases hb : b = b1
      · subst hb
        rw [Function.update_self, Function.update_self, Function.update_of_ne (ne_of_lt hlt), add_assoc,
          zmod2_vec_add_self, add_zero]
      · rw [Function.update_of_ne hb, Function.update_of_ne hb]
    have hτ_ne : ∀ Λ ∈ S_hi, τ Λ ≠ Λ := fun Λ hΛ => by
      rcases hhi_b01 Λ hΛ with ⟨b0, b1, hb0, hb1, hΛ0, _, _, _⟩
      intro heq
      have h1 := congrFun heq b1
      have hτ_eq : τ Λ = Function.update Λ b1 (Λ b1 + Λ b0) := by dsimp only [τ]; rw [hb0, hb1]
      rw [hτ_eq, Function.update_self] at h1
      have h2 := congrArg (Λ b1 + ·) h1
      rw [← add_assoc, zmod2_vec_add_self, zero_add] at h2
      exact hΛ0 h2
    have hτ_w : ∀ Λ ∈ S_hi, wZ (τ Λ) = wZ Λ := fun Λ hΛ => by
      dsimp only [wZ]; rw [hτ_span Λ hΛ]
    have hpair : ∀ s : Finset (Fin j → A),
        (∀ x ∈ s, τ x ∈ s ∧ τ (τ x) = x ∧ τ x ≠ x ∧ wZ (τ x) = wZ x) →
        Even (∑ x ∈ s, wZ x) := by
      intro s
      induction s using Finset.strongInduction with
      | H s ih =>
        intro hs
        by_cases hempty : s = ∅
        · subst hempty; simp
        · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨x, hx⟩
          have ⟨hτx, hinv, hne, hw⟩ := hs x hx
          let s' := (s.erase x).erase (τ x)
          have hsub : s' ⊂ s := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
            · intro heq
              have : x ∈ s' := heq.symm ▸ hx
              exact (Finset.mem_erase.mp (Finset.mem_erase.mp this).2).1 rfl
          have hs' : ∀ y ∈ s', τ y ∈ s' ∧ τ (τ y) = y ∧ τ y ≠ y ∧ wZ (τ y) = wZ y := by
            intro y hy
            have hy1 := Finset.mem_erase.mp hy
            have hy2 := Finset.mem_erase.mp hy1.2
            have ⟨hτy, hinv_y, hne_y, hw_y⟩ := hs y hy2.2
            refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hτy⟩⟩, hinv_y, hne_y, hw_y⟩
            · intro heq; exact hy2.1 (by rw [← hinv_y, heq, hinv])
            · intro heq; exact hy1.1 (by rw [← hinv_y, heq])
          have hih := ih s' hsub hs'
          have hτx_in : τ x ∈ s.erase x := Finset.mem_erase.mpr ⟨hne, hτx⟩
          have hsum_eq : (∑ y ∈ s, wZ y) = wZ x + wZ (τ x) + ∑ y ∈ s', wZ y := by
            rw [← Finset.add_sum_erase s wZ hx, ← Finset.add_sum_erase (s.erase x) wZ hτx_in, add_assoc]
          rw [hsum_eq, hw]
          rcases hih with ⟨k, hk⟩
          exact ⟨wZ x + k, by omega⟩
    exact hpair S_hi fun Λ hΛ => ⟨hτ_mem Λ hΛ, hτ_inv Λ hΛ, hτ_ne Λ hΛ, hτ_w Λ hΛ⟩
  have hodd_lo : Odd (∑ Λ ∈ S_lo, matCharZ Λ * wZ Λ) := by
    let S_one : Finset (Fin j → A) :=
      Finset.univ.filter (fun Λ => (∀ b : Fin j, Λ b = 0 ∨ Λ b = α) ∧ Λ ≠ 0)
    have hlo_van : ∀ Λ ∈ S_lo, Λ ∉ S_one → matCharZ Λ * wZ Λ = 0 := by
      intro Λ hΛ hnot
      have hfr_le1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) ≤ 1 := by
        have := (Finset.mem_filter.mp hΛ).2; omega
      by_cases hmem : α ∈ Submodule.span (ZMod 2) (Set.range Λ)
      · exfalso
        have hle : Submodule.span (ZMod 2) {α} ≤ Submodule.span (ZMod 2) (Set.range Λ) :=
          Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
        have hfr1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({α} : Set A)) = 1 :=
          finrank_span_singleton hα
        have hmono : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({α} : Set A)) ≤
            Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) :=
          Submodule.finrank_mono hle
        have hfr_eq : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) = 1 :=
          le_antisymm hfr_le1 (hfr1 ▸ hmono)
        have heq : Submodule.span (ZMod 2) (Set.range Λ) = Submodule.span (ZMod 2) {α} :=
          (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr1, hfr_eq])).symm
        apply hnot
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro b
          have hb : Λ b ∈ Submodule.span (ZMod 2) {α} := heq ▸ Submodule.subset_span ⟨b, rfl⟩
          rcases Submodule.mem_span_singleton.mp hb with ⟨c, hc⟩
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · left; rw [← hc, zero_smul]
          · right; rw [← hc, one_smul]
        · intro h0
          rw [h0] at hmem
          have hbot : Submodule.span (ZMod 2) (Set.range (0 : Fin j → A)) = ⊥ := by
            rw [Submodule.span_eq_bot]; rintro _ ⟨b, rfl⟩; rfl
          rw [hbot] at hmem
          exact hα (by simpa using hmem)
      · simp [wZ, hmem]
    have hsub : S_one ⊆ S_lo := by
      intro Λ hΛ
      rcases (Finset.mem_filter.mp hΛ).2 with ⟨hall, _⟩
      have hle : Submodule.span (ZMod 2) (Set.range Λ) ≤ Submodule.span (ZMod 2) {α} := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        rcases hall b with h0 | h1
        · rw [h0]; exact Submodule.zero_mem _
        · rw [h1]; exact Submodule.subset_span (Set.mem_singleton _)
      have hfr1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) ≤ 1 := by
        calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ))
            ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({α} : Set A)) := Submodule.finrank_mono hle
          _ = 1 := finrank_span_singleton hα
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    rw [← Finset.sum_subset hsub hlo_van]
    have hterm_odd : ∀ Λ ∈ S_one, Odd (matCharZ Λ * wZ Λ) := fun Λ hΛ => by
      rcases (Finset.mem_filter.mp hΛ).2 with ⟨hall, hne0⟩
      have hhex : ∃ b : Fin j, Λ b = α := by
        by_contra hnone; push Not at hnone
        apply hne0; funext b
        rcases hall b with h0 | h1
        · exact h0
        · exact absurd h1 (hnone b)
      rcases hhex with ⟨b₀, hb₀⟩
      have hspan : Submodule.span (ZMod 2) (Set.range Λ) = Submodule.span (ZMod 2) {α} := by
        apply le_antisymm
        · rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩
          rcases hall b with h0 | h1
          · rw [h0]; exact Submodule.zero_mem _
          · rw [h1]; exact Submodule.subset_span (Set.mem_singleton _)
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hb₀ ▸ Submodule.subset_span ⟨b₀, rfl⟩))
      have hw_val : wZ Λ = (2 : ℤ) ^ (j - 1) - 1 := by
        dsimp only [wZ]
        rw [hspan, finrank_span_singleton hα]
        simp [Submodule.mem_span_singleton_self]
      rw [hw_val]
      refine (hmc_odd Λ).mul ?_
      have hjm1 : 1 ≤ j - 1 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hjm1
      refine ⟨(2 : ℤ) ^ k - 1, ?_⟩
      rw [hk, add_comm 1 k, pow_succ]
      ring
    have hcard_one : S_one.card = 2 ^ j - 1 := by
      let eqv : {Λ : Fin j → A // Λ ∈ S_one} ≃ {c : Fin j → ZMod 2 // c ≠ 0} :=
        { toFun := fun ⟨Λ, hΛ⟩ =>
            ⟨fun b => if Λ b = 0 then 0 else 1, fun h0 => by
              apply (Finset.mem_filter.mp hΛ).2.2
              funext b
              have hb := congrFun h0 b
              by_cases h1 : Λ b = 0
              · exact h1
              · simp [h1] at hb⟩
          invFun := fun ⟨c, hc⟩ =>
            ⟨fun b => c b • α, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              fun b => by
                rcases zmod2_eq_zero_or_one (c b) with hc0 | hc1
                · left; simp [hc0]
                · right; simp [hc1],
              fun h0 => hc (funext fun b => by
                have hb := congrFun h0 b
                rcases zmod2_eq_zero_or_one (c b) with h1 | h1
                · exact h1
                · rw [h1, one_smul] at hb; exact absurd hb hα)⟩⟩
          left_inv := fun ⟨Λ, hΛ⟩ => by
            apply Subtype.ext; funext b
            rcases (Finset.mem_filter.mp hΛ).2.1 b with h0 | h1
            · simp [h0]
            · simp [h1, hα]
          right_inv := fun ⟨c, _⟩ => by
            apply Subtype.ext; funext b
            rcases zmod2_eq_zero_or_one (c b) with h0 | h1
            · simp [h0]
            · simp [h1, hα] }
      rw [← Fintype.card_coe, Fintype.card_congr eqv]
      have h1 : Fintype.card {c : Fin j → ZMod 2 // c ≠ 0} = ((Finset.univ : Finset (Fin j → ZMod 2)).erase 0).card := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr
          { toFun := fun ⟨c, hc⟩ => ⟨c, Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩⟩
            invFun := fun ⟨c, hc⟩ => ⟨c, (Finset.mem_erase.mp hc).1⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl }
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [Fintype.card_pi]
    have hcard_odd : Odd S_one.card := by
      rw [hcard_one]
      have hpos : 1 ≤ j := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
      refine ⟨2 ^ k - 1, ?_⟩
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
      rw [hk, add_comm 1 k, pow_succ]
      omega
    have hsum_odd : ∀ (s : Finset (Fin j → A)), (∀ x ∈ s, Odd (matCharZ x * wZ x)) →
        (Odd s.card → Odd (∑ x ∈ s, matCharZ x * wZ x)) ∧
        (Even s.card → Even (∑ x ∈ s, matCharZ x * wZ x)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨fun h => by simp at h, fun _ => by simp⟩
      | insert a t ha ih =>
        intro hodd_all
        have hta := ih (fun x hx => hodd_all x (Finset.mem_insert_of_mem hx))
        have ha_odd := hodd_all a (Finset.mem_insert_self a t)
        rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
        constructor
        · intro hcard
          have ht_even : Even t.card := by
            rcases hcard with ⟨k, hk⟩; exact ⟨k, by omega⟩
          rcases ha_odd with ⟨u, hu⟩
          rcases hta.2 ht_even with ⟨v, hv⟩
          exact ⟨u + v, by omega⟩
        · intro hcard
          have ht_odd : Odd t.card := by
            rcases hcard with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
          rcases ha_odd with ⟨u, hu⟩
          rcases hta.1 ht_odd with ⟨v, hv⟩
          exact ⟨u + v + 1, by omega⟩
    exact (hsum_odd S_one hterm_odd).1 hcard_odd
  rw [hsplit]
  rcases heven_hi with ⟨a, ha⟩
  rcases hodd_lo with ⟨b, hb⟩
  exact ⟨a + b, by omega⟩

lemma fits_pad {A : Type*} (count : List A → ℚ) (test : List A → Prop) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂)
    (h1 : ∃ (u v : Fin k₁ → ℚ) (M : A → Matrix (Fin k₁) (Fin k₁) ℚ),
      ∀ w : List A, test w → (∑ i : Fin k₁, ∑ l : Fin k₁, u i * (w.map M).prod i l * v l) = count w) :
    ∃ (u v : Fin k₂ → ℚ) (M : A → Matrix (Fin k₂) (Fin k₂) ℚ),
      ∀ w : List A, test w → (∑ i : Fin k₂, ∑ l : Fin k₂, u i * (w.map M).prod i l * v l) = count w := by
  rcases h1 with ⟨u, v, M, hM⟩
  let u' : Fin k₂ → ℚ := fun i => if hi : i.val < k₁ then u ⟨i.val, hi⟩ else 0
  let v' : Fin k₂ → ℚ := fun j => if hj : j.val < k₁ then v ⟨j.val, hj⟩ else 0
  let M' : A → Matrix (Fin k₂) (Fin k₂) ℚ := fun h i j =>
    if hi : i.val < k₁ then if hj : j.val < k₁ then M h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0
  have hprod : ∀ (w : List A) (i j : Fin k₂) (hi : i.val < k₁) (hj : j.val < k₁),
      (w.map M').prod i j = (w.map M).prod ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
    intro w
    induction w with
    | nil =>
      intro i j hi hj
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, Fin.ext_iff]
    | cons h t ih =>
      intro i j hi hj
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun x : Fin k₂ => x.val < k₁))
        (Finset.subset_univ _)]
      · refine Finset.sum_bij (fun x hx => (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin k₁))
          (fun _ _ => Finset.mem_univ _)
          (fun x1 _ x2 _ heq => Fin.ext (congrArg (fun z : Fin k₁ => z.val) heq))
          (fun y _ => ⟨Fin.castLE hle y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.isLt⟩, by ext; rfl⟩)
          (fun x hx => by
            have hxk : x.val < k₁ := (Finset.mem_filter.mp hx).2
            rw [ih x j hxk hj]
            dsimp only [M']
            simp only [hi, hxk, ↓reduceDIte])
      · intro x _ hnot
        have hnk : ¬ (x.val < k₁) := fun hx => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
        dsimp only [M']
        simp only [hi, hnk, ↓reduceDIte, zero_mul]
  refine ⟨u', v', M', ?_⟩
  intro w hw
  rw [← hM w hw]
  rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun i : Fin k₂ => i.val < k₁)) (Finset.subset_univ _)]
  · refine Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k₁))
      (fun _ _ => Finset.mem_univ _)
      (fun i1 _ i2 _ heq => Fin.ext (congrArg (fun z : Fin k₁ => z.val) heq))
      (fun i' _ => ⟨Fin.castLE hle i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, i'.isLt⟩, by ext; rfl⟩)
      (fun i hi => by
        have hik : i.val < k₁ := (Finset.mem_filter.mp hi).2
        rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun j : Fin k₂ => j.val < k₁)) (Finset.subset_univ _)]
        · refine Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin k₁))
            (fun _ _ => Finset.mem_univ _)
            (fun j1 _ j2 _ heq => Fin.ext (congrArg (fun z : Fin k₁ => z.val) heq))
            (fun j' _ => ⟨Fin.castLE hle j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩, by ext; rfl⟩)
            (fun j hj => by
              have hjk : j.val < k₁ := (Finset.mem_filter.mp hj).2
              dsimp only [u', v']
              simp only [hik, hjk, ↓reduceDIte, hprod w i j hik hjk])
        · intro j _ hnot
          have hnk : ¬ (j.val < k₁) := fun hj => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
          dsimp only [v']; simp only [hnk, ↓reduceDIte, mul_zero])
  · intro i _ hnot
    have hnk : ¬ (i.val < k₁) := fun hi => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    apply Finset.sum_eq_zero; intro j _
    dsimp only [u']; simp only [hnk, ↓reduceDIte, zero_mul]

def nextIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

open Classical in
noncomputable def countVal {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2))
    (w : List (Fin m → ZMod 2)) : ℚ :=
  let good := (Finset.univ : Finset (Fin w.length → (Fin j → ZMod 2))).filter (fun x =>
    (∀ i : Fin w.length, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i)) ∧
    (∀ b : Fin j, ∀ a : Fin m, (∑ i : Fin w.length, w.get i a * x i b) = Y b a))
  (good.card : ℚ)

open Classical in
lemma countVal_eq_fourier {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2))
    (w : List (Fin m → ZMod 2)) :
    let Iso := (Finset.univ : Finset (Fin w.length → (Fin j → ZMod 2))).filter (fun x =>
      ∀ i : Fin w.length, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i))
    countVal Y w = ((2 ^ (m * j) : ℕ) : ℚ)⁻¹ *
      ∑ Λ : Fin j → (Fin m → ZMod 2), matChar Λ Y *
        ∑ x ∈ Iso, ∏ i : Fin w.length, char (x i) (linOf Λ (w.get i)) := by
  intro Iso
  let A := Fin m → ZMod 2
  let C := Fin j → ZMod 2
  let S : (Fin w.length → C) → (Fin j → A) := fun x b a => ∑ i : Fin w.length, w.get i a * x i b
  have hprod_eq : ∀ (Λ : Fin j → A) (x : Fin w.length → C),
      (∏ i : Fin w.length, char (x i) (linOf Λ (w.get i))) = matChar Λ (S x) := by
    intro Λ x
    dsimp only [char, matChar]
    rw [← chi_sum, ← chi_sum]
    congr 1
    dsimp only [dot, linOf, LinearMap.coe_mk, AddHom.coe_mk, S]
    calc (∑ i : Fin w.length, ∑ b : Fin j, x i b * ∑ a : Fin m, Λ b a * w.get i a)
        = ∑ i : Fin w.length, ∑ b : Fin j, ∑ a : Fin m, Λ b a * (w.get i a * x i b) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ b : Fin j, ∑ i : Fin w.length, ∑ a : Fin m, Λ b a * (w.get i a * x i b) := Finset.sum_comm
      _ = ∑ b : Fin j, ∑ a : Fin m, ∑ i : Fin w.length, Λ b a * (w.get i a * x i b) := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ b : Fin j, ∑ a : Fin m, Λ b a * ∑ i : Fin w.length, w.get i a * x i b := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
  have hmc_mul : ∀ (Λ Y₁ Y₂ : Fin j → A), matChar Λ Y₁ * matChar Λ Y₂ = matChar Λ (Y₁ + Y₂) := by
    intro Λ Y₁ Y₂
    dsimp only [matChar]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => (char_add_right (Λ b) (Y₁ b) (Y₂ b)).symm
  have hsum_swap : (∑ Λ : Fin j → A, matChar Λ Y * ∑ x ∈ Iso, ∏ i : Fin w.length, char (x i) (linOf Λ (w.get i))) =
      ∑ x ∈ Iso, ∑ Λ : Fin j → A, matChar Λ (Y + S x) := by
    calc (∑ Λ : Fin j → A, matChar Λ Y * ∑ x ∈ Iso, ∏ i : Fin w.length, char (x i) (linOf Λ (w.get i)))
        = ∑ Λ : Fin j → A, ∑ x ∈ Iso, matChar Λ (Y + S x) := by
          refine Finset.sum_congr rfl fun Λ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by rw [hprod_eq, hmc_mul]
      _ = ∑ x ∈ Iso, ∑ Λ : Fin j → A, matChar Λ (Y + S x) := Finset.sum_comm
  rw [hsum_swap]
  have hsum_mc : (∑ x ∈ Iso, ∑ Λ : Fin j → A, matChar Λ (Y + S x)) =
      ∑ x ∈ Iso, if Y + S x = 0 then ((2 ^ (m * j) : ℕ) : ℚ) else 0 :=
    Finset.sum_congr rfl fun x _ => sum_matChar_left (Y + S x)
  rw [hsum_mc]
  have hiff : ∀ x : Fin w.length → C, Y + S x = 0 ↔ ∀ b : Fin j, ∀ a : Fin m, S x b a = Y b a := by
    intro x
    constructor
    · intro h b a
      have hba : Y b a + S x b a = 0 := congrFun (congrFun h b) a
      have h2 := congrArg (Y b a + ·) hba
      rw [← add_assoc, zmod2_add_self, zero_add, add_zero] at h2
      exact h2
    · intro h
      funext b a
      change Y b a + S x b a = 0
      rw [h b a, zmod2_add_self]
  let good := (Finset.univ : Finset (Fin w.length → C)).filter (fun x =>
    (∀ i : Fin w.length, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i)) ∧
    (∀ b : Fin j, ∀ a : Fin m, (∑ i : Fin w.length, w.get i a * x i b) = Y b a))
  have hfilt : Iso.filter (fun x => Y + S x = 0) = good := by
    ext x
    simp only [Iso, good, Finset.mem_filter, Finset.mem_univ, true_and, hiff, S]
  have hsum_ite : (∑ x ∈ Iso, if Y + S x = 0 then ((2 ^ (m * j) : ℕ) : ℚ) else 0) =
      ((2 ^ (m * j) : ℕ) : ℚ) * (good.card : ℚ) := by
    rw [← Finset.sum_filter, hfilt, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum_ite]
  have hne : ((2 ^ (m * j) : ℕ) : ℚ) ≠ 0 := by positivity
  dsimp only [countVal]
  change (good.card : ℚ) = ((2 ^ (m * j) : ℕ) : ℚ)⁻¹ * (((2 ^ (m * j) : ℕ) : ℚ) * (good.card : ℚ))
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

open Classical in
lemma solve_j1 (m : ℕ) (Y : Fin 1 → (Fin m → ZMod 2)) (hY : Y ≠ 0) :
    let A := Fin m → ZMod 2
    let fits := fun (k : ℕ) (test : List A → Prop) =>
      ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List A, test w →
          (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = countVal Y w
    ∀ k : ℕ, (fits k (fun w => 0 < w.length) ↔ 2 ^ m ≤ k) ∧
      (fits k (fun _ => True) ↔ 2 ^ m ≤ k) := by
  intro A fits k
  have hY0 : Y 0 ≠ 0 := by
    intro h0
    apply hY
    funext b
    rw [Fin.eq_zero b]
    exact h0
  have hcount_formula : ∀ w : List A,
      countVal Y w = ((2 ^ m : ℕ) : ℚ)⁻¹ *
        ∑ α : A, char α (Y 0) * (w.map (fun h => 1 + char α h)).prod := by
    intro w
    rw [countVal_eq_fourier]
    have hIso_univ : (Finset.univ : Finset (Fin w.length → (Fin 1 → ZMod 2))).filter (fun x =>
        ∀ i : Fin w.length, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i)) = Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro i
      rcases zmod2_eq_zero_or_one (x i 0) with h1 | h1
      · left; funext b; rw [Fin.eq_zero b]; exact h1
      · rcases zmod2_eq_zero_or_one (x (nextIdx i) 0) with h2 | h2
        · right; left; funext b; rw [Fin.eq_zero b]; exact h2
        · right; right; funext b; rw [Fin.eq_zero b, h1, h2]
    rw [hIso_univ]
    simp only [mul_one]
    congr 1
    let eqv : (Fin 1 → A) ≃ A :=
      { toFun := fun Λ => Λ 0
        invFun := fun α _ => α
        left_inv := fun Λ => funext fun b => by rw [Fin.eq_zero b]
        right_inv := fun _ => rfl }
    refine Fintype.sum_equiv eqv _ _ fun Λ => ?_
    have hmc : matChar Λ Y = char (Λ 0) (Y 0) := by
      simp [matChar]
    rw [hmc]
    dsimp only [eqv, Equiv.coe_fn_mk]
    congr 1
    rw [← Fintype.prod_sum (fun i c => char c (linOf Λ (w.get i)))]
    have hfac : ∀ i : Fin w.length,
        (∑ c : Fin 1 → ZMod 2, char c (linOf Λ (w.get i))) = 1 + char (Λ 0) (w.get i) := by
      intro i
      let e1 : (Fin 1 → ZMod 2) ≃ ZMod 2 :=
        { toFun := fun c => c 0
          invFun := fun t _ => t
          left_inv := fun c => funext fun b => by rw [Fin.eq_zero b]
          right_inv := fun _ => rfl }
      rw [Fintype.sum_equiv e1 _ (fun t => chi (t * dot (Λ 0) (w.get i))) (fun c => by
        dsimp only [char, dot, linOf, LinearMap.coe_mk, AddHom.coe_mk, e1, Equiv.coe_fn_mk]
        rw [Fin.sum_univ_one]
        rfl)]
      have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      rw [huniv, Finset.sum_pair h01]
      simp [chi_zero, char]
    simp_rw [hfac]
    have hlist : ∀ (l : List A) (f : A → ℚ), (∏ i : Fin l.length, f (l.get i)) = (l.map f).prod := by
      intro l f
      induction l with
      | nil => simp
      | cons h t ih =>
        rw [List.map_cons, List.prod_cons]
        change (∏ i : Fin (t.length + 1), f ((h :: t).get i)) = f h * (t.map f).prod
        rw [Fin.prod_univ_succ]
        simp
    exact hlist w (fun h => 1 + char (Λ 0) h)
  have hup_base : fits (2 ^ m) (fun _ => True) := by
    have hcard : Fintype.card A = 2 ^ m := by simp [A]
    let eA : Fin (2 ^ m) ≃ A := (Fintype.equivFinOfCardEq hcard).symm
    let uA : A → ℚ := fun α => ((2 ^ m : ℕ) : ℚ)⁻¹ * char α (Y 0)
    let vA : A → ℚ := fun _ => 1
    let MA : A → Matrix A A ℚ := fun h α β => if α = β then 1 + char α h else 0
    have hMA_prod : ∀ (w : List A) (α β : A),
        (w.map MA).prod α β = if α = β then (w.map (fun h => 1 + char α h)).prod else 0 := by
      intro w
      induction w with
      | nil =>
        intro α β
        simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
      | cons h t ih =>
        intro α β
        simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
        rw [Finset.sum_eq_single α]
        · rw [ih α β]
          dsimp only [MA]
          by_cases hαβ : α = β
          · subst hαβ; simp
          · simp [hαβ]
        · intro γ _ hne; simp [MA, Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
    let u : Fin (2 ^ m) → ℚ := fun i => uA (eA i)
    let v : Fin (2 ^ m) → ℚ := fun l => vA (eA l)
    let M : A → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℚ := fun h i l => MA h (eA i) (eA l)
    have hM_prod : ∀ (w : List A) (i l : Fin (2 ^ m)),
        (w.map M).prod i l = (w.map MA).prod (eA i) (eA l) := by
      intro w
      induction w with
      | nil => intro i l; simp [Matrix.one_apply, eA.injective.eq_iff]
      | cons h t ih =>
        intro i l
        simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
        calc (∑ x : Fin (2 ^ m), M h i x * (t.map M).prod x l)
            = ∑ x : Fin (2 ^ m), MA h (eA i) (eA x) * (t.map MA).prod (eA x) (eA l) :=
              Finset.sum_congr rfl fun x _ => by rw [ih x l]
          _ = ∑ γ : A, MA h (eA i) γ * (t.map MA).prod γ (eA l) :=
              Equiv.sum_comp eA (fun γ => MA h (eA i) γ * (t.map MA).prod γ (eA l))
    refine ⟨u, v, M, fun w _ => ?_⟩
    rw [hcount_formula w]
    calc (∑ i : Fin (2 ^ m), ∑ l : Fin (2 ^ m), u i * (w.map M).prod i l * v l)
        = ∑ i : Fin (2 ^ m), ∑ l : Fin (2 ^ m), uA (eA i) * (w.map MA).prod (eA i) (eA l) * vA (eA l) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [hM_prod]
      _ = ∑ α : A, ∑ β : A, uA α * (w.map MA).prod α β * vA β := by
          calc _ = ∑ i : Fin (2 ^ m), ∑ β : A, uA (eA i) * (w.map MA).prod (eA i) β * vA β :=
                  Finset.sum_congr rfl fun i _ =>
                    Equiv.sum_comp eA (fun β => uA (eA i) * (w.map MA).prod (eA i) β * vA β)
            _ = _ := Equiv.sum_comp eA (fun α => ∑ β : A, uA α * (w.map MA).prod α β * vA β)
      _ = ∑ α : A, uA α * (w.map (fun h => 1 + char α h)).prod := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_eq_single α]
          · simp [hMA_prod, vA]
          · intro β _ hne; simp [hMA_prod, Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
      _ = ((2 ^ m : ℕ) : ℚ)⁻¹ * ∑ α : A, char α (Y 0) * (w.map (fun h => 1 + char α h)).prod := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => by dsimp only [uA]; ring
  have hup : 2 ^ m ≤ k → fits k (fun _ => True) := fun hle =>
    fits_pad (countVal Y) (fun _ => True) hle hup_base
  have hlo : fits k (fun w => 0 < w.length) → 2 ^ m ≤ k := by
    rintro ⟨u, v, M, hfit⟩
    let Φ : List A → (A → ℚ) := fun w α => (w.map (fun h => 1 + char α h)).prod
    have hΦ_append : ∀ w₁ w₂ : List A, Φ (w₁ ++ w₂) = Φ w₁ * Φ w₂ := fun w₁ w₂ => by
      funext α; simp [Φ]
    let Λ : (A → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun f => ((2 ^ m : ℕ) : ℚ)⁻¹ * ∑ α : A, char α (Y 0) * f α
        map_add' := fun f g => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c f => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => by ring }
    have hΛ_Φ : ∀ w : List A, Λ (Φ w) = countVal Y w := fun w => by
      rw [hcount_formula w]; rfl
    have hnondeg : ∀ f : A → ℚ, (∀ g : A → ℚ, Λ (f * g) = 0) → f = 0 := by
      intro f hall
      funext α
      have h := hall (fun β => if β = α then 1 else 0)
      dsimp only [Λ, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [Finset.sum_eq_single α] at h
      · simp only [Pi.mul_apply, ite_true, mul_one] at h
        have hc1 : ((2 ^ m : ℕ) : ℚ)⁻¹ ≠ 0 := by positivity
        have hc2 : char α (Y 0) ≠ 0 := by
          dsimp only [char, chi]; split_ifs <;> norm_num
        have h1 := (mul_eq_zero.mp h).resolve_left hc1
        exact (mul_eq_zero.mp h1).resolve_left hc2
      · intro β _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    let AlgPos : Submodule ℚ (A → ℚ) :=
      Submodule.span ℚ {f : A → ℚ | ∃ w : List A, 0 < w.length ∧ Φ w = f}
    have hmem_Φ : ∀ w : List A, 0 < w.length → Φ w ∈ AlgPos := fun w hw =>
      Submodule.subset_span ⟨w, hw, rfl⟩
    have hprod_all_zero : ∀ (l : List A) (β : A),
        (∀ h ∈ l, dot β h = 0) → Φ l β = (2 : ℚ) ^ l.length := by
      intro l β
      induction l with
      | nil => intro _; simp [Φ]
      | cons h t ih =>
        intro hall
        have hh : dot β h = 0 := hall h (List.mem_cons_self ..)
        have ht : ∀ x ∈ t, dot β x = 0 := fun x hx => hall x (List.mem_cons_of_mem h hx)
        simp only [Φ, List.map_cons, List.prod_cons, List.length_cons]
        rw [show char β h = 1 by simp [char, hh, chi_zero],
          show (t.map (fun h => 1 + char β h)).prod = (2 : ℚ) ^ t.length from ih ht, pow_succ]
        ring
    have hprod_exists_nz : ∀ (l : List A) (β : A),
        (∃ h ∈ l, dot β h ≠ 0) → Φ l β = 0 := by
      intro l β hex
      rcases hex with ⟨h, hm, hne⟩
      refine List.prod_eq_zero (List.mem_map.mpr ⟨h, hm, ?_⟩)
      simp [char, chi, hne]
    let eUnit : A → (A → ℚ) := fun α β => if β = α then 1 else 0
    have he0_mem : eUnit 0 ∈ AlgPos := by
      let w₀ : List A := (Finset.univ : Finset A).toList
      have hw₀_pos : 0 < w₀.length := by
        rw [Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
        positivity
      have hΦw₀ : Φ w₀ = ((2 : ℚ) ^ w₀.length) • eUnit 0 := by
        funext β
        simp only [Pi.smul_apply, smul_eq_mul, eUnit]
        by_cases hβ : β = 0
        · subst hβ
          simp only [ite_true, mul_one]
          exact hprod_all_zero w₀ 0 fun h _ => dot_zero_left h
        · simp only [hβ, ite_false, mul_zero]
          refine hprod_exists_nz w₀ β ?_
          have hex : ∃ i : Fin m, β i = 1 := by
            by_contra hall
            push Not at hall
            apply hβ; funext i
            rcases zmod2_eq_zero_or_one (β i) with h0 | h1
            · exact h0
            · exact absurd h1 (hall i)
          rcases hex with ⟨i, hi⟩
          refine ⟨Pi.single i (1 : ZMod 2), Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
          have hdot : dot β (Pi.single i (1 : ZMod 2)) = 1 := by
            dsimp only [dot]
            rw [Finset.sum_eq_single i]
            · simp [hi]
            · intro j _ hne; simp [Pi.single_eq_of_ne hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          rw [hdot]; decide
      have hmem := hmem_Φ w₀ hw₀_pos
      rw [hΦw₀] at hmem
      have hsc := AlgPos.smul_mem (((2 : ℚ) ^ w₀.length)⁻¹) hmem
      have hne : (2 : ℚ) ^ w₀.length ≠ 0 := by positivity
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hsc
    have he_mem : ∀ α : A, eUnit α ∈ AlgPos := by
      intro α
      by_cases hα : α = 0
      · subst hα; exact he0_mem
      · let sα : Finset A := Finset.univ.filter (fun h : A => dot α h = 0)
        let wα : List A := sα.toList
        have hwα_pos : 0 < wα.length := by
          rw [Finset.length_toList]
          refine Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, dot_zero_right α⟩⟩
        have hΦwα : Φ wα = ((2 : ℚ) ^ wα.length) • (eUnit 0 + eUnit α) := by
          funext β
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eUnit]
          by_cases hβ0 : β = 0
          · subst hβ0
            simp only [ite_true, Ne.symm hα, ite_false, add_zero, mul_one]
            exact hprod_all_zero wα 0 fun h _ => dot_zero_left h
          · by_cases hβα : β = α
            · subst hβα
              simp only [hβ0, ite_false, ite_true, zero_add, mul_one]
              exact hprod_all_zero wα β fun h hm => (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
            · simp only [hβ0, hβα, ite_false, add_zero, mul_zero]
              refine hprod_exists_nz wα β ?_
              by_contra hall
              push Not at hall
              have hle_perp : perp (Submodule.span (ZMod 2) {α}) ≤ perp (Submodule.span (ZMod 2) {β}) := by
                intro h hh
                rw [mem_perp_iff] at hh ⊢
                have hdotα : dot α h = 0 :=
                  hh α (Submodule.subset_span (Set.mem_singleton α))
                have hhm : h ∈ wα := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdotα⟩)
                have hdotβ : dot β h = 0 := hall h hhm
                intro u hu
                rw [Submodule.mem_span_singleton] at hu
                rcases hu with ⟨c, rfl⟩
                rw [dot_smul_left, hdotβ, mul_zero]
              have hle_span : Submodule.span (ZMod 2) {β} ≤ Submodule.span (ZMod 2) {α} :=
                perp_le_iff.mp hle_perp
              have hmem_span : β ∈ Submodule.span (ZMod 2) {α} :=
                hle_span (Submodule.subset_span (Set.mem_singleton β))
              rw [Submodule.mem_span_singleton] at hmem_span
              rcases hmem_span with ⟨c, hc⟩
              rcases zmod2_eq_zero_or_one c with rfl | rfl
              · simp at hc; exact hβ0 hc.symm
              · simp at hc; exact hβα hc.symm
        have hmem := hmem_Φ wα hwα_pos
        rw [hΦwα] at hmem
        have hsc := AlgPos.smul_mem (((2 : ℚ) ^ wα.length)⁻¹) hmem
        have hne : (2 : ℚ) ^ wα.length ≠ 0 := by positivity
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at hsc
        have hsub := AlgPos.sub_mem hsc he0_mem
        simpa using hsub
    have hAlgPos_top : ∀ f : A → ℚ, f ∈ AlgPos := by
      intro f
      have heq : f = ∑ α : A, f α • eUnit α := by
        funext β
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eUnit]
        rw [Finset.sum_eq_single β]
        · simp
        · intro α _ hne; simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      rw [heq]
      exact AlgPos.sum_mem fun α _ => AlgPos.smul_mem _ (he_mem α)
    have hrep : ∀ α : A, ∃ (s : Finset (List A)) (c : List A → ℚ),
        (∀ w ∈ s, 0 < w.length) ∧ (∑ w ∈ s, c w • Φ w) = eUnit α := by
      intro α
      have hmem : eUnit α ∈ AlgPos := he_mem α
      rw [Submodule.mem_span_set] at hmem
      rcases hmem with ⟨c, hc_supp, hc_sum⟩
      have hcho : ∀ f : A → ℚ, f ∈ c.support → ∃ w : List A, 0 < w.length ∧ Φ w = f := fun f hf =>
        hc_supp hf
      choose wOf hw_pos hw_eq using hcho
      let s : Finset (List A) := c.support.attach.image (fun x => wOf x.1 x.2)
      let cf : List A → ℚ := fun w => ∑ x ∈ c.support.attach.filter (fun x => wOf x.1 x.2 = w), c x.1
      refine ⟨s, cf, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
        exact hw_pos x.1 x.2
      · rw [← hc_sum]
        calc (∑ w ∈ s, cf w • Φ w)
            = ∑ w ∈ s, ∑ x ∈ c.support.attach.filter (fun x => wOf x.1 x.2 = w), c x.1 • Φ (wOf x.1 x.2) := by
              refine Finset.sum_congr rfl fun w _ => ?_
              dsimp only [cf]; rw [Finset.sum_smul]
              refine Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
          _ = ∑ x ∈ c.support.attach, c x.1 • Φ (wOf x.1 x.2) := by
              rw [← Finset.sum_fiberwise_of_maps_to (s := c.support.attach) (t := s)
                (g := fun x => wOf x.1 x.2) (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩)]
          _ = ∑ x ∈ c.support.attach, c x.1 • x.1 :=
              Finset.sum_congr rfl fun x _ => by rw [hw_eq x.1 x.2]
          _ = c.sum (fun f r => r • f) := by
              rw [Finsupp.sum, Finset.sum_attach c.support (fun f => c f • f)]
    choose sRep cRep hs_pos hs_eq using hrep
    let rowVec : A → (Fin k → ℚ) := fun α j =>
      ∑ w ∈ sRep α, cRep α w * ∑ i : Fin k, u i * (w.map M).prod i j
    have hlin : LinearIndependent ℚ rowVec := by
      rw [Fintype.linearIndependent_iff]
      intro β hβ
      let f : A → ℚ := ∑ α : A, β α • eUnit α
      have hf_zero_pos : ∀ w' : List A, 0 < w'.length → Λ (f * Φ w') = 0 := by
        intro w' hw'
        have h1 : f * Φ w' = ∑ α : A, β α • ∑ w ∈ sRep α, cRep α w • Φ (w ++ w') := by
          dsimp only [f]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← hs_eq α, smul_mul_assoc, Finset.sum_mul]
          congr 1; refine Finset.sum_congr rfl fun w _ => by rw [smul_mul_assoc, hΦ_append]
        rw [h1, map_sum]
        have h2 : (∑ α : A, Λ (β α • ∑ w ∈ sRep α, cRep α w • Φ (w ++ w'))) =
            ∑ j : Fin k, (∑ α : A, β α * rowVec α j) * ∑ l : Fin k, (w'.map M).prod j l * v l := by
          have hterm : ∀ α : A,
              Λ (β α • ∑ w ∈ sRep α, cRep α w • Φ (w ++ w')) =
              ∑ j : Fin k, (β α * rowVec α j) * ∑ l : Fin k, (w'.map M).prod j l * v l := by
            intro α
            rw [map_smul, map_sum, smul_eq_mul]
            have hinner : (∑ w ∈ sRep α, Λ (cRep α w • Φ (w ++ w'))) =
                ∑ j : Fin k, rowVec α j * ∑ l : Fin k, (w'.map M).prod j l * v l := by
              calc (∑ w ∈ sRep α, Λ (cRep α w • Φ (w ++ w')))
                  = ∑ w ∈ sRep α, cRep α w * ∑ i : Fin k, ∑ l : Fin k,
                      u i * ((w ++ w').map M).prod i l * v l := by
                    refine Finset.sum_congr rfl fun w _ => ?_
                    rw [map_smul, smul_eq_mul, hΛ_Φ, hfit (w ++ w') (by simp; omega)]
                _ = ∑ w ∈ sRep α, cRep α w * ∑ j : Fin k,
                      (∑ i : Fin k, u i * (w.map M).prod i j) * ∑ l : Fin k, (w'.map M).prod j l * v l := by
                    refine Finset.sum_congr rfl fun w _ => ?_
                    congr 1
                    simp_rw [List.map_append, List.prod_append, Matrix.mul_apply]
                    calc (∑ i : Fin k, ∑ l : Fin k, u i * (∑ j : Fin k, (w.map M).prod i j * (w'.map M).prod j l) * v l)
                        = ∑ i : Fin k, ∑ l : Fin k, ∑ j : Fin k,
                            (u i * (w.map M).prod i j) * ((w'.map M).prod j l * v l) := by
                          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
                          rw [Finset.mul_sum, Finset.sum_mul]
                          refine Finset.sum_congr rfl fun j _ => by ring
                      _ = ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k,
                            (u i * (w.map M).prod i j) * ((w'.map M).prod j l * v l) :=
                          Finset.sum_congr rfl fun i _ => Finset.sum_comm
                      _ = ∑ j : Fin k, ∑ i : Fin k, ∑ l : Fin k,
                            (u i * (w.map M).prod i j) * ((w'.map M).prod j l * v l) := Finset.sum_comm
                      _ = ∑ j : Fin k, (∑ i : Fin k, u i * (w.map M).prod i j) *
                            ∑ l : Fin k, (w'.map M).prod j l * v l := by
                          refine Finset.sum_congr rfl fun j _ => ?_
                          rw [Finset.sum_mul]
                          refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm
                _ = ∑ j : Fin k, rowVec α j * ∑ l : Fin k, (w'.map M).prod j l * v l := by
                    calc _ = ∑ w ∈ sRep α, ∑ j : Fin k,
                            (cRep α w * ∑ i : Fin k, u i * (w.map M).prod i j) *
                              ∑ l : Fin k, (w'.map M).prod j l * v l := by
                          refine Finset.sum_congr rfl fun w _ => ?_
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl fun j _ => by ring
                      _ = ∑ j : Fin k, ∑ w ∈ sRep α,
                            (cRep α w * ∑ i : Fin k, u i * (w.map M).prod i j) *
                              ∑ l : Fin k, (w'.map M).prod j l * v l := Finset.sum_comm
                      _ = _ := Finset.sum_congr rfl fun j _ => by dsimp only [rowVec]; rw [Finset.sum_mul]
            rw [hinner, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
          simp_rw [hterm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => (Finset.sum_mul ..).symm
        rw [h2]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hj : (∑ α : A, β α * rowVec α j) = 0 := by
          have := congrFun hβ j
          simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
        rw [hj, zero_mul]
      have hf_zero_all : ∀ g : A → ℚ, Λ (f * g) = 0 := by
        intro g
        refine Submodule.span_induction ?_ ?_ ?_ ?_ (hAlgPos_top g)
        · rintro _ ⟨w', hw', rfl⟩; exact hf_zero_pos w' hw'
        · rw [mul_zero, map_zero]
        · intro x y _ _ hx hy; rw [mul_add, map_add, hx, hy, add_zero]
        · intro c x _ hx; rw [mul_smul_comm, map_smul, hx, smul_zero]
      have hf0 : f = 0 := hnondeg f hf_zero_all
      intro α
      have h := congrFun hf0 α
      simp only [f, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
      rw [Finset.sum_eq_single α] at h
      · simpa [eUnit] using h
      · intro γ _ hne; simp [eUnit, Ne.symm hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    have hcard_le : Fintype.card A ≤ Module.finrank ℚ (Fin k → ℚ) := hlin.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hcard_le
    simpa [A] using hcard_le
  refine ⟨⟨hlo, fun hle => by rcases hup hle with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩⟩,
    ⟨fun h => hlo (by rcases h with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩), hup⟩⟩

def Tmat {r : ℕ} (z : ℚ) (h : Fin r → ZMod 2) :
    Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ :=
  let f := fun a : Fin r → ZMod 2 => if a = 0 then z - 1 else -1
  fun before after =>
    before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
      (fun a => after.elim (f a) (fun b => if b = a + h then 1 else 0))

noncomputable def codimD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) : ℕ :=
  m - Module.finrank (ZMod 2) D

lemma finrank_quot_eq_codimD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Module.finrank (ZMod 2) ((Fin m → ZMod 2) ⧸ D) = codimD D := by
  have h1 := Submodule.finrank_quotient_add_finrank D
  rw [Module.finrank_fin_fun] at h1
  dsimp only [codimD]; omega

noncomputable def quotEquiv {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    ((Fin m → ZMod 2) ⧸ D) ≃ₗ[ZMod 2] (Fin (codimD D) → ZMod 2) :=
  ((Module.finBasis (ZMod 2) ((Fin m → ZMod 2) ⧸ D)).reindex
    (finCongr (finrank_quot_eq_codimD D))).equivFun

noncomputable def projD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin (codimD D) → ZMod 2) :=
  (quotEquiv D).toLinearMap.comp D.mkQ

lemma projD_surjective {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Function.Surjective (projD D) :=
  (quotEquiv D).surjective.comp (Submodule.mkQ_surjective D)

lemma ker_projD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    LinearMap.ker (projD D) = D := by
  ext h
  simp only [LinearMap.mem_ker, projD, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

noncomputable def dualProjD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (Fin (codimD D) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun φ a := dot φ (projD D (Pi.single a (1 : ZMod 2)))
  map_add' φ₁ φ₂ := by funext a; exact dot_add_left φ₁ φ₂ _
  map_smul' c φ := by funext a; exact dot_smul_left c φ _

lemma dot_dualProjD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2))
    (φ : Fin (codimD D) → ZMod 2) (h : Fin m → ZMod 2) :
    dot (dualProjD D φ) h = dot φ (projD D h) := by
  have hh : h = ∑ a : Fin m, h a • Pi.single a (1 : ZMod 2) := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  conv_rhs => rw [hh, map_sum]
  dsimp only [dot, dualProjD, LinearMap.coe_mk, AddHom.coe_mk]
  calc (∑ a : Fin m, (∑ i : Fin (codimD D), φ i * projD D (Pi.single a 1) i) * h a)
      = ∑ a : Fin m, ∑ i : Fin (codimD D), φ i * (h a * projD D (Pi.single a 1) i) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin (codimD D), ∑ a : Fin m, φ i * (h a * projD D (Pi.single a 1) i) := Finset.sum_comm
    _ = ∑ i : Fin (codimD D), φ i * (∑ a : Fin m, (projD D (h a • Pi.single a 1)) i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by simp [map_smul]
    _ = ∑ i : Fin (codimD D), φ i * (∑ a : Fin m, projD D (h a • Pi.single a 1)) i := by
        refine Finset.sum_congr rfl fun i _ => by rw [Finset.sum_apply]

lemma char_dualProjD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2))
    (φ : Fin (codimD D) → ZMod 2) (h : Fin m → ZMod 2) :
    char (dualProjD D φ) h = char φ (projD D h) := by
  dsimp only [char]; rw [dot_dualProjD]

lemma dualProjD_injective {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Function.Injective (dualProjD D) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  funext i
  obtain ⟨h, hh⟩ := projD_surjective D (Pi.single i (1 : ZMod 2))
  have hdot := dot_dualProjD D φ h
  rw [hφ, dot_zero_left, hh] at hdot
  have h1 : dot φ (Pi.single i (1 : ZMod 2)) = φ i := by
    dsimp only [dot]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hne; simp [Pi.single_eq_of_ne hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [h1] at hdot
  exact hdot.symm

lemma range_dualProjD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    LinearMap.range (dualProjD D) = perp D := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨φ, rfl⟩
    rw [mem_perp_iff]
    intro h hh
    rw [dot_comm, dot_dualProjD]
    have hp : projD D h = 0 := by
      have : h ∈ LinearMap.ker (projD D) := by rwa [ker_projD]
      exact this
    rw [hp, dot_zero_right]
  · rw [LinearMap.finrank_range_of_inj (dualProjD_injective D), Module.finrank_fin_fun]
    have hfr := finrank_perp D
    dsimp only [codimD]; omega

lemma mem_perp_iff_exists_dualProjD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2))
    (α : Fin m → ZMod 2) :
    α ∈ perp D ↔ ∃ φ : Fin (codimD D) → ZMod 2, dualProjD D φ = α := by
  rw [← range_dualProjD D, LinearMap.mem_range]

noncomputable def cycleD {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) (z : ℚ)
    (w : List (Fin m → ZMod 2)) : ℚ :=
  let r := codimD D
  let π := projD D
  Matrix.trace (w.map (fun h => Tmat z (π h))).prod +
    (if π w.sum = 0 then z - 1 else -1) -
    (if π w.sum = 0 then ((2 ^ r : ℕ) : ℚ) else 0)

lemma cycleD_nil {m : ℕ} (D : Submodule (ZMod 2) (Fin m → ZMod 2)) (z : ℚ) :
    cycleD D z [] = z := by
  dsimp only [cycleD]
  simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero, ite_true]
  rw [Matrix.trace_one, Fintype.card_option, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  push_cast
  ring

private lemma list_prod_take_succ_rat {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Matrix α α ℚ)) (t : ℕ) (ht : t < L.length) :
    (L.take (t + 1)).prod = (L.take t).prod * L[t] := by
  rw [List.take_succ_eq_append_getElem ht, List.prod_append, List.prod_singleton]

private lemma list_prod_drop_take_succ_rat {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Matrix α α ℚ)) (k t : ℕ) (hkt : k ≤ t) (ht : t < L.length) :
    ((L.drop k).take (t + 1 - k)).prod = ((L.drop k).take (t - k)).prod * L[t] := by
  have h1 : t + 1 - k = (t - k) + 1 := by omega
  have hlt : t - k < (L.drop k).length := by simp; omega
  rw [h1, List.take_succ_eq_append_getElem hlt, List.prod_append, List.prod_singleton]
  simp [Nat.add_sub_of_le hkt]

private lemma list_prod_telescoping_rat {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (A : Fin n → Matrix α α ℚ) (E : Matrix α α ℚ) :
    let Q : Matrix α α ℚ := 1 - E
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
    rw [list_prod_take_succ_rat _ t hL1, list_prod_take_succ_rat _ t hL2]
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
      rw [list_prod_drop_take_succ_rat (List.ofFn A) k.val t (by omega) hL1, List.getElem_ofFn]
    · simp only [Fin.val_last]
      have h1 : t + 1 - t = 1 := by omega
      have hdrop : (((List.ofFn A).drop t).take 1).prod = A ⟨t, ht'⟩ := by
        have hlt : 0 < ((List.ofFn A).drop t).length := by simp; omega
        rw [List.take_succ_eq_append_getElem hlt]
        simp
      rw [h1, hdrop]

private lemma trace_rank1_mul_rat {α : Type*} [Fintype α] [DecidableEq α]
    (z₀ : α) (X : Matrix α α ℚ) :
    Matrix.trace (Matrix.of (fun r c : α => if r = z₀ ∧ c = z₀ then (1 : ℚ) else 0) * X) =
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

private lemma trace_telescoping_rat {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (A : Fin n → Matrix α α ℚ) (z₀ : α) :
    let E : Matrix α α ℚ := Matrix.of (fun r c => if r = z₀ ∧ c = z₀ then 1 else 0)
    let Q : Matrix α α ℚ := 1 - E
    Matrix.trace (List.ofFn A).prod - Matrix.trace (List.ofFn (fun i => Q * A i)).prod =
      ∑ k : Fin n,
        (((List.ofFn A).drop k.val).prod * ((List.ofFn (fun i => Q * A i)).take k.val).prod) z₀ z₀ := by
  intro E Q
  have h := list_prod_telescoping_rat n A E n (le_refl n)
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
  exact trace_rank1_mul_rat z₀ _

private lemma list_prod_intertwine_rat {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (P : Matrix α β ℚ) (L₁ : List (Matrix α α ℚ)) (L₂ : List (Matrix β β ℚ))
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

private lemma list_prod_succ_apply_eq_sum_rat {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (k : ℕ) (M : Fin (k + 1) → Matrix α α ℚ) (s₀ s₁ : α),
    (List.ofFn M).prod s₀ s₁ =
      ∑ traj : Fin k → α,
        M 0 s₀ (if h : 0 < k then traj ⟨0, h⟩ else s₁) *
        ∏ i : Fin k, M i.succ (traj i)
          (if h : i.val + 1 < k then traj ⟨i.val + 1, h⟩ else s₁) := by
  intro k
  induction k with
  | zero => intro M s₀ s₁; simp
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
      refine Finset.sum_congr rfl fun b _ => Finset.mul_sum ..
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

private lemma trace_list_prod_eq_sum_rat {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 0 < n) (M : Fin n → Matrix α α ℚ) :
    Matrix.trace (List.ofFn M).prod =
      ∑ v : Fin n → α, ∏ i : Fin n,
        M i (v i) (v (nextIdx i)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [list_prod_succ_apply_eq_sum_rat k M]
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
        congr 2; apply Fin.ext; dsimp [nextIdx]; exact Nat.mod_eq_of_lt (by omega)
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [lt_self_iff_false, ↓reduceDIte]
        congr 2
    · refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i.val + 1 < k
      · simp only [h, ↓reduceDIte]
        congr 2; apply Fin.ext; dsimp [nextIdx]; exact Nat.mod_eq_of_lt (by omega)
      · simp only [h, ↓reduceDIte]
        have heq : i.val + 1 = k := by omega
        congr 2; apply Fin.ext; dsimp [nextIdx]
        have h1 : i.val + 1 + 1 = k + 1 := by omega
        rw [h1, Nat.mod_self]

open Classical in
lemma walk_eq_sum_iso_rat {m j : ℕ} (Λ : Fin j → (Fin m → ZMod 2))
    (w : List (Fin m → ZMod 2)) (hw : 0 < w.length) :
    let Iso := (Finset.univ : Finset (Fin w.length → (Fin j → ZMod 2))).filter (fun x =>
      ∀ i : Fin w.length, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i))
    cycleD (LinearMap.ker (linOf Λ)) ((2 ^ j : ℕ) : ℚ) w =
      ∑ x ∈ Iso, ∏ i : Fin w.length, char (x i) (linOf Λ (w.get i)) := by
  intro Iso
  let D := LinearMap.ker (linOf Λ)
  let r := codimD D
  let B := Fin r → ZMod 2
  let π := projD D
  let n := w.length
  have hn : 0 < n := hw
  let z : ℚ := ((2 ^ j : ℕ) : ℚ)
  let ψbar : B →ₗ[ZMod 2] (Fin j → ZMod 2) :=
    (D.liftQ (linOf Λ) le_rfl).comp (quotEquiv D).symm.toLinearMap
  have hψbar_inj : Function.Injective ψbar := by
    have h1 : Function.Injective (D.liftQ (linOf Λ) le_rfl) := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ]; simp [D]
    exact h1.comp (quotEquiv D).symm.injective
  have hψbar_zero : ∀ b : B, ψbar b = 0 ↔ b = 0 := fun b => by
    rw [← map_zero ψbar, hψbar_inj.eq_iff]
  have hψbar_sym : ∀ h : Fin m → ZMod 2, ψbar (π h) = linOf Λ h := fun h => by
    dsimp only [ψbar, π, projD]
    simp
  let closeRun : B → ℚ := fun b => if b = 0 then z - 1 else -1
  have hclose_eq : ∀ b : B, closeRun b =
      ∑ c ∈ (Finset.univ : Finset (Fin j → ZMod 2)).erase 0, char c (ψbar b) := by
    intro b
    have h1 : (∑ c : Fin j → ZMod 2, char c (ψbar b)) =
        char 0 (ψbar b) + ∑ c ∈ (Finset.univ : Finset (Fin j → ZMod 2)).erase 0, char c (ψbar b) :=
      (Finset.add_sum_erase Finset.univ (fun c => char c (ψbar b)) (Finset.mem_univ 0)).symm
    simp only [sum_char_left, char_zero_left, hψbar_zero] at h1
    dsimp only [closeRun, z]
    by_cases hb : b = 0 <;> simp only [hb, ite_true, ite_false] at h1 ⊢ <;> linarith
  let T : Fin n → Matrix (Option B) (Option B) ℚ := fun i => Tmat z (π (w.get i))
  let M : Fin n → Matrix (Fin j → ZMod 2) (Fin j → ZMod 2) ℚ := fun i c₁ c₂ =>
    if c₁ = 0 ∨ c₂ = 0 ∨ c₁ = c₂ then char c₂ (linOf Λ (w.get i)) else 0
  let P : Matrix (Option B) (Fin j → ZMod 2) ℚ := fun s c =>
    match s with
    | none => if c = 0 then 1 else 0
    | some a => if c = 0 then 0 else char c (ψbar a)
  have hT_ofFn : List.ofFn T = w.map (fun h => Tmat z (π h)) := by
    apply List.ext_getElem
    · simp [n]
    · intro i h1 h2; simp [T]
  have hsum_get : (∑ i : Fin n, w.get i) = w.sum := by
    have haux : ∀ l : List (Fin m → ZMod 2), (∑ i : Fin l.length, l.get i) = l.sum := by
      intro l
      induction l with
      | nil => simp
      | cons h t ih =>
        rw [List.sum_cons]
        change (∑ i : Fin (t.length + 1), (h :: t).get i) = h + t.sum
        rw [Fin.sum_univ_succ]
        simp
    exact haux w
  have htrM : Matrix.trace (List.ofFn M).prod =
      ∑ x ∈ Iso, ∏ i : Fin n, char (x i) (linOf Λ (w.get i)) := by
    rw [trace_list_prod_eq_sum_rat hn M]
    let nextEquiv : Fin n ≃ Fin n :=
      { toFun := nextIdx
        invFun := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩
        left_inv := fun i => by
          ext; dsimp [nextIdx]
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
          ext; dsimp [nextIdx]
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
    have hshift : (∑ v : Fin n → Fin j → ZMod 2, ∏ i : Fin n, M i (v i) (v (nextIdx i))) =
        ∑ u : Fin n → Fin j → ZMod 2, ∏ i : Fin n, M i (u (nextEquiv.symm i)) (u i) := by
      let eShift : (Fin n → Fin j → ZMod 2) ≃ (Fin n → Fin j → ZMod 2) :=
        { toFun := fun v i => v (nextIdx i)
          invFun := fun u i => u (nextEquiv.symm i)
          left_inv := fun v => funext fun i => congrArg v (nextEquiv.apply_symm_apply i)
          right_inv := fun u => funext fun i => congrArg u (nextEquiv.symm_apply_apply i) }
      refine Fintype.sum_equiv eShift _ _ fun v => Finset.prod_congr rfl fun i _ => ?_
      exact congrArg (fun x => M i (v x) (v (nextIdx i))) (nextEquiv.apply_symm_apply i).symm
    rw [hshift]
    rw [← Finset.sum_filter_of_ne (p := fun u => (∏ i : Fin n, M i (u (nextEquiv.symm i)) (u i)) ≠ 0)]
    · refine Finset.sum_congr ?_ ?_
      · ext u
        simp only [Iso, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hprod i
          have hnz : ∀ k : Fin n, u (nextEquiv.symm k) = 0 ∨ u k = 0 ∨ u (nextEquiv.symm k) = u k := by
            intro k; by_contra hbad; apply hprod
            exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [M, hbad])
          have hk := hnz (nextIdx i)
          have hinv : nextEquiv.symm (nextIdx i) = i := nextEquiv.symm_apply_apply i
          rw [hinv] at hk
          exact hk
        · intro hiso
          refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
          have hcond : u (nextEquiv.symm k) = 0 ∨ u k = 0 ∨ u (nextEquiv.symm k) = u k := by
            have h1 := hiso (nextEquiv.symm k)
            have h2 : nextIdx (nextEquiv.symm k) = k := nextEquiv.apply_symm_apply k
            rwa [h2] at h1
          simp only [M, hcond, ↓reduceIte, char, chi]
          split_ifs <;> norm_num
      · intro u hu
        have hiso := (Finset.mem_filter.mp hu).2
        refine Finset.prod_congr rfl fun k _ => ?_
        have hcond : u (nextEquiv.symm k) = 0 ∨ u k = 0 ∨ u (nextEquiv.symm k) = u k := by
          have h1 := hiso (nextEquiv.symm k)
          have h2 : nextIdx (nextEquiv.symm k) = k := nextEquiv.apply_symm_apply k
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
          P none c' + P (some (π (w.get i))) c' := by
        rw [Fintype.sum_option]
        simp only [T, Tmat, Option.elim_none, Option.elim_some, one_mul]
        congr 1
        rw [Finset.sum_eq_single (π (w.get i))]
        · simp
        · intro b _ hne; simp only [List.get_eq_getElem] at hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hrhs : (∑ c : Fin j → ZMod 2, P none c * M i c c') = M i 0 c' := by
        rw [Finset.sum_eq_single 0]
        · simp [P]
        · intro c _ hne; simp [P, hne]
        · intro h; exact absurd (Finset.mem_univ 0) h
      rw [hlhs, hrhs]
      by_cases hc' : c' = 0
      · subst hc'; simp [P, M, char_zero_left]
      · simp [P, M, hc', hψbar_sym]
    | some a =>
      have hlhs : (∑ s' : Option B, T i (some a) s' * P s' c') =
          closeRun a * P none c' + P (some (a + π (w.get i))) c' := by
        rw [Fintype.sum_option]
        simp only [T, Tmat, closeRun, Option.elim_some, Option.elim_none]
        congr 1
        rw [Finset.sum_eq_single (a + π (w.get i))]
        · simp
        · intro b _ hne; simp only [List.get_eq_getElem] at hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hlhs]
      by_cases hc' : c' = 0
      · subst hc'
        simp only [P, ↓reduceIte, mul_one, add_zero]
        rw [hclose_eq a, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → ZMod 2))]
        simp only [↓reduceIte, zero_mul, zero_add]
        refine Finset.sum_congr rfl fun c hc => ?_
        have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
        simp [M, hc0, char_zero_left]
      · simp only [P, hc', ↓reduceIte, mul_zero, zero_add]
        rw [Finset.sum_eq_single c']
        · simp only [hc', ↓reduceIte, M, or_true, map_add, hψbar_sym]
          exact char_add_right c' (ψbar a) (linOf Λ (w.get i))
        · intro c _ hne
          by_cases hc0 : c = 0
          · simp [hc0]
          · simp [hc0, M, hc', hne]
        · intro h; exact absurd (Finset.mem_univ c') h
  let E_Z : Matrix (Fin j → ZMod 2) (Fin j → ZMod 2) ℚ := Matrix.of (fun r c => if r = 0 ∧ c = 0 then 1 else 0)
  let Q_Z : Matrix (Fin j → ZMod 2) (Fin j → ZMod 2) ℚ := 1 - E_Z
  let E_B : Matrix (Option B) (Option B) ℚ := Matrix.of (fun r c => if r = none ∧ c = none then 1 else 0)
  let Q_B : Matrix (Option B) (Option B) ℚ := 1 - E_B
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
      have hl : (∑ s' : Option B, (if (some a : Option B) = none ∧ s' = none then (1 : ℚ) else 0) * P s' c) = 0 :=
        Finset.sum_eq_zero fun _ _ => by simp
      have hr : (∑ c' : Fin j → ZMod 2, P (some a) c' * (if c' = 0 ∧ c = 0 then (1 : ℚ) else 0)) = 0 :=
        Finset.sum_eq_zero fun c' _ => by by_cases hc' : c' = 0 <;> simp [P, hc']
      rw [hl, hr]
  have hQP : Q_B * P = P * Q_Z := by
    dsimp only [Q_B, Q_Z]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hEP]
  have hQM_inter : ∀ i : Fin n, (Q_B * T i) * P = P * (Q_Z * M i) := fun i => by
    rw [Matrix.mul_assoc, hinter i, ← Matrix.mul_assoc, hQP, Matrix.mul_assoc]
  have htel_eq : Matrix.trace (List.ofFn M).prod - Matrix.trace (List.ofFn (fun i => Q_Z * M i)).prod =
      Matrix.trace (List.ofFn T).prod - Matrix.trace (List.ofFn (fun i => Q_B * T i)).prod := by
    rw [trace_telescoping_rat n M 0, trace_telescoping_rat n T none]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdrop : ((List.ofFn T).drop k.val).prod * P = P * ((List.ofFn M).drop k.val).prod := by
      apply list_prod_intertwine_rat P _ _ (by simp)
      intro i h1 _
      simp only [List.getElem_drop, List.getElem_ofFn]
      exact hinter ⟨k.val + i, by simp at h1; omega⟩
    have htake : ((List.ofFn (fun i => Q_B * T i)).take k.val).prod * P =
        P * ((List.ofFn (fun i => Q_Z * M i)).take k.val).prod := by
      apply list_prod_intertwine_rat P _ _ (by simp)
      intro i h1 _
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
    refine Finset.sum_eq_zero fun c _ => by by_cases hc : c = 0 <;> simp [hc, Ne.symm]
  have hQM_nz : ∀ (i : Fin n) (c₁ c₂ : Fin j → ZMod 2), c₁ ≠ 0 → (Q_Z * M i) c₁ c₂ = M i c₁ c₂ := by
    intro i c₁ c₂ hc₁
    simp only [Q_Z, E_Z, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single c₁]
    · simp [hc₁]
    · intro c _ hne; simp [hc₁, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ c₁) h
  have htr_QM : Matrix.trace (List.ofFn (fun i => Q_Z * M i)).prod = closeRun (π w.sum) := by
    rw [trace_list_prod_eq_sum_rat hn (fun i => Q_Z * M i)]
    let ConstNZ : Finset (Fin n → Fin j → ZMod 2) :=
      ((Finset.univ : Finset (Fin j → ZMod 2)).erase 0).image (fun c => fun _ : Fin n => c)
    have hvan : ∀ v : Fin n → Fin j → ZMod 2, v ∉ ConstNZ →
        (∏ i : Fin n, (Q_Z * M i) (v i) (v (nextIdx i))) = 0 := by
      intro v hv
      by_cases h0 : ∃ i : Fin n, v i = 0
      · rcases h0 with ⟨i, hi⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hQM_zero])
      · push Not at h0
        have hne_adj : ∃ i : Fin n, v i ≠ v (nextIdx i) := by
          by_contra hall
          push Not at hall
          have hconst : ∀ t : ℕ, (ht : t < n) → v ⟨t, ht⟩ = v ⟨0, hn⟩ := by
            intro t
            induction t with
            | zero => intro _; rfl
            | succ t ih =>
              intro ht
              have h1 := hall ⟨t, by omega⟩
              have hnext : nextIdx ⟨t, by omega⟩ = ⟨t + 1, ht⟩ := by
                ext; dsimp [nextIdx]; exact Nat.mod_eq_of_lt ht
              rw [hnext] at h1
              exact h1.symm.trans (ih (by omega))
          apply hv
          refine Finset.mem_image.mpr ⟨v ⟨0, hn⟩, Finset.mem_erase.mpr ⟨h0 ⟨0, hn⟩, Finset.mem_univ _⟩, ?_⟩
          funext i; exact (hconst i.val i.isLt).symm
        rcases hne_adj with ⟨i, hi⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by
          rw [hQM_nz i (v i) (v (nextIdx i)) (h0 i)]
          simp [M, h0 i, h0 (nextIdx i), hi])
    rw [← Finset.sum_subset (Finset.subset_univ ConstNZ) (fun v _ hv => hvan v hv)]
    rw [Finset.sum_image (fun c₁ _ c₂ _ heq => congrFun heq ⟨0, hn⟩)]
    rw [hclose_eq (π w.sum)]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    have hprod : (∏ i : Fin n, (Q_Z * M i) c c) = ∏ i : Fin n, char c (linOf Λ (w.get i)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hQM_nz i c c hc0]; simp [M]
    rw [hprod]
    dsimp only [char]
    rw [← chi_sum]
    congr 1
    have hψtot : ψbar (π w.sum) = ∑ i : Fin n, linOf Λ (w.get i) := by
      rw [hψbar_sym, ← hsum_get, map_sum]
    rw [hψtot]
    simp only [dot, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have hQT_none : ∀ (i : Fin n) (s₂ : Option B), (Q_B * T i) none s₂ = 0 := by
    intro i s₂
    simp only [Q_B, E_B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun s _ => by cases s <;> simp
  have hQT_some : ∀ (i : Fin n) (a : B) (s₂ : Option B), (Q_B * T i) (some a) s₂ = T i (some a) s₂ := by
    intro i a s₂
    simp only [Q_B, E_B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single (some a)]
    · simp
    · intro s _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ (some a)) h
  have htr_QT : Matrix.trace (List.ofFn (fun i => Q_B * T i)).prod =
      if π w.sum = 0 then ((2 ^ r : ℕ) : ℚ) else 0 := by
    rw [trace_list_prod_eq_sum_rat hn (fun i => Q_B * T i)]
    let symbol : Fin n → B := fun i => π (w.get i)
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
    have hpsum_n : psum n = π w.sum := by
      have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n) = Finset.univ := by
        ext i; simp
      simp only [psum, hfilt, symbol, ← map_sum, hsum_get]
    have hchar : ∀ s : Fin n → Option B,
        (∏ i : Fin n, (Q_B * T i) (s i) (s (nextIdx i))) ≠ 0 →
        π w.sum = 0 ∧ ∃ a₀ : B, ∀ i : Fin n, s i = some (a₀ + psum i.val) := by
      intro s hne
      have hall_ne : ∀ i : Fin n, (Q_B * T i) (s i) (s (nextIdx i)) ≠ 0 :=
        fun i => Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
      have hall_some : ∀ i : Fin n, ∃ a : B, s i = some a := by
        intro i
        cases hs : s i with
        | none => exfalso; exact hall_ne i (by rw [hs, hQT_none])
        | some a => exact ⟨a, rfl⟩
      rcases hall_some ⟨0, hn⟩ with ⟨a₀, ha₀⟩
      have hstep : ∀ i : Fin n, ∀ a : B, s i = some a → s (nextIdx i) = some (a + symbol i) := by
        intro i a hsi
        rcases hall_some (nextIdx i) with ⟨b, hsb⟩
        have h1 := hall_ne i
        rw [hsi, hQT_some, hsb] at h1
        simp only [T, Tmat, Option.elim_some] at h1
        have hbeq : b = a + symbol i := by
          by_contra hnb
          simp only [symbol, List.get_eq_getElem] at hnb
          simp [hnb] at h1
        rw [hsb, hbeq]
      have hform : ∀ t : ℕ, (ht : t < n) → s ⟨t, ht⟩ = some (a₀ + psum t) := by
        intro t
        induction t with
        | zero => intro _; rw [hpsum_zero, add_zero]; exact ha₀
        | succ t ih =>
          intro ht
          have h1 := hstep ⟨t, by omega⟩ (a₀ + psum t) (ih (by omega))
          have hnext : nextIdx ⟨t, by omega⟩ = ⟨t + 1, ht⟩ := by
            ext; dsimp [nextIdx]; exact Nat.mod_eq_of_lt ht
          rw [hnext, add_assoc, ← hpsum_succ t (by omega)] at h1
          exact h1
      have hwrap : s (nextIdx ⟨n - 1, by omega⟩) = some (a₀ + π w.sum) := by
        have h1 := hstep ⟨n - 1, by omega⟩ (a₀ + psum (n - 1)) (hform (n - 1) (by omega))
        have hps : psum (n - 1) + symbol ⟨n - 1, by omega⟩ = π w.sum := by
          have := hpsum_succ (n - 1) (by omega)
          have heq : n - 1 + 1 = n := by omega
          rw [heq, hpsum_n] at this
          exact this.symm
        rw [add_assoc, hps] at h1
        exact h1
      have hnext_last : nextIdx ⟨n - 1, by omega⟩ = ⟨0, hn⟩ := by
        ext; dsimp [nextIdx]
        have : n - 1 + 1 = n := by omega
        rw [this, Nat.mod_self]
      rw [hnext_last, ha₀] at hwrap
      have hadd : a₀ = a₀ + π w.sum := Option.some.inj hwrap
      have htot0 : π w.sum = 0 := by
        have h1 : a₀ + 0 = a₀ + π w.sum := by simpa using hadd
        exact (add_left_cancel h1).symm
      exact ⟨htot0, a₀, fun i => hform i.val i.isLt⟩
    by_cases htot : π w.sum = 0
    · simp only [htot, ↓reduceIte]
      let Trajs : Finset (Fin n → Option B) :=
        Finset.univ.image (fun a₀ : B => fun i : Fin n => some (a₀ + psum i.val))
      rw [← Finset.sum_subset (Finset.subset_univ Trajs)]
      · rw [Finset.sum_image]
        · calc (∑ a₀ : B, ∏ i : Fin n,
                  (Q_B * T i) (some (a₀ + psum i.val)) (some (a₀ + psum (nextIdx i).val)))
              = ∑ _a₀ : B, (1 : ℚ) := by
                refine Finset.sum_congr rfl fun a₀ _ => Finset.prod_eq_one fun i _ => ?_
                rw [hQT_some]
                simp only [T, Tmat, Option.elim_some]
                have hnext_eq : a₀ + psum (nextIdx i).val = a₀ + psum i.val + symbol i := by
                  by_cases hlt : i.val + 1 < n
                  · have hnv : (nextIdx i).val = i.val + 1 := Nat.mod_eq_of_lt hlt
                    rw [hnv, hpsum_succ i.val i.isLt, add_assoc]
                  · have hi : i.val + 1 = n := by omega
                    have hnv : (nextIdx i).val = 0 := by dsimp [nextIdx]; rw [hi, Nat.mod_self]
                    rw [hnv, hpsum_zero, add_zero, add_assoc]
                    have hps : psum i.val + symbol i = π w.sum := by
                      have := hpsum_succ i.val i.isLt
                      rw [hi, hpsum_n] at this
                      exact this.symm
                    rw [hps, htot, add_zero]
                simp [symbol, hnext_eq]
            _ = ((2 ^ r : ℕ) : ℚ) := by simp [B]
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
  dsimp only [cycleD]
  rw [← hT_ofFn]
  dsimp only [D, r, π, z, closeRun] at htel_eq ⊢
  linarith

open Classical in
lemma countVal_eq_sum_cycleD {m j : ℕ} (Y : Fin j → (Fin m → ZMod 2)) (hY : Y ≠ 0)
    (w : List (Fin m → ZMod 2)) :
    letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
    countVal Y w = ((2 ^ (m * j) : ℕ) : ℚ)⁻¹ *
      ∑ D : Submodule (ZMod 2) (Fin m → ZMod 2), coeffD Y D * cycleD D ((2 ^ j : ℕ) : ℚ) w := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  have hgroup : (∑ D : Submodule (ZMod 2) (Fin m → ZMod 2), coeffD Y D * cycleD D ((2 ^ j : ℕ) : ℚ) w) =
      ∑ Λ : Fin j → (Fin m → ZMod 2), matChar Λ Y * cycleD (LinearMap.ker (linOf Λ)) ((2 ^ j : ℕ) : ℚ) w := by
    calc (∑ D : Submodule (ZMod 2) (Fin m → ZMod 2), coeffD Y D * cycleD D ((2 ^ j : ℕ) : ℚ) w)
        = ∑ D : Submodule (ZMod 2) (Fin m → ZMod 2),
            ∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → (Fin m → ZMod 2) => LinearMap.ker (linOf Λ) = D),
              matChar Λ Y * cycleD (LinearMap.ker (linOf Λ)) ((2 ^ j : ℕ) : ℚ) w := by
          refine Finset.sum_congr rfl fun D _ => ?_
          dsimp only [coeffD]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun Λ hΛ => by rw [(Finset.mem_filter.mp hΛ).2]
      _ = ∑ Λ : Fin j → (Fin m → ZMod 2), matChar Λ Y * cycleD (LinearMap.ker (linOf Λ)) ((2 ^ j : ℕ) : ℚ) w :=
          Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  rw [hgroup]
  by_cases hw : w = []
  · subst hw
    simp_rw [cycleD_nil]
    rw [← Finset.sum_mul, sum_matChar_left]
    simp only [hY, ite_false, zero_mul, mul_zero]
    rw [countVal_eq_fourier]
    have hsum1 : ∀ Λ : Fin j → (Fin m → ZMod 2),
        (∑ x ∈ (Finset.univ : Finset (Fin ([] : List (Fin m → ZMod 2)).length → (Fin j → ZMod 2))).filter
          (fun x => ∀ i, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i)),
          ∏ i : Fin ([] : List (Fin m → ZMod 2)).length, char (x i) (linOf Λ (([] : List (Fin m → ZMod 2)).get i))) = 1 := by
      intro Λ
      have heq : (Finset.univ : Finset (Fin ([] : List (Fin m → ZMod 2)).length → (Fin j → ZMod 2))).filter
          (fun x => ∀ i, x i = 0 ∨ x (nextIdx i) = 0 ∨ x i = x (nextIdx i)) = Finset.univ := by
        ext x; simp
      rw [heq]
      have hprod1 : ∀ x : Fin ([] : List (Fin m → ZMod 2)).length → (Fin j → ZMod 2),
          (∏ i : Fin ([] : List (Fin m → ZMod 2)).length, char (x i) (linOf Λ (([] : List (Fin m → ZMod 2)).get i))) = 1 :=
        fun _ => Finset.prod_eq_one fun i _ => Fin.elim0 i
      simp_rw [hprod1]
      rw [Finset.sum_const, Finset.card_univ]
      simp
    simp_rw [hsum1, mul_one]
    rw [sum_matChar_left]
    simp [hY]
  · have hw_pos : 0 < w.length := List.length_pos_of_ne_nil hw
    rw [countVal_eq_fourier]
    congr 1
    refine Finset.sum_congr rfl fun Λ _ => ?_
    rw [walk_eq_sum_iso_rat Λ w hw_pos]

def vecE {r : ℕ} : Option (Fin r → ZMod 2) → ℚ := fun x => x.elim 1 (fun _ => 0)

def vecV {r : ℕ} (ψ : Fin r → ZMod 2) : Option (Fin r → ZMod 2) → ℚ :=
  fun x => x.elim 0 (fun a => char ψ a)

def rankOne {α : Type*} (u w : α → ℚ) : Matrix α α ℚ := fun i j => u i * w j

lemma rankOne_mul_rankOne {α : Type*} [Fintype α] (u₁ w₁ u₂ w₂ : α → ℚ) :
    rankOne u₁ w₁ * rankOne u₂ w₂ = (∑ x : α, w₁ x * u₂ x) • rankOne u₁ w₂ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, rankOne, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma dot_EE {r : ℕ} : (∑ x : Option (Fin r → ZMod 2), vecE x * vecE x) = 1 := by
  rw [Fintype.sum_option]; simp [vecE]

lemma dot_EV {r : ℕ} (ψ : Fin r → ZMod 2) :
    (∑ x : Option (Fin r → ZMod 2), vecE x * vecV ψ x) = 0 := by
  rw [Fintype.sum_option]; simp [vecE, vecV]

lemma dot_VE {r : ℕ} (ψ : Fin r → ZMod 2) :
    (∑ x : Option (Fin r → ZMod 2), vecV ψ x * vecE x) = 0 := by
  rw [Fintype.sum_option]; simp [vecE, vecV]

lemma dot_VV {r : ℕ} (ψ χ : Fin r → ZMod 2) :
    (∑ x : Option (Fin r → ZMod 2), vecV ψ x * vecV χ x) =
    if ψ = χ then ((2 ^ r : ℕ) : ℚ) else 0 := by
  rw [Fintype.sum_option]
  simp only [vecV, Option.elim_none, mul_zero, zero_add, Option.elim_some]
  have h1 : ∀ a : Fin r → ZMod 2, char ψ a * char χ a = char (ψ + χ) a := fun a =>
    (char_add_left ψ χ a).symm
  simp_rw [h1]
  rw [sum_char_right]
  have hiff : ψ + χ = 0 ↔ ψ = χ := by
    constructor
    · intro h
      have := congrArg (· + χ) h
      simpa [add_assoc, zmod2_vec_add_self] using this
    · rintro rfl; exact zmod2_vec_add_self ψ
  by_cases heq : ψ = χ
  · subst heq; simp [zmod2_vec_add_self]
  · have hne : ψ + χ ≠ 0 := fun h => heq (hiff.mp h)
    simp [heq, hne]

def Ptilde {r : ℕ} (h : Fin r → ZMod 2) :
    Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ :=
  fun before after =>
    before.elim (after.elim 1 (fun _ => 0))
      (fun a => after.elim 0 (fun b => if b = a + h then 1 else 0))

lemma Tmat_eq_T0_mul_Ptilde {r : ℕ} (z : ℚ) (h : Fin r → ZMod 2) :
    Tmat z h = Tmat z 0 * Ptilde h := by
  ext before after
  rw [Matrix.mul_apply, Fintype.sum_option]
  cases before with
  | none =>
    cases after with
    | none => simp [Tmat, Ptilde]
    | some b =>
      simp only [Tmat, Ptilde, Option.elim_none, Option.elim_some, mul_zero, zero_add]
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  | some a =>
    cases after with
    | none => simp [Tmat, Ptilde]
    | some b =>
      simp only [Tmat, Ptilde, Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma T0_cubic {r : ℕ} (z : ℚ) :
    Tmat z 0 * Tmat z 0 * Tmat z 0 - (3 : ℚ) • (Tmat z 0 * Tmat z 0) + (4 - z) • Tmat z 0 =
    (2 - z) • (1 : Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ) := by
  let X := Tmat (r := r) z 0
  let D := X - 1
  have hD_nn : D none none = 0 := by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply_eq]; simp [Tmat]
  have hD_ns : ∀ b, D none (some b) = if b = 0 then 1 else 0 := fun b => by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply_ne (by simp)]; simp [Tmat]
  have hD_sn : ∀ a, D (some a) none = if a = 0 then z - 1 else -1 := fun a => by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply_ne (by simp)]; simp [Tmat]
  have hD_ss : ∀ a b, D (some a) (some b) = 0 := fun a b => by
    dsimp only [D, X]; rw [Matrix.sub_apply, Matrix.one_apply]
    simp only [Tmat, Option.elim_some, add_zero, Option.some.injEq]
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := Ne.symm h
      simp [h, h']
  have hD2_nn : (D * D) none none = z - 1 := by
    rw [Matrix.mul_apply, Fintype.sum_option, hD_nn, zero_mul, zero_add]
    simp_rw [hD_ns, hD_sn]
    rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
    · simp
    · intro a _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  have hD2_ns : ∀ b, (D * D) none (some b) = 0 := fun b => by
    rw [Matrix.mul_apply, Fintype.sum_option, hD_nn, zero_mul, zero_add]
    simp_rw [hD_ss, mul_zero, Finset.sum_const_zero]
  have hD2_sn : ∀ a, (D * D) (some a) none = 0 := fun a => by
    rw [Matrix.mul_apply, Fintype.sum_option, hD_nn, mul_zero, zero_add]
    simp_rw [hD_ss, zero_mul, Finset.sum_const_zero]
  have hD2_ss : ∀ a b, (D * D) (some a) (some b) = (if a = 0 then z - 1 else -1) * (if b = 0 then 1 else 0) :=
    fun a b => by
      rw [Matrix.mul_apply, Fintype.sum_option, hD_sn, hD_ns]
      simp_rw [hD_ss, zero_mul, Finset.sum_const_zero, add_zero]
  have hD3 : D * D * D = (z - 1) • D := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.smul_apply, smul_eq_mul]
    cases i with
    | none =>
      cases j with
      | none =>
        rw [hD2_nn, hD_nn, mul_zero, zero_add]
        simp_rw [hD2_ns]; simp
      | some b =>
        rw [hD2_nn, hD_ns]
        simp_rw [hD2_ns]; simp
    | some a =>
      cases j with
      | none =>
        rw [hD2_sn, zero_mul, zero_add, hD_sn]
        simp_rw [hD2_ss, hD_sn]
        rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
        · simp [mul_comm]
        · intro x _ hne; simp [hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      | some b =>
        rw [hD2_sn, zero_mul, zero_add, hD_ss, mul_zero]
        simp_rw [hD_ss]; simp
  have hX : X = D + 1 := by simp [D]
  change X * X * X - (3 : ℚ) • (X * X) + (4 - z) • X = (2 - z) • 1
  rw [hX]
  have hexp : ((D + 1) * (D + 1) * (D + 1) - (3 : ℚ) • ((D + 1) * (D + 1)) + (4 - z) • (D + 1)) =
      (D * D * D - (z - 1) • D) + (2 - z) • 1 := by
    simp only [mul_add, add_mul, one_mul, mul_one, smul_add, sub_smul, one_smul]
    ext p q
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hexp, hD3, sub_self, zero_add]

def Qmat {r : ℕ} (ψ : Fin r → ZMod 2) :
    Matrix (Option (Fin r → ZMod 2)) (Option (Fin r → ZMod 2)) ℚ :=
  ((2 ^ r : ℕ) : ℚ)⁻¹ • ∑ h : Fin r → ZMod 2, char ψ h • Ptilde h

lemma Qmat_ne_zero {r : ℕ} (ψ : Fin r → ZMod 2) (hψ : ψ ≠ 0) :
    Qmat ψ = ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne (vecV ψ) (vecV ψ) := by
  ext before after
  simp only [Qmat, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne]
  congr 1
  cases before with
  | none =>
    cases after with
    | none =>
      simp only [Ptilde, Option.elim_none, mul_one, vecV, zero_mul]
      rw [sum_char_right]; simp [hψ]
    | some b => simp [Ptilde, vecV]
  | some a =>
    cases after with
    | none => simp [Ptilde, vecV]
    | some b =>
      simp only [Ptilde, Option.elim_some, vecV]
      rw [Finset.sum_eq_single (a + b)]
      · have heq : b = a + (a + b) := by rw [← add_assoc, zmod2_vec_add_self, zero_add]
        rw [← heq]; simp [char_add_right]
      · intro h _ hne
        have hne' : b ≠ a + h := by
          intro hb; apply hne
          have h1 := congrArg (a + ·) hb
          rw [← add_assoc, zmod2_vec_add_self, zero_add] at h1
          exact h1.symm
        simp [hne']
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma Qmat_zero {r : ℕ} :
    Qmat (0 : Fin r → ZMod 2) =
    rankOne vecE vecE + ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne (vecV 0) (vecV 0) := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext before after
  simp only [Qmat, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne]
  cases before with
  | none =>
    cases after with
    | none =>
      simp only [Ptilde, Option.elim_none, mul_one, vecE, vecV, mul_zero, add_zero, char_zero_left]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul,
        mul_one, inv_mul_cancel₀ hq0]
    | some b => simp [Ptilde, vecE, vecV]
  | some a =>
    cases after with
    | none => simp [Ptilde, vecE, vecV]
    | some b =>
      simp only [Ptilde, Option.elim_some, vecE, vecV, zero_mul, zero_add, char_zero_left, one_mul]
      congr 1
      rw [Finset.sum_eq_single (a + b)]
      · have heq : b = a + (a + b) := by rw [← add_assoc, zmod2_vec_add_self, zero_add]
        rw [← heq]; simp
      · intro h _ hne
        have hne' : b ≠ a + h := by
          intro hb; apply hne
          have h1 := congrArg (a + ·) hb
          rw [← add_assoc, zmod2_vec_add_self, zero_add] at h1
          exact h1.symm
        simp [hne']
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma Q0_mul_T0_mul_Qpsi {r : ℕ} (z : ℚ) (ψ : Fin r → ZMod 2) (hψ : ψ ≠ 0) :
    Qmat 0 * Tmat z 0 * Qmat ψ = ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV ψ) := by
  rw [Qmat_zero, Qmat_ne_zero ψ hψ]
  have hT_eq : Tmat z 0 * rankOne (vecV ψ) (vecV ψ) =
      rankOne vecE (vecV ψ) + rankOne (vecV ψ) (vecV ψ) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.add_apply]
    cases x with
    | none =>
      simp only [Tmat, rankOne, vecV, vecE, Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero, one_mul]
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp [char_zero_right]
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    | some a =>
      simp only [Tmat, rankOne, vecV, vecE, Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [Matrix.mul_assoc, Matrix.mul_smul, hT_eq, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne,
    dot_EE, dot_EV, dot_VE, dot_VV]
  simp [hψ.symm]

lemma Qpsi_mul_T0_mul_Q0 {r : ℕ} (z : ℚ) (ψ : Fin r → ZMod 2) (hψ : ψ ≠ 0) :
    Qmat ψ * Tmat z 0 * Qmat 0 = (z * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV ψ) vecE := by
  rw [Qmat_zero, Qmat_ne_zero ψ hψ]
  have hv_T : rankOne (vecV ψ) (vecV ψ) * Tmat z 0 =
      z • rankOne (vecV ψ) vecE + rankOne (vecV ψ) (vecV ψ) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rankOne, vecV, vecE, Tmat]
    cases y with
    | none =>
      simp only [Option.elim_none, Option.elim_some, mul_zero, zero_add, mul_one, add_zero]
      have hsum : (∑ a : Fin r → ZMod 2, char ψ a * (if a = 0 then z - 1 else -1)) = z := by
        have hrew : ∀ a : Fin r → ZMod 2,
            char ψ a * (if a = 0 then z - 1 else -1) = (if a = 0 then z else 0) - char ψ a := fun a => by
          by_cases ha : a = 0
          · subst ha; simp [char_zero_right]
          · simp [ha]
        simp_rw [hrew, Finset.sum_sub_distrib, sum_char_right]
        simp only [hψ, ite_false, sub_zero]
        rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
        · simp
        · intro a _ hne; simp [hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      cases x with
      | none => simp
      | some a =>
        simp only [Option.elim_some]
        have hfac : (∑ b : Fin r → ZMod 2, char ψ a * char ψ b * (if b = 0 then z - 1 else -1)) =
            char ψ a * ∑ b : Fin r → ZMod 2, char ψ b * (if b = 0 then z - 1 else -1) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
        rw [hfac, hsum]; ring
    | some b =>
      simp only [Option.elim_none, Option.elim_some, mul_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single b]
      · simp
      · intro a _ hne; have : b ≠ a := Ne.symm hne; simp [this]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [Matrix.smul_mul, hv_T, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne, rankOne_mul_rankOne,
    dot_EE, dot_EV, dot_VE, dot_VV]
  simp only [hψ, ite_false, one_smul, zero_smul, smul_zero, add_zero, zero_add, smul_smul, mul_comm]

lemma Enn_mul_T0_mul_Q0 {r : ℕ} (z : ℚ) :
    rankOne (vecE (r := r)) vecE * Tmat z 0 * Qmat 0 =
    rankOne (vecE (r := r)) vecE + ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV 0) := by
  rw [Qmat_zero]
  have he_T : rankOne (vecE (r := r)) vecE * Tmat z 0 =
      Matrix.of (fun x y => vecE x * (y.elim 1 (fun b => if b = 0 then 1 else 0))) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.of_apply]
    cases y <;> simp [rankOne, vecE, Tmat]
  have h1 : rankOne (vecE (r := r)) vecE * Tmat z 0 * rankOne vecE vecE = rankOne vecE vecE := by
    ext x y
    rw [he_T, Matrix.mul_apply, Fintype.sum_option]
    simp [rankOne, vecE]
  have h2 : rankOne (vecE (r := r)) vecE * Tmat z 0 * rankOne (vecV 0) (vecV 0) = rankOne vecE (vecV 0) := by
    ext x y
    rw [he_T, Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.of_apply, rankOne, vecV, Option.elim_none, mul_zero, zero_add, Option.elim_some]
    rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
    · simp [char_zero_left]
    · intro b _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [Matrix.mul_add, Matrix.mul_smul, h1, h2]

lemma Q0_mul_T0_mul_Enn {r : ℕ} (z : ℚ) :
    Qmat (r := r) 0 * Tmat z 0 * rankOne vecE vecE =
    rankOne (vecE (r := r)) vecE + ((z - ((2 ^ r : ℕ) : ℚ)) * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV 0) vecE := by
  rw [Qmat_zero]
  have hT_e : Tmat (r := r) z 0 * rankOne vecE vecE =
      Matrix.of (fun x y => (x.elim 1 (fun a => if a = 0 then z - 1 else -1)) * vecE y) := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.of_apply]
    cases x <;> simp [rankOne, vecE, Tmat]
  have h1 : rankOne (vecE (r := r)) vecE * (Tmat z 0 * rankOne vecE vecE) = rankOne vecE vecE := by
    ext x y
    rw [hT_e, Matrix.mul_apply, Fintype.sum_option]
    simp [rankOne, vecE]
  have h2 : rankOne (vecV (r := r) 0) (vecV 0) * (Tmat z 0 * rankOne vecE vecE) =
      (z - ((2 ^ r : ℕ) : ℚ)) • rankOne (vecV 0) vecE := by
    ext x y
    rw [hT_e, Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.of_apply, rankOne, vecV, Option.elim_none, mul_zero, zero_add, Option.elim_some,
      Matrix.smul_apply, smul_eq_mul, char_zero_left, one_mul]
    have hsum : (∑ a : Fin r → ZMod 2, (if a = 0 then z - 1 else -1 : ℚ)) = z - ((2 ^ r : ℕ) : ℚ) := by
      have hrew : ∀ a : Fin r → ZMod 2,
          (if a = 0 then z - 1 else -1 : ℚ) = (if a = 0 then z else 0) - 1 := fun a => by
        by_cases ha : a = 0 <;> simp [ha]
      simp_rw [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one]
      rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
      · simp
      · intro a _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    cases x with
    | none => simp
    | some a =>
      simp only [Option.elim_some, char_zero_left, one_mul]
      rw [← Finset.sum_mul, hsum]; ring
  rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.smul_mul, h1, h2, smul_smul, mul_comm]

lemma single_nn_eq {r : ℕ} :
    Matrix.single (none : Option (Fin r → ZMod 2)) none (1 : ℚ) = rankOne vecE vecE := by
  ext i j; cases i <;> cases j <;> simp [Matrix.single, rankOne, vecE]

lemma single_ns_eq {r : ℕ} (b : Fin r → ZMod 2) :
    Matrix.single (none : Option (Fin r → ZMod 2)) (some b) (1 : ℚ) =
    ((2 ^ r : ℕ) : ℚ)⁻¹ • ∑ ψ : Fin r → ZMod 2, char ψ b • rankOne vecE (vecV ψ) := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.single, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne, vecE, vecV]
  cases i with
  | some a => simp
  | none =>
    cases j with
    | none => simp
    | some b' =>
      simp only [Option.elim_none, Option.elim_some, one_mul, true_and, Option.some.injEq]
      have hrew : ∀ ψ : Fin r → ZMod 2, char ψ b * char ψ b' = char ψ (b + b') :=
        fun ψ => (char_add_right ψ b b').symm
      simp_rw [hrew, sum_char_left]
      have hiff : b + b' = 0 ↔ b = b' := by
        constructor
        · intro h; have := congrArg (· + b') h; simpa [add_assoc, zmod2_vec_add_self] using this
        · rintro rfl; exact zmod2_vec_add_self b
      by_cases heq : b = b'
      · subst heq; simp [zmod2_vec_add_self, inv_mul_cancel₀ hq0]
      · have hne : b + b' ≠ 0 := fun h => heq (hiff.mp h)
        simp [heq, hne]

lemma single_sn_eq {r : ℕ} (a : Fin r → ZMod 2) :
    Matrix.single (some a : Option (Fin r → ZMod 2)) none (1 : ℚ) =
    ((2 ^ r : ℕ) : ℚ)⁻¹ • ∑ ψ : Fin r → ZMod 2, char ψ a • rankOne (vecV ψ) vecE := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.single, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne, vecE, vecV]
  cases j with
  | some b => simp
  | none =>
    cases i with
    | none => simp
    | some a' =>
      simp only [Option.elim_none, Option.elim_some, mul_one, and_true, Option.some.injEq]
      have hrew : ∀ ψ : Fin r → ZMod 2, char ψ a * char ψ a' = char ψ (a + a') :=
        fun ψ => (char_add_right ψ a a').symm
      simp_rw [hrew, sum_char_left]
      have hiff : a + a' = 0 ↔ a = a' := by
        constructor
        · intro h; have := congrArg (· + a') h; simpa [add_assoc, zmod2_vec_add_self] using this
        · rintro rfl; exact zmod2_vec_add_self a
      by_cases heq : a = a'
      · subst heq; simp [zmod2_vec_add_self, inv_mul_cancel₀ hq0]
      · have hne : a + a' ≠ 0 := fun h => heq (hiff.mp h)
        simp [heq, hne]

lemma single_ss_eq {r : ℕ} (a b : Fin r → ZMod 2) :
    Matrix.single (some a : Option (Fin r → ZMod 2)) (some b) (1 : ℚ) =
    (((2 ^ r : ℕ) : ℚ)⁻¹ * ((2 ^ r : ℕ) : ℚ)⁻¹) •
      ∑ ψ : Fin r → ZMod 2, ∑ χ : Fin r → ZMod 2,
        (char ψ a * char χ b) • rankOne (vecV ψ) (vecV χ) := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  ext i j
  simp only [Matrix.single, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, rankOne, vecV]
  cases i with
  | none => simp
  | some a' =>
    cases j with
    | none => simp
    | some b' =>
      simp only [Option.elim_some, Option.some.injEq]
      have hsep : (∑ ψ : Fin r → ZMod 2, ∑ χ : Fin r → ZMod 2,
          char ψ a * char χ b * (char ψ a' * char χ b')) =
          (∑ ψ : Fin r → ZMod 2, char ψ (a + a')) * (∑ χ : Fin r → ZMod 2, char χ (b + b')) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => by rw [char_add_right, char_add_right]; ring
      rw [hsep, sum_char_left, sum_char_left]
      have hiff1 : a + a' = 0 ↔ a = a' := by
        constructor
        · intro h; have := congrArg (· + a') h; simpa [add_assoc, zmod2_vec_add_self] using this
        · rintro rfl; exact zmod2_vec_add_self a
      have hiff2 : b + b' = 0 ↔ b = b' := by
        constructor
        · intro h; have := congrArg (· + b') h; simpa [add_assoc, zmod2_vec_add_self] using this
        · rintro rfl; exact zmod2_vec_add_self b
      by_cases ha : a = a' <;> by_cases hb : b = b'
      · subst ha; subst hb; simp only [Matrix.of_apply, ite_true, and_self, zmod2_vec_add_self]; field_simp [hq0]
      · have hnb : b + b' ≠ 0 := fun h => hb (hiff2.mp h)
        simp [ha, hb, hnb]
      · have hna : a + a' ≠ 0 := fun h => ha (hiff1.mp h)
        simp [ha, hb, hna]
      · have hna : a + a' ≠ 0 := fun h => ha (hiff1.mp h)
        simp [ha, hb, hna]

lemma fourier_remainder {r j : ℕ} (hrj : r ≤ j) (a : Fin r → ZMod 2) :
    (if a = 0 then ((2 ^ j : ℕ) : ℚ) - 1 else -1) - (if a = 0 then ((2 ^ r : ℕ) : ℚ) else 0) =
    ∑ φ : Fin r → ZMod 2,
      (if φ = 0 then (2 : ℚ) ^ (j - r) - 2 else (2 : ℚ) ^ (j - r) - 1) * char φ a := by
  have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
  have hpow : ((2 ^ j : ℕ) : ℚ) = (2 : ℚ) ^ (j - r) * ((2 ^ r : ℕ) : ℚ) := by
    have hnat : 2 ^ j = 2 ^ (j - r) * 2 ^ r := by rw [← pow_add, Nat.sub_add_cancel hrj]
    exact_mod_cast hnat
  have hrew : ∀ φ : Fin r → ZMod 2,
      (if φ = 0 then (2 : ℚ) ^ (j - r) - 2 else (2 : ℚ) ^ (j - r) - 1) * char φ a =
      ((2 : ℚ) ^ (j - r) - 1) * char φ a - (if φ = 0 then 1 else 0) := fun φ => by
    by_cases h0 : φ = 0
    · subst h0; simp [char_zero_left]; ring
    · simp [h0]
  simp_rw [hrew, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_char_left]
  have hsum1 : (∑ φ : Fin r → ZMod 2, (if φ = 0 then (1 : ℚ) else 0)) = 1 := by
    rw [Finset.sum_eq_single (0 : Fin r → ZMod 2)]
    · simp
    · intro φ _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [hsum1]
  by_cases ha : a = 0
  · simp only [ha, ite_true, hpow]; ring
  · simp only [ha, ite_false, mul_zero, zero_sub, sub_zero]

structure B0 (z : ℚ) where
  a : ℚ
  b : ℚ

lemma B0.ext {z : ℚ} {x y : B0 z} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; cases ha; cases hb; rfl

instance (z : ℚ) : Zero (B0 z) := ⟨⟨0, 0⟩⟩
instance (z : ℚ) : One (B0 z) := ⟨⟨1, 0⟩⟩
instance (z : ℚ) : Add (B0 z) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance (z : ℚ) : Neg (B0 z) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance (z : ℚ) : Sub (B0 z) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance (z : ℚ) : SMul ℚ (B0 z) := ⟨fun c x => ⟨c * x.a, c * x.b⟩⟩
instance (z : ℚ) : Mul (B0 z) :=
  ⟨fun x y => ⟨x.a * y.a + (z - 2) * x.b * y.b, x.a * y.b + x.b * y.a + 2 * x.b * y.b⟩⟩

@[simp] lemma B0_zero_a (z : ℚ) : (0 : B0 z).a = 0 := rfl
@[simp] lemma B0_zero_b (z : ℚ) : (0 : B0 z).b = 0 := rfl
@[simp] lemma B0_one_a (z : ℚ) : (1 : B0 z).a = 1 := rfl
@[simp] lemma B0_one_b (z : ℚ) : (1 : B0 z).b = 0 := rfl
@[simp] lemma B0_add_a {z : ℚ} (x y : B0 z) : (x + y).a = x.a + y.a := rfl
@[simp] lemma B0_add_b {z : ℚ} (x y : B0 z) : (x + y).b = x.b + y.b := rfl
@[simp] lemma B0_neg_a {z : ℚ} (x : B0 z) : (-x).a = -x.a := rfl
@[simp] lemma B0_neg_b {z : ℚ} (x : B0 z) : (-x).b = -x.b := rfl
@[simp] lemma B0_sub_a {z : ℚ} (x y : B0 z) : (x - y).a = x.a - y.a := rfl
@[simp] lemma B0_sub_b {z : ℚ} (x y : B0 z) : (x - y).b = x.b - y.b := rfl
@[simp] lemma B0_smul_a {z : ℚ} (c : ℚ) (x : B0 z) : (c • x).a = c * x.a := rfl
@[simp] lemma B0_smul_b {z : ℚ} (c : ℚ) (x : B0 z) : (c • x).b = c * x.b := rfl
@[simp] lemma B0_mul_a {z : ℚ} (x y : B0 z) : (x * y).a = x.a * y.a + (z - 2) * x.b * y.b := rfl
@[simp] lemma B0_mul_b {z : ℚ} (x y : B0 z) : (x * y).b = x.a * y.b + x.b * y.a + 2 * x.b * y.b := rfl

instance (z : ℚ) : CommRing (B0 z) :=
  { zero_add := fun x => by refine B0.ext ?_ ?_ <;> simp
    , add_assoc := fun x y w => by refine B0.ext ?_ ?_ <;> simp [add_assoc]
    , add_zero := fun x => by refine B0.ext ?_ ?_ <;> simp
    , add_comm := fun x y => by refine B0.ext ?_ ?_ <;> simp [add_comm]
    neg_add_cancel := fun x => by refine B0.ext ?_ ?_ <;> simp
    sub_eq_add_neg := fun x y => by refine B0.ext ?_ ?_ <;> simp [sub_eq_add_neg]
    nsmul := nsmulRec
    zsmul := zsmulRec
    mul_assoc := fun x y w => by refine B0.ext ?_ ?_ <;> simp <;> ring
    one_mul := fun x => by refine B0.ext ?_ ?_ <;> simp
    mul_one := fun x => by refine B0.ext ?_ ?_ <;> simp
    left_distrib := fun x y w => by refine B0.ext ?_ ?_ <;> simp <;> ring
    right_distrib := fun x y w => by refine B0.ext ?_ ?_ <;> simp <;> ring
    zero_mul := fun x => by refine B0.ext ?_ ?_ <;> simp
    mul_zero := fun x => by refine B0.ext ?_ ?_ <;> simp
    mul_comm := fun x y => by refine B0.ext ?_ ?_ <;> simp <;> ring }

instance (z : ℚ) : Module ℚ (B0 z) :=
  { one_smul := fun x => by refine B0.ext ?_ ?_ <;> simp
    mul_smul := fun c d x => by refine B0.ext ?_ ?_ <;> simp [mul_assoc]
    smul_zero := fun c => by refine B0.ext ?_ ?_ <;> simp
    smul_add := fun c x y => by refine B0.ext ?_ ?_ <;> simp [mul_add]
    , add_smul := fun c d x => by refine B0.ext ?_ ?_ <;> simp [add_mul]
    zero_smul := fun x => by refine B0.ext ?_ ?_ <;> simp }

instance (z : ℚ) : IsScalarTower ℚ (B0 z) (B0 z) where
  smul_assoc c x y := by refine B0.ext ?_ ?_ <;> simp <;> ring

instance (z : ℚ) : SMulCommClass ℚ (B0 z) (B0 z) where
  smul_comm c x y := by refine B0.ext ?_ ?_ <;> simp <;> ring

def X0 (z : ℚ) : B0 z := ⟨0, 1⟩

lemma X0_sq (z : ℚ) : X0 z * X0 z = (z - 2) • (1 : B0 z) + (2 : ℚ) • X0 z := by
  refine B0.ext ?_ ?_ <;> simp [X0]

lemma X0_cubic (z : ℚ) :
    X0 z * X0 z * X0 z - (3 : ℚ) • (X0 z * X0 z) + (4 - z) • X0 z = (2 - z) • (1 : B0 z) := by
  refine B0.ext ?_ ?_ <;> simp [X0] <;> ring

def tr0 {z : ℚ} (x : B0 z) : ℚ := 2 * x.a + 2 * x.b

lemma tr0_add {z : ℚ} (x y : B0 z) : tr0 (x + y) = tr0 x + tr0 y := by
  simp [tr0]; ring

lemma tr0_smul {z : ℚ} (c : ℚ) (x : B0 z) : tr0 (c • x) = c * tr0 x := by
  simp [tr0]; ring

lemma tr0_nondeg {z : ℚ} (hz1 : z ≠ 1) (x : B0 z) (h : ∀ y : B0 z, tr0 (x * y) = 0) : x = 0 := by
  have h1 := h 1
  have h2 := h (X0 z)
  simp only [tr0, B0_mul_a, B0_mul_b, B0_one_a, B0_one_b, X0] at h1 h2
  have hxb : (z - 1) * x.b = 0 := by linarith
  have hzb : x.b = 0 := (mul_eq_zero.mp hxb).resolve_left (sub_ne_zero.mpr hz1)
  have hxa : x.a = 0 := by linarith
  refine B0.ext ?_ ?_ <;> simp [hxa, hzb]

lemma trace_Tmat_zero_eq_tr0 {r : ℕ} (hr : r = 0) (z : ℚ) (w : List (Fin r → ZMod 2)) :
    Matrix.trace (w.map (Tmat z)).prod = tr0 (w.map (fun _ => X0 z)).prod := by
  subst hr
  let toMat : B0 z → Matrix (Option (Fin 0 → ZMod 2)) (Option (Fin 0 → ZMod 2)) ℚ :=
    fun x => x.a • 1 + x.b • Tmat z 0
  have hT2 : Tmat (r := 0) z 0 * Tmat z 0 = (z - 2) • 1 + (2 : ℚ) • Tmat z 0 := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_option]
    have h0eq : ∀ v : Fin 0 → ZMod 2, v = 0 := fun v => funext fun k => Fin.elim0 k
    have huniv0 : (Finset.univ : Finset (Fin 0 → ZMod 2)) = {0} := by
      ext v; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact h0eq v
    rw [huniv0, Finset.sum_singleton]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    cases i with
    | none =>
      cases j with
      | none => simp [Tmat]
      | some b => rw [h0eq b]; simp [Tmat]; ring
    | some a =>
      rw [h0eq a]
      cases j with
      | none => simp [Tmat]; ring
      | some b => rw [h0eq b]; simp [Tmat]
  have htoMat_mul : ∀ x y : B0 z, toMat (x * y) = toMat x * toMat y := by
    intro x y
    dsimp only [toMat]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hT2]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, B0_mul_a, B0_mul_b]
    ring
  have hprod : (w.map (Tmat z)).prod = toMat (w.map (fun _ => X0 z)).prod := by
    induction w with
    | nil => simp [toMat]
    | cons h t ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih, htoMat_mul]
      congr 1
      have hh : h = 0 := funext fun k => Fin.elim0 k
      rw [hh]
      simp [toMat, X0]
  rw [hprod]
  dsimp only [toMat, tr0]
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
  have htrT : Matrix.trace (Tmat (r := 0) z 0) = 2 := by
    simp only [Matrix.trace, Matrix.diag]
    rw [Fintype.sum_option]
    have h0eq : ∀ v : Fin 0 → ZMod 2, v = 0 := fun v => funext fun k => Fin.elim0 k
    have huniv0 : (Finset.univ : Finset (Fin 0 → ZMod 2)) = {0} := by
      ext v; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact h0eq v
    rw [huniv0, Finset.sum_singleton]
    simp [Tmat]; norm_num
  rw [htrT, Fintype.card_option, Fintype.card_fun, Fintype.card_fin]
  simp only [pow_zero, smul_eq_mul]
  ring

def castVec {r₁ r₂ : ℕ} (h : r₁ = r₂) (v : Fin r₁ → ZMod 2) : Fin r₂ → ZMod 2 :=
  fun i => v (finCongr h.symm i)

lemma castVec_zero {r₁ r₂ : ℕ} (h : r₁ = r₂) : castVec h 0 = 0 := rfl

lemma castVec_add {r₁ r₂ : ℕ} (h : r₁ = r₂) (u v : Fin r₁ → ZMod 2) :
    castVec h (u + v) = castVec h u + castVec h v := rfl

lemma char_castVec {r₁ r₂ : ℕ} (h : r₁ = r₂) (u v : Fin r₁ → ZMod 2) :
    char (castVec h u) (castVec h v) = char u v := by
  subst h; rfl

lemma castVec_eq_zero_iff {r₁ r₂ : ℕ} (h : r₁ = r₂) (v : Fin r₁ → ZMod 2) :
    castVec h v = 0 ↔ v = 0 := by
  subst h; rfl

lemma trace_Tmat_castVec {r₁ r₂ : ℕ} (h : r₁ = r₂) (z : ℚ) (w : List (Fin r₁ → ZMod 2)) :
    Matrix.trace (w.map (fun a => Tmat z (castVec h a))).prod = Matrix.trace (w.map (Tmat z)).prod := by
  subst h; rfl

abbrev NZ (j : ℕ) := {φ : Fin j → ZMod 2 // φ ≠ 0}

abbrev IdxTop (j : ℕ) := Option (NZ j)

lemma card_IdxTop (j : ℕ) : Fintype.card (IdxTop j) = 2 ^ j := by
  rw [Fintype.card_option]
  have h1 : Fintype.card (NZ j) = ((Finset.univ : Finset (Fin j → ZMod 2)).erase 0).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun φ => ⟨φ.1, Finset.mem_erase.mpr ⟨φ.2, Finset.mem_univ _⟩⟩
        invFun := fun φ => ⟨φ.1, (Finset.mem_erase.mp φ.2).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  have hpos : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by decide)
  omega

def S0 (j : ℕ) : Matrix (IdxTop j) (IdxTop j) ℚ := fun before after =>
  before.elim 1 (fun φ => after.elim 1 (fun ψ => if φ = ψ then 1 else 0))

def Sdiag {j : ℕ} (h : Fin j → ZMod 2) : Matrix (IdxTop j) (IdxTop j) ℚ := fun before after =>
  before.elim (after.elim 1 (fun _ => 0))
    (fun φ => after.elim 0 (fun ψ => if φ = ψ then char φ.1 h else 0))

def Smat {j : ℕ} (h : Fin j → ZMod 2) : Matrix (IdxTop j) (IdxTop j) ℚ :=
  S0 j * Sdiag h

lemma Sdiag_zero (j : ℕ) : Sdiag (0 : Fin j → ZMod 2) = 1 := by
  ext p q
  cases p <;> cases q <;> simp [Sdiag, Matrix.one_apply, char_zero_right]

lemma Smat_zero (j : ℕ) : Smat (0 : Fin j → ZMod 2) = S0 j := by
  rw [Smat, Sdiag_zero, Matrix.mul_one]

lemma Smat_apply {j : ℕ} (h : Fin j → ZMod 2) (p q : IdxTop j) :
    Smat h p q =
    p.elim (q.elim 1 (fun ψ => char ψ.1 h))
      (fun φ => q.elim 1 (fun ψ => if φ = ψ then char ψ.1 h else 0)) := by
  dsimp only [Smat]
  rw [Matrix.mul_apply, Fintype.sum_option]
  cases p with
  | none =>
    cases q with
    | none => simp [S0, Sdiag]
    | some ψ =>
      simp only [S0, Sdiag, Option.elim_none, Option.elim_some, mul_zero, zero_add, one_mul]
      rw [Finset.sum_eq_single ψ]
      · simp
      · intro φ _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  | some φ =>
    cases q with
    | none => simp [S0, Sdiag]
    | some ψ =>
      simp only [S0, Sdiag, Option.elim_none, Option.elim_some, mul_zero, zero_add]
      rw [Finset.sum_eq_single φ]
      · by_cases hEq : φ = ψ
        · subst hEq; simp
        · simp [hEq]
      · intro χ _ hne; simp [Ne.symm hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot

def QSmat {j : ℕ} (ψ : Fin j → ZMod 2) : Matrix (IdxTop j) (IdxTop j) ℚ :=
  ((2 ^ j : ℕ) : ℚ)⁻¹ • ∑ h : Fin j → ZMod 2, char ψ h • Sdiag h

lemma QSmat_zero (j : ℕ) :
    QSmat (0 : Fin j → ZMod 2) = Matrix.single (none : IdxTop j) none (1 : ℚ) := by
  have hz0 : ((2 ^ j : ℕ) : ℚ) ≠ 0 := by positivity
  ext p q
  simp only [QSmat, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, char_zero_left, one_mul, Matrix.single]
  cases p with
  | none =>
    cases q with
    | none =>
      simp only [Sdiag, Option.elim_none, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one, Matrix.of_apply, ite_true]
      exact inv_mul_cancel₀ hz0
    | some ψ => simp [Sdiag]
  | some φ =>
    cases q with
    | none => simp [Sdiag]
    | some ψ =>
      by_cases hEq : φ = ψ
      · subst hEq
        simp only [Sdiag, Option.elim_some, ite_true, Matrix.of_apply, reduceCtorEq, and_self, ite_false]
        rw [sum_char_right]; simp [φ.2]
      · simp [Sdiag, hEq]

lemma QSmat_ne_zero {j : ℕ} (ψ : Fin j → ZMod 2) (hψ : ψ ≠ 0) :
    QSmat ψ = Matrix.single (some ⟨ψ, hψ⟩ : IdxTop j) (some ⟨ψ, hψ⟩) (1 : ℚ) := by
  have hz0 : ((2 ^ j : ℕ) : ℚ) ≠ 0 := by positivity
  ext p q
  simp only [QSmat, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.single]
  cases p with
  | none =>
    cases q with
    | none =>
      simp only [Sdiag, Option.elim_none, mul_one, Matrix.of_apply, reduceCtorEq, and_self, ite_false]
      rw [sum_char_right]; simp [hψ]
    | some χ => simp [Sdiag]
  | some φ =>
    cases q with
    | none => simp [Sdiag]
    | some χ =>
      by_cases hφχ : φ = χ
      · subst hφχ
        simp only [Sdiag, Option.elim_some, ite_true, Matrix.of_apply, Option.some.injEq, and_self]
        have hrew : ∀ h : Fin j → ZMod 2, char ψ h * char φ.1 h = char (ψ + φ.1) h :=
          fun h => (char_add_left ψ φ.1 h).symm
        simp_rw [hrew, sum_char_right]
        have hiff : ψ + φ.1 = 0 ↔ φ = ⟨ψ, hψ⟩ := by
          constructor
          · intro h
            apply Subtype.ext
            have h1 := congrArg (ψ + ·) h
            rw [← add_assoc, zmod2_vec_add_self, zero_add, add_zero] at h1
            exact h1
          · rintro rfl; exact zmod2_vec_add_self ψ
        by_cases hEq : φ = ⟨ψ, hψ⟩
        · subst hEq; simp [zmod2_vec_add_self]
        · have hne : ψ + φ.1 ≠ 0 := fun h => hEq (hiff.mp h)
          simp [Ne.symm hEq, hne]
      · have hnot : ¬ ((⟨ψ, hψ⟩ : NZ j) = φ ∧ (⟨ψ, hψ⟩ : NZ j) = χ) := by
          rintro ⟨rfl, h2⟩; exact hφχ h2
        simp [Sdiag, hφχ, hnot]

lemma QSmat0_mul_S0_mul_QSmat {j : ℕ} (ψ : Fin j → ZMod 2) (hψ : ψ ≠ 0) :
    QSmat 0 * S0 j * QSmat ψ = Matrix.single (none : IdxTop j) (some ⟨ψ, hψ⟩) (1 : ℚ) := by
  rw [QSmat_zero, QSmat_ne_zero ψ hψ]
  ext p q
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  cases p with
  | none =>
    cases q with
    | none =>
      refine Finset.sum_eq_zero fun x _ => by simp
    | some χ =>
      rw [Finset.sum_eq_single (some ⟨ψ, hψ⟩ : IdxTop j)]
      · rw [Finset.sum_eq_single (none : IdxTop j)]
        · by_cases hEq : χ = ⟨ψ, hψ⟩
          · subst hEq; simp [S0]
          · simp [Ne.symm hEq]
        · intro y _ hne; simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · intro x _ hne; simp [Ne.symm hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  | some φ =>
    simp

lemma QSmat_mul_S0_mul_QSmat0 {j : ℕ} (ψ : Fin j → ZMod 2) (hψ : ψ ≠ 0) :
    QSmat ψ * S0 j * QSmat 0 = Matrix.single (some ⟨ψ, hψ⟩ : IdxTop j) none (1 : ℚ) := by
  rw [QSmat_zero, QSmat_ne_zero ψ hψ]
  ext p q
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  cases q with
  | some χ =>
    simp only [reduceCtorEq, and_false, ite_false]
    refine Finset.sum_eq_zero fun x _ => by simp
  | none =>
    rw [Finset.sum_eq_single (none : IdxTop j)]
    · simp only [ite_true, mul_one, and_true]
      rw [Finset.sum_eq_single (some ⟨ψ, hψ⟩ : IdxTop j)]
      · by_cases hEq : p = some ⟨ψ, hψ⟩
        · subst hEq; simp [S0]
        · simp [Ne.symm hEq]
      · intro y _ hne; simp [Ne.symm hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · intro x _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma Fmat_block_decomp (j : ℕ) :
    let z : ℚ := ((2 ^ j : ℕ) : ℚ)
    let F : Matrix (Option (Fin j → ZMod 2)) (IdxTop j ⊕ Unit) ℚ := fun x col =>
      col.elim (fun s => s.elim (vecE x) (fun φ => vecV φ.1 x)) (fun _ => vecV 0 x)
    let Finv : Matrix (IdxTop j ⊕ Unit) (Option (Fin j → ZMod 2)) ℚ := fun row x =>
      row.elim (fun s => s.elim (vecE x) (fun φ => z⁻¹ * vecV φ.1 x)) (fun _ => z⁻¹ * vecV 0 x)
    Finv * F = 1 ∧ F * Finv = 1 ∧
    ∀ (w : List (Fin j → ZMod 2)),
      (∀ p q : IdxTop j, (Finv * (w.map (Tmat z)).prod * F) (Sum.inl p) (Sum.inl q) = (w.map Smat).prod p q) ∧
      (∀ q : IdxTop j, (Finv * (w.map (Tmat z)).prod * F) (Sum.inr ()) (Sum.inl q) = 0) ∧
      ((Finv * (w.map (Tmat z)).prod * F) (Sum.inr ()) (Sum.inr ()) = 1) := by
  intro z F Finv
  have hz0 : z ≠ 0 := by dsimp only [z]; positivity
  have hFinv_F : Finv * F = 1 := by
    ext r c
    rw [Matrix.mul_apply, Matrix.one_apply]
    cases r with
    | inl p =>
      cases p with
      | none =>
        cases c with
        | inl q =>
          cases q with
          | none => simp only [Finv, F, Sum.elim_inl, Option.elim_none, ite_true]; exact dot_EE
          | some ψ => simp only [Finv, F, Sum.elim_inl, Option.elim_none, Option.elim_some, Sum.inl.injEq, reduceCtorEq, ite_false]; exact dot_EV ψ.1
        | inr u =>
          cases u; simp only [Finv, F, Sum.elim_inl, Sum.elim_inr, Option.elim_none, reduceCtorEq, ite_false]; exact dot_EV 0
      | some φ =>
        cases c with
        | inl q =>
          cases q with
          | none =>
            simp only [Finv, F, Sum.elim_inl, Option.elim_some, Option.elim_none, Sum.inl.injEq, reduceCtorEq, ite_false]
            have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV φ.1 x * vecE x) =
                z⁻¹ * ∑ x : Option (Fin j → ZMod 2), vecV φ.1 x * vecE x := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
            rw [h1, dot_VE, mul_zero]
          | some ψ =>
            simp only [Finv, F, Sum.elim_inl, Option.elim_some, Sum.inl.injEq, Option.some.injEq]
            have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV φ.1 x * vecV ψ.1 x) =
                z⁻¹ * ∑ x : Option (Fin j → ZMod 2), vecV φ.1 x * vecV ψ.1 x := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
            rw [h1, dot_VV]
            by_cases hEq : φ = ψ
            · subst hEq; simp [z]
            · have hne : φ.1 ≠ ψ.1 := fun h => hEq (Subtype.ext h)
              simp [hEq, hne]
        | inr u =>
          cases u
          simp only [Finv, F, Sum.elim_inl, Sum.elim_inr, Option.elim_some, reduceCtorEq, ite_false]
          have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV φ.1 x * vecV 0 x) =
              z⁻¹ * ∑ x : Option (Fin j → ZMod 2), vecV φ.1 x * vecV 0 x := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
          rw [h1, dot_VV]; simp [φ.2]
    | inr u =>
      cases u
      cases c with
      | inl q =>
        cases q with
        | none =>
          simp only [Finv, F, Sum.elim_inr, Sum.elim_inl, Option.elim_none, reduceCtorEq, ite_false]
          have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV 0 x * vecE x) =
              z⁻¹ * ∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecE x := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
          rw [h1, dot_VE, mul_zero]
        | some ψ =>
          simp only [Finv, F, Sum.elim_inr, Sum.elim_inl, Option.elim_some, reduceCtorEq, ite_false]
          have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV 0 x * vecV ψ.1 x) =
              z⁻¹ * ∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecV ψ.1 x := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
          rw [h1, dot_VV]; simp [Ne.symm ψ.2]
      | inr v =>
        cases v
        simp only [Finv, F, Sum.elim_inr, ite_true]
        have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV 0 x * vecV 0 x) =
            z⁻¹ * ∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecV 0 x := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
        rw [h1, dot_VV]; simp [z]
  have hF_Finv : F * Finv = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ k : IdxTop j ⊕ Unit, F x k * Finv k y) = _
    rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_unique (ι := Unit)]
    cases x with
    | none =>
      cases y with
      | none => simp [F, Finv, vecE, vecV]
      | some b => simp [F, Finv, vecE, vecV]
    | some a =>
      cases y with
      | none => simp [F, Finv, vecE, vecV]
      | some b =>
        simp only [F, Finv, Sum.elim_inl, Sum.elim_inr, Option.elim_none, Option.elim_some,
          vecE, vecV, mul_zero, zero_add, Option.some.injEq]
        have hcomb : (∑ φ : NZ j, char φ.1 a * (z⁻¹ * char φ.1 b)) + char 0 a * (z⁻¹ * char 0 b) =
            z⁻¹ * ∑ φ : Fin j → ZMod 2, char φ (a + b) := by
          rw [← Finset.add_sum_erase Finset.univ (fun φ => char φ (a + b)) (Finset.mem_univ (0 : Fin j → ZMod 2))]
          rw [mul_add, Finset.mul_sum, add_comm]
          congr 1
          · rw [char_add_right]; ring
          · rw [Finset.sum_subtype (p := fun φ : Fin j → ZMod 2 => φ ≠ 0)
              (Finset.univ.erase (0 : Fin j → ZMod 2))
              (fun φ => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
              (fun φ => z⁻¹ * char φ (a + b))]
            refine Finset.sum_congr rfl fun φ _ => by rw [char_add_right]; ring
        rw [hcomb, sum_char_left]
        have hiff : a + b = 0 ↔ a = b := by
          constructor
          · intro h; have := congrArg (· + b) h; simpa [add_assoc, zmod2_vec_add_self] using this
          · rintro rfl; exact zmod2_vec_add_self a
        by_cases hEq : a = b
        · subst hEq; simp [z, zmod2_vec_add_self, inv_mul_cancel₀ hz0]
        · have hne : a + b ≠ 0 := fun h => hEq (hiff.mp h)
          simp [hEq, hne]
  have hsingle : ∀ h : Fin j → ZMod 2,
      (∀ p q : IdxTop j, (Finv * Tmat z h * F) (Sum.inl p) (Sum.inl q) = Smat h p q) ∧
      (∀ q : IdxTop j, (Finv * Tmat z h * F) (Sum.inr ()) (Sum.inl q) = 0) ∧
      ((Finv * Tmat z h * F) (Sum.inr ()) (Sum.inr ()) = 1) := by
    intro h
    have hTF_col : ∀ (x : Option (Fin j → ZMod 2)) (c : IdxTop j ⊕ Unit),
        (Tmat z h * F) x c =
        match c with
        | Sum.inl none => x.elim 1 (fun a => if a = 0 then z - 1 else -1)
        | Sum.inl (some ψ) => char ψ.1 h * (vecE x + vecV ψ.1 x)
        | Sum.inr () => vecE x + vecV 0 x := by
      intro x c
      rw [Matrix.mul_apply, Fintype.sum_option]
      cases c with
      | inl q =>
        cases q with
        | none =>
          cases x <;> simp [Tmat, F, vecE, vecV]
        | some ψ =>
          cases x with
          | none =>
            simp only [Tmat, F, Sum.elim_inl, Option.elim_none, Option.elim_some, vecE, vecV,
              mul_zero, zero_add, add_zero, mul_one]
            rw [Finset.sum_eq_single h]
            · simp
            · intro b _ hne; simp [hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          | some a =>
            simp only [Tmat, F, Sum.elim_inl, Option.elim_none, Option.elim_some, vecE, vecV,
              mul_zero, zero_add]
            rw [Finset.sum_eq_single (a + h)]
            · simp [char_add_right, mul_comm]
            · intro b _ hne; simp [hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
      | inr u =>
        cases u
        cases x with
        | none =>
          simp only [Tmat, F, Sum.elim_inr, Option.elim_none, Option.elim_some, vecE, vecV,
            mul_zero, zero_add, add_zero, char_zero_left]
          rw [Finset.sum_eq_single h]
          · simp
          · intro b _ hne; simp [hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        | some a =>
          simp only [Tmat, F, Sum.elim_inr, Option.elim_none, Option.elim_some, vecE, vecV,
            mul_zero, zero_add, char_zero_left]
          rw [Finset.sum_eq_single (a + h)]
          · simp
          · intro b _ hne; simp [hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
    have hmul_assoc : Finv * Tmat z h * F = Finv * (Tmat z h * F) := Matrix.mul_assoc ..
    rw [hmul_assoc]
    refine ⟨?_, ?_, ?_⟩
    · intro p q
      rw [Matrix.mul_apply, Smat_apply]
      simp_rw [hTF_col]
      cases p with
      | none =>
        cases q with
        | none =>
          rw [Fintype.sum_option]; simp [Finv, vecE]
        | some ψ =>
          have h1 : (∑ x : Option (Fin j → ZMod 2), vecE x * (char ψ.1 h * (vecE x + vecV ψ.1 x))) =
              char ψ.1 h * ((∑ x : Option (Fin j → ZMod 2), vecE x * vecE x) +
                ∑ x : Option (Fin j → ZMod 2), vecE x * vecV ψ.1 x) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          simp only [Finv, Sum.elim_inl, Option.elim_none, Option.elim_some]
          rw [h1, dot_EE, dot_EV]; ring
      | some φ =>
        cases q with
        | none =>
          rw [Fintype.sum_option]
          simp only [Finv, Sum.elim_inl, Option.elim_some, Option.elim_none, vecV, mul_zero]
          have hsum : (∑ a : Fin j → ZMod 2, char φ.1 a * (if a = 0 then z - 1 else -1)) = z := by
            have hrew : ∀ a : Fin j → ZMod 2,
                char φ.1 a * (if a = 0 then z - 1 else -1) = (if a = 0 then z else 0) - char φ.1 a := fun a => by
              by_cases ha : a = 0
              · subst ha; simp [char_zero_right]
              · simp [ha]
            simp_rw [hrew, Finset.sum_sub_distrib, sum_char_right]
            simp only [φ.2, ite_false, sub_zero]
            rw [Finset.sum_eq_single (0 : Fin j → ZMod 2)]
            · simp
            · intro a _ hne; simp [hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          have hfac : (∑ a : Fin j → ZMod 2, z⁻¹ * char φ.1 a * (if a = 0 then z - 1 else -1)) =
              z⁻¹ * ∑ a : Fin j → ZMod 2, char φ.1 a * (if a = 0 then z - 1 else -1) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
          rw [hfac, hsum, inv_mul_cancel₀ hz0]; ring
        | some ψ =>
          simp only [Finv, Sum.elim_inl, Option.elim_some]
          have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV φ.1 x * (char ψ.1 h * (vecE x + vecV ψ.1 x))) =
              z⁻¹ * char ψ.1 h * ((∑ x, vecV φ.1 x * vecE x) + ∑ x, vecV φ.1 x * vecV ψ.1 x) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          rw [h1, dot_VE, dot_VV, zero_add]
          by_cases hEq : φ = ψ
          · subst hEq; simp only [ite_true]; change z⁻¹ * char φ.1 h * z = char φ.1 h
            rw [mul_comm (z⁻¹), mul_assoc, inv_mul_cancel₀ hz0, mul_one]
          · have hne : φ.1 ≠ ψ.1 := fun h1 => hEq (Subtype.ext h1)
            simp [hEq, hne]
    · intro q
      rw [Matrix.mul_apply]
      simp_rw [hTF_col]
      cases q with
      | none =>
        rw [Fintype.sum_option]
        simp only [Finv, Sum.elim_inr, Option.elim_none, Option.elim_some, vecV, mul_zero, zero_add,
          char_zero_left, mul_one]
        have hsum : (∑ a : Fin j → ZMod 2, (if a = 0 then z - 1 else -1 : ℚ)) = 0 := by
          have hrew : ∀ a : Fin j → ZMod 2,
              (if a = 0 then z - 1 else -1 : ℚ) = (if a = 0 then z else 0) - 1 := fun a => by
            by_cases ha : a = 0 <;> simp [ha]
          simp_rw [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one]
          rw [Finset.sum_eq_single (0 : Fin j → ZMod 2)]
          · simp [z]
          · intro a _ hne; simp [hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        rw [← Finset.mul_sum, hsum, mul_zero]
      | some ψ =>
        simp only [Finv, Sum.elim_inr]
        have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV 0 x * (char ψ.1 h * (vecE x + vecV ψ.1 x))) =
            z⁻¹ * char ψ.1 h * ((∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecE x) +
              ∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecV ψ.1 x) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [h1, dot_VE, dot_VV]; simp [Ne.symm ψ.2]
    · rw [Matrix.mul_apply]
      simp_rw [hTF_col]
      simp only [Finv, Sum.elim_inr]
      have h1 : (∑ x : Option (Fin j → ZMod 2), z⁻¹ * vecV 0 x * (vecE x + vecV 0 x)) =
          z⁻¹ * ((∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecE x) +
            ∑ x : Option (Fin j → ZMod 2), vecV 0 x * vecV 0 x) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [h1, dot_VE, dot_VV]; simp [z, inv_mul_cancel₀ hz0]
  refine ⟨hFinv_F, hF_Finv, ?_⟩
  intro w
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.mul_one, hFinv_F]
    refine ⟨fun p q => by simp [Matrix.one_apply], fun q => by simp [Matrix.one_apply], by simp [Matrix.one_apply]⟩
  | cons h t ih =>
    rcases hsingle h with ⟨hs_tl, hs_bl, hs_br⟩
    rcases ih with ⟨it_tl, it_bl, it_br⟩
    have hsplit : Finv * ((h :: t).map (Tmat z)).prod * F =
        (Finv * Tmat z h * F) * (Finv * (t.map (Tmat z)).prod * F) := by
      simp only [List.map_cons, List.prod_cons]
      calc Finv * (Tmat z h * (t.map (Tmat z)).prod) * F
          = Finv * (Tmat z h * (1 * (t.map (Tmat z)).prod)) * F := by rw [Matrix.one_mul]
        _ = Finv * (Tmat z h * ((F * Finv) * (t.map (Tmat z)).prod)) * F := by rw [hF_Finv]
        _ = (Finv * Tmat z h * F) * (Finv * (t.map (Tmat z)).prod * F) := by simp only [Matrix.mul_assoc]
    rw [hsplit]
    refine ⟨?_, ?_, ?_⟩
    · intro p q
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Matrix.mul_apply]
      change (∑ k : IdxTop j ⊕ Unit, _) = _
      rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
      simp_rw [hs_tl, it_tl, it_bl, mul_zero, add_zero]
    · intro q
      rw [Matrix.mul_apply]
      change (∑ k : IdxTop j ⊕ Unit, _) = 0
      rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
      simp_rw [hs_bl, it_bl, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · rw [Matrix.mul_apply]
      change (∑ k : IdxTop j ⊕ Unit, _) = 1
      rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
      simp_rw [hs_bl, zero_mul, Finset.sum_const_zero, zero_add, hs_br, it_br, mul_one]

lemma trace_Tmat_eq_one_add_trace_Smat {j : ℕ} (w : List (Fin j → ZMod 2)) :
    Matrix.trace (w.map (Tmat ((2 ^ j : ℕ) : ℚ))).prod = Matrix.trace (w.map Smat).prod + 1 := by
  let z : ℚ := ((2 ^ j : ℕ) : ℚ)
  let F : Matrix (Option (Fin j → ZMod 2)) (IdxTop j ⊕ Unit) ℚ := fun x col =>
    col.elim (fun s => s.elim (vecE x) (fun φ => vecV φ.1 x)) (fun _ => vecV 0 x)
  let Finv : Matrix (IdxTop j ⊕ Unit) (Option (Fin j → ZMod 2)) ℚ := fun row x =>
    row.elim (fun s => s.elim (vecE x) (fun φ => z⁻¹ * vecV φ.1 x)) (fun _ => z⁻¹ * vecV 0 x)
  rcases Fmat_block_decomp j with ⟨_, hF_Finv, hw⟩
  rcases hw w with ⟨htl, _, hbr⟩
  have htr : Matrix.trace (w.map (Tmat z)).prod = Matrix.trace (Finv * (w.map (Tmat z)).prod * F) := by
    calc Matrix.trace (w.map (Tmat z)).prod
        = Matrix.trace ((w.map (Tmat z)).prod * 1) := by rw [Matrix.mul_one]
      _ = Matrix.trace ((w.map (Tmat z)).prod * (F * Finv)) := by rw [hF_Finv]
      _ = Matrix.trace (((w.map (Tmat z)).prod * F) * Finv) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (Finv * ((w.map (Tmat z)).prod * F)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Finv * (w.map (Tmat z)).prod * F) := by rw [Matrix.mul_assoc]
  rw [htr]
  simp only [Matrix.trace, Matrix.diag]
  change (∑ k : IdxTop j ⊕ Unit, (Finv * (w.map (Tmat z)).prod * F) k k) = _
  rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit), hbr]
  congr 1
  exact Finset.sum_congr rfl fun p _ => htl p p

lemma S0_cubic (j : ℕ) :
    let z : ℚ := ((2 ^ j : ℕ) : ℚ)
    S0 j * S0 j * S0 j - (3 : ℚ) • (S0 j * S0 j) + (4 - z) • S0 j = (2 - z) • (1 : Matrix (IdxTop j) (IdxTop j) ℚ) := by
  intro z
  let T0 : Matrix (Option (Fin j → ZMod 2)) (Option (Fin j → ZMod 2)) ℚ := Tmat z 0
  let F : Matrix (Option (Fin j → ZMod 2)) (IdxTop j ⊕ Unit) ℚ := fun x col =>
    col.elim (fun s => s.elim (vecE x) (fun φ => vecV φ.1 x)) (fun _ => vecV 0 x)
  let Finv : Matrix (IdxTop j ⊕ Unit) (Option (Fin j → ZMod 2)) ℚ := fun row x =>
    row.elim (fun s => s.elim (vecE x) (fun φ => z⁻¹ * vecV φ.1 x)) (fun _ => z⁻¹ * vecV 0 x)
  rcases Fmat_block_decomp j with ⟨hFinv_F, _, hw⟩
  have h1 := (hw [0]).1
  have h2 := (hw [0, 0]).1
  have h3 := (hw [0, 0, 0]).1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one, Smat_zero] at h1 h2 h3
  have hcub : T0 * T0 * T0 - (3 : ℚ) • (T0 * T0) + (4 - z) • T0 = (2 - z) • 1 := T0_cubic (r := j) z
  have hconj : Finv * (T0 * T0 * T0 - (3 : ℚ) • (T0 * T0) + (4 - z) • T0) * F =
      Finv * ((2 - z) • (1 : Matrix (Option (Fin j → ZMod 2)) (Option (Fin j → ZMod 2)) ℚ)) * F := by
    rw [hcub]
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hFinv_F] at hconj
  ext p q
  have hent := congrFun (congrFun hconj (Sum.inl p)) (Sum.inl q)
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hent ⊢
  have hp3 : (Finv * (T0 * T0 * T0) * F) (Sum.inl p) (Sum.inl q) = (S0 j * S0 j * S0 j) p q := by
    rw [Matrix.mul_assoc T0 T0 T0]
    exact (h3 p q).trans (by rw [Matrix.mul_assoc])
  have hp2 : (Finv * (T0 * T0) * F) (Sum.inl p) (Sum.inl q) = (S0 j * S0 j) p q := h2 p q
  have hp1 : (Finv * T0 * F) (Sum.inl p) (Sum.inl q) = S0 j p q := h1 p q
  have h1eq : (1 : Matrix (IdxTop j ⊕ Unit) (IdxTop j ⊕ Unit) ℚ) (Sum.inl p) (Sum.inl q) =
      (1 : Matrix (IdxTop j) (IdxTop j) ℚ) p q := by
    simp [Matrix.one_apply]
  rw [hp3, hp2, hp1, h1eq] at hent
  exact hent

open Classical in
lemma sum_char_projD_eq {m : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (D : Submodule (ZMod 2) (Fin m → ZMod 2)) (f : (Fin (codimD D) → ZMod 2) → M)
    (ψ : Fin m → ZMod 2) :
    ((2 ^ m : ℕ) : ℚ)⁻¹ • ∑ h : Fin m → ZMod 2, char ψ h • f (projD D h) =
    if hψ : ψ ∈ perp D then
      ((2 ^ codimD D : ℕ) : ℚ)⁻¹ • ∑ y : Fin (codimD D) → ZMod 2,
        char (Classical.choose ((mem_perp_iff_exists_dualProjD D ψ).mp hψ)) y • f y
    else 0 := by
  let A := Fin m → ZMod 2
  let r := codimD D
  let π := projD D
  have hfib : (∑ h : A, char ψ h • f (π h)) =
      ∑ y : Fin r → ZMod 2, ∑ h ∈ Finset.univ.filter (fun h : A => π h = y), char ψ h • f y := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset A))
      (t := (Finset.univ : Finset (Fin r → ZMod 2))) (g := fun h => π h)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun h hh => ?_
    rw [(Finset.mem_filter.mp hh).2]
  rw [hfib]
  have hper_y : ∀ y : Fin r → ZMod 2,
      (∑ h ∈ Finset.univ.filter (fun h : A => π h = y), char ψ h • f y) =
      (if hψ : ψ ∈ perp D then
        ((2 ^ Module.finrank (ZMod 2) D : ℕ) : ℚ) *
          char (Classical.choose ((mem_perp_iff_exists_dualProjD D ψ).mp hψ)) y
      else 0) • f y := by
    intro y
    rw [← Finset.sum_smul]
    congr 1
    obtain ⟨h₀, hh₀⟩ := projD_surjective D y
    let : Fintype D := Fintype.ofFinite _
    have hsum_eq : (∑ h ∈ Finset.univ.filter (fun h : A => π h = y), char ψ h) =
        ∑ d : D, char ψ (h₀ + d.1) := by
      symm
      refine Finset.sum_bij (fun d _ => h₀ + d.1)
        (fun d _ => by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hd0 : π d.1 = 0 := by
            have : d.1 ∈ LinearMap.ker (projD D) := by rw [ker_projD]; exact d.2
            exact this
          rw [map_add, hh₀, hd0, add_zero])
        (fun d₁ _ d₂ _ heq => by
          apply Subtype.ext
          have h1 := congrArg (h₀ + ·) heq
          simpa [← add_assoc, zmod2_vec_add_self] using h1)
        (fun h hh => by
          have hπ : π h = y := (Finset.mem_filter.mp hh).2
          have hmemD : h₀ + h ∈ D := by
            rw [← ker_projD D, LinearMap.mem_ker, map_add, hh₀, hπ, zmod2_vec_add_self]
          exact ⟨⟨h₀ + h, hmemD⟩, Finset.mem_univ _, by rw [← add_assoc, zmod2_vec_add_self, zero_add]⟩)
        (fun _ _ => rfl)
    rw [hsum_eq]
    have hfac : (∑ d : D, char ψ (h₀ + d.1)) = char ψ h₀ * ∑ d : D, char ψ d.1 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => char_add_right ψ h₀ d.1
    rw [hfac]
    have hsub : (∑ d : D, char ψ d.1) = if ψ ∈ perp D then ((2 ^ Module.finrank (ZMod 2) D : ℕ) : ℚ) else 0 := by
      have h1 := sum_char_subspace D ψ
      have h2 : (∑ d : D, char ψ d.1) = ∑ d : D, char d.1 ψ :=
        Finset.sum_congr rfl fun d _ => char_comm ψ d.1
      rw [h2, h1]
    rw [hsub]
    by_cases hψ : ψ ∈ perp D
    · simp only [hψ, ↓reduceDIte, ite_true]
      set φ := Classical.choose ((mem_perp_iff_exists_dualProjD D ψ).mp hψ)
      have hch : dualProjD D φ = ψ := Classical.choose_spec ((mem_perp_iff_exists_dualProjD D ψ).mp hψ)
      have hcEq : char ψ h₀ = char φ y := by
        rw [← hch, char_dualProjD, hh₀]
      rw [hcEq, mul_comm]
    · simp [hψ]
  simp_rw [hper_y]
  by_cases hψ : ψ ∈ perp D
  · simp only [hψ, ↓reduceDIte]
    have hpow : ((2 ^ m : ℕ) : ℚ)⁻¹ * ((2 ^ Module.finrank (ZMod 2) D : ℕ) : ℚ) = ((2 ^ r : ℕ) : ℚ)⁻¹ := by
      have hm_eq : Module.finrank (ZMod 2) D + r = m := by
        have hle := Submodule.finrank_le D
        rw [Module.finrank_fin_fun] at hle
        dsimp only [r, codimD]; omega
      have hnat : 2 ^ m = 2 ^ Module.finrank (ZMod 2) D * 2 ^ r := by
        rw [← pow_add, hm_eq]
      have hcast : ((2 ^ m : ℕ) : ℚ) = ((2 ^ Module.finrank (ZMod 2) D : ℕ) : ℚ) * ((2 ^ r : ℕ) : ℚ) := by
        exact_mod_cast hnat
      have h1 : ((2 ^ Module.finrank (ZMod 2) D : ℕ) : ℚ) ≠ 0 := by positivity
      have h2 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
      rw [hcast]
      field_simp [h1, h2]
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul, smul_smul, ← mul_assoc, hpow]
  · simp [hψ]

open Classical in
lemma sum_coeffD_cycleD_decomp {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2))
    (hY : Y ≠ 0) (w : List (Fin m → ZMod 2)) :
    letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
    let A := Fin m → ZMod 2
    let z : ℚ := ((2 ^ j : ℕ) : ℚ)
    let SubD := {D : Submodule (ZMod 2) A // 0 < codimD D ∧ codimD D < j}
    let TopD := {D : Submodule (ZMod 2) A // codimD D = j}
    let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
    let Schar : Finset A := if m < j ∧ 2 ≤ rankY then Finset.univ.erase 0 else Finset.univ
    (∑ D : Submodule (ZMod 2) A, coeffD Y D * cycleD D z w) =
      coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod +
      (∑ D : SubD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Tmat z (projD D.1 h))).prod) +
      (∑ D : TopD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Smat (castVec D.2 (projD D.1 h)))).prod) +
      (∑ α ∈ Schar, (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum) := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  intro A z SubD TopD rankY Schar
  let rem : Submodule (ZMod 2) A → ℚ := fun D =>
    if codimD D ≤ j then
      (if projD D w.sum = 0 then z - 1 else -1) -
        (if projD D w.sum = 0 then ((2 ^ codimD D : ℕ) : ℚ) else 0)
    else 0
  let main : Submodule (ZMod 2) A → ℚ := fun D =>
    if h0 : codimD D = 0 then tr0 (w.map (fun _ => X0 z)).prod
    else if hlt : codimD D < j then Matrix.trace (w.map (fun h => Tmat z (projD D h))).prod
    else if heq : codimD D = j then Matrix.trace (w.map (fun h => Smat (castVec heq (projD D h)))).prod + 1
    else 0
  have hterm : ∀ D : Submodule (ZMod 2) A,
      coeffD Y D * cycleD D z w = coeffD Y D * main D + coeffD Y D * rem D := by
    intro D
    by_cases hgt : j < codimD D
    · have hc0 : coeffD Y D = 0 := coeffD_eq_zero_of_lt Y D hgt
      simp [hc0]
    · have hle : codimD D ≤ j := by omega
      rw [← mul_add]
      congr 1
      dsimp only [cycleD, main, rem]
      simp only [hle, ite_true]
      by_cases h0 : codimD D = 0
      · simp only [h0, ↓reduceDIte]
        have htr := trace_Tmat_zero_eq_tr0 h0 z (w.map (projD D))
        rw [List.map_map, List.map_map] at htr
        have htr' : Matrix.trace (w.map (fun h => Tmat z (projD D h))).prod =
            tr0 (w.map (fun _ => X0 z)).prod := htr
        rw [htr']; ring
      · simp only [h0, ↓reduceDIte]
        by_cases hlt : codimD D < j
        · simp only [hlt, ↓reduceDIte]; ring
        · have heq : codimD D = j := by omega
          simp only [hlt, ↓reduceDIte]
          simp only [heq, ↓reduceDIte]
          have h1 := trace_Tmat_castVec heq z (w.map (projD D))
          have h2 := trace_Tmat_eq_one_add_trace_Smat (j := j) (w.map (fun h => castVec heq (projD D h)))
          rw [List.map_map, List.map_map] at h1 h2
          have h1' : Matrix.trace (w.map (fun h => Tmat z (castVec heq (projD D h)))).prod =
              Matrix.trace (w.map (fun h => Tmat z (projD D h))).prod := h1
          have h2' : Matrix.trace (w.map (fun h => Tmat z (castVec heq (projD D h)))).prod =
              Matrix.trace (w.map (fun h => Smat (castVec heq (projD D h)))).prod + 1 := h2
          rw [← h1', h2']; ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have hmain_split : (∑ D : Submodule (ZMod 2) A, coeffD Y D * main D) =
      coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod +
      (∑ D : SubD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Tmat z (projD D.1 h))).prod) +
      (∑ D : TopD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Smat (castVec D.2 (projD D.1 h)))).prod) +
      (∑ D : TopD, coeffD Y D.1) := by
    have hcodim0_iff : ∀ D : Submodule (ZMod 2) A, codimD D = 0 ↔ D = ⊤ := fun D => by
      constructor
      · intro h0
        have hle : Module.finrank (ZMod 2) D ≤ m := by
          have := Submodule.finrank_le D
          rwa [Module.finrank_fin_fun] at this
        have h0' : m - Module.finrank (ZMod 2) D = 0 := h0
        have hfr : Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) A := by
          rw [Module.finrank_fin_fun]; omega
        exact Submodule.eq_top_of_finrank_eq hfr
      · rintro rfl
        change m - Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin m → ZMod 2)) = 0
        rw [finrank_top, Module.finrank_fin_fun]; omega
    have hrew : ∀ D : Submodule (ZMod 2) A,
        coeffD Y D * main D =
        (if D = ⊤ then coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod else 0) +
        (if 0 < codimD D ∧ codimD D < j then coeffD Y D * Matrix.trace (w.map (fun h => Tmat z (projD D h))).prod else 0) +
        (if heq : codimD D = j then coeffD Y D * Matrix.trace (w.map (fun x => Smat (castVec heq (projD D x)))).prod + coeffD Y D else 0) := by
      intro D
      dsimp only [main]
      by_cases h0 : codimD D = 0
      · have htop : D = ⊤ := (hcodim0_iff D).mp h0
        subst htop
        have hj0 : (0 : ℕ) ≠ j := by omega
        simp [h0, hj0]
      · have hntop : D ≠ ⊤ := fun h => h0 ((hcodim0_iff D).mpr h)
        by_cases hlt : codimD D < j
        · have hpos : 0 < codimD D := Nat.pos_of_ne_zero h0
          have hne : codimD D ≠ j := by omega
          simp [h0, hntop, hlt, hpos, hne]
        · by_cases heq : codimD D = j
          · simp only [h0, hntop, hlt, ↓reduceDIte, ite_false, zero_add]
            simp only [heq, ↓reduceDIte, lt_self_iff_false, and_false, ite_false, add_zero]
            ring
          · simp [h0, hntop, hlt, heq]
    simp_rw [hrew, Finset.sum_add_distrib]
    have hs1 : (∑ D : Submodule (ZMod 2) A, if D = ⊤ then coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod else 0) =
        coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod := by
      rw [Finset.sum_eq_single (⊤ : Submodule (ZMod 2) A)]
      · simp
      · intro D _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    have hs2 : (∑ D : Submodule (ZMod 2) A, if 0 < codimD D ∧ codimD D < j then
          coeffD Y D * Matrix.trace (w.map (fun h => Tmat z (projD D h))).prod else 0) =
        ∑ D : SubD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Tmat z (projD D.1 h))).prod := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (p := fun D : Submodule (ZMod 2) A => 0 < codimD D ∧ codimD D < j)
        (Finset.univ.filter _) (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
    have hs3 : (∑ D : Submodule (ZMod 2) A, if heq : codimD D = j then
          coeffD Y D * Matrix.trace (w.map (fun x => Smat (castVec heq (projD D x)))).prod + coeffD Y D else 0) =
        (∑ D : TopD, coeffD Y D.1 * Matrix.trace (w.map (fun x => Smat (castVec D.2 (projD D.1 x)))).prod) +
        ∑ D : TopD, coeffD Y D.1 := by
      rw [← Finset.sum_add_distrib]
      have hfilt : (∑ D : Submodule (ZMod 2) A, if heq : codimD D = j then
            coeffD Y D * Matrix.trace (w.map (fun x => Smat (castVec heq (projD D x)))).prod + coeffD Y D else 0) =
          ∑ D ∈ Finset.univ.filter (fun D : Submodule (ZMod 2) A => codimD D = j),
            if heq : codimD D = j then
              coeffD Y D * Matrix.trace (w.map (fun x => Smat (castVec heq (projD D x)))).prod + coeffD Y D else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun D _ => by by_cases h : codimD D = j <;> simp [h]
      rw [hfilt]
      rw [Finset.sum_subtype (p := fun D : Submodule (ZMod 2) A => codimD D = j)
        (Finset.univ.filter _) (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _]
      refine Finset.sum_congr rfl fun D _ => by simp [D.2]
    rw [hs1, hs2, hs3]
    ring
  have hrem_eq : (∑ D : TopD, coeffD Y D.1) + (∑ D : Submodule (ZMod 2) A, coeffD Y D * rem D) =
      ∑ α ∈ Schar, (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum := by
    have hrem_D : ∀ D : Submodule (ZMod 2) A,
        (if codimD D = j then coeffD Y D else 0) + coeffD Y D * rem D =
        coeffD Y D * ∑ α : A,
          (if α = 0 then (if codimD D < j then (2 : ℚ) ^ (j - codimD D) - 2 else 0)
           else if α ∈ perp D then (2 : ℚ) ^ (j - codimD D) - 1 else 0) * char α w.sum := by
      intro D
      by_cases hgt : j < codimD D
      · have hc0 : coeffD Y D = 0 := coeffD_eq_zero_of_lt Y D hgt
        simp [hc0]
      · have hle : codimD D ≤ j := by omega
        dsimp only [rem]
        simp only [hle, ite_true]
        have hf := fourier_remainder hle (projD D w.sum)
        dsimp only [z]
        rw [hf]
        have hbij : (∑ φ : Fin (codimD D) → ZMod 2,
              (if φ = 0 then (2 : ℚ) ^ (j - codimD D) - 2 else (2 : ℚ) ^ (j - codimD D) - 1) * char φ (projD D w.sum)) =
            ∑ α : A, (if α = 0 then (2 : ℚ) ^ (j - codimD D) - 2
              else if α ∈ perp D then (2 : ℚ) ^ (j - codimD D) - 1 else 0) * char α w.sum := by
          rw [← Finset.sum_subset (s₁ := Finset.univ.image (dualProjD D)) (Finset.subset_univ _)]
          · rw [Finset.sum_image (fun φ₁ _ φ₂ _ heq => dualProjD_injective D heq)]
            refine Finset.sum_congr rfl fun φ _ => ?_
            rw [char_dualProjD]
            congr 1
            by_cases hφ0 : φ = 0
            · subst hφ0; simp
            · have hα0 : dualProjD D φ ≠ 0 := fun h => hφ0 (dualProjD_injective D (by simpa using h))
              have hmem : dualProjD D φ ∈ perp D := (mem_perp_iff_exists_dualProjD D _).mpr ⟨φ, rfl⟩
              simp [hφ0, hα0, hmem]
          · intro α _ hnot
            have hα0 : α ≠ 0 := by
              rintro rfl; apply hnot
              exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, map_zero _⟩
            have hnotmem : α ∉ perp D := by
              intro hm; apply hnot
              rcases (mem_perp_iff_exists_dualProjD D α).mp hm with ⟨φ, rfl⟩
              exact Finset.mem_image.mpr ⟨φ, Finset.mem_univ _, rfl⟩
            simp [hα0, hnotmem]
        rw [hbij]
        by_cases heq : codimD D = j
        · simp only [heq, ite_true, lt_self_iff_false, ite_false, Nat.sub_self, pow_zero]
          have hsL : (∑ α : A, (if α = 0 then (1 : ℚ) - 2 else if α ∈ perp D then 1 - 1 else 0) * char α w.sum) = -1 := by
            rw [Finset.sum_eq_single (0 : A)]
            · simp [char_zero_left]; norm_num
            · intro α _ hα0; simp [hα0]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          have hsR : (∑ α : A, (if α = 0 then (0 : ℚ) else if α ∈ perp D then 1 - 1 else 0) * char α w.sum) = 0 := by
            refine Finset.sum_eq_zero fun α _ => by by_cases hα0 : α = 0 <;> simp [hα0]
          rw [hsL, hsR]; ring
        · have hlt : codimD D < j := by omega
          simp only [heq, ite_false, zero_add, hlt, ite_true]
    have htop_sum : (∑ D : TopD, coeffD Y D.1) =
        ∑ D : Submodule (ZMod 2) A, if codimD D = j then coeffD Y D else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun D : Submodule (ZMod 2) A => codimD D = j)
        (Finset.univ.filter _) (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _).symm
    rw [htop_sum, ← Finset.sum_add_distrib]
    simp_rw [hrem_D]
    have hswap : (∑ D : Submodule (ZMod 2) A, coeffD Y D * ∑ α : A,
          (if α = 0 then (if codimD D < j then (2 : ℚ) ^ (j - codimD D) - 2 else 0)
           else if α ∈ perp D then (2 : ℚ) ^ (j - codimD D) - 1 else 0) * char α w.sum) =
        ∑ α : A, (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum := by
      calc (∑ D : Submodule (ZMod 2) A, coeffD Y D * ∑ α : A,
              (if α = 0 then (if codimD D < j then (2 : ℚ) ^ (j - codimD D) - 2 else 0)
               else if α ∈ perp D then (2 : ℚ) ^ (j - codimD D) - 1 else 0) * char α w.sum)
          = ∑ D : Submodule (ZMod 2) A, ∑ α : A,
              (coeffD Y D * (if α = 0 then (if codimD D < j then (2 : ℚ) ^ (j - codimD D) - 2 else 0)
               else if α ∈ perp D then (2 : ℚ) ^ (j - codimD D) - 1 else 0)) * char α w.sum := by
            refine Finset.sum_congr rfl fun D _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun α _ => by ring
        _ = ∑ α : A, (∑ D : Submodule (ZMod 2) A,
              coeffD Y D * (if α = 0 then (if codimD D < j then (2 : ℚ) ^ (j - codimD D) - 2 else 0)
               else if α ∈ perp D then (2 : ℚ) ^ (j - codimD D) - 1 else 0)) * char α w.sum := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun α _ => (Finset.sum_mul ..).symm
        _ = ∑ α : A, (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum := by
            refine Finset.sum_congr rfl fun α _ => ?_
            congr 1
            have hfibD : ∀ f : Submodule (ZMod 2) A → ℚ,
                (∑ D : Submodule (ZMod 2) A, coeffD Y D * f D) =
                ∑ Λ : Fin j → A, matChar Λ Y * f (LinearMap.ker (linOf Λ)) := fun f => by
              calc (∑ D : Submodule (ZMod 2) A, coeffD Y D * f D)
                  = ∑ D : Submodule (ZMod 2) A,
                      ∑ Λ ∈ Finset.univ.filter (fun Λ : Fin j → A => LinearMap.ker (linOf Λ) = D),
                        matChar Λ Y * f (LinearMap.ker (linOf Λ)) := by
                    refine Finset.sum_congr rfl fun D _ => ?_
                    dsimp only [coeffD]; rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun Λ hΛ => by rw [(Finset.mem_filter.mp hΛ).2]
                _ = ∑ Λ : Fin j → A, matChar Λ Y * f (LinearMap.ker (linOf Λ)) :=
                    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
            rw [hfibD]
            by_cases hα0 : α = 0
            · simp only [hα0, ite_true]; rfl
            · simp only [hα0, ite_false]
              dsimp only [kappa_nz_num]
              refine Finset.sum_congr rfl fun Λ _ => ?_
              rw [perp_ker_linOf Λ]
              have hcd : codimD (LinearMap.ker (linOf Λ)) = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Λ)) :=
                codim_ker_linOf Λ
              rw [hcd]
    rw [hswap]
    dsimp only [Schar]
    by_cases hcond : m < j ∧ 2 ≤ rankY
    · simp only [hcond, ite_true]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : A))]
      have hk0 : kappa0_num Y = 0 := (kappa0_num_eq_zero_iff hj Y hY).mpr hcond
      simp [hk0]
    · simp only [hcond, ite_false]
  rw [hmain_split]
  linarith

open Classical in
lemma card_idx_eq_least {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2)) :
    letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
    let A := Fin m → ZMod 2
    let SubD := {D : Submodule (ZMod 2) A // 0 < codimD D ∧ codimD D < j}
    let TopD := {D : Submodule (ZMod 2) A // codimD D = j}
    let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
    let Schar : Finset A := if m < j ∧ 2 ≤ rankY then Finset.univ.erase 0 else Finset.univ
    let I := Fin 2 ⊕
      (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
      (TopD × (IdxTop j × IdxTop j)) ⊕
      {α : A // α ∈ Schar}
    let blocks : ℕ := ∑ D : Submodule (ZMod 2) A,
      let r := m - Module.finrank (ZMod 2) D
      if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2
    Fintype.card I = 2 + 2 ^ m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0) := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  intro A SubD TopD rankY Schar I blocks
  have hSchar_card : Schar.card = 2 ^ m - (if m < j ∧ 2 ≤ rankY then 1 else 0) := by
    dsimp only [Schar]
    by_cases hcond : m < j ∧ 2 ≤ rankY
    · simp [hcond, A]
    · simp [hcond, A]
  have hblocks_eq : blocks =
      (∑ D : SubD, (2 ^ codimD D.1 + 1) ^ 2) + ∑ D : TopD, (2 ^ j) ^ 2 := by
    dsimp only [blocks]
    have hnat_split : ∀ r : ℕ,
        (if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2) =
        (if 0 < r ∧ r < j then (2 ^ r + 1) ^ 2 else 0) +
        (if r = j then (2 ^ j) ^ 2 else 0) := by
      intro r; split_ifs <;> first | rfl | omega | (simp_all)
    have hsplit : ∀ D : Submodule (ZMod 2) A,
        (let r := m - Module.finrank (ZMod 2) D
         if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2) =
        (if 0 < codimD D ∧ codimD D < j then (2 ^ codimD D + 1) ^ 2 else 0) +
        (if codimD D = j then (2 ^ j) ^ 2 else 0) :=
      fun D => hnat_split (m - Module.finrank (ZMod 2) D)
    simp_rw [hsplit, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_filter]
      exact Finset.sum_subtype (p := fun D : Submodule (ZMod 2) A => 0 < codimD D ∧ codimD D < j)
        (Finset.univ.filter _) (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
    · rw [← Finset.sum_filter]
      exact Finset.sum_subtype (p := fun D : Submodule (ZMod 2) A => codimD D = j)
        (Finset.univ.filter _) (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
  dsimp only [I]
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_prod, card_IdxTop, Fintype.card_coe, hSchar_card]
  have hsub_card : (∑ D : SubD, Fintype.card (Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2))) =
      ∑ D : SubD, (2 ^ codimD D.1 + 1) ^ 2 := by
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fun, Fintype.card_fin, ZMod.card, sq]
  have htop_card : Fintype.card TopD * (2 ^ j * 2 ^ j) = ∑ _D : TopD, (2 ^ j) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]
  rw [hsub_card, htop_card, hblocks_eq]
  have hpow_pos : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
  by_cases hcond : m < j ∧ 2 ≤ rankY
  · simp [hcond]; omega
  · simp [hcond]; omega

open Classical in
lemma upper_bound_jge2 {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2)) (hY : Y ≠ 0) :
    letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
    let A := Fin m → ZMod 2
    let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
    let blocks : ℕ := ∑ D : Submodule (ZMod 2) A,
      let r := m - Module.finrank (ZMod 2) D
      if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2
    let least : ℕ := 2 + 2 ^ m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0)
    ∃ (u v : Fin least → ℚ) (M : A → Matrix (Fin least) (Fin least) ℚ),
      ∀ w : List A, (∑ i : Fin least, ∑ l : Fin least, u i * (w.map M).prod i l * v l) = countVal Y w := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  intro A rankY blocks least
  let z : ℚ := ((2 ^ j : ℕ) : ℚ)
  let s : ℚ := ((2 ^ (m * j) : ℕ) : ℚ)⁻¹
  let SubD := {D : Submodule (ZMod 2) A // 0 < codimD D ∧ codimD D < j}
  let TopD := {D : Submodule (ZMod 2) A // codimD D = j}
  let Schar : Finset A := if m < j ∧ 2 ≤ rankY then Finset.univ.erase 0 else Finset.univ
  let I := Fin 2 ⊕
    (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
    (TopD × (IdxTop j × IdxTop j)) ⊕
    {α : A // α ∈ Schar}
  have hIcard : Fintype.card I = least := card_idx_eq_least hj Y
  let eI : Fin least ≃ I := (Fintype.equivFinOfCardEq hIcard).symm
  let M0 : Matrix (Fin 2) (Fin 2) ℚ := fun t₁ t₂ =>
    if t₁ = 0 then (if t₂ = 0 then 0 else 1) else (if t₂ = 0 then z - 2 else 2)
  have hM0_prod : ∀ (w : List A) (t₁ t₂ : Fin 2),
      let x := (w.map (fun _ => X0 z)).prod
      (w.map (fun _ => M0)).prod t₁ t₂ =
      if t₁ = 0 then (if t₂ = 0 then x.a else x.b)
      else (if t₂ = 0 then (z - 2) * x.b else x.a + 2 * x.b) := by
    intro w
    induction w with
    | nil =>
      intro t₁ t₂
      fin_cases t₁ <;> fin_cases t₂ <;> simp [Matrix.one_apply]
    | cons h t ih =>
      intro t₁ t₂
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two]
      rw [ih 0 t₂, ih 1 t₂]
      fin_cases t₁ <;> fin_cases t₂ <;> simp [M0, X0] <;> ring
  let uI : I → ℚ := fun x =>
    match x with
    | Sum.inl t => if t = 0 then 1 else 0
    | Sum.inr (Sum.inl ⟨D, p, i⟩) => if p = i then s * coeffD Y D.1 else 0
    | Sum.inr (Sum.inr (Sum.inl (D, p, i))) => if p = i then s * coeffD Y D.1 else 0
    | Sum.inr (Sum.inr (Sum.inr α)) => s * (if α.1 = 0 then kappa0_num Y else kappa_nz_num Y α.1)
  let vI : I → ℚ := fun x =>
    match x with
    | Sum.inl _ => 2 * s * coeffD Y ⊤
    | Sum.inr (Sum.inl ⟨_, p, l⟩) => if p = l then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl (_, p, l))) => if p = l then 1 else 0
    | Sum.inr (Sum.inr (Sum.inr _)) => 1
  let subMat : A → (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) →
      (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) → ℚ :=
    fun h ⟨D₁, p₁, i⟩ ⟨D₂, p₂, l⟩ =>
      if hD : D₁ = D₂ then
        let p₂' : Option (Fin (codimD D₁.1) → ZMod 2) := hD ▸ p₂
        let l' : Option (Fin (codimD D₁.1) → ZMod 2) := hD ▸ l
        if p₁ = p₂' then Tmat z (projD D₁.1 h) i l' else 0
      else 0
  let subProd : List A → (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) →
      (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) → ℚ :=
    fun w ⟨D₁, p₁, i⟩ ⟨D₂, p₂, l⟩ =>
      if hD : D₁ = D₂ then
        let p₂' : Option (Fin (codimD D₁.1) → ZMod 2) := hD ▸ p₂
        let l' : Option (Fin (codimD D₁.1) → ZMod 2) := hD ▸ l
        if p₁ = p₂' then (w.map (fun h => Tmat z (projD D₁.1 h))).prod i l' else 0
      else 0
  let MI : A → Matrix I I ℚ := fun h x y =>
    match x, y with
    | Sum.inl t₁, Sum.inl t₂ => M0 t₁ t₂
    | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => subMat h a b
    | Sum.inr (Sum.inr (Sum.inl (D₁, p₁, i))), Sum.inr (Sum.inr (Sum.inl (D₂, p₂, l))) =>
      if D₁ = D₂ ∧ p₁ = p₂ then Smat (castVec D₁.2 (projD D₁.1 h)) i l else 0
    | Sum.inr (Sum.inr (Sum.inr α₁)), Sum.inr (Sum.inr (Sum.inr α₂)) =>
      if α₁ = α₂ then char α₁.1 h else 0
    | _, _ => 0
  have hMI_prod : ∀ (w : List A) (x y : I),
      (w.map MI).prod x y =
      match x, y with
      | Sum.inl t₁, Sum.inl t₂ => (w.map (fun _ => M0)).prod t₁ t₂
      | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => subProd w a b
      | Sum.inr (Sum.inr (Sum.inl (D₁, p₁, i))), Sum.inr (Sum.inr (Sum.inl (D₂, p₂, l))) =>
        if D₁ = D₂ ∧ p₁ = p₂ then (w.map (fun h => Smat (castVec D₁.2 (projD D₁.1 h)))).prod i l else 0
      | Sum.inr (Sum.inr (Sum.inr α₁)), Sum.inr (Sum.inr (Sum.inr α₂)) =>
        if α₁ = α₂ then char α₁.1 w.sum else 0
      | _, _ => 0 := by
    intro w
    induction w with
    | nil =>
      intro x y
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Matrix.one_apply, char_zero_right]
      dsimp only [I]
      rcases x with t₁ | (⟨D₁, p₁, i⟩ | (⟨D₁, p₁, i⟩ | α₁)) <;>
      rcases y with t₂ | (⟨D₂, p₂, l⟩ | (⟨D₂, p₂, l⟩ | α₂))
      · simp
      · simp
      · simp
      · simp
      · simp
      · dsimp only [subProd]
        by_cases hD : D₁ = D₂
        · subst hD
          by_cases hp : p₁ = p₂
          · subst hp
            by_cases hil : i = l
            · subst hil; simp
            · simp [hil]
          · simp [hp]
        · simp [hD]
      · simp
      · simp
      · simp
      · simp
      · by_cases hD : D₁ = D₂
        · subst hD
          by_cases hp : p₁ = p₂
          · subst hp
            by_cases hil : i = l
            · subst hil; simp
            · simp [hil]
          · simp [hp]
        · simp [hD]
      · simp
      · simp
      · simp
      · simp
      · by_cases hα : α₁ = α₂
        · subst hα; simp
        · simp [hα]
    | cons h t ih =>
      intro x y
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Matrix.mul_apply]
      change (∑ k : Fin 2 ⊕
        (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
        (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar}, MI h x k * (t.map MI).prod k y) = _
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      rcases x with t₁ | (⟨D₁, p₁, i⟩ | (⟨D₁, p₁, i⟩ | α₁)) <;>
      rcases y with t₂ | (⟨D₂, p₂, l⟩ | (⟨D₂, p₂, l⟩ | α₂))
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp only [MI, ih, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
        rw [Fintype.sum_sigma]
        rw [Finset.sum_eq_single D₁]
        · rw [Fintype.sum_prod_type, Finset.sum_eq_single p₁]
          · dsimp only [subMat, subProd]
            by_cases hD : D₁ = D₂
            · subst hD
              by_cases hp : p₁ = p₂
              · subst hp; simp only [↓reduceDIte, ite_true, Matrix.mul_apply]; rfl
              · simp [hp]
            · simp [hD]
          · intro p' _ hne
            refine Finset.sum_eq_zero fun k _ => by simp [subMat, Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · intro D' _ hne
          refine Finset.sum_eq_zero fun k _ => by simp [subMat, Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp only [MI, ih, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
        rw [Fintype.sum_prod_type, Finset.sum_eq_single D₁]
        · rw [Fintype.sum_prod_type, Finset.sum_eq_single p₁]
          · by_cases hD : D₁ = D₂
            · subst hD
              by_cases hp : p₁ = p₂
              · subst hp; simp only [ite_true, and_self]
              · simp [hp]
            · simp [hD]
          · intro p' _ hne; refine Finset.sum_eq_zero fun k _ => by simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · intro D' _ hne; refine Finset.sum_eq_zero fun k _ => by simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp [MI, ih]
      · simp only [MI, ih, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
        rw [Finset.sum_eq_single α₁]
        · by_cases hα : α₁ = α₂
          · subst hα; simp only [ite_true]; exact (char_add_right α₁.1 h t.sum).symm
          · simp [hα]
        · intro α' _ hne; simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
  let u : Fin least → ℚ := fun i => uI (eI i)
  let v : Fin least → ℚ := fun l => vI (eI l)
  let M : A → Matrix (Fin least) (Fin least) ℚ := fun h i l => MI h (eI i) (eI l)
  have hM_prod : ∀ (w : List A) (i l : Fin least),
      (w.map M).prod i l = (w.map MI).prod (eI i) (eI l) := by
    intro w
    induction w with
    | nil => intro i l; simp [Matrix.one_apply, eI.injective.eq_iff]
    | cons h t ih =>
      intro i l
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      calc (∑ k : Fin least, M h i k * (t.map M).prod k l)
          = ∑ k : Fin least, MI h (eI i) (eI k) * (t.map MI).prod (eI k) (eI l) :=
            Finset.sum_congr rfl fun k _ => by rw [ih k l]
        _ = ∑ y : I, MI h (eI i) y * (t.map MI).prod y (eI l) :=
            Equiv.sum_comp eI (fun y => MI h (eI i) y * (t.map MI).prod y (eI l))
  refine ⟨u, v, M, ?_⟩
  intro w
  rw [countVal_eq_sum_cycleD Y hY w, sum_coeffD_cycleD_decomp hj Y hY w]
  calc (∑ i : Fin least, ∑ l : Fin least, u i * (w.map M).prod i l * v l)
      = ∑ i : Fin least, ∑ l : Fin least, uI (eI i) * (w.map MI).prod (eI i) (eI l) * vI (eI l) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [hM_prod]
    _ = ∑ x : I, ∑ y : I, uI x * (w.map MI).prod x y * vI y := by
        calc _ = ∑ i : Fin least, ∑ y : I, uI (eI i) * (w.map MI).prod (eI i) y * vI y :=
                Finset.sum_congr rfl fun i _ =>
                  Equiv.sum_comp eI (fun y => uI (eI i) * (w.map MI).prod (eI i) y * vI y)
          _ = _ := Equiv.sum_comp eI (fun x => ∑ y : I, uI x * (w.map MI).prod x y * vI y)
    _ = s * (coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod +
          (∑ D : SubD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Tmat z (projD D.1 h))).prod) +
          (∑ D : TopD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Smat (castVec D.2 (projD D.1 h)))).prod) +
          ∑ α ∈ Schar, (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum) := by
        change (∑ x : Fin 2 ⊕
          (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
          (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
          ∑ y : Fin 2 ⊕
            (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
            (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
            uI x * (w.map MI).prod x y * vI y) = _
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
        have hB0 : (∑ t₁ : Fin 2, ∑ y : Fin 2 ⊕
            (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
            (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
            uI (Sum.inl t₁) * (w.map MI).prod (Sum.inl t₁) y * vI y) =
            s * (coeffD Y ⊤ * tr0 (w.map (fun _ => X0 z)).prod) := by
          have h1 : ∀ t₁ : Fin 2, (∑ y : Fin 2 ⊕
              (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
              (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
              uI (Sum.inl t₁) * (w.map MI).prod (Sum.inl t₁) y * vI y) =
              ∑ t₂ : Fin 2, uI (Sum.inl t₁) * (w.map (fun _ => M0)).prod t₁ t₂ * (2 * s * coeffD Y ⊤) := by
            intro t₁
            rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
            simp [hMI_prod, vI]
          simp_rw [h1, Fin.sum_univ_two, hM0_prod w]
          simp only [uI, tr0]
          norm_num; ring
        have hSub : (∑ a : Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2),
            ∑ y : Fin 2 ⊕
              (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
              (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
              uI (Sum.inr (Sum.inl a)) * (w.map MI).prod (Sum.inr (Sum.inl a)) y * vI y) =
            s * ∑ D : SubD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Tmat z (projD D.1 h))).prod := by
          rw [Fintype.sum_sigma, Finset.mul_sum]
          refine Finset.sum_congr rfl fun D _ => ?_
          rw [Fintype.sum_prod_type]
          simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single p]
          · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
            simp only [hMI_prod, uI, vI, ite_true, mul_zero, zero_mul, Finset.sum_const_zero,
              zero_add, add_zero]
            rw [Fintype.sum_sigma, Finset.sum_eq_single D]
            · rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
              · rw [Finset.sum_eq_single p]
                · simp [subProd]; ring
                · intro l _ hne; simp [Ne.symm hne]
                · intro hnot; exact absurd (Finset.mem_univ _) hnot
              · intro p' _ hne; refine Finset.sum_eq_zero fun l _ => by simp [subProd, Ne.symm hne]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · intro D' _ hne; refine Finset.sum_eq_zero fun k _ => by simp [subProd, Ne.symm hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · intro i _ hne; refine Finset.sum_eq_zero fun y _ => by simp [uI, Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        have hTop : (∑ a : TopD × (IdxTop j × IdxTop j),
            ∑ y : Fin 2 ⊕
              (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
              (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
              uI (Sum.inr (Sum.inr (Sum.inl a))) * (w.map MI).prod (Sum.inr (Sum.inr (Sum.inl a))) y * vI y) =
            s * ∑ D : TopD, coeffD Y D.1 * Matrix.trace (w.map (fun h => Smat (castVec D.2 (projD D.1 h)))).prod := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun D _ => ?_
          rw [Fintype.sum_prod_type]
          simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single p]
          · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
            simp only [hMI_prod, uI, vI, ite_true, mul_zero, zero_mul, Finset.sum_const_zero,
              zero_add, add_zero]
            rw [Fintype.sum_prod_type, Finset.sum_eq_single D]
            · rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
              · rw [Finset.sum_eq_single p]
                · simp; ring
                · intro l _ hne; simp [Ne.symm hne]
                · intro hnot; exact absurd (Finset.mem_univ _) hnot
              · intro p' _ hne; refine Finset.sum_eq_zero fun l _ => by simp [Ne.symm hne]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · intro D' _ hne; refine Finset.sum_eq_zero fun k _ => by simp [Ne.symm hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · intro i _ hne; refine Finset.sum_eq_zero fun y _ => by simp [uI, Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        have hSc : (∑ α₁ : {α : A // α ∈ Schar},
            ∑ y : Fin 2 ⊕
              (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
              (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar},
              uI (Sum.inr (Sum.inr (Sum.inr α₁))) * (w.map MI).prod (Sum.inr (Sum.inr (Sum.inr α₁))) y * vI y) =
            s * ∑ α ∈ Schar, (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum := by
          rw [← Finset.sum_coe_sort Schar, Finset.mul_sum]
          refine Finset.sum_congr rfl fun α₁ _ => ?_
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
          simp only [hMI_prod, uI, vI, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_one]
          rw [Finset.sum_eq_single α₁]
          · simp; ring
          · intro α₂ _ hne; simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        rw [hB0, hSub, hTop, hSc]
        ring

lemma list_prod_const_idemp {R : Type*} [Ring R] [Module ℚ R] [IsScalarTower ℚ R R]
    [SMulCommClass ℚ R R] (c : ℚ) (E : R) (hE : E * E = E) :
    ∀ n : ℕ, 0 < n → (List.replicate n (c • E)).prod = (c ^ n) • E := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    by_cases hk : k = 0
    · subst hk; simp
    · rw [List.replicate_succ, List.prod_cons, ih (Nat.pos_of_ne_zero hk),
        smul_mul_smul_comm, hE, pow_succ']

abbrev AlgTy822 (m j : ℕ) (Schar : Finset (Fin m → ZMod 2)) :=
  B0 ((2 ^ j : ℕ) : ℚ) ×
  (∀ D : {D : Submodule (ZMod 2) (Fin m → ZMod 2) // 0 < codimD D ∧ codimD D < j},
    Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ) ×
  ({D : Submodule (ZMod 2) (Fin m → ZMod 2) // codimD D = j} →
    Matrix (IdxTop j) (IdxTop j) ℚ) ×
  ({α : Fin m → ZMod 2 // α ∈ Schar} → ℚ)

noncomputable def phi822 {m j : ℕ} (Schar : Finset (Fin m → ZMod 2))
    (w : List (Fin m → ZMod 2)) : AlgTy822 m j Schar :=
  ((w.map (fun _ => X0 ((2 ^ j : ℕ) : ℚ))).prod,
   fun D => (w.map (fun h => Tmat ((2 ^ j : ℕ) : ℚ) (projD D.1 h))).prod,
   fun D => (w.map (fun h => Smat (castVec D.2 (projD D.1 h)))).prod,
   fun α => char α.1 w.sum)

lemma phi822_append {m j : ℕ} (Schar : Finset (Fin m → ZMod 2))
    (w₁ w₂ : List (Fin m → ZMod 2)) :
    (phi822 Schar (w₁ ++ w₂) : AlgTy822 m j Schar) = phi822 Schar w₁ * phi822 Schar w₂ := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [phi822, pow_add]
  · funext D; simp [phi822]
  · funext D; simp [phi822]
  · funext α; simp only [phi822, List.sum_append, Prod.snd_mul, Pi.mul_apply]
    exact char_add_right α.1 w₁.sum w₂.sum

private lemma trace_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (p q : ι) :
    Matrix.trace (M * Matrix.single q p (1 : ℚ)) = M p q := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.sum_eq_single p]
  · rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · simp [Matrix.single]
    · intro x _ hne; simp [Matrix.single, Ne.symm hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · intro x _ hne
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun y _ => by simp [Matrix.single, Ne.symm hne]
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

open Classical in
private lemma algPos_sub_all_jge2 {m j : ℕ} (hj : 2 ≤ j) (Schar : Finset (Fin m → ZMod 2))
    (AlgPos : Submodule ℚ (AlgTy822 m j Schar))
    (hmul_mem : ∀ a ∈ AlgPos, ∀ b ∈ AlgPos, a * b ∈ AlgPos)
    (hlist_prod_mem : ∀ (L : List (AlgTy822 m j Schar)), L ≠ [] → (∀ a ∈ L, a ∈ AlgPos) → L.prod ∈ AlgPos)
    (Φ0 : AlgTy822 m j Schar)
    (hΦ0 : Φ0 ∈ AlgPos)
    (hΦ0_val : Φ0 = (X0 ((2 ^ j : ℕ) : ℚ), fun _ => Tmat ((2 ^ j : ℕ) : ℚ) 0, fun _ => S0 j, 1))
    (Q : (Fin m → ZMod 2) → AlgTy822 m j Schar)
    (hQ_mem : ∀ ψ, Q ψ ∈ AlgPos)
    (hQ_sub_of_dual : ∀ (D : {D : Submodule (ZMod 2) (Fin m → ZMod 2) // 0 < codimD D ∧ codimD D < j})
      (φ : Fin (codimD D.1) → ZMod 2), (Q (dualProjD D.1 φ)).2.1 D = Qmat φ)
    (hQ0_sub : ∀ (D : {D : Submodule (ZMod 2) (Fin m → ZMod 2) // 0 < codimD D ∧ codimD D < j}),
      (Q 0).2.1 D = Qmat 0)
    (Zop : (Fin m → ZMod 2) → AlgTy822 m j Schar)
    (hZop_mem : ∀ ψ, Zop ψ ∈ AlgPos)
    (hZop_fst : ∀ ψ, ψ ≠ 0 → (Zop ψ).1 = 0)
    (hZop_schar : ∀ ψ, ψ ≠ 0 → (Zop ψ).2.2.2 = 0)
    (hZop_sub : ∀ (D : {D : Submodule (ZMod 2) (Fin m → ZMod 2) // 0 < codimD D ∧ codimD D < j})
      (ψ : Fin m → ZMod 2), ψ ≠ 0 →
      (Zop ψ).2.1 D = if ψ ∈ perp D.1 then (((2 ^ j : ℕ) : ℚ) * ((2 ^ codimD D.1 : ℕ) : ℚ)⁻¹) • rankOne vecE vecE else 0)
    (hTop_all : ∀ (D : {D : Submodule (ZMod 2) (Fin m → ZMod 2) // codimD D = j})
      (M : Matrix (IdxTop j) (IdxTop j) ℚ), ((0, 0, Pi.single D M, 0) : AlgTy822 m j Schar) ∈ AlgPos) :
    ∀ (D : {D : Submodule (ZMod 2) (Fin m → ZMod 2) // 0 < codimD D ∧ codimD D < j})
      (M : Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ),
      ((0, Pi.single D M, 0, 0) : AlgTy822 m j Schar) ∈ AlgPos := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  let A := Fin m → ZMod 2
  let z : ℚ := ((2 ^ j : ℕ) : ℚ)
  have hz0 : z ≠ 0 := by dsimp only [z]; positivity
  let SubD := {D : Submodule (ZMod 2) A // 0 < codimD D ∧ codimD D < j}
  let TopD := {D : Submodule (ZMod 2) A // codimD D = j}
  let injSub : (D : SubD) → Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ → AlgTy822 m j Schar :=
    fun D M => (0, Pi.single D M, 0, 0)
  let injTop : TopD → Matrix (IdxTop j) (IdxTop j) ℚ → AlgTy822 m j Schar :=
    fun D M => (0, 0, Pi.single D M, 0)
  let Xop : A → AlgTy822 m j Schar := fun ψ => Q 0 * Φ0 * Q ψ
  let Yop : A → AlgTy822 m j Schar := fun ψ => Q ψ * Φ0 * Q 0
  have hXop_mem : ∀ ψ : A, Xop ψ ∈ AlgPos := fun ψ =>
    hmul_mem _ (hmul_mem _ (hQ_mem 0) _ hΦ0) _ (hQ_mem ψ)
  have hYop_mem : ∀ ψ : A, Yop ψ ∈ AlgPos := fun ψ =>
    hmul_mem _ (hmul_mem _ (hQ_mem ψ) _ hΦ0) _ (hQ_mem 0)
  have hprod_fst : ∀ L : List (AlgTy822 m j Schar), L.prod.1 = (L.map Prod.fst).prod := by
    intro L; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hprod_sub : ∀ (L : List (AlgTy822 m j Schar)) (D : SubD), L.prod.2.1 D = (L.map (fun a => a.2.1 D)).prod := by
    intro L D; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hprod_schar : ∀ (L : List (AlgTy822 m j Schar)) (α : {α : A // α ∈ Schar}),
      L.prod.2.2.2 α = (L.map (fun a => a.2.2.2 α)).prod := by
    intro L α; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hSub_ind : ∀ d : ℕ, ∀ D : SubD, j - d ≤ codimD D.1 →
      ∀ M : Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ,
        injSub D M ∈ AlgPos := by
    intro d
    induction d with
    | zero =>
      intro D hle; exfalso; have := D.2.2; omega
    | succ d ih =>
      intro D hle
      by_cases hprev : j - d ≤ codimD D.1
      · exact ih D hprev
      · have hcodim_eq : codimD D.1 = j - (d + 1) := by have := D.2.2; omega
        have hIH_gt : ∀ D' : SubD, codimD D.1 < codimD D'.1 →
            ∀ M', injSub D' M' ∈ AlgPos := fun D' hlt M' => ih D' (by omega) M'
        let r := codimD D.1
        have hr_pos : 0 < r := D.2.1
        have hr_lt : r < j := D.2.2
        have hq0 : ((2 ^ r : ℕ) : ℚ) ≠ 0 := by positivity
        have hzr_ne : z - ((2 ^ r : ℕ) : ℚ) ≠ 0 := by
          dsimp only [z]
          have hlt : 2 ^ r < 2 ^ j := Nat.pow_lt_pow_right (by decide) hr_lt
          have hltQ : ((2 ^ r : ℕ) : ℚ) < ((2 ^ j : ℕ) : ℚ) := by exact_mod_cast hlt
          linarith
        have hfrW : Module.finrank (ZMod 2) (perp D.1) = r := by
          have h1 := finrank_perp D.1; dsimp only [r, codimD]; omega
        let bW : Module.Basis (Fin r) (ZMod 2) (perp D.1) :=
          (Module.finBasis (ZMod 2) (perp D.1)).reindex (finCongr hfrW)
        have hbW_ne : ∀ i : Fin r, (bW i).1 ≠ 0 := fun i h0 =>
          bW.ne_zero i (Subtype.ext h0)
        let L : List (AlgTy822 m j Schar) := List.ofFn (fun i : Fin r => Zop (bW i).1)
        have hL_ne : L ≠ [] := by
          intro h; have hlen := congrArg List.length h; simp [L] at hlen; omega
        have hL_mem : L.prod ∈ AlgPos :=
          hlist_prod_mem L hL_ne fun a ha => by
            rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
            exact hZop_mem (bW i).1
        let cD : ℚ := (z * ((2 ^ r : ℕ) : ℚ)⁻¹) ^ r
        have hcD_ne : cD ≠ 0 := by
          dsimp only [cD]; exact pow_ne_zero _ (mul_ne_zero hz0 (inv_ne_zero hq0))
        let gtSub : Finset SubD := Finset.univ.filter (fun D' : SubD => codimD D.1 < codimD D'.1)
        let corr : AlgTy822 m j Schar := (∑ D' : TopD, injTop D' (L.prod.2.2.1 D')) +
          ∑ D' ∈ gtSub, injSub D' (L.prod.2.1 D')
        have hcorr_mem : corr ∈ AlgPos :=
          AlgPos.add_mem (AlgPos.sum_mem fun D' _ => hTop_all D' _)
            (AlgPos.sum_mem fun D' hD' => hIH_gt D' (Finset.mem_filter.mp hD').2 _)
        have hpure : L.prod - corr = injSub D (cD • rankOne vecE vecE) := by
          refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
          · simp only [corr, injSub, Prod.fst_sub, Prod.fst_add, Prod.fst_sum, injTop,
              Finset.sum_const_zero, add_zero, sub_zero]
            rw [hprod_fst]
            exact List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW ⟨0, hr_pos⟩).1,
              List.mem_ofFn.mpr ⟨⟨0, hr_pos⟩, rfl⟩, hZop_fst _ (hbW_ne _)⟩)
          · funext D'
            simp only [corr, injSub, injTop, Prod.snd_sub, Prod.fst_sub, Prod.snd_add, Prod.fst_add,
              Prod.snd_sum, Prod.fst_sum, Pi.sub_apply, Finset.sum_apply, Finset.sum_const_zero, zero_add]
            by_cases hgt : codimD D.1 < codimD D'.1
            · have hne : D' ≠ D := by rintro rfl; omega
              simp only [Pi.single_eq_of_ne hne]
              rw [Finset.sum_eq_single D']
              · simp [Pi.single_eq_same]
              · intro D'' _ hne''; simp [Pi.single_eq_of_ne (Ne.symm hne'')]
              · intro hnot; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ D', hgt⟩) hnot
            · have hcorr0 : (∑ D'' ∈ gtSub, Pi.single D'' (L.prod.2.1 D'') D') = 0 := by
                refine Finset.sum_eq_zero fun D'' hD'' => ?_
                have hlt'' := (Finset.mem_filter.mp hD'').2
                have hne'' : D' ≠ D'' := by rintro rfl; exact hgt hlt''
                simp [Pi.single_eq_of_ne hne'']
              rw [hcorr0, sub_zero, hprod_sub]
              by_cases hEq : D' = D
              · rcases hEq with rfl
                simp only [Pi.single_eq_same]
                have hmap : L.map (fun a => a.2.1 D') =
                    List.replicate r ((z * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecE (r := r)) vecE) := by
                  apply List.ext_getElem
                  · simp [L]
                  · intro idx h1 h2
                    simp only [L, List.getElem_map, List.getElem_ofFn, List.getElem_replicate]
                    rw [hZop_sub D' _ (hbW_ne ⟨idx, by simp [L] at h1; exact h1⟩)]
                    simp [(bW ⟨idx, by simp [L] at h1; exact h1⟩).2, r, z]
                rw [hmap]
                have hidemp : rankOne (vecE (r := r)) vecE * rankOne vecE vecE = rankOne vecE vecE := by
                  rw [rankOne_mul_rankOne, dot_EE, one_smul]
                exact list_prod_const_idemp _ _ hidemp r hr_pos
              · simp only [Pi.single_eq_of_ne hEq]
                have hnot_le : ¬ (perp D.1 ≤ perp D'.1) := by
                  intro hleW
                  have hfr1 := Submodule.finrank_mono hleW
                  have hfr2 : Module.finrank (ZMod 2) (perp D'.1) = codimD D'.1 := by
                    have := finrank_perp D'.1; dsimp only [codimD]; omega
                  have hfr_eq : Module.finrank (ZMod 2) (perp D.1) = Module.finrank (ZMod 2) (perp D'.1) := by
                    dsimp only [r] at hfrW; omega
                  have heqW : perp D.1 = perp D'.1 := Submodule.eq_of_le_of_finrank_eq hleW hfr_eq
                  exact hEq (Subtype.ext (perp_inj heqW).symm)
                have hex : ∃ i : Fin r, (bW i).1 ∉ perp D'.1 := by
                  by_contra hall
                  push Not at hall
                  apply hnot_le
                  intro x hx
                  have hrep := bW.sum_repr ⟨x, hx⟩
                  have hval : x = ∑ i : Fin r, (bW.repr ⟨x, hx⟩) i • (bW i).1 := by
                    have := congrArg Subtype.val hrep
                    rw [Submodule.coe_sum] at this
                    exact this.symm
                  rw [hval]
                  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hall i)
                rcases hex with ⟨i, hi⟩
                refine List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW i).1,
                  List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩)
                rw [hZop_sub D' _ (hbW_ne i)]; simp [hi]
          · funext D'
            simp only [corr, injSub, injTop, Prod.snd_sub, Prod.fst_sub, Prod.snd_add, Prod.fst_add,
              Prod.snd_sum, Prod.fst_sum, Pi.sub_apply, Finset.sum_apply,
              Pi.zero_apply, Finset.sum_const_zero, add_zero]
            rw [Finset.sum_eq_single D']
            · simp [Pi.single_eq_same]
            · intro D'' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · funext α
            simp only [corr, injSub, injTop, Prod.snd_sub, Prod.snd_add, Prod.snd_sum,
              Pi.sub_apply, Pi.zero_apply, Finset.sum_const_zero, add_zero, sub_zero]
            rw [hprod_schar]
            exact List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW ⟨0, hr_pos⟩).1,
              List.mem_ofFn.mpr ⟨⟨0, hr_pos⟩, rfl⟩, by rw [hZop_schar _ (hbW_ne _)]; rfl⟩)
        have hEnn_mem : injSub D (rankOne vecE vecE) ∈ AlgPos := by
          have h1 : injSub D (cD • rankOne vecE vecE) ∈ AlgPos := by
            rw [← hpure]; exact AlgPos.sub_mem hL_mem hcorr_mem
          have h2 := AlgPos.smul_mem cD⁻¹ h1
          have heq : cD⁻¹ • injSub D (cD • rankOne vecE vecE) = injSub D (rankOne vecE vecE) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp [Pi.single_eq_same, smul_smul, inv_mul_cancel₀ hcD_ne]
            · simp [Pi.single_eq_of_ne hEq]
          rwa [heq] at h2
        have hEv_nz : ∀ φ : Fin r → ZMod 2, φ ≠ 0 → injSub D (rankOne vecE (vecV φ)) ∈ AlgPos := by
          intro φ hφ
          have hprod : injSub D (rankOne vecE vecE) * Xop (dualProjD D.1 φ) =
              injSub D (((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV φ)) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Xop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hQ0_sub, hΦ0_val]
            by_cases hEq : D' = D
            · rcases hEq with rfl
              simp only [Pi.single_eq_same, hQ_sub_of_dual]
              rw [Q0_mul_T0_mul_Qpsi z φ hφ, Matrix.mul_smul, rankOne_mul_rankOne, dot_EE, one_smul]
            · simp [Pi.single_eq_of_ne hEq]
          have hmem := hmul_mem _ hEnn_mem _ (hXop_mem (dualProjD D.1 φ))
          rw [hprod] at hmem
          have hsc := AlgPos.smul_mem ((2 ^ r : ℕ) : ℚ) hmem
          have heq : ((2 ^ r : ℕ) : ℚ) • injSub D (((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV φ)) =
              injSub D (rankOne vecE (vecV φ)) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp [Pi.single_eq_same, smul_smul, mul_inv_cancel₀ hq0]
            · simp [Pi.single_eq_of_ne hEq]
          rwa [heq] at hsc
        have hvE_nz : ∀ φ : Fin r → ZMod 2, φ ≠ 0 → injSub D (rankOne (vecV φ) vecE) ∈ AlgPos := by
          intro φ hφ
          have hprod : Yop (dualProjD D.1 φ) * injSub D (rankOne vecE vecE) =
              injSub D ((z * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV φ) vecE) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Yop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hQ0_sub, hΦ0_val]
            by_cases hEq : D' = D
            · rcases hEq with rfl
              simp only [Pi.single_eq_same, hQ_sub_of_dual]
              rw [Qpsi_mul_T0_mul_Q0 z φ hφ, Matrix.smul_mul, rankOne_mul_rankOne, dot_EE, one_smul]
            · simp [Pi.single_eq_of_ne hEq]
          have hmem := hmul_mem _ (hYop_mem (dualProjD D.1 φ)) _ hEnn_mem
          rw [hprod] at hmem
          have hsc := AlgPos.smul_mem (z⁻¹ * ((2 ^ r : ℕ) : ℚ)) hmem
          have hnz : (z⁻¹ * ((2 ^ r : ℕ) : ℚ)) * (z * ((2 ^ r : ℕ) : ℚ)⁻¹) = 1 := by field_simp [hz0, hq0]
          have heq : (z⁻¹ * ((2 ^ r : ℕ) : ℚ)) • injSub D ((z * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV φ) vecE) =
              injSub D (rankOne (vecV φ) vecE) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp only [Pi.single_eq_same, smul_smul]; rw [hnz, one_smul]
            · simp [Pi.single_eq_of_ne hEq]
          rwa [heq] at hsc
        have hEv0_mem : injSub D (rankOne vecE (vecV 0)) ∈ AlgPos := by
          have hprod : injSub D (rankOne vecE vecE) * Φ0 * Q 0 =
              injSub D (rankOne vecE vecE + ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV 0)) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hQ0_sub, hΦ0_val]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp only [Pi.single_eq_same]; exact Enn_mul_T0_mul_Q0 z
            · simp [Pi.single_eq_of_ne hEq]
          have hmem := hmul_mem _ (hmul_mem _ hEnn_mem _ hΦ0) _ (hQ_mem 0)
          rw [hprod] at hmem
          have hsub := AlgPos.sub_mem hmem hEnn_mem
          have hsc := AlgPos.smul_mem ((2 ^ r : ℕ) : ℚ) hsub
          have heq : ((2 ^ r : ℕ) : ℚ) •
              (injSub D (rankOne vecE vecE + ((2 ^ r : ℕ) : ℚ)⁻¹ • rankOne vecE (vecV 0)) -
                injSub D (rankOne vecE vecE)) = injSub D (rankOne vecE (vecV 0)) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.smul_snd, Prod.smul_fst, Prod.snd_sub, Prod.fst_sub,
              Pi.smul_apply, Pi.sub_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp [Pi.single_eq_same, smul_smul]
            · simp [Pi.single_eq_of_ne hEq]
          rwa [heq] at hsc
        have hv0E_mem : injSub D (rankOne (vecV 0) vecE) ∈ AlgPos := by
          have hprod : Q 0 * Φ0 * injSub D (rankOne vecE vecE) =
              injSub D (rankOne vecE vecE + ((z - ((2 ^ r : ℕ) : ℚ)) * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV 0) vecE) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hQ0_sub, hΦ0_val]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp only [Pi.single_eq_same]; exact Q0_mul_T0_mul_Enn z
            · simp [Pi.single_eq_of_ne hEq]
          have hmem := hmul_mem _ (hmul_mem _ (hQ_mem 0) _ hΦ0) _ hEnn_mem
          rw [hprod] at hmem
          have hsub := AlgPos.sub_mem hmem hEnn_mem
          have hsc := AlgPos.smul_mem ((z - ((2 ^ r : ℕ) : ℚ))⁻¹ * ((2 ^ r : ℕ) : ℚ)) hsub
          have hnz : ((z - ((2 ^ r : ℕ) : ℚ))⁻¹ * ((2 ^ r : ℕ) : ℚ)) *
              ((z - ((2 ^ r : ℕ) : ℚ)) * ((2 ^ r : ℕ) : ℚ)⁻¹) = 1 := by field_simp [hzr_ne, hq0]
          have heq : ((z - ((2 ^ r : ℕ) : ℚ))⁻¹ * ((2 ^ r : ℕ) : ℚ)) •
              (injSub D (rankOne vecE vecE + ((z - ((2 ^ r : ℕ) : ℚ)) * ((2 ^ r : ℕ) : ℚ)⁻¹) • rankOne (vecV 0) vecE) -
                injSub D (rankOne vecE vecE)) = injSub D (rankOne (vecV 0) vecE) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.smul_snd, Prod.smul_fst, Prod.snd_sub, Prod.fst_sub,
              Pi.smul_apply, Pi.sub_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl
              simp only [Pi.single_eq_same, add_sub_cancel_left, smul_smul]
              rw [hnz, one_smul]
            · simp [Pi.single_eq_of_ne hEq]
          rwa [heq] at hsc
        have hEv_all : ∀ φ : Fin r → ZMod 2, injSub D (rankOne vecE (vecV φ)) ∈ AlgPos := fun φ => by
          by_cases h0 : φ = 0
          · subst h0; exact hEv0_mem
          · exact hEv_nz φ h0
        have hvE_all : ∀ φ : Fin r → ZMod 2, injSub D (rankOne (vecV φ) vecE) ∈ AlgPos := fun φ => by
          by_cases h0 : φ = 0
          · subst h0; exact hv0E_mem
          · exact hvE_nz φ h0
        have hvV_all : ∀ φ χ : Fin r → ZMod 2, injSub D (rankOne (vecV φ) (vecV χ)) ∈ AlgPos := by
          intro φ χ
          have hprod : injSub D (rankOne (vecV φ) vecE) * injSub D (rankOne vecE (vecV χ)) =
              injSub D (rankOne (vecV φ) (vecV χ)) := by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'
            simp only [injSub, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp only [Pi.single_eq_same]; rw [rankOne_mul_rankOne, dot_EE, one_smul]
            · simp [Pi.single_eq_of_ne hEq]
          rw [← hprod]
          exact hmul_mem _ (hvE_all φ) _ (hEv_all χ)
        have hunit_mem : ∀ p q : Option (Fin (codimD D.1) → ZMod 2),
            injSub D (Matrix.single p q (1 : ℚ)) ∈ AlgPos := by
          intro p q
          have hinj_smul : ∀ (c : ℚ) (X : Matrix (Option (Fin (codimD D.1) → ZMod 2))
              (Option (Fin (codimD D.1) → ZMod 2)) ℚ), c • injSub D X = injSub D (c • X) := fun c X => by
            refine Prod.ext (by simp [injSub]) (Prod.ext ?_ (Prod.ext (by funext D'; simp [injSub])
              (by funext α; simp [injSub])))
            funext D'; simp only [injSub, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp [Pi.single_eq_same]
            · simp [Pi.single_eq_of_ne hEq]
          have hinj_sum : ∀ (f : (Fin (codimD D.1) → ZMod 2) →
              Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ),
              (∑ φ : Fin (codimD D.1) → ZMod 2, injSub D (f φ)) =
              injSub D (∑ φ : Fin (codimD D.1) → ZMod 2, f φ) := fun f => by
            refine Prod.ext (by simp [injSub, Prod.fst_sum]) (Prod.ext ?_
              (Prod.ext (by funext D'; simp [injSub, Prod.snd_sum])
              (by funext α; simp [injSub, Prod.snd_sum])))
            funext D'; simp only [injSub, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
            by_cases hEq : D' = D
            · rcases hEq with rfl; simp [Pi.single_eq_same]
            · simp [Pi.single_eq_of_ne hEq]
          cases p with
          | none =>
            cases q with
            | none => rw [single_nn_eq]; exact hEnn_mem
            | some b =>
              rw [single_ns_eq b, ← hinj_smul]
              refine AlgPos.smul_mem _ ?_
              have hEqSum := hinj_sum (fun φ => char φ b • rankOne vecE (vecV φ))
              have hmem : (∑ φ : Fin (codimD D.1) → ZMod 2,
                  injSub D (char φ b • rankOne vecE (vecV φ))) ∈ AlgPos :=
                AlgPos.sum_mem fun φ _ => by rw [← hinj_smul]; exact AlgPos.smul_mem _ (hEv_all φ)
              exact hEqSum ▸ hmem
          | some a =>
            cases q with
            | none =>
              rw [single_sn_eq a, ← hinj_smul]
              refine AlgPos.smul_mem _ ?_
              have hEqSum := hinj_sum (fun φ => char φ a • rankOne (vecV φ) vecE)
              have hmem : (∑ φ : Fin (codimD D.1) → ZMod 2,
                  injSub D (char φ a • rankOne (vecV φ) vecE)) ∈ AlgPos :=
                AlgPos.sum_mem fun φ _ => by rw [← hinj_smul]; exact AlgPos.smul_mem _ (hvE_all φ)
              exact hEqSum ▸ hmem
            | some b =>
              rw [single_ss_eq a b, ← hinj_smul]
              refine AlgPos.smul_mem _ ?_
              have hEqSum := hinj_sum (fun φ => ∑ χ : Fin (codimD D.1) → ZMod 2,
                (char φ a * char χ b) • rankOne (vecV φ) (vecV χ))
              have hmem : (∑ φ : Fin (codimD D.1) → ZMod 2,
                  injSub D (∑ χ : Fin (codimD D.1) → ZMod 2,
                    (char φ a * char χ b) • rankOne (vecV φ) (vecV χ))) ∈ AlgPos :=
                AlgPos.sum_mem fun φ _ => by
                  have hEqIn := hinj_sum (fun χ => (char φ a * char χ b) • rankOne (vecV φ) (vecV χ))
                  have hinner : (∑ χ : Fin (codimD D.1) → ZMod 2,
                      injSub D ((char φ a * char χ b) • rankOne (vecV φ) (vecV χ))) ∈ AlgPos :=
                    AlgPos.sum_mem fun χ _ => by rw [← hinj_smul]; exact AlgPos.smul_mem _ (hvV_all φ χ)
                  exact hEqIn ▸ hinner
              exact hEqSum ▸ hmem
        intro M
        have hdecomp : injSub D M = ∑ p : Option (Fin (codimD D.1) → ZMod 2),
            ∑ q : Option (Fin (codimD D.1) → ZMod 2), M p q • injSub D (Matrix.single p q (1 : ℚ)) := by
          refine Prod.ext (by simp [injSub, Prod.fst_sum]) (Prod.ext ?_
            (Prod.ext (by funext D'; simp [injSub, Prod.snd_sum, Prod.fst_sum])
            (by funext α; simp [injSub, Prod.snd_sum])))
          funext D'
          simp only [injSub, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst,
            Finset.sum_apply, Pi.smul_apply]
          by_cases hEq : D' = D
          · rcases hEq with rfl
            simp only [Pi.single_eq_same]
            ext p q
            simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
            rw [Finset.sum_eq_single p]
            · rw [Finset.sum_eq_single q]
              · simp [Matrix.single]
              · intro y _ hne; simp [Matrix.single, hne]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · intro x _ hne; refine Finset.sum_eq_zero fun y _ => by simp [Matrix.single, hne]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
          · simp [Pi.single_eq_of_ne hEq]
        rw [hdecomp]
        exact AlgPos.sum_mem fun p _ => AlgPos.sum_mem fun q _ => AlgPos.smul_mem _ (hunit_mem p q)
  have hSub_all : ∀ (D : SubD)
      (M : Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ),
      injSub D M ∈ AlgPos := fun D M => hSub_ind j D (by omega) M
  exact hSub_all

open Classical in
lemma algPos_eq_top_jge2 {m j : ℕ} (hj : 2 ≤ j) (Schar : Finset (Fin m → ZMod 2)) :
    ∀ a : AlgTy822 m j Schar,
      a ∈ Submodule.span ℚ {x : AlgTy822 m j Schar | ∃ w : List (Fin m → ZMod 2), 0 < w.length ∧ phi822 Schar w = x} := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  let A := Fin m → ZMod 2
  let z : ℚ := ((2 ^ j : ℕ) : ℚ)
  have hz_ge4 : (4 : ℚ) ≤ z := by
    dsimp only [z]
    have hnat : 4 ≤ 2 ^ j := by
      have h1 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
      omega
    exact_mod_cast hnat
  have hz0 : z ≠ 0 := by linarith
  have h2z : (2 - z : ℚ) ≠ 0 := by linarith
  have h1z : (1 - z : ℚ) ≠ 0 := by linarith
  let SubD := {D : Submodule (ZMod 2) A // 0 < codimD D ∧ codimD D < j}
  let TopD := {D : Submodule (ZMod 2) A // codimD D = j}
  let Φ : List A → AlgTy822 m j Schar := phi822 Schar
  have hΦ_append : ∀ w₁ w₂ : List A, Φ (w₁ ++ w₂) = Φ w₁ * Φ w₂ := phi822_append Schar
  let injB0 : B0 z → AlgTy822 m j Schar := fun x => (x, 0, 0, 0)
  let injSub : (D : SubD) → Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ → AlgTy822 m j Schar :=
    fun D M => (0, Pi.single D M, 0, 0)
  let injTop : TopD → Matrix (IdxTop j) (IdxTop j) ℚ → AlgTy822 m j Schar :=
    fun D M => (0, 0, Pi.single D M, 0)
  let injSchar : {α : A // α ∈ Schar} → ℚ → AlgTy822 m j Schar :=
    fun α c => (0, 0, 0, Pi.single α c)
  let AlgPos : Submodule ℚ (AlgTy822 m j Schar) :=
    Submodule.span ℚ {a : AlgTy822 m j Schar | ∃ w : List A, 0 < w.length ∧ Φ w = a}
  have hmem_Φ : ∀ w : List A, 0 < w.length → Φ w ∈ AlgPos := fun w hw =>
    Submodule.subset_span ⟨w, hw, rfl⟩
  have hmul_mem : ∀ a ∈ AlgPos, ∀ b ∈ AlgPos, a * b ∈ AlgPos := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨w₁, hw₁, rfl⟩ b hb
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨w₂, hw₂, rfl⟩
        rw [← hΦ_append]
        exact hmem_Φ (w₁ ++ w₂) (by simp; omega)
      · rw [mul_zero]; exact AlgPos.zero_mem
      · intro x y _ _ hx hy; rw [mul_add]; exact AlgPos.add_mem hx hy
      · intro c x _ hx; rw [mul_smul_comm]; exact AlgPos.smul_mem c hx
    · intro b _; rw [zero_mul]; exact AlgPos.zero_mem
    · intro x y _ _ hx hy b hb; rw [add_mul]; exact AlgPos.add_mem (hx b hb) (hy b hb)
    · intro c x _ hx b hb; rw [smul_mul_assoc]; exact AlgPos.smul_mem c (hx b hb)
  have hlist_prod_mem : ∀ (L : List (AlgTy822 m j Schar)), L ≠ [] → (∀ a ∈ L, a ∈ AlgPos) → L.prod ∈ AlgPos := by
    intro L
    induction L with
    | nil => intro h; exact absurd rfl h
    | cons a t ih =>
      intro _ hall
      rw [List.prod_cons]
      by_cases ht : t = []
      · subst ht; rw [List.prod_nil, mul_one]; exact hall a (List.mem_cons_self ..)
      · exact hmul_mem _ (hall a (List.mem_cons_self ..)) _
          (ih ht fun x hx => hall x (List.mem_cons_of_mem a hx))
  have hΦ0 : Φ [0] ∈ AlgPos := hmem_Φ [0] (by simp)
  have hΦ0_val : Φ [0] = (X0 z, fun _ => Tmat z 0, fun _ => S0 j, 1) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [Φ, phi822, z]
    · funext D; simp [Φ, phi822, z]
    · funext D; simp [Φ, phi822, castVec_zero, Smat_zero]
    · funext α; simp [Φ, phi822, char_zero_right]
  have hΦ0_cubic : Φ [0] * Φ [0] * Φ [0] - (3 : ℚ) • (Φ [0] * Φ [0]) + (4 - z) • Φ [0] =
      (2 - z) • (1 : AlgTy822 m j Schar) := by
    rw [hΦ0_val]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · exact X0_cubic z
    · funext D; exact T0_cubic z
    · funext D; exact S0_cubic j
    · funext α
      simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_mul, Prod.snd_one,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.one_apply, smul_eq_mul]
      ring
  have hone_mem : (1 : AlgTy822 m j Schar) ∈ AlgPos := by
    have hlin : Φ [0] * Φ [0] * Φ [0] - (3 : ℚ) • (Φ [0] * Φ [0]) + (4 - z) • Φ [0] ∈ AlgPos :=
      AlgPos.add_mem
        (AlgPos.sub_mem (hmul_mem _ (hmul_mem _ hΦ0 _ hΦ0) _ hΦ0)
          (AlgPos.smul_mem 3 (hmul_mem _ hΦ0 _ hΦ0)))
        (AlgPos.smul_mem (4 - z) hΦ0)
    rw [hΦ0_cubic] at hlin
    have hsc := AlgPos.smul_mem (2 - z)⁻¹ hlin
    rwa [smul_smul, inv_mul_cancel₀ h2z, one_smul] at hsc
  let U : A → AlgTy822 m j Schar := fun h =>
    (1, fun D => Ptilde (projD D.1 h), fun D => Sdiag (castVec D.2 (projD D.1 h)), fun α => char α.1 h)
  have hU_mem : ∀ h : A, U h ∈ AlgPos := by
    intro h
    let inv0 : AlgTy822 m j Schar := (2 - z)⁻¹ • (Φ [0] * Φ [0] - (3 : ℚ) • Φ [0] + (4 - z) • (1 : AlgTy822 m j Schar))
    have hinv0_mem : inv0 ∈ AlgPos :=
      AlgPos.smul_mem _ (AlgPos.add_mem
        (AlgPos.sub_mem (hmul_mem _ hΦ0 _ hΦ0) (AlgPos.smul_mem 3 hΦ0))
        (AlgPos.smul_mem (4 - z) hone_mem))
    have hinv0_mul : inv0 * Φ [0] = 1 := by
      dsimp only [inv0]
      rw [smul_mul_assoc, add_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
        hΦ0_cubic, smul_smul, inv_mul_cancel₀ h2z, one_smul]
    have hfact : Φ [h] = Φ [0] * U h := by
      rw [hΦ0_val]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [Φ, phi822, U, z]
      · funext D; simp only [Φ, phi822, U, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply]
        exact Tmat_eq_T0_mul_Ptilde z (projD D.1 h)
      · funext D; simp only [Φ, phi822, U, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply]; rfl
      · funext α; simp [Φ, phi822, U]
    have heq : inv0 * Φ [h] = U h := by rw [hfact, ← mul_assoc, hinv0_mul, one_mul]
    rw [← heq]
    exact hmul_mem _ hinv0_mem _ (hmem_Φ [h] (by simp))
  let Q : A → AlgTy822 m j Schar := fun ψ => ((2 ^ m : ℕ) : ℚ)⁻¹ • ∑ h : A, char ψ h • U h
  have hQ_mem : ∀ ψ : A, Q ψ ∈ AlgPos := fun ψ =>
    AlgPos.smul_mem _ (AlgPos.sum_mem fun h _ => AlgPos.smul_mem _ (hU_mem h))
  have hQ_fst : ∀ ψ : A, (Q ψ).1 = if ψ = 0 then (1 : B0 z) else 0 := by
    intro ψ
    have hm0 : ((2 ^ m : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [Q, U, Prod.smul_fst, Prod.fst_sum]
    rw [← Finset.sum_smul, sum_char_right]
    by_cases h0 : ψ = 0
    · subst h0; simp [smul_smul]
    · simp [h0]
  have hQ_schar : ∀ (ψ : A) (α : {α : A // α ∈ Schar}),
      (Q ψ).2.2.2 α = if α.1 = ψ then 1 else 0 := by
    intro ψ ⟨α, hα⟩
    have hm0 : ((2 ^ m : ℕ) : ℚ) ≠ 0 := by positivity
    have hcomp : (Q ψ).2.2.2 ⟨α, hα⟩ = ((2 ^ m : ℕ) : ℚ)⁻¹ * ∑ h : Fin m → ZMod 2, char (ψ + α) h := by
      have h1 : (Q ψ).2.2.2 ⟨α, hα⟩ = ((2 ^ m : ℕ) : ℚ)⁻¹ * ∑ h : A, char ψ h * char α h := by
        simp [Q, U, Prod.smul_snd, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [h1]
      congr 1
      exact Finset.sum_congr rfl fun h _ => (char_add_left ψ α h).symm
    rw [hcomp, sum_char_right]
    have hiff : ψ + α = 0 ↔ α = ψ := by
      constructor
      · intro h
        have h1 := congrArg (ψ + ·) h
        have hz2 : ψ + ψ = 0 := zmod2_vec_add_self ψ
        simpa [← add_assoc, hz2] using h1
      · rintro rfl; exact zmod2_vec_add_self α
    by_cases hEq : α = ψ
    · subst hEq
      have hz2 : α + α = 0 := zmod2_vec_add_self α
      simp [hz2, inv_mul_cancel₀ hm0]
    · have hne : ψ + α ≠ 0 := fun h => hEq (hiff.mp h)
      simp [hEq, hne]
  have hQ_sub_of_dual : ∀ (D : SubD) (φ : Fin (codimD D.1) → ZMod 2),
      (Q (dualProjD D.1 φ)).2.1 D = Qmat φ := by
    intro D φ
    have hmem : dualProjD D.1 φ ∈ perp D.1 := (mem_perp_iff_exists_dualProjD D.1 _).mpr ⟨φ, rfl⟩
    have h1 := sum_char_projD_eq D.1 (fun y => Ptilde y) (dualProjD D.1 φ)
    simp only [hmem, ↓reduceDIte] at h1
    have hch : Classical.choose ((mem_perp_iff_exists_dualProjD D.1 (dualProjD D.1 φ)).mp hmem) = φ :=
      dualProjD_injective D.1 (Classical.choose_spec ((mem_perp_iff_exists_dualProjD D.1 (dualProjD D.1 φ)).mp hmem))
    rw [hch] at h1
    have hcomp : (Q (dualProjD D.1 φ)).2.1 D =
        ((2 ^ m : ℕ) : ℚ)⁻¹ • ∑ h : A, char (dualProjD D.1 φ) h • Ptilde (projD D.1 h) := by
      simp only [Q, U, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, Pi.smul_apply,
        Finset.sum_apply]
    rw [hcomp, h1]; rfl
  have hQ_sub_of_not_mem : ∀ (D : SubD) (ψ : A), ψ ∉ perp D.1 → (Q ψ).2.1 D = 0 := by
    intro D ψ hnot
    have h1 := sum_char_projD_eq D.1 (fun y => Ptilde y) ψ
    simp only [hnot, ↓reduceDIte] at h1
    have hcomp : (Q ψ).2.1 D = ((2 ^ m : ℕ) : ℚ)⁻¹ • ∑ h : A, char ψ h • Ptilde (projD D.1 h) := by
      simp only [Q, U, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, Pi.smul_apply,
        Finset.sum_apply]
    rw [hcomp, h1]
  have hQ_top_of_dual : ∀ (D : TopD) (φ : Fin (codimD D.1) → ZMod 2),
      (Q (dualProjD D.1 φ)).2.2.1 D = QSmat (castVec D.2 φ) := by
    intro D φ
    have hmem : dualProjD D.1 φ ∈ perp D.1 := (mem_perp_iff_exists_dualProjD D.1 _).mpr ⟨φ, rfl⟩
    have h1 := sum_char_projD_eq D.1 (fun y => Sdiag (castVec D.2 y)) (dualProjD D.1 φ)
    simp only [hmem, ↓reduceDIte] at h1
    have hch : Classical.choose ((mem_perp_iff_exists_dualProjD D.1 (dualProjD D.1 φ)).mp hmem) = φ :=
      dualProjD_injective D.1 (Classical.choose_spec ((mem_perp_iff_exists_dualProjD D.1 (dualProjD D.1 φ)).mp hmem))
    rw [hch] at h1
    have hcomp : (Q (dualProjD D.1 φ)).2.2.1 D =
        ((2 ^ m : ℕ) : ℚ)⁻¹ • ∑ h : A, char (dualProjD D.1 φ) h • Sdiag (castVec D.2 (projD D.1 h)) := by
      simp only [Q, U, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, Pi.smul_apply,
        Finset.sum_apply]
    rw [hcomp, h1]
    have hcd : codimD D.1 = j := D.2
    let eqv : (Fin (codimD D.1) → ZMod 2) ≃ (Fin j → ZMod 2) :=
      { toFun := castVec hcd
        invFun := castVec hcd.symm
        left_inv := fun v => by funext i; dsimp [castVec]; simp
        right_inv := fun v => by funext i; dsimp [castVec]; simp }
    dsimp only [QSmat]
    rw [show ((2 ^ codimD D.1 : ℕ) : ℚ) = ((2 ^ j : ℕ) : ℚ) by rw [hcd]]
    congr 1
    refine Fintype.sum_equiv eqv _ _ fun y => ?_
    dsimp only [eqv, Equiv.coe_fn_mk]
    rw [char_castVec hcd φ y]
  have hQ_top_of_not_mem : ∀ (D : TopD) (ψ : A), ψ ∉ perp D.1 → (Q ψ).2.2.1 D = 0 := by
    intro D ψ hnot
    have h1 := sum_char_projD_eq D.1 (fun y => Sdiag (castVec D.2 y)) ψ
    simp only [hnot, ↓reduceDIte] at h1
    have hcomp : (Q ψ).2.2.1 D =
        ((2 ^ m : ℕ) : ℚ)⁻¹ • ∑ h : A, char ψ h • Sdiag (castVec D.2 (projD D.1 h)) := by
      simp only [Q, U, Prod.smul_snd, Prod.smul_fst, Prod.snd_sum, Prod.fst_sum, Pi.smul_apply,
        Finset.sum_apply]
    rw [hcomp, h1]
  have hQ0_sub : ∀ D : SubD, (Q 0).2.1 D = Qmat 0 := fun D => by
    have h0 := hQ_sub_of_dual D 0; simpa using h0
  have hQ0_top : ∀ D : TopD, (Q 0).2.2.1 D = QSmat 0 := fun D => by
    have h0 := hQ_top_of_dual D 0; simpa [castVec_zero] using h0
  let Xop : A → AlgTy822 m j Schar := fun ψ => Q 0 * Φ [0] * Q ψ
  let Yop : A → AlgTy822 m j Schar := fun ψ => Q ψ * Φ [0] * Q 0
  let Zop : A → AlgTy822 m j Schar := fun ψ => Xop ψ * Yop ψ
  have hXop_mem : ∀ ψ : A, Xop ψ ∈ AlgPos := fun ψ =>
    hmul_mem _ (hmul_mem _ (hQ_mem 0) _ hΦ0) _ (hQ_mem ψ)
  have hYop_mem : ∀ ψ : A, Yop ψ ∈ AlgPos := fun ψ =>
    hmul_mem _ (hmul_mem _ (hQ_mem ψ) _ hΦ0) _ (hQ_mem 0)
  have hZop_mem : ∀ ψ : A, Zop ψ ∈ AlgPos := fun ψ =>
    hmul_mem _ (hXop_mem ψ) _ (hYop_mem ψ)
  have hZop_fst : ∀ ψ : A, ψ ≠ 0 → (Zop ψ).1 = 0 := fun ψ hψ => by
    simp [Zop, Xop, Yop, hQ_fst, hψ]
  have hZop_schar : ∀ ψ : A, ψ ≠ 0 → (Zop ψ).2.2.2 = 0 := fun ψ hψ => by
    funext α
    simp only [Zop, Xop, Yop, Prod.snd_mul, Pi.mul_apply, hQ_schar, hΦ0_val, mul_one, Pi.zero_apply]
    by_cases h0 : α.1 = 0
    · simp [h0, Ne.symm hψ]
    · simp [h0]
  have hZop_sub : ∀ (D : SubD) (ψ : A), ψ ≠ 0 →
      (Zop ψ).2.1 D = if ψ ∈ perp D.1 then (z * ((2 ^ codimD D.1 : ℕ) : ℚ)⁻¹) • rankOne vecE vecE else 0 := by
    intro D ψ hψ
    by_cases hmem : ψ ∈ perp D.1
    · simp only [hmem, ite_true]
      rcases (mem_perp_iff_exists_dualProjD D.1 ψ).mp hmem with ⟨φ, rfl⟩
      have hφ : φ ≠ 0 := by rintro rfl; exact hψ (map_zero _)
      simp only [Zop, Xop, Yop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hQ0_sub, hΦ0_val,
        hQ_sub_of_dual]
      rw [Q0_mul_T0_mul_Qpsi z φ hφ, Qpsi_mul_T0_mul_Q0 z φ hφ,
        smul_mul_smul_comm, rankOne_mul_rankOne, dot_VV]
      simp only [ite_true, smul_smul]
      congr 1
      have hq0 : ((2 ^ codimD D.1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp [hq0]
    · simp only [hmem, ite_false]
      simp [Zop, Xop, Yop, hQ_sub_of_not_mem D ψ hmem]
  have hZop_top : ∀ (D : TopD) (ψ : A), ψ ≠ 0 →
      (Zop ψ).2.2.1 D = if ψ ∈ perp D.1 then Matrix.single (none : IdxTop j) none (1 : ℚ) else 0 := by
    intro D ψ hψ
    by_cases hmem : ψ ∈ perp D.1
    · simp only [hmem, ite_true]
      rcases (mem_perp_iff_exists_dualProjD D.1 ψ).mp hmem with ⟨φ, rfl⟩
      have hφ : φ ≠ 0 := by rintro rfl; exact hψ (map_zero _)
      have hφ' : castVec D.2 φ ≠ 0 := fun h => hφ ((castVec_eq_zero_iff D.2 φ).mp h)
      simp only [Zop, Xop, Yop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hQ0_top, hΦ0_val,
        hQ_top_of_dual]
      rw [QSmat0_mul_S0_mul_QSmat (castVec D.2 φ) hφ', QSmat_mul_S0_mul_QSmat0 (castVec D.2 φ) hφ']
      ext p q
      simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
      cases p with
      | some a => simp
      | none =>
        cases q with
        | some b =>
          simp only [reduceCtorEq, and_false, ite_false]
          refine Finset.sum_eq_zero fun x _ => by simp
        | none =>
          rw [Finset.sum_eq_single (some ⟨castVec D.2 φ, hφ'⟩ : IdxTop j)]
          · simp
          · intro x _ hne; simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · simp only [hmem, ite_false]
      simp [Zop, Xop, Yop, hQ_top_of_not_mem D ψ hmem]
  have hprod_fst : ∀ L : List (AlgTy822 m j Schar), L.prod.1 = (L.map Prod.fst).prod := by
    intro L; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hprod_sub : ∀ (L : List (AlgTy822 m j Schar)) (D : SubD), L.prod.2.1 D = (L.map (fun a => a.2.1 D)).prod := by
    intro L D; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hprod_top : ∀ (L : List (AlgTy822 m j Schar)) (D : TopD), L.prod.2.2.1 D = (L.map (fun a => a.2.2.1 D)).prod := by
    intro L D; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hprod_schar : ∀ (L : List (AlgTy822 m j Schar)) (α : {α : A // α ∈ Schar}),
      L.prod.2.2.2 α = (L.map (fun a => a.2.2.2 α)).prod := by
    intro L α; induction L with | nil => rfl | cons a t ih => simp [ih]
  have hTop_all : ∀ (D : TopD) (M : Matrix (IdxTop j) (IdxTop j) ℚ), injTop D M ∈ AlgPos := by
    intro D
    have hfrW : Module.finrank (ZMod 2) (perp D.1) = j := by
      have h1 := finrank_perp D.1
      have h2 : codimD D.1 = j := D.2
      dsimp only [codimD] at h2; omega
    let bW : Module.Basis (Fin j) (ZMod 2) (perp D.1) :=
      (Module.finBasis (ZMod 2) (perp D.1)).reindex (finCongr hfrW)
    have hbW_ne : ∀ i : Fin j, (bW i).1 ≠ 0 := fun i h0 =>
      bW.ne_zero i (Subtype.ext h0)
    let L : List (AlgTy822 m j Schar) := List.ofFn (fun i : Fin j => Zop (bW i).1)
    have hL_ne : L ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      simp [L] at hlen; omega
    have hL_mem : L.prod ∈ AlgPos :=
      hlist_prod_mem L hL_ne fun a ha => by
        rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
        exact hZop_mem (bW i).1
    have hEnn_eq : L.prod = injTop D (Matrix.single (none : IdxTop j) none (1 : ℚ)) := by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · rw [hprod_fst]
        refine List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW ⟨0, by omega⟩).1,
          List.mem_ofFn.mpr ⟨⟨0, by omega⟩, rfl⟩, hZop_fst _ (hbW_ne _)⟩)
      · funext D'
        rw [hprod_sub]
        have hnot_le : ¬ (perp D.1 ≤ perp D'.1) := by
          intro hle
          have hfr1 := Submodule.finrank_mono hle
          have hfr2 : Module.finrank (ZMod 2) (perp D'.1) = codimD D'.1 := by
            have := finrank_perp D'.1; dsimp only [codimD]; omega
          have hlt : codimD D'.1 < j := D'.2.2
          omega
        have hex : ∃ i : Fin j, (bW i).1 ∉ perp D'.1 := by
          by_contra hall
          push Not at hall
          apply hnot_le
          intro x hx
          have hrep := bW.sum_repr ⟨x, hx⟩
          have hval : x = ∑ i : Fin j, (bW.repr ⟨x, hx⟩) i • (bW i).1 := by
            have := congrArg Subtype.val hrep
            rw [Submodule.coe_sum] at this
            exact this.symm
          rw [hval]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hall i)
        rcases hex with ⟨i, hi⟩
        refine List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW i).1,
          List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩)
        rw [hZop_sub D' _ (hbW_ne i)]; simp [hi]
      · funext D'
        rw [hprod_top]
        by_cases hDD' : D' = D
        · rcases hDD' with rfl
          simp only [injTop, Pi.single_eq_same]
          have hmap : L.map (fun a => a.2.2.1 D') =
              List.replicate j (Matrix.single (none : IdxTop j) none (1 : ℚ)) := by
            apply List.ext_getElem
            · simp [L]
            · intro idx h1 h2
              simp only [L, List.getElem_map, List.getElem_ofFn, List.getElem_replicate]
              rw [hZop_top D' _ (hbW_ne ⟨idx, by simp [L] at h1; exact h1⟩)]
              simp [(bW ⟨idx, by simp [L] at h1; exact h1⟩).2]
          rw [hmap]
          have hidemp : Matrix.single (none : IdxTop j) (none : IdxTop j) (1 : ℚ) *
              Matrix.single (none : IdxTop j) (none : IdxTop j) (1 : ℚ) =
              Matrix.single (none : IdxTop j) (none : IdxTop j) (1 : ℚ) := by
            ext p q; simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
            cases p <;> cases q
            · rw [Finset.sum_eq_single (none : IdxTop j)]
              · simp
              · intro x _ hne; simp [Ne.symm hne]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · refine Finset.sum_eq_zero fun x _ => by simp
            · refine Finset.sum_eq_zero fun x _ => by simp
            · refine Finset.sum_eq_zero fun x _ => by simp
          have hpow := list_prod_const_idemp (1 : ℚ) (Matrix.single (none : IdxTop j) none (1 : ℚ))
            hidemp j (by omega)
          simpa using hpow
        · simp only [injTop, Pi.single_eq_of_ne hDD']
          have hnot_le : ¬ (perp D.1 ≤ perp D'.1) := by
            intro hle
            have hfr' : Module.finrank (ZMod 2) (perp D'.1) = j := by
              have h1 := finrank_perp D'.1
              have h2 : codimD D'.1 = j := D'.2
              dsimp only [codimD] at h2; omega
            have heqW : perp D.1 = perp D'.1 := Submodule.eq_of_le_of_finrank_eq hle (by omega)
            exact hDD' (Subtype.ext (perp_inj heqW).symm)
          have hex : ∃ i : Fin j, (bW i).1 ∉ perp D'.1 := by
            by_contra hall
            push Not at hall
            apply hnot_le
            intro x hx
            have hrep := bW.sum_repr ⟨x, hx⟩
            have hval : x = ∑ i : Fin j, (bW.repr ⟨x, hx⟩) i • (bW i).1 := by
              have := congrArg Subtype.val hrep
              rw [Submodule.coe_sum] at this
              exact this.symm
            rw [hval]
            exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hall i)
          rcases hex with ⟨i, hi⟩
          refine List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW i).1,
            List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩)
          rw [hZop_top D' _ (hbW_ne i)]; simp [hi]
      · funext α
        rw [hprod_schar]
        refine List.prod_eq_zero (List.mem_map.mpr ⟨Zop (bW ⟨0, by omega⟩).1,
          List.mem_ofFn.mpr ⟨⟨0, by omega⟩, rfl⟩, by rw [hZop_schar _ (hbW_ne _)]; rfl⟩)
    have hEnn_mem : injTop D (Matrix.single (none : IdxTop j) none (1 : ℚ)) ∈ AlgPos := by
      rwa [← hEnn_eq]
    have hEns_mem : ∀ φ : NZ j, injTop D (Matrix.single (none : IdxTop j) (some φ) (1 : ℚ)) ∈ AlgPos := by
      intro φ
      let φ' : Fin (codimD D.1) → ZMod 2 := castVec D.2.symm φ.1
      have hcast : castVec D.2 φ' = φ.1 := by funext i; dsimp [φ', castVec]; simp
      have hprod : injTop D (Matrix.single (none : IdxTop j) none (1 : ℚ)) * Φ [0] * Q (dualProjD D.1 φ') =
          injTop D (Matrix.single (none : IdxTop j) (some φ) (1 : ℚ)) := by
        refine Prod.ext (by simp [injTop]) (Prod.ext (by funext D'; simp [injTop])
          (Prod.ext ?_ (by funext α; simp [injTop])))
        funext D'
        simp only [injTop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hΦ0_val]
        by_cases hEq : D' = D
        · rcases hEq with rfl
          simp only [Pi.single_eq_same, hQ_top_of_dual, hcast]
          rw [← QSmat_zero j, QSmat0_mul_S0_mul_QSmat φ.1 φ.2]
        · simp [Pi.single_eq_of_ne hEq]
      rw [← hprod]
      exact hmul_mem _ (hmul_mem _ hEnn_mem _ hΦ0) _ (hQ_mem _)
    have hEsn_mem : ∀ φ : NZ j, injTop D (Matrix.single (some φ : IdxTop j) none (1 : ℚ)) ∈ AlgPos := by
      intro φ
      let φ' : Fin (codimD D.1) → ZMod 2 := castVec D.2.symm φ.1
      have hcast : castVec D.2 φ' = φ.1 := by funext i; dsimp [φ', castVec]; simp
      have hprod : Q (dualProjD D.1 φ') * Φ [0] * injTop D (Matrix.single (none : IdxTop j) none (1 : ℚ)) =
          injTop D (Matrix.single (some φ : IdxTop j) none (1 : ℚ)) := by
        refine Prod.ext (by simp [injTop]) (Prod.ext (by funext D'; simp [injTop])
          (Prod.ext ?_ (by funext α; simp [injTop])))
        funext D'
        simp only [injTop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, hΦ0_val]
        by_cases hEq : D' = D
        · rcases hEq with rfl
          simp only [Pi.single_eq_same, hQ_top_of_dual, hcast]
          rw [← QSmat_zero j, QSmat_mul_S0_mul_QSmat0 φ.1 φ.2]
        · simp [Pi.single_eq_of_ne hEq]
      rw [← hprod]
      exact hmul_mem _ (hmul_mem _ (hQ_mem _) _ hΦ0) _ hEnn_mem
    have hEss_mem : ∀ φ ψ : NZ j, injTop D (Matrix.single (some φ : IdxTop j) (some ψ) (1 : ℚ)) ∈ AlgPos := by
      intro φ ψ
      have hprod : injTop D (Matrix.single (some φ : IdxTop j) none (1 : ℚ)) *
          injTop D (Matrix.single (none : IdxTop j) (some ψ) (1 : ℚ)) =
          injTop D (Matrix.single (some φ : IdxTop j) (some ψ) (1 : ℚ)) := by
        refine Prod.ext (by simp [injTop]) (Prod.ext (by funext D'; simp [injTop])
          (Prod.ext ?_ (by funext α; simp [injTop])))
        funext D'
        simp only [injTop, Prod.snd_mul, Prod.fst_mul, Pi.mul_apply]
        by_cases hEq : D' = D
        · rcases hEq with rfl
          simp only [Pi.single_eq_same]
          ext p q
          simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
          rw [Finset.sum_eq_single (none : IdxTop j)]
          · by_cases hp : some φ = p <;> by_cases hq : some ψ = q <;> simp [hp, hq]
          · intro x _ hne; simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · simp [Pi.single_eq_of_ne hEq]
      rw [← hprod]
      exact hmul_mem _ (hEsn_mem φ) _ (hEns_mem ψ)
    have hunit_mem : ∀ p q : IdxTop j, injTop D (Matrix.single p q (1 : ℚ)) ∈ AlgPos := fun p q => by
      cases p with
      | none => cases q with | none => exact hEnn_mem | some ψ => exact hEns_mem ψ
      | some φ => cases q with | none => exact hEsn_mem φ | some ψ => exact hEss_mem φ ψ
    intro M
    have hdecomp : injTop D M = ∑ p : IdxTop j, ∑ q : IdxTop j, M p q • injTop D (Matrix.single p q (1 : ℚ)) := by
      refine Prod.ext (by simp [injTop, Prod.fst_sum]) (Prod.ext
        (by funext D'; simp [injTop, Prod.snd_sum, Prod.fst_sum])
        (Prod.ext ?_ (by funext α; simp [injTop, Prod.snd_sum])))
      funext D'
      simp only [injTop, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst,
        Finset.sum_apply, Pi.smul_apply]
      by_cases hEq : D' = D
      · rcases hEq with rfl
        simp only [Pi.single_eq_same]
        ext p q
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single p]
        · rw [Finset.sum_eq_single q]
          · simp [Matrix.single]
          · intro y _ hne; simp [Matrix.single, hne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · intro x _ hne; refine Finset.sum_eq_zero fun y _ => by simp [Matrix.single, hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · simp [Pi.single_eq_of_ne hEq]
    rw [hdecomp]
    exact AlgPos.sum_mem fun p _ => AlgPos.sum_mem fun q _ => AlgPos.smul_mem _ (hunit_mem p q)
  have hSub_all : ∀ (D : SubD)
      (M : Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ),
      injSub D M ∈ AlgPos :=
    algPos_sub_all_jge2 hj Schar AlgPos hmul_mem hlist_prod_mem (Φ [0]) hΦ0 hΦ0_val Q hQ_mem
      hQ_sub_of_dual hQ0_sub Zop hZop_mem hZop_fst hZop_schar hZop_sub hTop_all
  have hSchar_nz : ∀ α : {α : A // α ∈ Schar}, α.1 ≠ 0 → injSchar α 1 ∈ AlgPos := by
    intro α hα
    let rem : AlgTy822 m j Schar := Q α.1 - (∑ D : SubD, injSub D ((Q α.1).2.1 D)) -
      (∑ D : TopD, injTop D ((Q α.1).2.2.1 D))
    have hrem_mem : rem ∈ AlgPos :=
      AlgPos.sub_mem (AlgPos.sub_mem (hQ_mem α.1)
        (AlgPos.sum_mem fun D _ => hSub_all D _))
        (AlgPos.sum_mem fun D _ => hTop_all D _)
    have hrem_eq : rem = injSchar α 1 := by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [rem, injSub, injTop, injSchar, Prod.fst_sum, hQ_fst, hα]
      · funext D
        simp only [rem, injSub, injTop, injSchar, Prod.snd_sub, Prod.fst_sub, Prod.snd_sum,
          Prod.fst_sum, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply, Finset.sum_const_zero, sub_zero]
        rw [Finset.sum_eq_single D]
        · simp [Pi.single_eq_same]
        · intro D' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · funext D
        simp only [rem, injSub, injTop, injSchar, Prod.snd_sub, Prod.fst_sub, Prod.snd_sum,
          Prod.fst_sum, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply, Finset.sum_const_zero, sub_zero]
        rw [Finset.sum_eq_single D]
        · simp [Pi.single_eq_same]
        · intro D' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · funext β
        simp only [rem, injSub, injTop, injSchar, Prod.snd_sub, Prod.snd_sum, Pi.sub_apply,
          Pi.zero_apply, Finset.sum_const_zero, sub_zero, hQ_schar]
        by_cases hEq : β = α
        · subst hEq; simp
        · have hne : β.1 ≠ α.1 := fun h => hEq (Subtype.ext h)
          simp [hEq, hne]
    rwa [← hrem_eq]
  let R0 : AlgTy822 m j Schar := Q 0 - (∑ D : SubD, injSub D ((Q 0).2.1 D)) - (∑ D : TopD, injTop D ((Q 0).2.2.1 D))
  have hR0_mem : R0 ∈ AlgPos :=
    AlgPos.sub_mem (AlgPos.sub_mem (hQ_mem 0)
      (AlgPos.sum_mem fun D _ => hSub_all D _))
      (AlgPos.sum_mem fun D _ => hTop_all D _)
  have hR0_val : R0 = (1, 0, 0, fun α => if α.1 = 0 then 1 else 0) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [R0, injSub, injTop, Prod.fst_sum, hQ_fst]
    · funext D
      simp only [R0, injSub, injTop, Prod.snd_sub, Prod.fst_sub, Prod.snd_sum, Prod.fst_sum,
        Pi.sub_apply, Finset.sum_apply, Pi.zero_apply, Finset.sum_const_zero, sub_zero]
      rw [Finset.sum_eq_single D]
      · simp [Pi.single_eq_same]
      · intro D' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · funext D
      simp only [R0, injSub, injTop, Prod.snd_sub, Prod.fst_sub, Prod.snd_sum, Prod.fst_sum,
        Pi.sub_apply, Finset.sum_apply, Pi.zero_apply, Finset.sum_const_zero, sub_zero]
      rw [Finset.sum_eq_single D]
      · simp [Pi.single_eq_same]
      · intro D' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · funext α
      simp [R0, injSub, injTop, Prod.snd_sum, hQ_schar]
  let R1 : AlgTy822 m j Schar := R0 * Φ [0]
  let R2 : AlgTy822 m j Schar := R1 * Φ [0]
  have hR1_mem : R1 ∈ AlgPos := hmul_mem _ hR0_mem _ hΦ0
  have hR2_mem : R2 ∈ AlgPos := hmul_mem _ hR1_mem _ hΦ0
  have hR1_val : R1 = (X0 z, 0, 0, fun α => if α.1 = 0 then 1 else 0) := by
    dsimp only [R1]; rw [hR0_val, hΦ0_val]
    refine Prod.ext (by simp) (Prod.ext (by funext D; simp) (Prod.ext (by funext D; simp)
      (by funext α; simp)))
  have hR2_val : R2 = (X0 z * X0 z, 0, 0, fun α => if α.1 = 0 then 1 else 0) := by
    dsimp only [R2]; rw [hR1_val, hΦ0_val]
    refine Prod.ext (by simp) (Prod.ext (by funext D; simp) (Prod.ext (by funext D; simp)
      (by funext α; simp)))
  have hB0_and_0 : injB0 1 ∈ AlgPos ∧ injB0 (X0 z) ∈ AlgPos ∧
      ∀ α : {α : A // α ∈ Schar}, injSchar α 1 ∈ AlgPos := by
    by_cases h0 : (0 : A) ∈ Schar
    · let Z0 : AlgTy822 m j Schar := R2 - (2 : ℚ) • R1 - (z - 2) • R0
      have hZ0_mem : Z0 ∈ AlgPos :=
        AlgPos.sub_mem (AlgPos.sub_mem hR2_mem (AlgPos.smul_mem 2 hR1_mem))
          (AlgPos.smul_mem (z - 2) hR0_mem)
      have hZ0_val : Z0 = (1 - z) • injSchar ⟨0, h0⟩ 1 := by
        dsimp only [Z0]; rw [hR2_val, hR1_val, hR0_val]
        refine Prod.ext ?_ (Prod.ext (by funext D; simp [injSchar]) (Prod.ext (by funext D; simp [injSchar]) ?_))
        · simp only [injSchar, Prod.fst_sub, Prod.smul_fst, smul_zero]
          rw [X0_sq z]; refine B0.ext ?_ ?_ <;> simp [X0] <;> ring
        · funext β
          simp only [injSchar, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          by_cases hβ : β = ⟨0, h0⟩
          · subst hβ; simp
          · have hne : β.1 ≠ 0 := fun h => hβ (Subtype.ext h)
            simp [hβ, hne]
      have he0_mem : injSchar ⟨0, h0⟩ 1 ∈ AlgPos := by
        rw [hZ0_val] at hZ0_mem
        have hsc := AlgPos.smul_mem (1 - z)⁻¹ hZ0_mem
        rwa [smul_smul, inv_mul_cancel₀ h1z, one_smul] at hsc
      have hB1 : injB0 1 ∈ AlgPos := by
        have heq : R0 - injSchar ⟨0, h0⟩ 1 = injB0 1 := by
          rw [hR0_val]
          refine Prod.ext (by simp [injB0, injSchar]) (Prod.ext (by funext D; simp [injB0, injSchar])
            (Prod.ext (by funext D; simp [injB0, injSchar]) ?_))
          funext β
          simp only [injB0, injSchar, Prod.snd_sub, Pi.sub_apply, Pi.zero_apply]
          by_cases hβ : β = ⟨0, h0⟩
          · subst hβ; simp
          · have hne : β.1 ≠ 0 := fun h => hβ (Subtype.ext h)
            simp [hβ, hne]
        rw [← heq]; exact AlgPos.sub_mem hR0_mem he0_mem
      have hBX : injB0 (X0 z) ∈ AlgPos := by
        have heq : R1 - injSchar ⟨0, h0⟩ 1 = injB0 (X0 z) := by
          rw [hR1_val]
          refine Prod.ext (by simp [injB0, injSchar]) (Prod.ext (by funext D; simp [injB0, injSchar])
            (Prod.ext (by funext D; simp [injB0, injSchar]) ?_))
          funext β
          simp only [injB0, injSchar, Prod.snd_sub, Pi.sub_apply, Pi.zero_apply]
          by_cases hβ : β = ⟨0, h0⟩
          · subst hβ; simp
          · have hne : β.1 ≠ 0 := fun h => hβ (Subtype.ext h)
            simp [hβ, hne]
        rw [← heq]; exact AlgPos.sub_mem hR1_mem he0_mem
      refine ⟨hB1, hBX, fun α => ?_⟩
      by_cases hα0 : α.1 = 0
      · have hEq : α = ⟨0, h0⟩ := Subtype.ext hα0
        rw [hEq]; exact he0_mem
      · exact hSchar_nz α hα0
    · have hB1 : injB0 1 ∈ AlgPos := by
        have heq : R0 = injB0 1 := by
          rw [hR0_val]
          refine Prod.ext (by simp [injB0]) (Prod.ext (by funext D; simp [injB0])
            (Prod.ext (by funext D; simp [injB0]) ?_))
          funext β
          have hne : β.1 ≠ 0 := fun h => h0 (h ▸ β.2)
          simp [injB0, hne]
        rwa [← heq]
      have hBX : injB0 (X0 z) ∈ AlgPos := by
        have heq : R1 = injB0 (X0 z) := by
          rw [hR1_val]
          refine Prod.ext (by simp [injB0]) (Prod.ext (by funext D; simp [injB0])
            (Prod.ext (by funext D; simp [injB0]) ?_))
          funext β
          have hne : β.1 ≠ 0 := fun h => h0 (h ▸ β.2)
          simp [injB0, hne]
        rwa [← heq]
      refine ⟨hB1, hBX, fun α => hSchar_nz α (fun h => h0 (h ▸ α.2))⟩
  rcases hB0_and_0 with ⟨hB1_mem, hBX_mem, hSchar_all⟩
  intro a
  have hB0_mem : injB0 a.1 ∈ AlgPos := by
    have heq : injB0 a.1 = a.1.a • injB0 1 + a.1.b • injB0 (X0 z) := by
      refine Prod.ext ?_ (Prod.ext (by funext D; simp [injB0])
        (Prod.ext (by funext D; simp [injB0]) (by funext α; simp [injB0])))
      refine B0.ext ?_ ?_ <;> simp [injB0, X0]
    rw [heq]
    exact AlgPos.add_mem (AlgPos.smul_mem _ hB1_mem) (AlgPos.smul_mem _ hBX_mem)
  have hdecomp : a = injB0 a.1 + (∑ D : SubD, injSub D (a.2.1 D)) +
      (∑ D : TopD, injTop D (a.2.2.1 D)) + ∑ α : {α : A // α ∈ Schar}, a.2.2.2 α • injSchar α 1 := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [injB0, injSub, injTop, injSchar, Prod.fst_sum]
    · funext D
      simp only [injB0, injSub, injTop, injSchar, Prod.snd_add, Prod.fst_add, Prod.snd_sum,
        Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.zero_apply, smul_zero, Finset.sum_const_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single D]
      · simp [Pi.single_eq_same]
      · intro D' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · funext D
      simp only [injB0, injSub, injTop, injSchar, Prod.snd_add, Prod.fst_add, Prod.snd_sum,
        Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.zero_apply, smul_zero, Finset.sum_const_zero, zero_add, add_zero]
      rw [Finset.sum_eq_single D]
      · simp [Pi.single_eq_same]
      · intro D' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · funext α
      simp only [injB0, injSub, injTop, injSchar, Prod.snd_add, Prod.snd_sum, Prod.smul_snd,
        Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single α]
      · simp
      · intro α' _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [hdecomp]
  exact AlgPos.add_mem (AlgPos.add_mem (AlgPos.add_mem hB0_mem
    (AlgPos.sum_mem fun D _ => hSub_all D _))
    (AlgPos.sum_mem fun D _ => hTop_all D _))
    (AlgPos.sum_mem fun α _ => AlgPos.smul_mem _ (hSchar_all α))

open Classical in
lemma lower_bound_jge2 {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2)) (hY : Y ≠ 0)
    (k : ℕ) (u v : Fin k → ℚ) (M : (Fin m → ZMod 2) → Matrix (Fin k) (Fin k) ℚ)
    (hfit : ∀ w : List (Fin m → ZMod 2), 0 < w.length →
      (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = countVal Y w) :
    letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
    let A := Fin m → ZMod 2
    let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
    let blocks : ℕ := ∑ D : Submodule (ZMod 2) A,
      let r := m - Module.finrank (ZMod 2) D
      if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2
    2 + 2 ^ m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0) ≤ k := by
  let : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  intro A rankY blocks
  let z : ℚ := ((2 ^ j : ℕ) : ℚ)
  let s : ℚ := ((2 ^ (m * j) : ℕ) : ℚ)⁻¹
  have hs0 : s ≠ 0 := by dsimp only [s]; positivity
  have hz_ge4 : (4 : ℚ) ≤ z := by
    dsimp only [z]
    have hnat : 4 ≤ 2 ^ j := by
      have h1 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
      omega
    exact_mod_cast hnat
  have hz1 : z ≠ 1 := by linarith
  let SubD := {D : Submodule (ZMod 2) A // 0 < codimD D ∧ codimD D < j}
  let TopD := {D : Submodule (ZMod 2) A // codimD D = j}
  let Schar : Finset A := if m < j ∧ 2 ≤ rankY then Finset.univ.erase 0 else Finset.univ
  let Φ : List A → AlgTy822 m j Schar := phi822 Schar
  have hΦ_append : ∀ w₁ w₂ : List A, Φ (w₁ ++ w₂) = Φ w₁ * Φ w₂ := phi822_append Schar
  let Λ : AlgTy822 m j Schar →ₗ[ℚ] ℚ :=
    { toFun := fun a => s * (coeffD Y ⊤ * tr0 a.1 +
        (∑ D : SubD, coeffD Y D.1 * Matrix.trace (a.2.1 D)) +
        (∑ D : TopD, coeffD Y D.1 * Matrix.trace (a.2.2.1 D)) +
        ∑ α : {α : A // α ∈ Schar}, (if α.1 = 0 then kappa0_num Y else kappa_nz_num Y α.1) * a.2.2.2 α)
      map_add' := fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, tr0_add, Pi.add_apply, Matrix.trace_add, mul_add,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c a => by
        simp only [Prod.smul_fst, Prod.smul_snd, tr0_smul, Pi.smul_apply, Matrix.trace_smul,
          smul_eq_mul, RingHom.id_apply]
        have h1 : (∑ D : SubD, coeffD Y D.1 * (c * Matrix.trace (a.2.1 D))) =
            c * ∑ D : SubD, coeffD Y D.1 * Matrix.trace (a.2.1 D) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun D _ => by ring
        have h2 : (∑ D : TopD, coeffD Y D.1 * (c * Matrix.trace (a.2.2.1 D))) =
            c * ∑ D : TopD, coeffD Y D.1 * Matrix.trace (a.2.2.1 D) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun D _ => by ring
        have h3 : (∑ α : {α : A // α ∈ Schar},
              (if α.1 = 0 then kappa0_num Y else kappa_nz_num Y α.1) * (c * a.2.2.2 α)) =
            c * ∑ α : {α : A // α ∈ Schar},
              (if α.1 = 0 then kappa0_num Y else kappa_nz_num Y α.1) * a.2.2.2 α := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun α _ => by ring
        rw [h1, h2, h3]; ring }
  have hΛ_Φ : ∀ w : List A, Λ (Φ w) = countVal Y w := by
    intro w
    rw [countVal_eq_sum_cycleD Y hY w, sum_coeffD_cycleD_decomp hj Y hY w]
    dsimp only [Λ, Φ, phi822, LinearMap.coe_mk, AddHom.coe_mk, s, z]
    congr 1; congr 1
    exact Finset.sum_coe_sort Schar (fun α => (if α = 0 then kappa0_num Y else kappa_nz_num Y α) * char α w.sum)
  have hcoeff_top_ne : coeffD Y (⊤ : Submodule (ZMod 2) A) ≠ 0 := by
    apply coeffD_ne_zero
    rw [finrank_top, Module.finrank_fin_fun]; omega
  have hcoeff_sub_ne : ∀ D : SubD, coeffD Y D.1 ≠ 0 := fun D =>
    coeffD_ne_zero Y D.1 (le_of_lt D.2.2)
  have hcoeff_topD_ne : ∀ D : TopD, coeffD Y D.1 ≠ 0 := fun D =>
    coeffD_ne_zero Y D.1 (le_of_eq D.2)
  have hcoeff_Schar_ne : ∀ α : {α : A // α ∈ Schar},
      (if α.1 = 0 then kappa0_num Y else kappa_nz_num Y α.1) ≠ 0 := by
    intro ⟨α, hα⟩
    by_cases h0 : α = 0
    · subst h0
      simp only [ite_true]
      intro hzero
      have hcond : m < j ∧ 2 ≤ rankY := (kappa0_num_eq_zero_iff hj Y hY).mp hzero
      dsimp only [Schar] at hα
      simp only [hcond] at hα
      exact (Finset.mem_erase.mp hα).1 rfl
    · simp only [h0, ite_false]
      exact kappa_nz_num_ne_zero hj Y α h0
  let injB0 : B0 z → AlgTy822 m j Schar := fun x => (x, 0, 0, 0)
  let injSub : (D : SubD) → Matrix (Option (Fin (codimD D.1) → ZMod 2)) (Option (Fin (codimD D.1) → ZMod 2)) ℚ → AlgTy822 m j Schar :=
    fun D M => (0, Pi.single D M, 0, 0)
  let injTop : TopD → Matrix (IdxTop j) (IdxTop j) ℚ → AlgTy822 m j Schar :=
    fun D M => (0, 0, Pi.single D M, 0)
  let injSchar : {α : A // α ∈ Schar} → ℚ → AlgTy822 m j Schar :=
    fun α c => (0, 0, 0, Pi.single α c)
  have hnondeg : ∀ a : AlgTy822 m j Schar, (∀ b : AlgTy822 m j Schar, Λ (a * b) = 0) → a = 0 := by
    intro a hall
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · apply tr0_nondeg hz1
      intro y
      have h := hall (injB0 y)
      simp only [Λ, injB0, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, mul_zero,
        Pi.zero_apply, Matrix.trace_zero, Finset.sum_const_zero, add_zero] at h
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs0)).resolve_left hcoeff_top_ne
    · funext D
      ext p q
      have h := hall (injSub D (Matrix.single q p (1 : ℚ)))
      simp only [Λ, injSub, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, mul_zero,
        tr0, B0_zero_a, B0_zero_b, zero_add, add_zero, Pi.zero_apply, Matrix.trace_zero,
        Finset.sum_const_zero] at h
      rw [Finset.sum_eq_single D] at h
      · simp only [Pi.mul_apply, Pi.single_eq_same] at h
        rw [trace_mul_single] at h
        exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs0)).resolve_left (hcoeff_sub_ne D)
      · intro D' _ hne
        simp only [Pi.mul_apply, Pi.single_eq_of_ne hne, mul_zero, Matrix.trace_zero]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · funext D
      ext p q
      have h := hall (injTop D (Matrix.single q p (1 : ℚ)))
      simp only [Λ, injTop, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, mul_zero,
        tr0, B0_zero_a, B0_zero_b, zero_add, add_zero, Pi.zero_apply, Matrix.trace_zero,
        Finset.sum_const_zero] at h
      rw [Finset.sum_eq_single D] at h
      · simp only [Pi.mul_apply, Pi.single_eq_same] at h
        rw [trace_mul_single] at h
        exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs0)).resolve_left (hcoeff_topD_ne D)
      · intro D' _ hne
        simp only [Pi.mul_apply, Pi.single_eq_of_ne hne, mul_zero, Matrix.trace_zero]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · funext α
      have h := hall (injSchar α 1)
      simp only [Λ, injSchar, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul, mul_zero,
        tr0, B0_zero_a, B0_zero_b, zero_add, add_zero, Pi.zero_apply, Matrix.trace_zero,
        Finset.sum_const_zero] at h
      rw [Finset.sum_eq_single α] at h
      · simp only [Pi.mul_apply, Pi.single_eq_same, mul_one] at h
        exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs0)).resolve_left (hcoeff_Schar_ne α)
      · intro α' _ hne
        simp only [Pi.mul_apply, Pi.single_eq_of_ne hne, mul_zero]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  let AlgPos : Submodule ℚ (AlgTy822 m j Schar) :=
    Submodule.span ℚ {a : AlgTy822 m j Schar | ∃ w : List A, 0 < w.length ∧ Φ w = a}
  have hAlgPos_top : ∀ a : AlgTy822 m j Schar, a ∈ AlgPos := algPos_eq_top_jge2 hj Schar
  let I := Fin 2 ⊕
    (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
    (TopD × (IdxTop j × IdxTop j)) ⊕
    {α : A // α ∈ Schar}
  let basisElem : I → AlgTy822 m j Schar := fun idx =>
    match idx with
    | Sum.inl t => if t = 0 then injB0 1 else injB0 (X0 z)
    | Sum.inr (Sum.inl ⟨D, p, q⟩) => injSub D (Matrix.single p q (1 : ℚ))
    | Sum.inr (Sum.inr (Sum.inl (D, p, q))) => injTop D (Matrix.single p q (1 : ℚ))
    | Sum.inr (Sum.inr (Sum.inr α)) => injSchar α 1
  have hrep : ∀ idx : I, ∃ (sw : Finset (List A)) (cf : List A → ℚ),
      (∀ w ∈ sw, 0 < w.length) ∧ (∑ w ∈ sw, cf w • Φ w) = basisElem idx := by
    intro idx
    have hmem : basisElem idx ∈ AlgPos := hAlgPos_top (basisElem idx)
    rw [Submodule.mem_span_set] at hmem
    rcases hmem with ⟨c, hc_supp, hc_sum⟩
    have hcho : ∀ a : AlgTy822 m j Schar, a ∈ c.support → ∃ w : List A, 0 < w.length ∧ Φ w = a := fun a ha =>
      hc_supp ha
    choose wOf hw_pos hw_eq using hcho
    let sw : Finset (List A) := c.support.attach.image (fun x => wOf x.1 x.2)
    let cf : List A → ℚ := fun w => ∑ x ∈ c.support.attach.filter (fun x => wOf x.1 x.2 = w), c x.1
    refine ⟨sw, cf, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
      exact hw_pos x.1 x.2
    · rw [← hc_sum]
      calc (∑ w ∈ sw, cf w • Φ w)
          = ∑ w ∈ sw, ∑ x ∈ c.support.attach.filter (fun x => wOf x.1 x.2 = w), c x.1 • Φ (wOf x.1 x.2) := by
            refine Finset.sum_congr rfl fun w _ => ?_
            dsimp only [cf]; rw [Finset.sum_smul]
            refine Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
        _ = ∑ x ∈ c.support.attach, c x.1 • Φ (wOf x.1 x.2) := by
            rw [← Finset.sum_fiberwise_of_maps_to (s := c.support.attach) (t := sw)
              (g := fun x => wOf x.1 x.2) (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩)]
        _ = ∑ x ∈ c.support.attach, c x.1 • x.1 :=
            Finset.sum_congr rfl fun x _ => by rw [hw_eq x.1 x.2]
        _ = c.sum (fun a r => r • a) := by
            rw [Finsupp.sum, Finset.sum_attach c.support (fun a => c a • a)]
  choose sRep cRep hs_pos hs_eq using hrep
  let rowVec : I → (Fin k → ℚ) := fun idx r =>
    ∑ w ∈ sRep idx, cRep idx w * ∑ i : Fin k, u i * (w.map M).prod i r
  have hlin : LinearIndependent ℚ rowVec := by
    rw [Fintype.linearIndependent_iff]
    intro β hβ
    let a : AlgTy822 m j Schar := ∑ idx : I, β idx • basisElem idx
    have ha_zero_pos : ∀ w' : List A, 0 < w'.length → Λ (a * Φ w') = 0 := by
      intro w' hw'
      have h1 : a * Φ w' = ∑ idx : I, β idx • ∑ w ∈ sRep idx, cRep idx w • Φ (w ++ w') := by
        dsimp only [a]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun idx _ => ?_
        rw [← hs_eq idx, smul_mul_assoc, Finset.sum_mul]
        congr 1; refine Finset.sum_congr rfl fun w _ => by rw [smul_mul_assoc, hΦ_append]
      rw [h1, map_sum]
      have h2 : (∑ idx : I, Λ (β idx • ∑ w ∈ sRep idx, cRep idx w • Φ (w ++ w'))) =
          ∑ r : Fin k, (∑ idx : I, β idx * rowVec idx r) * ∑ l : Fin k, (w'.map M).prod r l * v l := by
        have hterm : ∀ idx : I,
            Λ (β idx • ∑ w ∈ sRep idx, cRep idx w • Φ (w ++ w')) =
            ∑ r : Fin k, (β idx * rowVec idx r) * ∑ l : Fin k, (w'.map M).prod r l * v l := by
          intro idx
          rw [map_smul, map_sum, smul_eq_mul]
          have hinner : (∑ w ∈ sRep idx, Λ (cRep idx w • Φ (w ++ w'))) =
              ∑ r : Fin k, rowVec idx r * ∑ l : Fin k, (w'.map M).prod r l * v l := by
            calc (∑ w ∈ sRep idx, Λ (cRep idx w • Φ (w ++ w')))
                = ∑ w ∈ sRep idx, cRep idx w * ∑ i : Fin k, ∑ l : Fin k,
                    u i * ((w ++ w').map M).prod i l * v l := by
                  refine Finset.sum_congr rfl fun w _ => ?_
                  rw [map_smul, smul_eq_mul, hΛ_Φ, hfit (w ++ w') (by simp; omega)]
              _ = ∑ w ∈ sRep idx, cRep idx w * ∑ r : Fin k,
                    (∑ i : Fin k, u i * (w.map M).prod i r) * ∑ l : Fin k, (w'.map M).prod r l * v l := by
                  refine Finset.sum_congr rfl fun w _ => ?_
                  congr 1
                  simp_rw [List.map_append, List.prod_append, Matrix.mul_apply]
                  calc (∑ i : Fin k, ∑ l : Fin k, u i * (∑ r : Fin k, (w.map M).prod i r * (w'.map M).prod r l) * v l)
                      = ∑ i : Fin k, ∑ l : Fin k, ∑ r : Fin k,
                          (u i * (w.map M).prod i r) * ((w'.map M).prod r l * v l) := by
                        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
                        rw [Finset.mul_sum, Finset.sum_mul]
                        refine Finset.sum_congr rfl fun r _ => by ring
                    _ = ∑ i : Fin k, ∑ r : Fin k, ∑ l : Fin k,
                          (u i * (w.map M).prod i r) * ((w'.map M).prod r l * v l) :=
                        Finset.sum_congr rfl fun i _ => Finset.sum_comm
                    _ = ∑ r : Fin k, ∑ i : Fin k, ∑ l : Fin k,
                          (u i * (w.map M).prod i r) * ((w'.map M).prod r l * v l) := Finset.sum_comm
                    _ = ∑ r : Fin k, (∑ i : Fin k, u i * (w.map M).prod i r) *
                          ∑ l : Fin k, (w'.map M).prod r l * v l := by
                        refine Finset.sum_congr rfl fun r _ => ?_
                        rw [Finset.sum_mul]
                        refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm
              _ = ∑ r : Fin k, rowVec idx r * ∑ l : Fin k, (w'.map M).prod r l * v l := by
                  calc _ = ∑ w ∈ sRep idx, ∑ r : Fin k,
                          (cRep idx w * ∑ i : Fin k, u i * (w.map M).prod i r) *
                            ∑ l : Fin k, (w'.map M).prod r l * v l := by
                        refine Finset.sum_congr rfl fun w _ => ?_
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun r _ => by ring
                    _ = ∑ r : Fin k, ∑ w ∈ sRep idx,
                          (cRep idx w * ∑ i : Fin k, u i * (w.map M).prod i r) *
                            ∑ l : Fin k, (w'.map M).prod r l * v l := Finset.sum_comm
                    _ = _ := Finset.sum_congr rfl fun r _ => by dsimp only [rowVec]; rw [Finset.sum_mul]
          rw [hinner, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => by ring
        simp_rw [hterm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => (Finset.sum_mul ..).symm
      rw [h2]
      refine Finset.sum_eq_zero fun r _ => ?_
      have hr : (∑ idx : I, β idx * rowVec idx r) = 0 := by
        have := congrFun hβ r
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
      rw [hr, zero_mul]
    have ha_zero_all : ∀ b : AlgTy822 m j Schar, Λ (a * b) = 0 := by
      intro b
      refine Submodule.span_induction ?_ ?_ ?_ ?_ (hAlgPos_top b)
      · rintro _ ⟨w', hw', rfl⟩; exact ha_zero_pos w' hw'
      · rw [mul_zero, map_zero]
      · intro x y _ _ hx hy; rw [mul_add, map_add, hx, hy, add_zero]
      · intro c x _ hx; rw [mul_smul_comm, map_smul, hx, smul_zero]
    have ha0 : a = 0 := hnondeg a ha_zero_all
    intro idx
    rcases idx with t | (⟨D, p, q⟩ | (⟨D, p, q⟩ | α))
    · have ha1 : a.1 = 0 := congrArg Prod.fst ha0
      have ha1_eq : a.1 = β (Sum.inl 0) • (1 : B0 z) + β (Sum.inl 1) • X0 z := by
        dsimp only [a]
        rw [Prod.fst_sum]
        change (∑ x : Fin 2 ⊕
          (Σ D : SubD, Option (Fin (codimD D.1) → ZMod 2) × Option (Fin (codimD D.1) → ZMod 2)) ⊕
          (TopD × (IdxTop j × IdxTop j)) ⊕ {α : A // α ∈ Schar}, (β x • basisElem x).1) = _
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
        simp [basisElem, injB0, injSub, injTop, injSchar]
      rw [ha1_eq] at ha1
      fin_cases t
      · have := congrArg B0.a ha1; simpa [X0] using this
      · have := congrArg B0.b ha1; simpa [X0] using this
    · have h := congrArg (fun x : AlgTy822 m j Schar => x.2.1 D p q) ha0
      simp only [a, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, Prod.snd_zero,
        Prod.fst_zero, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply,
        Pi.zero_apply, Matrix.zero_apply, smul_eq_mul] at h
      rw [Finset.sum_eq_single (Sum.inr (Sum.inl ⟨D, p, q⟩))] at h
      · simpa [basisElem, injSub, Matrix.single] using h
      · intro idx' _ hne
        rcases idx' with t' | (⟨D', p', q'⟩ | (⟨D', p', q'⟩ | α'))
        · simp [basisElem, injB0]; split_ifs <;> simp
        · by_cases hD : D' = D
          · subst hD
            have hpq : ¬ (p' = p ∧ q' = q) := by rintro ⟨rfl, rfl⟩; exact hne rfl
            simp [basisElem, injSub, Matrix.single, hpq]
          · simp [basisElem, injSub, Pi.single_eq_of_ne (Ne.symm hD)]
        · simp [basisElem, injTop]
        · simp [basisElem, injSchar]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · have h := congrArg (fun x : AlgTy822 m j Schar => x.2.2.1 D p q) ha0
      simp only [a, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, Prod.snd_zero,
        Prod.fst_zero, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply,
        Pi.zero_apply, Matrix.zero_apply, smul_eq_mul] at h
      rw [Finset.sum_eq_single (Sum.inr (Sum.inr (Sum.inl (D, p, q))))] at h
      · simpa [basisElem, injTop, Matrix.single] using h
      · intro idx' _ hne
        rcases idx' with t' | (⟨D', p', q'⟩ | (⟨D', p', q'⟩ | α'))
        · simp [basisElem, injB0]; split_ifs <;> simp
        · simp [basisElem, injSub]
        · by_cases hD : D' = D
          · subst hD
            have hpq : ¬ (p' = p ∧ q' = q) := by rintro ⟨rfl, rfl⟩; exact hne rfl
            simp [basisElem, injTop, Matrix.single, hpq]
          · simp [basisElem, injTop, Pi.single_eq_of_ne (Ne.symm hD)]
        · simp [basisElem, injSchar]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · have h := congrArg (fun x : AlgTy822 m j Schar => x.2.2.2 α) ha0
      simp only [a, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Finset.sum_apply, Pi.smul_apply,
        Pi.zero_apply, smul_eq_mul] at h
      rw [Finset.sum_eq_single (Sum.inr (Sum.inr (Sum.inr α)))] at h
      · simpa [basisElem, injSchar] using h
      · intro idx' _ hne
        rcases idx' with t' | (⟨D', p', q'⟩ | (⟨D', p', q'⟩ | α'))
        · simp [basisElem, injB0]; split_ifs <;> simp
        · simp [basisElem, injSub]
        · simp [basisElem, injTop]
        · have hne' : α ≠ α' := fun heq => hne (by rw [heq])
          simp [basisElem, injSchar, Pi.single_eq_of_ne hne']
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
  have hcard_le : Fintype.card I ≤ Module.finrank ℚ (Fin k → ℚ) := hlin.fintype_card_le_finrank
  rw [Module.finrank_fin_fun, card_idx_eq_least hj Y] at hcard_le
  exact hcard_le

open Classical in
lemma solve_jge2 {m j : ℕ} (hj : 2 ≤ j) (Y : Fin j → (Fin m → ZMod 2)) (hY : Y ≠ 0) (k N : ℕ)
    (hN : N =
      letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
      let A := Fin m → ZMod 2
      let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
      let blocks : ℕ := ∑ D : Submodule (ZMod 2) A,
        let r := m - Module.finrank (ZMod 2) D
        if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2
      2 + 2 ^ m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0)) :
    ((∃ (u v : Fin k → ℚ) (M : (Fin m → ZMod 2) → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List (Fin m → ZMod 2), 0 < w.length →
          (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = countVal Y w) ↔
      N ≤ k) ∧
    ((∃ (u v : Fin k → ℚ) (M : (Fin m → ZMod 2) → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List (Fin m → ZMod 2), True →
          (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = countVal Y w) ↔
      N ≤ k) := by
  subst hN
  have hup :
      (letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
       let A := Fin m → ZMod 2
       let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
       let blocks : ℕ := ∑ D : Submodule (ZMod 2) A,
         let r := m - Module.finrank (ZMod 2) D
         if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2
       2 + 2 ^ m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0)) ≤ k →
      ∃ (u v : Fin k → ℚ) (M : (Fin m → ZMod 2) → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List (Fin m → ZMod 2), True →
          (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = countVal Y w := by
    intro hle
    have hbase := upper_bound_jge2 hj Y hY
    refine fits_pad (countVal Y) (fun _ => True) hle ?_
    rcases hbase with ⟨u, v, M, hM⟩
    exact ⟨u, v, M, fun w _ => hM w⟩
  have hlo :
      (∃ (u v : Fin k → ℚ) (M : (Fin m → ZMod 2) → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List (Fin m → ZMod 2), 0 < w.length →
          (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = countVal Y w) →
      (letI : Fintype (Submodule (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
       let A := Fin m → ZMod 2
       let rankY := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Y))
       let blocks : ℕ := ∑ D : Submodule (ZMod 2) A,
         let r := m - Module.finrank (ZMod 2) D
         if r = 0 ∨ j < r then 0 else (2 ^ r + (if r = j then 0 else 1)) ^ 2
       2 + 2 ^ m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0)) ≤ k := by
    rintro ⟨u, v, M, hM⟩
    exact lower_bound_jge2 hj Y hY k u v M hM
  refine ⟨⟨hlo, fun hle => by rcases hup hle with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩⟩,
    ⟨fun h => hlo (by rcases h with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩), hup⟩⟩

end PEqualNP.Outside.L_lib_822_aux

theorem PEqualNP.Outside.L_lib_822 :
    ∀ (m j : ℕ),
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let A := Fin m → F
      let C := Fin j → F
      letI : Fintype (Submodule F A) := Fintype.ofFinite _
      ∀ (Y : Fin j → A), Y ≠ 0 →
      let rankY := Module.finrank F (Submodule.span F (Set.range Y))
      let count := fun w : List A =>
        let next := fun i : Fin w.length =>
          (⟨(i.val+1) % w.length, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ : Fin w.length)
        let good := (Finset.univ : Finset (Fin w.length → C)).filter (fun x =>
          (∀ i, x i = 0 ∨ x (next i) = 0 ∨ x i = x (next i)) ∧
          (∀ b : Fin j, ∀ a : Fin m, (∑ i, w.get i a * x i b) = Y b a))
        (good.card : ℚ)
      let fits := fun (k : ℕ) (test : List A → Prop) =>
        ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
          ∀ w : List A, test w →
            (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) = count w
      let blocks : ℕ := ∑ D : Submodule F A,
        let r := m - Module.finrank F D
        if r = 0 ∨ j < r then 0 else (2^r + (if r = j then 0 else 1))^2
      let least : ℕ := if j = 1 then 2^m else
        2 + 2^m + blocks - (if m < j ∧ 2 ≤ rankY then 1 else 0)
      ∀ k : ℕ, (fits k (fun w => 0 < w.length) ↔ least ≤ k) ∧
        (fits k (fun _ => True) ↔ least ≤ k) := by
  intro m j F A C Y hY rankY count fits blocks least k
  have hcount_eq : ∀ w : List A, count w = PEqualNP.Outside.L_lib_822_aux.countVal Y w := fun w => by
    dsimp only [count, PEqualNP.Outside.L_lib_822_aux.countVal]
    exact congrArg (Nat.cast (R := ℚ)) (Finset.card_bij (fun x _ => x)
      (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx)
      (fun _ _ _ _ h => h)
      (fun x hx => ⟨x, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx, rfl⟩))
  have hfits_iff : ∀ (test : List A → Prop),
      fits k test ↔
      ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
        ∀ w : List A, test w →
          (∑ i : Fin k, ∑ l : Fin k, u i * (w.map M).prod i l * v l) =
          PEqualNP.Outside.L_lib_822_aux.countVal Y w := by
    intro test
    have hdec : (fun a b : Fin k => Classical.propDecidable (a = b)) = instDecidableEqFin k :=
      Subsingleton.elim _ _
    constructor <;> (rintro ⟨u, v, M, hM⟩; refine ⟨u, v, M, fun w hw => ?_⟩)
    · rw [← hcount_eq w, ← hM w hw]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      congr 2
      have h1 : @List.prod (Matrix (Fin k) (Fin k) ℚ) Matrix.instMulOfFintypeOfAddCommMonoid
          (@Matrix.one (Fin k) ℚ (fun a b => Classical.propDecidable (a = b)) _ _) (w.map M) =
          @List.prod (Matrix (Fin k) (Fin k) ℚ) Matrix.instMulOfFintypeOfAddCommMonoid
          (@Matrix.one (Fin k) ℚ (instDecidableEqFin k) _ _) (w.map M) := by rw [hdec]
      exact (congrFun (congrFun h1 i) l).symm
    · rw [hcount_eq w, ← hM w hw]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      congr 2
      have h1 : @List.prod (Matrix (Fin k) (Fin k) ℚ) Matrix.instMulOfFintypeOfAddCommMonoid
          (@Matrix.one (Fin k) ℚ (fun a b => Classical.propDecidable (a = b)) _ _) (w.map M) =
          @List.prod (Matrix (Fin k) (Fin k) ℚ) Matrix.instMulOfFintypeOfAddCommMonoid
          (@Matrix.one (Fin k) ℚ (instDecidableEqFin k) _ _) (w.map M) := by rw [hdec]
      exact congrFun (congrFun h1 i) l
  by_cases hj0 : j = 0
  · subst hj0; exfalso; apply hY; funext b; exact Fin.elim0 b
  · by_cases hj1 : j = 1
    · subst hj1
      have hleast : least = 2 ^ m := by dsimp only [least]; simp
      rw [hleast, hfits_iff, hfits_iff]
      exact PEqualNP.Outside.L_lib_822_aux.solve_j1 m Y hY k
    · have hj : 2 ≤ j := by omega
      rw [hfits_iff, hfits_iff]
      refine PEqualNP.Outside.L_lib_822_aux.solve_jge2 hj Y hY k least ?_
      dsimp only [least, blocks, rankY, F, A]
      simp only [hj1, ↓reduceIte]
      congr 1
      · congr 1
        refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun D _ => ?_
        split_ifs <;> simp_all
      · split_ifs <;> simp_all

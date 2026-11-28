import PEqualNP.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PEqualNP.Outside.L_lib_1003_aux

abbrev F2 := ZMod 2

private lemma zmod2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_mul_self (x : F2) : x * x = x := by
  fin_cases x <;> rfl

private lemma zmod2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_ne_zero_iff (x : F2) : x ≠ 0 ↔ x = 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · exact ⟨fun h => (h rfl).elim, fun h => (zero_ne_one h).elim⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

private lemma zmod2_eq_iff_add_eq_zero (x y : F2) : x = y ↔ x + y = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rcases zmod2_eq_zero_or_one y with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => (zero_ne_one h).elim, fun h => by rw [zero_add] at h; exact (one_ne_zero h).elim⟩
  · exact ⟨fun h => (one_ne_zero h).elim, fun h => by rw [add_zero] at h; exact (one_ne_zero h).elim⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

private lemma card_f2 : Fintype.card F2 = 2 := by
  decide

private lemma card_fun_f2 {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card (α → F2) = 2 ^ Fintype.card α := by
  rw [Fintype.card_pi]
  simp

private lemma card_fin_f2 (k : ℕ) : Fintype.card (Fin k → F2) = 2 ^ k := by
  rw [card_fun_f2, Fintype.card_fin]

private lemma vec_eq_of_linearMap {α : Type*} [Fintype α] [DecidableEq α]
    (ψ : (α → F2) →ₗ[F2] F2) :
    ∃ c : α → F2, ∀ x : α → F2, dotProduct c x = ψ x := by
  refine ⟨fun i => ψ (Pi.single i 1), fun x => ?_⟩
  have hx : x = ∑ i : α, x i • Pi.single i (1 : F2) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum]
  simp only [LinearMap.map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma exists_extend_dot {α : Type*} [Fintype α] [DecidableEq α]
    (W : Submodule F2 (α → F2)) (φ : W →ₗ[F2] F2) :
    ∃ c : α → F2, ∀ w : W, dotProduct c w.1 = φ w := by
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  let proj : (α → F2) →ₗ[F2] W := Submodule.projectionOnto W W' hW'
  obtain ⟨c, hc⟩ := vec_eq_of_linearMap (φ.comp proj)
  refine ⟨c, fun w => ?_⟩
  rw [hc w.1]
  change φ (Submodule.projectionOnto W W' hW' w.1) = φ w
  rw [Submodule.projectionOnto_apply_left]

private def orth {α : Type*} [Fintype α] (W : Submodule F2 (α → F2)) :
    Submodule F2 (α → F2) :=
  { carrier := { u | ∀ w ∈ W, dotProduct u w = 0 }
    zero_mem' := fun w _ => by simp, add_mem' := fun hu hv w hw => by rw [add_dotProduct, hu w hw, hv w hw, add_zero]
    smul_mem' := fun c u hu w hw => by rw [smul_dotProduct, hu w hw, smul_zero] }

private lemma mem_orth_iff {α : Type*} [Fintype α] (W : Submodule F2 (α → F2))
    (u : α → F2) : u ∈ orth W ↔ ∀ w ∈ W, dotProduct u w = 0 :=
  Iff.rfl

private lemma finrank_orth_ge {α : Type*} [Fintype α] [DecidableEq α]
    (W : Submodule F2 (α → F2)) :
    Fintype.card α ≤ Module.finrank F2 W + Module.finrank F2 (orth W) := by
  let b := Module.finBasis F2 W
  let Φ : (α → F2) →ₗ[F2] (Fin (Module.finrank F2 W) → F2) :=
    { toFun := fun u i => dotProduct u (b i).1
      map_add' := fun u v => by ext i; simp [add_dotProduct]
      map_smul' := fun c u => by ext i; simp [smul_dotProduct] }
  have hker : LinearMap.ker Φ = orth W := by
    ext u
    simp only [LinearMap.mem_ker, mem_orth_iff]
    constructor
    · intro hu w hw
      have hw' : (⟨w, hw⟩ : W) = ∑ i, b.repr ⟨w, hw⟩ i • b i := (b.sum_repr ⟨w, hw⟩).symm
      have hw1 : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i).1 := by
        calc w = W.subtype ⟨w, hw⟩ := rfl
          _ = W.subtype (∑ i, b.repr ⟨w, hw⟩ i • b i) := congrArg W.subtype hw'
          _ = ∑ i, b.repr ⟨w, hw⟩ i • (b i).1 := by simp only [map_sum, map_smul]; rfl
      rw [hw1, dotProduct_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, show dotProduct u (b i).1 = Φ u i from rfl, hu]
      simp
    · intro hu
      ext i
      exact hu (b i).1 (b i).2
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Module.finrank_self, mul_one] at hrk
  have hle : Module.finrank F2 (LinearMap.range Φ) ≤ Module.finrank F2 W := by
    calc Module.finrank F2 (LinearMap.range Φ)
        ≤ Module.finrank F2 (Fin (Module.finrank F2 W) → F2) := Submodule.finrank_le _
      _ = Module.finrank F2 W := by simp
  omega

private lemma finrank_orth_eq {α : Type*} [Fintype α] [DecidableEq α]
    (W : Submodule F2 (α → F2)) :
    Module.finrank F2 W + Module.finrank F2 (orth W) = Fintype.card α := by
  let b := Module.finBasis F2 W
  let Φ : (α → F2) →ₗ[F2] (Fin (Module.finrank F2 W) → F2) :=
    { toFun := fun u i => dotProduct u (b i).1
      map_add' := fun u v => by ext i; simp [add_dotProduct]
      map_smul' := fun c u => by ext i; simp [smul_dotProduct] }
  have hker : LinearMap.ker Φ = orth W := by
    ext u
    simp only [LinearMap.mem_ker, mem_orth_iff]
    constructor
    · intro hu w hw
      have hw' : (⟨w, hw⟩ : W) = ∑ i, b.repr ⟨w, hw⟩ i • b i := (b.sum_repr ⟨w, hw⟩).symm
      have hw1 : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i).1 := by
        calc w = W.subtype ⟨w, hw⟩ := rfl
          _ = W.subtype (∑ i, b.repr ⟨w, hw⟩ i • b i) := congrArg W.subtype hw'
          _ = ∑ i, b.repr ⟨w, hw⟩ i • (b i).1 := by simp only [map_sum, map_smul]; rfl
      rw [hw1, dotProduct_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, show dotProduct u (b i).1 = Φ u i from rfl, hu]
      simp
    · intro hu
      ext i
      exact hu (b i).1 (b i).2
  have horth_range : orth (LinearMap.range Φ) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hsum : (∑ i : Fin (Module.finrank F2 W), v i • b i) = 0 := by
      apply Subtype.ext
      ext a
      have ha := hv (Φ (Pi.single a 1)) ⟨Pi.single a 1, rfl⟩
      rw [dotProduct] at ha
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, single_dotProduct, one_mul] at ha
      simpa [Finset.sum_apply, smul_eq_mul] using ha
    have hli := Fintype.linearIndependent_iff.mp b.linearIndependent v hsum
    ext i
    exact hli i
  have hge := finrank_orth_ge (LinearMap.range Φ)
  rw [horth_range, finrank_bot, add_zero, Fintype.card_fin] at hge
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hker, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Module.finrank_self, mul_one] at hrk
  have hle : Module.finrank F2 (LinearMap.range Φ) ≤ Module.finrank F2 W := by
    calc Module.finrank F2 (LinearMap.range Φ)
        ≤ Module.finrank F2 (Fin (Module.finrank F2 W) → F2) := Submodule.finrank_le _
      _ = Module.finrank F2 W := by simp
  omega

private lemma orth_orth {α : Type*} [Fintype α] [DecidableEq α]
    (W : Submodule F2 (α → F2)) : orth (orth W) = W := by
  have hle : W ≤ orth (orth W) := by
    intro w hw u hu
    rw [dotProduct_comm]
    exact hu w hw
  have h1 := finrank_orth_eq W
  have h2 := finrank_orth_eq (orth W)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

private lemma card_ker_mul_le {V W : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    [AddCommGroup W] [Module F2 W] [Fintype W] (f : V →ₗ[F2] W) [Fintype (LinearMap.ker f)] :
    Fintype.card V ≤ Fintype.card (LinearMap.ker f) * Fintype.card W := by
  let _ : Fintype (LinearMap.range f) := Fintype.ofFinite _
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hV := Module.card_eq_pow_finrank (K := F2) (V := V)
  have hK := Module.card_eq_pow_finrank (K := F2) (V := LinearMap.ker f)
  have hW := Module.card_eq_pow_finrank (K := F2) (V := W)
  simp only [card_f2] at hV hK hW
  have hRle : Module.finrank F2 (LinearMap.range f) ≤ Module.finrank F2 W := Submodule.finrank_le _
  calc Fintype.card V = 2 ^ Module.finrank F2 V := hV
    _ = 2 ^ (Module.finrank F2 (LinearMap.range f) + Module.finrank F2 (LinearMap.ker f)) := by
          rw [hrk]
    _ = 2 ^ Module.finrank F2 (LinearMap.ker f) * 2 ^ Module.finrank F2 (LinearMap.range f) := by
          rw [pow_add, mul_comm]
    _ ≤ 2 ^ Module.finrank F2 (LinearMap.ker f) * 2 ^ Module.finrank F2 W :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hRle)
    _ = Fintype.card (LinearMap.ker f) * Fintype.card W := by rw [← hK, ← hW]

private lemma card_ker_mul_eq_of_surj {V W : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    [AddCommGroup W] [Module F2 W] [Fintype W] (f : V →ₗ[F2] W) [Fintype (LinearMap.ker f)]
    (hsurj : Function.Surjective f) :
    Fintype.card (LinearMap.ker f) * Fintype.card W = Fintype.card V := by
  have htop : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, finrank_top] at hrk
  have hV := Module.card_eq_pow_finrank (K := F2) (V := V)
  have hK := Module.card_eq_pow_finrank (K := F2) (V := LinearMap.ker f)
  have hW := Module.card_eq_pow_finrank (K := F2) (V := W)
  simp only [card_f2] at hV hK hW
  rw [hK, hW, hV, ← pow_add, add_comm, hrk]

private def Quad {k : ℕ} (f : (Fin k → F2) → F2) : Prop :=
  ∃ (b : F2) (l : Fin k → F2) (M : Fin k → Fin k → F2),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j

private lemma quad_const {k : ℕ} (b : F2) : Quad (k := k) (fun _ => b) :=
  ⟨b, 0, fun _ _ => 0, fun _ => by simp⟩

private lemma quad_linear {k : ℕ} (l : Fin k → F2) : Quad (k := k) (fun s => dotProduct l s) :=
  ⟨0, l, fun _ _ => 0, fun _ => by simp⟩

private lemma quad_mul_linear {k : ℕ} (a b : Fin k → F2) :
    Quad (k := k) (fun s => dotProduct a s * dotProduct b s) := by
  refine ⟨0, 0, fun i j => a i * b j, fun s => ?_⟩
  dsimp only
  rw [zero_dotProduct, zero_add, zero_add]
  simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma quad_add {k : ℕ} {f g : (Fin k → F2) → F2} (hf : Quad f) (hg : Quad g) :
    Quad (fun s => f s + g s) := by
  rcases hf with ⟨b1, l1, M1, h1⟩
  rcases hg with ⟨b2, l2, M2, h2⟩
  refine ⟨b1 + b2, l1 + l2, fun i j => M1 i j + M2 i j, fun s => ?_⟩
  dsimp only
  rw [h1 s, h2 s, add_dotProduct]
  have hM : ∑ i, ∑ j, (M1 i j + M2 i j) * s i * s j =
      (∑ i, ∑ j, M1 i j * s i * s j) + (∑ i, ∑ j, M2 i j * s i * s j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hM]
  ring

private lemma quad_smul {k : ℕ} (c : F2) {f : (Fin k → F2) → F2} (hf : Quad f) :
    Quad (fun s => c * f s) := by
  rcases hf with ⟨b, l, M, h⟩
  refine ⟨c * b, c • l, fun i j => c * M i j, fun s => ?_⟩
  dsimp only
  rw [h s, smul_dotProduct, smul_eq_mul]
  have hM : ∑ i, ∑ j, c * M i j * s i * s j = c * ∑ i, ∑ j, M i j * s i * s j := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hM]
  ring

private lemma quad_coord {k : ℕ} (i : Fin k) : Quad (k := k) (fun s => s i) := by
  have := quad_linear (k := k) (Pi.single i 1)
  convert this using 1
  ext s
  simp [single_dotProduct]

private lemma quad_coord_mul {k : ℕ} (i j : Fin k) : Quad (k := k) (fun s => s i * s j) := by
  have := quad_mul_linear (k := k) (Pi.single i 1) (Pi.single j 1)
  convert this using 1
  ext s
  simp [single_dotProduct]

private def quadSub {k : ℕ} (E : Finset (Fin k → F2)) : Submodule F2 (E → F2) :=
  { carrier := { g | ∃ f : (Fin k → F2) → F2, Quad f ∧ ∀ x : E, g x = f x.1 }
    zero_mem' := ⟨fun _ => 0, quad_const 0, fun _ => rfl⟩, add_mem' := fun ⟨f1, hf1, h1⟩ ⟨f2, hf2, h2⟩ =>
      ⟨fun s => f1 s + f2 s, quad_add hf1 hf2, fun x => by simp [h1 x, h2 x]⟩
    smul_mem' := fun c _ ⟨f, hf, h⟩ =>
      ⟨fun s => c * f s, quad_smul c hf, fun x => by simp [h x]⟩ }

private def indE {k : ℕ} (E : Finset (Fin k → F2)) (U : Finset (Fin k → F2)) : E → F2 :=
  fun x => if x.1 ∈ U then 1 else 0

private def suppE {k : ℕ} (E : Finset (Fin k → F2)) (u : E → F2) : Finset (Fin k → F2) :=
  E.filter (fun s => ∃ h : s ∈ E, u ⟨s, h⟩ = 1)

private lemma suppE_subset {k : ℕ} (E : Finset (Fin k → F2)) (u : E → F2) :
    suppE E u ⊆ E :=
  Finset.filter_subset _ _

private lemma mem_suppE_iff {k : ℕ} (E : Finset (Fin k → F2)) (u : E → F2) (x : E) :
    x.1 ∈ suppE E u ↔ u x = 1 := by
  simp [suppE, x.2]

private lemma indE_suppE {k : ℕ} (E : Finset (Fin k → F2)) (u : E → F2) :
    indE E (suppE E u) = u := by
  ext x
  simp only [indE, mem_suppE_iff]
  rcases zmod2_eq_zero_or_one (u x) with h | h <;> simp [h]

private lemma suppE_indE {k : ℕ} (E : Finset (Fin k → F2)) {U : Finset (Fin k → F2)}
    (hU : U ⊆ E) : suppE E (indE E U) = U := by
  ext s
  dsimp only [suppE]
  rw [Finset.mem_filter]
  simp only [indE]
  constructor
  · rintro ⟨_, _, h1⟩
    by_contra hns
    simp [hns] at h1
  · intro hs
    exact ⟨hU hs, ⟨hU hs, by simp [hs]⟩⟩

private lemma sum_eq_dot_indE {k : ℕ} (E : Finset (Fin k → F2)) {U : Finset (Fin k → F2)}
    (hU : U ⊆ E) (f : (Fin k → F2) → F2) :
    ∑ s ∈ U, f s = dotProduct (indE E U) (fun x : E => f x.1) := by
  simp only [dotProduct, indE]
  rw [Finset.sum_coe_sort E (fun s => (if s ∈ U then (1 : F2) else 0) * f s)]
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  congr 1
  ext s
  simp only [Finset.mem_filter]
  exact ⟨fun hs => ⟨hU hs, hs⟩, fun h => h.2⟩

private lemma dot_eq_sum_suppE {k : ℕ} (E : Finset (Fin k → F2)) (u : E → F2)
    (f : (Fin k → F2) → F2) :
    dotProduct u (fun x : E => f x.1) = ∑ s ∈ suppE E u, f s := by
  rw [sum_eq_dot_indE E (suppE_subset E u) f, indE_suppE]

private noncomputable def relSet {k : ℕ} (E : Finset (Fin k → F2)) : Finset (Finset (Fin k → F2)) :=
  E.powerset.filter (fun U => @decide
    (∀ f : (Fin k → F2) → F2, Quad f → (∑ s ∈ U, f s) = 0) (Classical.propDecidable _))

private lemma mem_relSet_iff {k : ℕ} (E : Finset (Fin k → F2)) (U : Finset (Fin k → F2)) :
    U ∈ relSet E ↔ U ⊆ E ∧ ∀ f : (Fin k → F2) → F2, Quad f → (∑ s ∈ U, f s) = 0 := by
  simp [relSet, Finset.mem_powerset]

private lemma indE_mem_orth_iff {k : ℕ} (E : Finset (Fin k → F2)) {U : Finset (Fin k → F2)}
    (hU : U ⊆ E) : indE E U ∈ orth (quadSub E) ↔ U ∈ relSet E := by
  rw [mem_orth_iff, mem_relSet_iff]
  constructor
  · intro h
    refine ⟨hU, fun f hf => ?_⟩
    rw [sum_eq_dot_indE E hU f]
    exact h (fun x : E => f x.1) ⟨f, hf, fun _ => rfl⟩
  · rintro ⟨_, h⟩ g ⟨f, hf, hfg⟩
    have hfun : g = fun x : E => f x.1 := funext hfg
    rw [hfun, ← sum_eq_dot_indE E hU f]
    exact h f hf

private lemma suppE_mem_relSet_iff {k : ℕ} (E : Finset (Fin k → F2)) (u : E → F2) :
    suppE E u ∈ relSet E ↔ u ∈ orth (quadSub E) := by
  rw [← indE_mem_orth_iff E (suppE_subset E u), indE_suppE]

private noncomputable def relEquiv {k : ℕ} (E : Finset (Fin k → F2)) :
    (relSet E) ≃ orth (quadSub E) :=
  { toFun := fun U => ⟨indE E U.1, (indE_mem_orth_iff E ((mem_relSet_iff E U.1).mp U.2).1).mpr U.2⟩
    invFun := fun u => ⟨suppE E u.1, (suppE_mem_relSet_iff E u.1).mpr u.2⟩
    left_inv := fun U => Subtype.ext (suppE_indE E ((mem_relSet_iff E U.1).mp U.2).1)
    right_inv := fun u => Subtype.ext (indE_suppE E u.1) }

private lemma exists_quad_agree_iff {k : ℕ} (E : Finset (Fin k → F2)) (g : (Fin k → F2) → F2) :
    (∃ f : (Fin k → F2) → F2, Quad f ∧ ∀ s ∈ E, g s = f s) ↔
    (∀ U ∈ relSet E, ∑ s ∈ U, g s = 0) := by
  have h1 : (∃ f : (Fin k → F2) → F2, Quad f ∧ ∀ s ∈ E, g s = f s) ↔
      (fun x : E => g x.1) ∈ quadSub E := by
    constructor
    · rintro ⟨f, hf, hfg⟩
      exact ⟨f, hf, fun x => hfg x.1 x.2⟩
    · rintro ⟨f, hf, hfg⟩
      exact ⟨f, hf, fun s hs => hfg ⟨s, hs⟩⟩
  rw [h1, ← orth_orth (quadSub E), mem_orth_iff]
  constructor
  · intro h U hU
    rw [sum_eq_dot_indE E ((mem_relSet_iff E U).mp hU).1 g, dotProduct_comm]
    exact h (indE E U) ((indE_mem_orth_iff E ((mem_relSet_iff E U).mp hU).1).mpr hU)
  · intro h u hu
    rw [dotProduct_comm, dot_eq_sum_suppE]
    exact h (suppE E u) ((suppE_mem_relSet_iff E u).mpr hu)

private def tripleF {k : ℕ} (a b c s : Fin k → F2) : F2 :=
  dotProduct a s * dotProduct b s * dotProduct c s

private def sigF {k : ℕ} (U : Finset (Fin k → F2)) (a b c : Fin k → F2) : F2 :=
  ∑ s ∈ U, tripleF a b c s

private lemma sigF_eq_dot {k : ℕ} (U : Finset (Fin k → F2)) (a b c : Fin k → F2) :
    sigF U a b c = dotProduct c (fun j => ∑ s ∈ U, dotProduct a s * dotProduct b s * s j) := by
  rw [dotProduct]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sigF, tripleF]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show dotProduct c s = ∑ j, c j * s j from rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private def fitF {k : ℕ} (E : Finset (Fin k → F2)) (h : (Fin k → F2) → F2)
    (a b : Fin k → F2) : Prop :=
  ∃ (c : Fin k → F2) (f : (Fin k → F2) → F2), Quad f ∧ ∀ s ∈ E, h s = f s + tripleF a b c s

private lemma fitF_iff {k : ℕ} (E : Finset (Fin k → F2)) (h : (Fin k → F2) → F2)
    (a b : Fin k → F2) :
    fitF E h a b ↔
      ∀ U ∈ (relSet E).filter (fun U => (∑ s ∈ U, h s) = 1), ∃ c : Fin k → F2, sigF U a b c = 1 := by
  have hstep1 : fitF E h a b ↔
      ∃ c : Fin k → F2, ∀ U ∈ relSet E, sigF U a b c = ∑ s ∈ U, h s := by
    constructor
    · rintro ⟨c, f, hf, hfeq⟩
      refine ⟨c, fun U hU => ?_⟩
      have hsub := ((mem_relSet_iff E U).mp hU).1
      have hf0 := ((mem_relSet_iff E U).mp hU).2 f hf
      have hsum : ∑ s ∈ U, h s = (∑ s ∈ U, f s) + sigF U a b c := by
        simp only [sigF, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s hs => hfeq s (hsub hs)
      rw [hsum, hf0, zero_add]
    · rintro ⟨c, hc⟩
      have hq : ∀ U ∈ relSet E, ∑ s ∈ U, (h s + tripleF a b c s) = 0 := by
        intro U hU
        rw [Finset.sum_add_distrib]
        change (∑ s ∈ U, h s) + sigF U a b c = 0
        rw [hc U hU, zmod2_add_self]
      obtain ⟨f, hf, hfg⟩ := (exists_quad_agree_iff E (fun s => h s + tripleF a b c s)).mpr hq
      refine ⟨c, f, hf, fun s hs => ?_⟩
      have h1 := hfg s hs
      calc h s = (h s + tripleF a b c s) + tripleF a b c s := by
              rw [add_assoc, zmod2_add_self, add_zero]
        _ = f s + tripleF a b c s := by rw [h1]
  rw [hstep1]
  let R := orth (quadSub E)
  let L : R →ₗ[F2] (Fin k → F2) :=
    { toFun := fun u j => dotProduct u.1 (fun x : E => dotProduct a x.1 * dotProduct b x.1 * x.1 j)
      map_add' := fun u v => by ext j; simp [add_dotProduct]
      map_smul' := fun r u => by ext j; simp [smul_dotProduct] }
  let lam : R →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct u.1 (fun x : E => h x.1)
      map_add' := fun u v => by simp [add_dotProduct]
      map_smul' := fun r u => by simp [smul_dotProduct] }
  have hL_sig : ∀ (u : R) (c : Fin k → F2),
      dotProduct c (L u) = sigF (suppE E u.1) a b c := by
    intro u c
    rw [sigF_eq_dot]
    congr 1
    ext j
    exact dot_eq_sum_suppE E u.1 (fun s => dotProduct a s * dotProduct b s * s j)
  have hlam_sum : ∀ u : R, lam u = ∑ s ∈ suppE E u.1, h s := by
    intro u
    exact dot_eq_sum_suppE E u.1 h
  constructor
  · rintro ⟨c, hc⟩ U hU
    rw [Finset.mem_filter] at hU
    exact ⟨c, by rw [hc U hU.1, hU.2]⟩
  · intro hall
    have hker : LinearMap.ker L ≤ LinearMap.ker lam := by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      by_contra hne
      have h1 : lam u = 1 := (zmod2_ne_zero_iff _).mp hne
      have hUrel : suppE E u.1 ∈ relSet E := (suppE_mem_relSet_iff E u.1).mpr u.2
      have hUodd : suppE E u.1 ∈ (relSet E).filter (fun U => (∑ s ∈ U, h s) = 1) := by
        rw [Finset.mem_filter]
        exact ⟨hUrel, by rw [← hlam_sum u, h1]⟩
      obtain ⟨c, hc⟩ := hall (suppE E u.1) hUodd
      have h0 : sigF (suppE E u.1) a b c = 0 := by
        rw [← hL_sig u c, hu, dotProduct_zero]
      rw [h0] at hc
      exact zero_ne_one hc
    let φ : LinearMap.range L →ₗ[F2] F2 :=
      { toFun := fun y => lam (Classical.choose y.2)
        map_add' := fun y1 y2 => by
          have h1 := Classical.choose_spec y1.2
          have h2 := Classical.choose_spec y2.2
          have h12 := Classical.choose_spec (y1 + y2).2
          have hdiff : Classical.choose (y1 + y2).2 - (Classical.choose y1.2 + Classical.choose y2.2) ∈
              LinearMap.ker L := by
            rw [LinearMap.mem_ker, map_sub, map_add, h12, h1, h2]
            exact sub_self _
          have hlam0 := hker hdiff
          rw [LinearMap.mem_ker, map_sub, map_add, sub_eq_zero] at hlam0
          exact hlam0
        map_smul' := fun r y => by
          have hy := Classical.choose_spec y.2
          have hry := Classical.choose_spec (r • y).2
          have hdiff : Classical.choose (r • y).2 - r • Classical.choose y.2 ∈ LinearMap.ker L := by
            rw [LinearMap.mem_ker, map_sub, map_smul, hry, hy]
            exact sub_self _
          have hlam0 := hker hdiff
          rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hlam0
          simpa using hlam0 }
    obtain ⟨c, hc⟩ := exists_extend_dot (LinearMap.range L) φ
    refine ⟨c, fun U hU => ?_⟩
    let u : R := relEquiv E ⟨U, hU⟩
    have hsupp : suppE E u.1 = U := suppE_indE E ((mem_relSet_iff E U).mp hU).1
    rw [← hsupp, ← hL_sig u c, ← hlam_sum u]
    have hEq := hc ⟨L u, ⟨u, rfl⟩⟩
    have hspec := Classical.choose_spec (⟨u, rfl⟩ : L u ∈ LinearMap.range L)
    have hdiff : Classical.choose (⟨u, rfl⟩ : L u ∈ LinearMap.range L) - u ∈ LinearMap.ker L := by
      rw [LinearMap.mem_ker, map_sub, hspec, sub_self]
    have hlam0 := hker hdiff
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hlam0
    simpa [φ, hlam0] using hEq

private lemma sigF_symm12 {k : ℕ} (U : Finset (Fin k → F2)) (a b c : Fin k → F2) :
    sigF U a b c = sigF U b a c := by
  simp only [sigF, tripleF]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

private lemma sigF_symm23 {k : ℕ} (U : Finset (Fin k → F2)) (a b c : Fin k → F2) :
    sigF U a b c = sigF U a c b := by
  simp only [sigF, tripleF]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

private lemma sigF_add_left {k : ℕ} (U : Finset (Fin k → F2)) (a1 a2 b c : Fin k → F2) :
    sigF U (a1 + a2) b c = sigF U a1 b c + sigF U a2 b c := by
  simp only [sigF, tripleF, add_dotProduct, add_mul, Finset.sum_add_distrib]

private lemma sigF_add_mid {k : ℕ} (U : Finset (Fin k → F2)) (a b1 b2 c : Fin k → F2) :
    sigF U a (b1 + b2) c = sigF U a b1 c + sigF U a b2 c := by
  rw [sigF_symm12, sigF_add_left, sigF_symm12, sigF_symm12 U b2]

private lemma sigF_add_right {k : ℕ} (U : Finset (Fin k → F2)) (a b c1 c2 : Fin k → F2) :
    sigF U a b (c1 + c2) = sigF U a b c1 + sigF U a b c2 := by
  rw [sigF_symm23, sigF_add_mid, sigF_symm23, sigF_symm23 U a c2]

private lemma sigF_smul_left {k : ℕ} (U : Finset (Fin k → F2)) (r : F2) (a b c : Fin k → F2) :
    sigF U (r • a) b c = r * sigF U a b c := by
  simp only [sigF, tripleF, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

private lemma sigF_smul_mid {k : ℕ} (U : Finset (Fin k → F2)) (r : F2) (a b c : Fin k → F2) :
    sigF U a (r • b) c = r * sigF U a b c := by
  rw [sigF_symm12, sigF_smul_left, sigF_symm12]

private lemma sigF_smul_right {k : ℕ} (U : Finset (Fin k → F2)) (r : F2) (a b c : Fin k → F2) :
    sigF U a b (r • c) = r * sigF U a b c := by
  rw [sigF_symm23, sigF_smul_mid, sigF_symm23]

private lemma sigF_diag12 {k : ℕ} {E U : Finset (Fin k → F2)} (hU : U ∈ relSet E)
    (a c : Fin k → F2) : sigF U a a c = 0 := by
  have h1 : ∀ s, tripleF a a c s = dotProduct a s * dotProduct c s := by
    intro s
    simp only [tripleF, zmod2_mul_self]
  simp only [sigF, h1]
  exact ((mem_relSet_iff E U).mp hU).2 _ (quad_mul_linear a c)

private lemma sigF_diag23 {k : ℕ} {E U : Finset (Fin k → F2)} (hU : U ∈ relSet E)
    (a b : Fin k → F2) : sigF U a b b = 0 := by
  rw [sigF_symm12, sigF_symm23, sigF_symm12]
  exact sigF_diag12 hU b a

private lemma sigF_diag13 {k : ℕ} {E U : Finset (Fin k → F2)} (hU : U ∈ relSet E)
    (a b : Fin k → F2) : sigF U a b a = 0 := by
  rw [sigF_symm23]
  exact sigF_diag12 hU a b

private lemma odd_card_le_half_rel {k : ℕ} (E : Finset (Fin k → F2)) (h : (Fin k → F2) → F2)
    (hne : ((relSet E).filter (fun U => (∑ s ∈ U, h s) = 1)).Nonempty) :
    2 * ((relSet E).filter (fun U => (∑ s ∈ U, h s) = 1)).card = (relSet E).card := by
  let R := orth (quadSub E)
  let _ : Fintype R := Fintype.ofFinite R
  let lam : R →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct u.1 (fun x : E => h x.1)
      map_add' := fun u v => by simp [add_dotProduct]
      map_smul' := fun r u => by simp [smul_dotProduct] }
  let _ : Fintype (LinearMap.ker lam) := Fintype.ofFinite _
  obtain ⟨U0, hU0⟩ := hne
  rw [Finset.mem_filter] at hU0
  let u0 : R := relEquiv E ⟨U0, hU0.1⟩
  have hu0 : lam u0 = 1 := by
    change dotProduct u0.1 (fun x : E => h x.1) = 1
    rw [dot_eq_sum_suppE E u0.1 h]
    change ∑ s ∈ suppE E (indE E U0), h s = 1
    rw [suppE_indE E ((mem_relSet_iff E U0).mp hU0.1).1, hU0.2]
  have hsurj : Function.Surjective lam := by
    intro y
    rcases zmod2_eq_zero_or_one y with rfl | rfl
    · exact ⟨0, map_zero lam⟩
    · exact ⟨u0, hu0⟩
  have hker := card_ker_mul_eq_of_surj lam hsurj
  rw [card_f2] at hker
  let oddF := (relSet E).filter (fun U => (∑ s ∈ U, h s) = 1)
  let evenF := (relSet E).filter (fun U => (∑ s ∈ U, h s) = 0)
  have hpart : oddF.card + evenF.card = (relSet E).card := by
    have hdisj : Disjoint oddF evenF := by
      rw [Finset.disjoint_left]
      intro U h1 h2
      simp only [oddF, evenF, Finset.mem_filter] at h1 h2
      rw [h2.2] at h1
      exact zero_ne_one h1.2
    have hunion : oddF ∪ evenF = relSet E := by
      ext U
      simp only [oddF, evenF, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hU, _⟩ | ⟨hU, _⟩) <;> exact hU
      · intro hU
        rcases zmod2_eq_zero_or_one (∑ s ∈ U, h s) with h0 | h1
        · exact Or.inr ⟨hU, h0⟩
        · exact Or.inl ⟨hU, h1⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have heven_eq : evenF.card = Fintype.card (LinearMap.ker lam) := by
    rw [← Fintype.card_coe]
    let eqv : evenF ≃ LinearMap.ker lam :=
      { toFun := fun U =>
          ⟨relEquiv E ⟨U.1, (Finset.mem_filter.mp U.2).1⟩, by
            rw [LinearMap.mem_ker]
            change dotProduct (indE E U.1) (fun x : E => h x.1) = 0
            rw [dot_eq_sum_suppE, suppE_indE E ((mem_relSet_iff E U.1).mp (Finset.mem_filter.mp U.2).1).1]
            exact (Finset.mem_filter.mp U.2).2⟩
        invFun := fun u =>
          ⟨suppE E u.1.1, by
            rw [Finset.mem_filter]
            refine ⟨(suppE_mem_relSet_iff E u.1.1).mpr u.1.2, ?_⟩
            rw [← dot_eq_sum_suppE E u.1.1 h]
            exact u.2⟩
        left_inv := fun U =>
          Subtype.ext (suppE_indE E ((mem_relSet_iff E U.1).mp (Finset.mem_filter.mp U.2).1).1)
        right_inv := fun u => Subtype.ext (Subtype.ext (indE_suppE E u.1.1)) }
    exact Fintype.card_congr eqv
  have hrel_eq : (relSet E).card = Fintype.card R := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (relEquiv E)
  change 2 * oddF.card = (relSet E).card
  omega

private lemma zero_sig_gives_many_rels {k : ℕ} {E U : Finset (Fin k → F2)}
    (hU : U ∈ relSet E) (hne : U.Nonempty)
    (hzero : ∀ a b c : Fin k → F2, sigF U a b c = 0) :
    16 ≤ (relSet E).card := by
  have hsubE : U ⊆ E := ((mem_relSet_iff E U).mp hU).1
  have hquadU : ∀ f : (Fin k → F2) → F2, Quad f → ∑ s ∈ U, f s = 0 :=
    ((mem_relSet_iff E U).mp hU).2
  have hcut : ∀ (α : F2) (a : Fin k → F2),
      U.filter (fun s => α + dotProduct a s = 1) ∈ relSet E := by
    intro α a
    rw [mem_relSet_iff]
    refine ⟨Finset.Subset.trans (Finset.filter_subset _ _) hsubE, fun f hf => ?_⟩
    have hfilt : ∑ s ∈ U.filter (fun s => α + dotProduct a s = 1), f s =
        ∑ s ∈ U, (α + dotProduct a s) * f s := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      rcases zmod2_eq_zero_or_one (α + dotProduct a s) with h0 | h1
      · simp [h0]
      · simp [h1]
    rw [hfilt]
    rcases hf with ⟨b, l, M, hfEq⟩
    have hexp : ∀ s, (α + dotProduct a s) * f s =
        α * f s + (b * dotProduct a s + dotProduct a s * dotProduct l s) +
        ∑ i, ∑ j, M i j * tripleF a (Pi.single i 1) (Pi.single j 1) s := by
      intro s
      have hM : dotProduct a s * ∑ i, ∑ j, M i j * s i * s j =
          ∑ i, ∑ j, M i j * tripleF a (Pi.single i 1) (Pi.single j 1) s := by
        simp only [Finset.mul_sum, tripleF, single_dotProduct, one_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      calc (α + dotProduct a s) * f s
          = α * f s + dotProduct a s * (b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j) := by
              rw [hfEq s]; ring
        _ = α * f s + (b * dotProduct a s + dotProduct a s * dotProduct l s) +
            dotProduct a s * ∑ i, ∑ j, M i j * s i * s j := by ring
        _ = α * f s + (b * dotProduct a s + dotProduct a s * dotProduct l s) +
            ∑ i, ∑ j, M i j * tripleF a (Pi.single i 1) (Pi.single j 1) s := by rw [hM]
    have h1 : ∑ s ∈ U, α * f s = 0 := hquadU _ (quad_smul α ⟨b, l, M, hfEq⟩)
    have h2 : ∑ s ∈ U, (b * dotProduct a s + dotProduct a s * dotProduct l s) = 0 :=
      hquadU _ (quad_add (quad_smul b (quad_linear a)) (quad_mul_linear a l))
    have h3 : ∑ s ∈ U, ∑ i, ∑ j, M i j * tripleF a (Pi.single i 1) (Pi.single j 1) s = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum]
      change M i j * sigF U a (Pi.single i 1) (Pi.single j 1) = 0
      rw [hzero, mul_zero]
    rw [Finset.sum_congr rfl (fun s _ => hexp s), Finset.sum_add_distrib, Finset.sum_add_distrib,
      h1, h2, h3, add_zero, add_zero]
  obtain ⟨u0, hu0⟩ := hne
  let V : Submodule F2 (Fin k → F2) :=
    Submodule.span F2 { v : Fin k → F2 | ∃ s ∈ U, v = s + u0 }
  have hdim : 4 ≤ Module.finrank F2 V := by
    by_contra hlt
    have hlt' : Module.finrank F2 V < 4 := Nat.lt_of_not_le hlt
    let d := Module.finrank F2 V
    let b := Module.finBasis F2 V
    have hex_dual : ∀ r : Fin d, ∃ a : Fin k → F2,
        ∀ t : Fin d, dotProduct a (b t).1 = if t = r then 1 else 0 := by
      intro r
      let φ : V →ₗ[F2] F2 :=
        { toFun := fun v => b.repr v r
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }
      obtain ⟨a, ha⟩ := exists_extend_dot V φ
      refine ⟨a, fun t => ?_⟩
      rw [ha (b t)]
      simp [φ, Finsupp.single_apply, eq_comm]
    choose a ha using hex_dual
    let P : (Fin k → F2) → F2 := fun s => ∏ r : Fin d, (1 + dotProduct (a r) (s + u0))
    have hPu0 : P u0 = 1 := by
      simp only [P]
      refine Finset.prod_eq_one fun r _ => ?_
      have hu00 : u0 + u0 = 0 := by ext i; exact zmod2_add_self _
      rw [hu00, dotProduct_zero, add_zero]
    have hPne : ∀ s ∈ U, s ≠ u0 → P s = 0 := by
      intro s hs hne'
      have hmem : s + u0 ∈ V := Submodule.subset_span ⟨s, hs, rfl⟩
      have hnz : (⟨s + u0, hmem⟩ : V) ≠ 0 := by
        intro h0
        apply hne'
        ext i
        have hi := congrFun (congrArg Subtype.val h0) i
        exact (zmod2_eq_iff_add_eq_zero (s i) (u0 i)).mpr hi
      have hexr : ∃ r : Fin d, b.repr ⟨s + u0, hmem⟩ r ≠ 0 := by
        by_contra hall
        apply hnz
        have hrep : b.repr ⟨s + u0, hmem⟩ = 0 := by
          ext r
          by_contra hr
          exact hall ⟨r, hr⟩
        exact b.repr.injective (by simp [hrep])
      obtain ⟨r, hr⟩ := hexr
      have hdot1 : dotProduct (a r) (s + u0) = 1 := by
        have hv : (⟨s + u0, hmem⟩ : V) = ∑ t : Fin d, b.repr ⟨s + u0, hmem⟩ t • b t :=
          (b.sum_repr _).symm
        have hv1 : s + u0 = ∑ t : Fin d, b.repr ⟨s + u0, hmem⟩ t • (b t).1 := by
          calc s + u0 = V.subtype ⟨s + u0, hmem⟩ := rfl
            _ = V.subtype (∑ t : Fin d, b.repr ⟨s + u0, hmem⟩ t • b t) := congrArg V.subtype hv
            _ = ∑ t : Fin d, b.repr ⟨s + u0, hmem⟩ t • (b t).1 := by
              simp only [map_sum, map_smul]; rfl
        rw [hv1, dotProduct_sum]
        simp only [dotProduct_smul, smul_eq_mul, ha r]
        rw [Finset.sum_eq_single r]
        · simp [(zmod2_ne_zero_iff _).mp hr]
        · intro t _ htr; simp [htr]
        · intro h; exact (h (Finset.mem_univ _)).elim
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by rw [hdot1]; exact zmod2_add_self 1)
    have hsum1 : ∑ s ∈ U, P s = 1 := by
      rw [Finset.sum_eq_single u0]
      · exact hPu0
      · intro s hs hne'; exact hPne s hs hne'
      · intro h; exact (h hu0).elim
    have hsum0 : ∑ s ∈ U, P s = 0 := by
      have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      rcases hd_cases with hd | hd | hd | hd
      · have hP1 : ∀ s, P s = 1 := fun s => by
          simp only [P]
          exact Finset.prod_eq_one fun r _ => (Fin.elim0 (hd ▸ r))
        simp only [hP1]
        exact hquadU _ (quad_const 1)
      · let r0 : Fin d := ⟨0, by omega⟩
        have hP1 : ∀ s, P s = (1 + dotProduct (a r0) u0) + dotProduct (a r0) s := by
          intro s
          simp only [P]
          rw [Finset.prod_eq_single r0]
          · rw [dotProduct_add]; ring
          · intro r _ hr; exfalso; exact hr (Fin.ext (by omega))
          · intro h; exact (h (Finset.mem_univ _)).elim
        simp only [hP1]
        exact hquadU _ (quad_add (quad_const _) (quad_linear _))
      · let r0 : Fin d := ⟨0, by omega⟩
        let r1 : Fin d := ⟨1, by omega⟩
        have hP2 : ∀ s, P s =
            ((1 + dotProduct (a r0) u0) + dotProduct (a r0) s) *
            ((1 + dotProduct (a r1) u0) + dotProduct (a r1) s) := by
          intro s
          simp only [P]
          have huniv : (Finset.univ : Finset (Fin d)) = {r0, r1} := by
            ext r; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
            have : r.val = 0 ∨ r.val = 1 := by omega
            rcases this with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Fin.ext h)
          rw [huniv, Finset.prod_pair (by intro h; have := congrArg Fin.val h; simp [r0, r1] at this)]
          rw [dotProduct_add, dotProduct_add]; ring
        have hqP2 : Quad P := by
          have hex : ∀ s, P s =
              (1 + dotProduct (a r0) u0) * (1 + dotProduct (a r1) u0) +
              ((1 + dotProduct (a r1) u0) * dotProduct (a r0) s +
               (1 + dotProduct (a r0) u0) * dotProduct (a r1) s) +
              dotProduct (a r0) s * dotProduct (a r1) s := fun s => by rw [hP2 s]; ring
          have hfun : P = fun s =>
              (1 + dotProduct (a r0) u0) * (1 + dotProduct (a r1) u0) +
              ((1 + dotProduct (a r1) u0) * dotProduct (a r0) s +
               (1 + dotProduct (a r0) u0) * dotProduct (a r1) s) +
              dotProduct (a r0) s * dotProduct (a r1) s := funext hex
          rw [hfun]
          exact quad_add (quad_add (quad_const _)
            (quad_add (quad_smul _ (quad_linear _)) (quad_smul _ (quad_linear _))))
            (quad_mul_linear _ _)
        exact hquadU P hqP2
      · let r0 : Fin d := ⟨0, by omega⟩
        let r1 : Fin d := ⟨1, by omega⟩
        let r2 : Fin d := ⟨2, by omega⟩
        let c0 := 1 + dotProduct (a r0) u0
        let c1 := 1 + dotProduct (a r1) u0
        let c2 := 1 + dotProduct (a r2) u0
        have hP3 : ∀ s, P s =
            (c0 + dotProduct (a r0) s) * (c1 + dotProduct (a r1) s) * (c2 + dotProduct (a r2) s) := by
          intro s
          simp only [P]
          have huniv : (Finset.univ : Finset (Fin d)) = {r0, r1, r2} := by
            ext r; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
            have : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
            rcases this with h | h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Or.inl (Fin.ext h))
            · exact Or.inr (Or.inr (Fin.ext h))
          rw [huniv]
          have h01 : r0 ≠ r1 := fun h => by have := congrArg Fin.val h; simp [r0, r1] at this
          have h02 : r0 ≠ r2 := fun h => by have := congrArg Fin.val h; simp [r0, r2] at this
          have h12 : r1 ≠ r2 := fun h => by have := congrArg Fin.val h; simp [r1, r2] at this
          rw [Finset.prod_insert (by simp [h01, h02]), Finset.prod_pair h12]
          simp only [c0, c1, c2, dotProduct_add]
          ring
        let Qpart : (Fin k → F2) → F2 := fun s =>
          c0 * c1 * c2 +
          (c1 * c2 * dotProduct (a r0) s + c0 * c2 * dotProduct (a r1) s + c0 * c1 * dotProduct (a r2) s) +
          (c2 * (dotProduct (a r0) s * dotProduct (a r1) s) +
           c1 * (dotProduct (a r0) s * dotProduct (a r2) s) +
           c0 * (dotProduct (a r1) s * dotProduct (a r2) s))
        have hqQ : Quad Qpart :=
          quad_add (quad_add (quad_const _)
            (quad_add (quad_add (quad_smul _ (quad_linear _)) (quad_smul _ (quad_linear _)))
              (quad_smul _ (quad_linear _))))
            (quad_add (quad_add (quad_smul _ (quad_mul_linear _ _))
              (quad_smul _ (quad_mul_linear _ _))) (quad_smul _ (quad_mul_linear _ _)))
        have hsplit : ∀ s, P s = Qpart s + tripleF (a r0) (a r1) (a r2) s := by
          intro s
          rw [hP3 s]
          simp only [Qpart, tripleF]
          ring
        simp only [hsplit, Finset.sum_add_distrib]
        rw [hquadU Qpart hqQ, zero_add]
        exact hzero (a r0) (a r1) (a r2)
    rw [hsum0] at hsum1
    exact zero_ne_one hsum1
  have hex4 : ∃ (pts : Fin 4 → Fin k → F2),
      (∀ t, pts t ∈ U) ∧ LinearIndependent F2 (fun t : Fin 4 => pts t + u0) := by
    let genSet : Set (Fin k → F2) := { v | ∃ s ∈ U, v = s + u0 }
    obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent F2 genSet
    have hcard : 4 ≤ Module.finrank F2 (Submodule.span F2 B) := by
      rw [hBspan]; exact hdim
    have hfinB : Set.Finite B := Set.Finite.subset (Set.toFinite genSet) hBsub
    let _ : Fintype B := hfinB.fintype
    have hBcard : 4 ≤ Fintype.card B := by
      have hfr := finrank_span_eq_card (R := F2) hBli
      rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq] at hfr
      calc 4 ≤ Module.finrank F2 (Submodule.span F2 B) := hcard
        _ = Fintype.card B := by rw [hfr]
    let fB : Fin 4 → B := fun t => (Fintype.equivFin B).symm ⟨t.val, by omega⟩
    have hfBinj : Function.Injective fB := fun t1 t2 h => by
      have h1 := (Fintype.equivFin B).symm.injective h
      exact Fin.ext (by simpa using congrArg Fin.val h1)
    have hli4 : LinearIndependent F2 (fun t : Fin 4 => (fB t).1) :=
      hBli.comp fB hfBinj
    have hmemU : ∀ t : Fin 4, ∃ s ∈ U, (fB t).1 = s + u0 := fun t => hBsub (fB t).2
    choose pts hptsU hptseq using hmemU
    refine ⟨pts, hptsU, ?_⟩
    have hfun : (fun t : Fin 4 => pts t + u0) = (fun t : Fin 4 => (fB t).1) :=
      funext fun t => (hptseq t).symm
    rw [hfun]
    exact hli4
  obtain ⟨pts, hptsU, hli4⟩ := hex4
  let V4 := Submodule.span F2 (Set.range (fun t : Fin 4 => pts t + u0))
  let b4 : Module.Basis (Fin 4) F2 V4 := Module.Basis.span hli4
  have hex_dual4 : ∀ r : Fin 4, ∃ a : Fin k → F2,
      ∀ t : Fin 4, dotProduct a (pts t + u0) = if t = r then 1 else 0 := by
    intro r
    let φ : V4 →ₗ[F2] F2 :=
      { toFun := fun v => b4.repr v r
        map_add' := fun x y => by simp
        map_smul' := fun c x => by simp }
    obtain ⟨a, ha⟩ := exists_extend_dot V4 φ
    refine ⟨a, fun t => ?_⟩
    have hbt : (b4 t).1 = pts t + u0 := congrArg Subtype.val (Module.Basis.span_apply hli4 t)
    rw [← hbt, ha (b4 t)]
    simp [φ, Finsupp.single_apply, eq_comm]
  choose a ha using hex_dual4
  let mapW : (Fin 4 → F2) → Finset (Fin k → F2) := fun c =>
    U.filter (fun s => (∑ r : Fin 4, c r * dotProduct (a r) u0) +
      dotProduct (∑ r : Fin 4, c r • a r) s = 1)
  have hmap_mem : ∀ c : Fin 4 → F2, mapW c ∈ relSet E := fun c =>
    hcut (∑ r : Fin 4, c r * dotProduct (a r) u0) (∑ r : Fin 4, c r • a r)
  have hmap_inj : Function.Injective mapW := by
    intro c1 c2 hEq
    ext t
    have heval : ∀ c : Fin 4 → F2,
        (∑ r : Fin 4, c r * dotProduct (a r) u0) +
          dotProduct (∑ r : Fin 4, c r • a r) (pts t) = c t := by
      intro c
      rw [sum_dotProduct]
      simp only [smul_dotProduct, smul_eq_mul, ← Finset.sum_add_distrib]
      have hterm : ∀ r : Fin 4,
          c r * dotProduct (a r) u0 + c r * dotProduct (a r) (pts t) =
            c r * dotProduct (a r) (pts t + u0) := by
        intro r; rw [dotProduct_add]; ring
      simp only [hterm, ha]
      rw [Finset.sum_eq_single t]
      · simp
      · intro r _ hrt; simp [Ne.symm hrt]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hmem_iff : ∀ c : Fin 4 → F2, pts t ∈ mapW c ↔ c t = 1 := by
      intro c
      simp only [mapW, Finset.mem_filter, hptsU t, true_and, heval c]
    have h12 : c1 t = 1 ↔ c2 t = 1 := by
      rw [← hmem_iff c1, ← hmem_iff c2, hEq]
    rcases zmod2_eq_zero_or_one (c1 t) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_one (c2 t) with h2 | h2
    · rw [h1, h2]
    · exfalso; have := h12.mpr h2; rw [h1] at this; exact zero_ne_one this
    · exfalso; have := h12.mp h1; rw [h2] at this; exact zero_ne_one this
    · rw [h1, h2]
  have hsub : (Finset.univ.image mapW) ⊆ relSet E := by
    intro W hW
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hW
    exact hmap_mem c
  calc 16 = Fintype.card (Fin 4 → F2) := by rw [card_fin_f2]; norm_num
    _ = (Finset.univ : Finset (Fin 4 → F2)).card := rfl
    _ = (Finset.univ.image mapW).card := (Finset.card_image_of_injective _ hmap_inj).symm
    _ ≤ (relSet E).card := Finset.card_le_card hsub

private lemma bound_from_four_forms {k : ℕ} (E : Finset (Fin k → F2)) (h : (Fin k → F2) → F2)
    (hforms : (((relSet E).filter (fun U => (∑ s ∈ U, h s) = 1)).image sigF).card ≤ 4)
    (hnonz : ∀ U ∈ (relSet E).filter (fun U => (∑ s ∈ U, h s) = 1),
      ∃ a b c : Fin k → F2, sigF U a b c = 1) :
    3 * 2 ^ (2 * k) ≤
      32 * ((Finset.univ : Finset ((Fin k → F2) × (Fin k → F2))).filter
        (fun v => @decide (fitF E h v.1 v.2) (Classical.propDecidable _))).card := by
  classical
  let S := Fin k → F2
  let odd := (relSet E).filter (fun U => (∑ s ∈ U, h s) = 1)
  let forms := odd.image sigF
  let pairs := (Finset.univ : Finset (S × S)).filter
    (fun v => @decide (fitF E h v.1 v.2) (Classical.propDecidable _))
  by_cases hodd_empty : odd = ∅
  · have hpairs : pairs = Finset.univ := by
      ext v
      simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff, iff_true]
      rw [fitF_iff]
      intro U hU
      simp [odd, hodd_empty] at hU
    change 3 * 2 ^ (2 * k) ≤ 32 * pairs.card
    rw [hpairs, Finset.card_univ, Fintype.card_prod, card_fin_f2, ← pow_add, ← two_mul]
    omega
  have hforms_ne : forms.Nonempty := by
    obtain ⟨U, hU⟩ := Finset.nonempty_iff_ne_empty.mpr hodd_empty
    exact ⟨sigF U, Finset.mem_image.mpr ⟨U, hU, rfl⟩⟩

  have hT_props : ∀ T ∈ forms,
      (∃ U ∈ odd, sigF U = T) ∧
      (∀ a1 a2 b c, T (a1 + a2) b c = T a1 b c + T a2 b c) ∧
      (∀ a b1 b2 c, T a (b1 + b2) c = T a b1 c + T a b2 c) ∧
      (∀ a b c1 c2, T a b (c1 + c2) = T a b c1 + T a b c2) ∧
      (∀ r a b c, T (r • a) b c = r * T a b c) ∧
      (∀ r a b c, T a (r • b) c = r * T a b c) ∧
      (∀ r a b c, T a b (r • c) = r * T a b c) ∧
      (∀ a c, T a a c = 0) ∧
      (∀ a b, T a b b = 0) ∧
      (∀ a b, T a b a = 0) ∧
      (∃ a b c, T a b c = 1) := by
    intro T hT
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
    have hUrel : U ∈ relSet E := (Finset.mem_filter.mp hU).1
    exact ⟨⟨U, hU, rfl⟩, sigF_add_left U, sigF_add_mid U, sigF_add_right U,
      sigF_smul_left U, sigF_smul_mid U, sigF_smul_right U,
      sigF_diag12 hUrel, sigF_diag23 hUrel, sigF_diag13 hUrel, hnonz U hU⟩

  let rad (T : S → S → S → F2) : Finset S :=
    Finset.univ.filter (fun a => ∀ b c : S, T a b c = 0)
  have hrad_card : ∀ T ∈ forms, 8 * (rad T).card ≤ 2 ^ k := by
    intro T hT
    obtain ⟨_, haddL, _, _, hsmulL, _, _, hd12, hd23, hd13, ⟨a0, b0, c0, h1⟩⟩ := hT_props T hT

    obtain ⟨⟨U, hU, rfl⟩, _, _, _, _, _, _, _, _, _, _⟩ := hT_props T hT
    let Φ : S →ₗ[F2] (Fin 3 → F2) :=
      { toFun := fun x i =>
          if i.val = 0 then sigF U x b0 c0
          else if i.val = 1 then sigF U a0 x c0
          else sigF U a0 b0 x
        map_add' := fun x y => by
          ext i
          simp only [Pi.add_apply]
          by_cases h0 : i.val = 0
          · simp only [if_pos h0]; exact sigF_add_left U x y b0 c0
          · by_cases h1' : i.val = 1
            · simp only [if_neg h0, if_pos h1']; exact sigF_add_mid U a0 x y c0
            · simp only [if_neg h0, if_neg h1']; exact sigF_add_right U a0 b0 x y
        map_smul' := fun r x => by
          ext i
          simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
          by_cases h0 : i.val = 0
          · simp only [if_pos h0]; exact sigF_smul_left U r x b0 c0
          · by_cases h1' : i.val = 1
            · simp only [if_neg h0, if_pos h1']; exact sigF_smul_mid U r a0 x c0
            · simp only [if_neg h0, if_neg h1']; exact sigF_smul_right U r a0 b0 x }
    have hsurj : Function.Surjective Φ := by
      intro y
      refine ⟨y 0 • a0 + y 1 • b0 + y 2 • c0, ?_⟩
      ext i
      have hUrel : U ∈ relSet E := (Finset.mem_filter.mp hU).1
      fin_cases i
      · change sigF U (y 0 • a0 + y 1 • b0 + y 2 • c0) b0 c0 = y 0
        simp [sigF_add_left U, sigF_smul_left U, h1, sigF_diag12 hUrel, sigF_diag13 hUrel]
      · change sigF U a0 (y 0 • a0 + y 1 • b0 + y 2 • c0) c0 = y 1
        simp [sigF_add_mid U, sigF_smul_mid U, h1, sigF_diag12 hUrel, sigF_diag23 hUrel]
      · change sigF U a0 b0 (y 0 • a0 + y 1 • b0 + y 2 • c0) = y 2
        simp [sigF_add_right U, sigF_smul_right U, h1, sigF_diag13 hUrel, sigF_diag23 hUrel]
    have hker := card_ker_mul_eq_of_surj Φ hsurj
    rw [card_fin_f2, card_fin_f2, show (2 ^ 3 : ℕ) = 8 from rfl] at hker
    have hsub : rad (sigF U) ⊆ Finset.univ.filter (fun x => x ∈ LinearMap.ker Φ) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [LinearMap.mem_ker]
      ext i
      change (if i.val = 0 then sigF U x b0 c0
        else if i.val = 1 then sigF U a0 x c0
        else sigF U a0 b0 x) = 0
      by_cases h0 : i.val = 0
      · simp only [if_pos h0, hx.2 b0 c0]
      · by_cases h1' : i.val = 1
        · simp only [if_neg h0, if_pos h1']
          rw [sigF_symm12]; exact hx.2 a0 c0
        · simp only [if_neg h0, if_neg h1']
          rw [sigF_symm23, sigF_symm12]; exact hx.2 a0 b0
    have hker_card : (Finset.univ.filter (fun x => x ∈ LinearMap.ker Φ)).card =
        Fintype.card (LinearMap.ker Φ) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        { toFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
          invFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hle := Finset.card_le_card hsub
    rw [hker_card] at hle
    omega
  let badA : Finset S := forms.biUnion rad
  let goodA : Finset S := Finset.univ \ badA
  have hbadA_le : 8 * badA.card ≤ 4 * 2 ^ k := by
    calc 8 * badA.card ≤ 8 * ∑ T ∈ forms, (rad T).card :=
          Nat.mul_le_mul_left 8 Finset.card_biUnion_le
      _ = ∑ T ∈ forms, 8 * (rad T).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _T ∈ forms, 2 ^ k := Finset.sum_le_sum hrad_card
      _ = forms.card * 2 ^ k := by simp
      _ ≤ 4 * 2 ^ k := Nat.mul_le_mul_right _ hforms
  have hgoodA_ge : 2 ^ k ≤ 2 * goodA.card := by
    have hcard : goodA.card + badA.card = 2 ^ k := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ badA)
      simpa [goodA, S, card_fin_f2] using h1
    omega

  have hslice : ∀ a ∈ goodA,
      3 * 2 ^ k ≤ 16 * (Finset.univ.filter (fun b : S => fitF E h a b)).card := by
    intro a ha
    have ha_not_rad : ∀ T ∈ forms, ∃ b0 c0 : S, T a b0 c0 = 1 := by
      intro T hT
      have hna : a ∉ rad T := by
        intro hmem
        have hba : a ∈ badA := Finset.mem_biUnion.mpr ⟨T, hT, hmem⟩
        exact (Finset.mem_sdiff.mp ha).2 hba
      simp only [rad, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hna
      obtain ⟨b0, c0, hne⟩ := hna
      exact ⟨b0, c0, (zmod2_ne_zero_iff _).mp hne⟩

    have hexΨ : ∀ T ∈ forms, ∃ Ψ : S →ₗ[F2] (Fin 2 → F2),
        Function.Surjective Ψ ∧ ∀ b : S, (∀ c : S, T a b c = 0) → Ψ b = 0 := by
      intro T hT
      obtain ⟨⟨U, hU, rfl⟩, _, _, _, _, _, _, _, _, _, _⟩ := hT_props T hT
      obtain ⟨b0, c0, h1⟩ := ha_not_rad (sigF U) hT
      have hUrel : U ∈ relSet E := (Finset.mem_filter.mp hU).1
      let Ψ : S →ₗ[F2] (Fin 2 → F2) :=
        { toFun := fun y i => if i.val = 0 then sigF U a y c0 else sigF U a b0 y
          map_add' := fun x y => by
            ext i; simp only [Pi.add_apply]
            by_cases h0 : i.val = 0
            · simp only [if_pos h0]; exact sigF_add_mid U a x y c0
            · simp only [if_neg h0]; exact sigF_add_right U a b0 x y
          map_smul' := fun r x => by
            ext i; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
            by_cases h0 : i.val = 0
            · simp only [if_pos h0]; exact sigF_smul_mid U r a x c0
            · simp only [if_neg h0]; exact sigF_smul_right U r a b0 x }
      refine ⟨Ψ, ?_, ?_⟩
      · intro y
        refine ⟨y 0 • b0 + y 1 • c0, ?_⟩
        ext i
        fin_cases i
        · change sigF U a (y 0 • b0 + y 1 • c0) c0 = y 0
          simp [sigF_add_mid U, sigF_smul_mid U, h1, sigF_diag23 hUrel]
        · change sigF U a b0 (y 0 • b0 + y 1 • c0) = y 1
          simp [sigF_add_right U, sigF_smul_right U, h1, sigF_diag23 hUrel]
      · intro b hb
        ext i
        change (if i.val = 0 then sigF U a b c0 else sigF U a b0 b) = 0
        by_cases h0 : i.val = 0
        · simp only [if_pos h0, hb c0]
        · simp only [if_neg h0]
          rw [sigF_symm23]; exact hb b0
    choose Ψ hΨ using fun T : forms => hexΨ T.1 T.2
    let H (T : forms) : Finset S := Finset.univ.filter (fun b => Ψ T b = 0)
    have hH_card : ∀ T : forms, 4 * (H T).card = 2 ^ k := by
      intro T
      have hker := card_ker_mul_eq_of_surj (Ψ T) (hΨ T).1
      rw [card_fin_f2, card_fin_f2, show (2 ^ 2 : ℕ) = 4 from rfl] at hker
      have hEq : (H T).card = Fintype.card (LinearMap.ker (Ψ T)) := by
        rw [← Fintype.card_coe]
        exact Fintype.card_congr
          { toFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
            invFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hEq]
      omega
    have hH_inter : ∀ T1 T2 : forms, 2 ^ k ≤ 16 * (H T1 ∩ H T2).card := by
      intro T1 T2
      let P := (Ψ T1).prod (Ψ T2)
      have hle := card_ker_mul_le P
      rw [card_fin_f2, Fintype.card_prod, card_fin_f2, show 2 ^ 2 * 2 ^ 2 = 16 from rfl] at hle
      have hEq : (H T1 ∩ H T2).card = Fintype.card (LinearMap.ker P) := by
        rw [← Fintype.card_coe]
        exact Fintype.card_congr
          { toFun := fun x =>
              ⟨x.1, by
                have hx := Finset.mem_inter.mp x.2
                rw [LinearMap.mem_ker]
                exact Prod.ext (Finset.mem_filter.mp hx.1).2 (Finset.mem_filter.mp hx.2).2⟩
            invFun := fun x =>
              ⟨x.1, Finset.mem_inter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst x.2⟩,
                 Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.snd x.2⟩⟩⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hEq]
      omega
    obtain ⟨T0val, hT0mem⟩ := hforms_ne
    let T0 : forms := ⟨T0val, hT0mem⟩
    let unionH : Finset S := (Finset.univ : Finset forms).biUnion H
    have hunion_le : unionH.card ≤ (H T0).card +
        ∑ T ∈ (Finset.univ : Finset forms).erase T0, (H T \ H T0).card := by
      have hsub : unionH ⊆ H T0 ∪ ((Finset.univ : Finset forms).erase T0).biUnion (fun T => H T \ H T0) := by
        intro b hb
        obtain ⟨T, _, hbT⟩ := Finset.mem_biUnion.mp hb
        by_cases h0 : b ∈ H T0
        · exact Finset.mem_union_left _ h0
        · have hne : T ≠ T0 := fun hEq => h0 (hEq ▸ hbT)
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨T, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩,
              Finset.mem_sdiff.mpr ⟨hbT, h0⟩⟩)
      calc unionH.card
          ≤ (H T0 ∪ ((Finset.univ : Finset forms).erase T0).biUnion (fun T => H T \ H T0)).card :=
            Finset.card_le_card hsub
        _ ≤ (H T0).card + (((Finset.univ : Finset forms).erase T0).biUnion (fun T => H T \ H T0)).card :=
            Finset.card_union_le _ _
        _ ≤ (H T0).card + ∑ T ∈ (Finset.univ : Finset forms).erase T0, (H T \ H T0).card :=
            Nat.add_le_add_left Finset.card_biUnion_le _
    have hsdiff_le : ∀ T : forms, 16 * (H T \ H T0).card ≤ 3 * 2 ^ k := by
      intro T
      have h1 := Finset.card_sdiff_add_card_inter (H T) (H T0)
      have h2 := hH_card T
      have h3 := hH_inter T T0
      omega
    have herase_card : ((Finset.univ : Finset forms).erase T0).card ≤ 3 := by
      have hforms' : forms.card ≤ 4 := hforms
      rw [Finset.card_erase_of_mem (Finset.mem_univ T0), Finset.card_univ, Fintype.card_coe]
      omega
    have hunion16 : 16 * unionH.card ≤ 13 * 2 ^ k := by
      have hstep : 16 * ∑ T ∈ (Finset.univ : Finset forms).erase T0, (H T \ H T0).card ≤
          9 * 2 ^ k := by
        calc 16 * ∑ T ∈ (Finset.univ : Finset forms).erase T0, (H T \ H T0).card
            = ∑ T ∈ (Finset.univ : Finset forms).erase T0, 16 * (H T \ H T0).card := by
                rw [Finset.mul_sum]
          _ ≤ ∑ _T ∈ (Finset.univ : Finset forms).erase T0, 3 * 2 ^ k :=
                Finset.sum_le_sum fun T _ => hsdiff_le T
          _ = ((Finset.univ : Finset forms).erase T0).card * (3 * 2 ^ k) := by simp
          _ ≤ 3 * (3 * 2 ^ k) := Nat.mul_le_mul_right _ herase_card
          _ = 9 * 2 ^ k := by ring
      have hT0_4 := hH_card T0
      omega
    have hgoodB_sub : Finset.univ \ unionH ⊆ Finset.univ.filter (fun b : S => fitF E h a b) := by
      intro b hb
      rw [Finset.mem_sdiff] at hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [fitF_iff]
      intro U hU
      have hTmem : sigF U ∈ forms := Finset.mem_image.mpr ⟨U, hU, rfl⟩
      let T : forms := ⟨sigF U, hTmem⟩
      have hbnotH : b ∉ H T := fun hmem =>
        hb.2 (Finset.mem_biUnion.mpr ⟨T, Finset.mem_univ _, hmem⟩)
      have hΨne : Ψ T b ≠ 0 := by
        simpa [H] using hbnotH
      have hnotall : ¬(∀ c : S, sigF U a b c = 0) := fun hall => hΨne ((hΨ T).2 b hall)
      obtain ⟨c, hc⟩ := Classical.not_forall.mp hnotall
      exact ⟨c, (zmod2_ne_zero_iff _).mp hc⟩
    have hcomp : (Finset.univ \ unionH).card + unionH.card = 2 ^ k := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ unionH)
      simpa [S, card_fin_f2] using h1
    have hle := Finset.card_le_card hgoodB_sub
    omega

  have hpairs_ge : (∑ a ∈ goodA, (Finset.univ.filter (fun b : S => fitF E h a b)).card) ≤
      pairs.card := by
    let fiber (a : S) : Finset (S × S) :=
      (Finset.univ.filter (fun b : S => fitF E h a b)).image (fun b => (a, b))
    have hdisj : (goodA : Set S).PairwiseDisjoint fiber := by
      intro a1 _ a2 _ hne
      change Disjoint (fiber a1) (fiber a2)
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      obtain ⟨b1, _, rfl⟩ := Finset.mem_image.mp hv1
      obtain ⟨b2, _, hEq⟩ := Finset.mem_image.mp hv2
      exact hne (congrArg Prod.fst hEq).symm
    have hsub : goodA.biUnion fiber ⊆ pairs := by
      intro v hv
      obtain ⟨a, _, hvF⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hvF
      simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff]
      exact (Finset.mem_filter.mp hb).2
    have hcard_fiber : ∀ a, (fiber a).card =
        (Finset.univ.filter (fun b : S => fitF E h a b)).card := fun a =>
      Finset.card_image_of_injective _ (fun _ _ hEq => congrArg Prod.snd hEq)
    calc ∑ a ∈ goodA, (Finset.univ.filter (fun b : S => fitF E h a b)).card
        = ∑ a ∈ goodA, (fiber a).card := Finset.sum_congr rfl fun a _ => (hcard_fiber a).symm
      _ = (goodA.biUnion fiber).card := (Finset.card_biUnion hdisj).symm
      _ ≤ pairs.card := Finset.card_le_card hsub
  have h16 : goodA.card * (3 * 2 ^ k) ≤ 16 * pairs.card := by
    calc goodA.card * (3 * 2 ^ k)
        = ∑ _a ∈ goodA, 3 * 2 ^ k := by simp
      _ ≤ ∑ a ∈ goodA, 16 * (Finset.univ.filter (fun b : S => fitF E h a b)).card :=
          Finset.sum_le_sum hslice
      _ = 16 * ∑ a ∈ goodA, (Finset.univ.filter (fun b : S => fitF E h a b)).card := by
          rw [← Finset.mul_sum]
      _ ≤ 16 * pairs.card := Nat.mul_le_mul_left 16 hpairs_ge
  calc 3 * 2 ^ (2 * k)
      = 2 ^ k * (3 * 2 ^ k) := by rw [two_mul, pow_add]; ring
    _ ≤ (2 * goodA.card) * (3 * 2 ^ k) := Nat.mul_le_mul_right _ hgoodA_ge
    _ = 2 * (goodA.card * (3 * 2 ^ k)) := by ring
    _ ≤ 2 * (16 * pairs.card) := Nat.mul_le_mul_left 2 h16
    _ = 32 * pairs.card := by ring

private def det3 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : F2) : F2 :=
  a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b2 * c0 + a2 * b0 * c1 + a2 * b1 * c0

private def sdet3 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : F2) : F2 :=
  a0 * b1 * c2 - a0 * b2 * c1 - a1 * b0 * c2 + a1 * b2 * c0 + a2 * b0 * c1 - a2 * b1 * c0

private lemma zmod2_neg_eq (x : F2) : -x = x := by
  fin_cases x <;> rfl

private lemma det3_eq_sdet3 (a0 b0 c0 a1 b1 c1 a2 b2 c2 : F2) :
    det3 a0 b0 c0 a1 b1 c1 a2 b2 c2 = sdet3 a0 b0 c0 a1 b1 c1 a2 b2 c2 := by
  simp only [det3, sdet3, sub_eq_add_neg, zmod2_neg_eq]

private lemma plucker_det3 (a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3 a4 b4 c4 : F2) :
    det3 a2 b2 c2 a3 b3 c3 a4 b4 c4 * det3 a0 b0 c0 a1 b1 c1 a4 b4 c4 =
    det3 a0 b0 c0 a2 b2 c2 a4 b4 c4 * det3 a1 b1 c1 a3 b3 c3 a4 b4 c4 +
    det3 a1 b1 c1 a2 b2 c2 a4 b4 c4 * det3 a0 b0 c0 a3 b3 c3 a4 b4 c4 := by
  simp only [det3_eq_sdet3]
  have hsub :
      sdet3 a2 b2 c2 a3 b3 c3 a4 b4 c4 * sdet3 a0 b0 c0 a1 b1 c1 a4 b4 c4 =
      sdet3 a0 b0 c0 a2 b2 c2 a4 b4 c4 * sdet3 a1 b1 c1 a3 b3 c3 a4 b4 c4 -
      sdet3 a1 b1 c1 a2 b2 c2 a4 b4 c4 * sdet3 a0 b0 c0 a3 b3 c3 a4 b4 c4 := by
    simp only [sdet3]
    ring
  rw [hsub, sub_eq_add_neg, zmod2_neg_eq]

private lemma sum_f2_eq (g : F2 → F2) : ∑ x : F2, g x = g 0 + g 1 := by
  have huniv : (Finset.univ : Finset F2) = {0, 1} := by
    ext x; rcases zmod2_eq_zero_or_one x with rfl | rfl <;> simp
  rw [huniv, Finset.sum_pair zero_ne_one]

private lemma sum_f2_const (c : F2) : ∑ _x : F2, c = 0 := by
  rw [sum_f2_eq, zmod2_add_self]

private lemma sum_cube3_quad_eval (c0 c1 c2 c3 c12 c13 c23 : F2) :
    ∑ t : F2 × F2 × F2,
      (c0 + c1 * t.1 + c2 * t.2.1 + c3 * t.2.2 +
       c12 * t.1 * t.2.1 + c13 * t.1 * t.2.2 + c23 * t.2.1 * t.2.2) = 0 := by
  simp only [Fintype.sum_prod_type, sum_f2_eq]
  have h1 : ∀ x y : F2, x + y = x - y := fun x y => by rw [sub_eq_add_neg, zmod2_neg_eq]
  have hcalc :
      (c0 + c1 * 0 + c2 * 0 + c3 * 0 + c12 * 0 * 0 + c13 * 0 * 0 + c23 * 0 * 0) -
      (c0 + c1 * 0 + c2 * 0 + c3 * 1 + c12 * 0 * 0 + c13 * 0 * 1 + c23 * 0 * 1) -
      ((c0 + c1 * 0 + c2 * 1 + c3 * 0 + c12 * 0 * 1 + c13 * 0 * 0 + c23 * 1 * 0) -
       (c0 + c1 * 0 + c2 * 1 + c3 * 1 + c12 * 0 * 1 + c13 * 0 * 1 + c23 * 1 * 1)) -
      ((c0 + c1 * 1 + c2 * 0 + c3 * 0 + c12 * 1 * 0 + c13 * 1 * 0 + c23 * 0 * 0) -
       (c0 + c1 * 1 + c2 * 0 + c3 * 1 + c12 * 1 * 0 + c13 * 1 * 1 + c23 * 0 * 1) -
       ((c0 + c1 * 1 + c2 * 1 + c3 * 0 + c12 * 1 * 1 + c13 * 1 * 0 + c23 * 1 * 0) -
        (c0 + c1 * 1 + c2 * 1 + c3 * 1 + c12 * 1 * 1 + c13 * 1 * 1 + c23 * 1 * 1))) = 0 := by
    ring
  simpa only [sub_eq_add_neg, zmod2_neg_eq] using hcalc

private lemma sum_cube3_triple_eval (x0 x1 x2 y0 y1 y2 z0 z1 z2 : F2) :
    ∑ t : F2 × F2 × F2,
      (x0 * t.1 + x1 * t.2.1 + x2 * t.2.2) *
      (y0 * t.1 + y1 * t.2.1 + y2 * t.2.2) *
      (z0 * t.1 + z1 * t.2.1 + z2 * t.2.2) =
    det3 x0 y0 z0 x1 y1 z1 x2 y2 z2 := by
  simp only [Fintype.sum_prod_type, sum_f2_eq]
  have hcalc :
      ((x0 * 0 + x1 * 0 + x2 * 0) * (y0 * 0 + y1 * 0 + y2 * 0) * (z0 * 0 + z1 * 0 + z2 * 0) -
       (x0 * 0 + x1 * 0 + x2 * 1) * (y0 * 0 + y1 * 0 + y2 * 1) * (z0 * 0 + z1 * 0 + z2 * 1) -
       ((x0 * 0 + x1 * 1 + x2 * 0) * (y0 * 0 + y1 * 1 + y2 * 0) * (z0 * 0 + z1 * 1 + z2 * 0) -
        (x0 * 0 + x1 * 1 + x2 * 1) * (y0 * 0 + y1 * 1 + y2 * 1) * (z0 * 0 + z1 * 1 + z2 * 1))) -
      ((x0 * 1 + x1 * 0 + x2 * 0) * (y0 * 1 + y1 * 0 + y2 * 0) * (z0 * 1 + z1 * 0 + z2 * 0) -
       (x0 * 1 + x1 * 0 + x2 * 1) * (y0 * 1 + y1 * 0 + y2 * 1) * (z0 * 1 + z1 * 0 + z2 * 1) -
       ((x0 * 1 + x1 * 1 + x2 * 0) * (y0 * 1 + y1 * 1 + y2 * 0) * (z0 * 1 + z1 * 1 + z2 * 0) -
        (x0 * 1 + x1 * 1 + x2 * 1) * (y0 * 1 + y1 * 1 + y2 * 1) * (z0 * 1 + z1 * 1 + z2 * 1))) =
      -det3 x0 y0 z0 x1 y1 z1 x2 y2 z2 := by
    simp only [det3]
    ring
  simpa only [sub_eq_add_neg, zmod2_neg_eq] using hcalc

private lemma paw_counterexample {k : ℕ} (hk : 5 ≤ k) :
    ∃ (E : Finset (Fin k → F2)) (h : (Fin k → F2) → F2),
      (relSet E).card = 16 ∧ ∀ a b : Fin k → F2, ¬ fitF E h a b := by
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  let i3 : Fin k := ⟨3, by omega⟩
  let i4 : Fin k := ⟨4, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have h02 : i0 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i0, i2] at this
  have h03 : i0 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i0, i3] at this
  have h04 : i0 ≠ i4 := by intro h; have := congrArg Fin.val h; simp [i0, i4] at this
  have h12 : i1 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i1, i2] at this
  have h13 : i1 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i1, i3] at this
  have h14 : i1 ≠ i4 := by intro h; have := congrArg Fin.val h; simp [i1, i4] at this
  have h23 : i2 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i2, i3] at this
  have h24 : i2 ≠ i4 := by intro h; have := congrArg Fin.val h; simp [i2, i4] at this
  have h34 : i3 ≠ i4 := by intro h; have := congrArg Fin.val h; simp [i3, i4] at this
  let emb (b0 b1 b2 b3 b4 : F2) : Fin k → F2 := fun j =>
    if j = i0 then b0 else if j = i1 then b1 else if j = i2 then b2
    else if j = i3 then b3 else if j = i4 then b4 else 0
  have hemb_i0 : ∀ b0 b1 b2 b3 b4, emb b0 b1 b2 b3 b4 i0 = b0 := fun _ _ _ _ _ => by simp [emb]
  have hemb_i1 : ∀ b0 b1 b2 b3 b4, emb b0 b1 b2 b3 b4 i1 = b1 := fun _ _ _ _ _ => by
    simp [emb, h01.symm]
  have hemb_i2 : ∀ b0 b1 b2 b3 b4, emb b0 b1 b2 b3 b4 i2 = b2 := fun _ _ _ _ _ => by
    simp [emb, h02.symm, h12.symm]
  have hemb_i3 : ∀ b0 b1 b2 b3 b4, emb b0 b1 b2 b3 b4 i3 = b3 := fun _ _ _ _ _ => by
    simp [emb, h03.symm, h13.symm, h23.symm]
  have hemb_i4 : ∀ b0 b1 b2 b3 b4, emb b0 b1 b2 b3 b4 i4 = b4 := fun _ _ _ _ _ => by
    simp [emb, h04.symm, h14.symm, h24.symm, h34.symm]
  have hemb_other : ∀ b0 b1 b2 b3 b4 (j : Fin k),
      j ≠ i0 → j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → emb b0 b1 b2 b3 b4 j = 0 := by
    intro b0 b1 b2 b3 b4 j hj0 hj1 hj2 hj3 hj4
    simp [emb, hj0, hj1, hj2, hj3, hj4]
  have hemb_inj : ∀ b0 b1 b2 b3 b4 c0 c1 c2 c3 c4,
      emb b0 b1 b2 b3 b4 = emb c0 c1 c2 c3 c4 →
      b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 ∧ b4 = c4 := by
    intro b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 hEq
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hemb_i0] using congrFun hEq i0
    · simpa [hemb_i1] using congrFun hEq i1
    · simpa [hemb_i2] using congrFun hEq i2
    · simpa [hemb_i3] using congrFun hEq i3
    · simpa [hemb_i4] using congrFun hEq i4
  have hdot_emb : ∀ (a : Fin k → F2) (b0 b1 b2 b3 b4 : F2),
      dotProduct a (emb b0 b1 b2 b3 b4) =
        a i0 * b0 + a i1 * b1 + a i2 * b2 + a i3 * b3 + a i4 * b4 := by
    intro a b0 b1 b2 b3 b4
    let S5 : Finset (Fin k) := {i0, i1, i2, i3, i4}
    have hsum : dotProduct a (emb b0 b1 b2 b3 b4) = ∑ j ∈ S5, a j * emb b0 b1 b2 b3 b4 j := by
      simp only [dotProduct]
      symm
      apply Finset.sum_subset (Finset.subset_univ S5)
      intro j _ hj
      simp only [S5, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      rw [hemb_other b0 b1 b2 b3 b4 j hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2, mul_zero]
    rw [hsum]
    simp only [S5]
    rw [Finset.sum_insert (by simp [h01, h02, h03, h04]),
        Finset.sum_insert (by simp [h12, h13, h14]),
        Finset.sum_insert (by simp [h23, h24]),
        Finset.sum_pair h34,
        hemb_i0, hemb_i1, hemb_i2, hemb_i3, hemb_i4]
    ring

  let mkCube (g : F2 × F2 × F2 → Fin k → F2) : Finset (Fin k → F2) := Finset.univ.image g
  let g0 : F2 × F2 × F2 → Fin k → F2 := fun t => emb 0 0 t.1 t.2.1 t.2.2
  let g1 : F2 × F2 × F2 → Fin k → F2 := fun t => emb 0 t.1 t.2.1 0 t.2.2
  let g2 : F2 × F2 × F2 → Fin k → F2 := fun t => emb t.1 0 t.2.1 0 t.2.2
  let g3 : F2 × F2 × F2 → Fin k → F2 := fun t => emb t.1 t.2.1 0 0 t.2.2
  have hg0_inj : Function.Injective g0 := fun t1 t2 h => by
    have h' := hemb_inj _ _ _ _ _ _ _ _ _ _ h
    exact Prod.ext h'.2.2.1 (Prod.ext h'.2.2.2.1 h'.2.2.2.2)
  have hg1_inj : Function.Injective g1 := fun t1 t2 h => by
    have h' := hemb_inj _ _ _ _ _ _ _ _ _ _ h
    exact Prod.ext h'.2.1 (Prod.ext h'.2.2.1 h'.2.2.2.2)
  have hg2_inj : Function.Injective g2 := fun t1 t2 h => by
    have h' := hemb_inj _ _ _ _ _ _ _ _ _ _ h
    exact Prod.ext h'.1 (Prod.ext h'.2.2.1 h'.2.2.2.2)
  have hg3_inj : Function.Injective g3 := fun t1 t2 h => by
    have h' := hemb_inj _ _ _ _ _ _ _ _ _ _ h
    exact Prod.ext h'.1 (Prod.ext h'.2.1 h'.2.2.2.2)
  let U0 := mkCube g0
  let U1 := mkCube g1
  let U2 := mkCube g2
  let U3 := mkCube g3
  let E : Finset (Fin k → F2) := U0 ∪ U1 ∪ U2 ∪ U3

  have hcube_quad : ∀ (g : F2 × F2 × F2 → Fin k → F2) (p q r : Fin k),
      Function.Injective g →
      (∀ t : F2 × F2 × F2, ∀ j : Fin k,
        g t j = (if j = p then t.1 else 0) + (if j = q then t.2.1 else 0) + (if j = r then t.2.2 else 0)) →
      ∀ f : (Fin k → F2) → F2, Quad f → ∑ s ∈ mkCube g, f s = 0 := by
    intro g p q r hginj hgval f hf
    rw [Finset.sum_image (fun x _ y _ h => hginj h)]
    rcases hf with ⟨b, l, M, hfEq⟩
    have hdot : ∀ t : F2 × F2 × F2,
        dotProduct l (g t) = l p * t.1 + l q * t.2.1 + l r * t.2.2 := by
      intro t
      simp only [dotProduct, hgval t, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hquadM : ∀ t : F2 × F2 × F2,
        ∑ i, ∑ j, M i j * g t i * g t j =
          (M p p) * t.1 + (M q q) * t.2.1 + (M r r) * t.2.2 +
          (M p q + M q p) * t.1 * t.2.1 +
          (M p r + M r p) * t.1 * t.2.2 +
          (M q r + M r q) * t.2.1 * t.2.2 := by
      intro t
      have hinner : ∀ i : Fin k, ∑ j, M i j * g t i * g t j =
          g t i * (M i p * t.1 + M i q * t.2.1 + M i r * t.2.2) := by
        intro i
        have h1 : ∀ j, M i j * g t i * g t j = g t i * (M i j * g t j) := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.mul_sum]
        congr 1
        simp only [hgval t, mul_add, Finset.sum_add_distrib, mul_ite,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      simp only [hinner]
      simp only [hgval t, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hs1 : t.1 * t.1 = t.1 := zmod2_mul_self _
      have hs2 : t.2.1 * t.2.1 = t.2.1 := zmod2_mul_self _
      have hs3 : t.2.2 * t.2.2 = t.2.2 := zmod2_mul_self _
      calc t.1 * (M p p * t.1 + M p q * t.2.1 + M p r * t.2.2) +
           t.2.1 * (M q p * t.1 + M q q * t.2.1 + M q r * t.2.2) +
           t.2.2 * (M r p * t.1 + M r q * t.2.1 + M r r * t.2.2)
          = M p p * (t.1 * t.1) + M q q * (t.2.1 * t.2.1) + M r r * (t.2.2 * t.2.2) +
            (M p q + M q p) * t.1 * t.2.1 + (M p r + M r p) * t.1 * t.2.2 +
            (M q r + M r q) * t.2.1 * t.2.2 := by ring
        _ = _ := by rw [hs1, hs2, hs3]; ring
    have hfev : ∀ t : F2 × F2 × F2, f (g t) =
        b + (l p + M p p) * t.1 + (l q + M q q) * t.2.1 + (l r + M r r) * t.2.2 +
        (M p q + M q p) * t.1 * t.2.1 + (M p r + M r p) * t.1 * t.2.2 +
        (M q r + M r q) * t.2.1 * t.2.2 := by
      intro t
      rw [hfEq (g t), hdot t, hquadM t]
      ring
    simp only [hfev]
    exact sum_cube3_quad_eval _ _ _ _ _ _ _
  have hU0_rel : U0 ∈ relSet E := by
    rw [mem_relSet_iff]
    refine ⟨by intro s hs; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hs)),
      hcube_quad g0 i2 i3 i4 hg0_inj (fun t j => by
        by_cases hj0 : j = i0
        · subst hj0; simp [g0, hemb_i0, h02, h03, h04]
        · by_cases hj1 : j = i1
          · subst hj1; simp [g0, hemb_i1, h12, h13, h14]
          · by_cases hj2 : j = i2
            · subst hj2; simp [g0, hemb_i2, h23, h24]
            · by_cases hj3 : j = i3
              · subst hj3; simp [g0, hemb_i3, h23.symm, h34]
              · by_cases hj4 : j = i4
                · subst hj4; simp [g0, hemb_i4, h24.symm, h34.symm]
                · simp [g0, hemb_other _ _ _ _ _ j hj0 hj1 hj2 hj3 hj4, hj2, hj3, hj4])⟩
  have hU1_rel : U1 ∈ relSet E := by
    rw [mem_relSet_iff]
    refine ⟨by intro s hs; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hs)),
      hcube_quad g1 i1 i2 i4 hg1_inj (fun t j => by
        by_cases hj0 : j = i0
        · subst hj0; simp [g1, hemb_i0, h01, h02, h04]
        · by_cases hj1 : j = i1
          · subst hj1; simp [g1, hemb_i1, h12, h14]
          · by_cases hj2 : j = i2
            · subst hj2; simp [g1, hemb_i2, h12.symm, h24]
            · by_cases hj3 : j = i3
              · subst hj3; simp [g1, hemb_i3, h13.symm, h23.symm, h34]
              · by_cases hj4 : j = i4
                · subst hj4; simp [g1, hemb_i4, h14.symm, h24.symm]
                · simp [g1, hemb_other _ _ _ _ _ j hj0 hj1 hj2 hj3 hj4, hj1, hj2, hj4])⟩
  have hU2_rel : U2 ∈ relSet E := by
    rw [mem_relSet_iff]
    refine ⟨by intro s hs; exact Finset.mem_union_left _ (Finset.mem_union_right _ hs),
      hcube_quad g2 i0 i2 i4 hg2_inj (fun t j => by
        by_cases hj0 : j = i0
        · subst hj0; simp [g2, hemb_i0, h02, h04]
        · by_cases hj1 : j = i1
          · subst hj1; simp [g2, hemb_i1, h01.symm, h12, h14]
          · by_cases hj2 : j = i2
            · subst hj2; simp [g2, hemb_i2, h02.symm, h24]
            · by_cases hj3 : j = i3
              · subst hj3; simp [g2, hemb_i3, h03.symm, h23.symm, h34]
              · by_cases hj4 : j = i4
                · subst hj4; simp [g2, hemb_i4, h04.symm, h24.symm]
                · simp [g2, hemb_other _ _ _ _ _ j hj0 hj1 hj2 hj3 hj4, hj0, hj2, hj4])⟩
  have hU3_rel : U3 ∈ relSet E := by
    rw [mem_relSet_iff]
    refine ⟨by intro s hs; exact Finset.mem_union_right _ hs,
      hcube_quad g3 i0 i1 i4 hg3_inj (fun t j => by
        by_cases hj0 : j = i0
        · subst hj0; simp [g3, hemb_i0, h01, h04]
        · by_cases hj1 : j = i1
          · subst hj1; simp [g3, hemb_i1, h01.symm, h14]
          · by_cases hj2 : j = i2
            · subst hj2; simp [g3, hemb_i2, h02.symm, h12.symm, h24]
            · by_cases hj3 : j = i3
              · subst hj3; simp [g3, hemb_i3, h03.symm, h13.symm, h34]
              · by_cases hj4 : j = i4
                · subst hj4; simp [g3, hemb_i4, h04.symm, h14.symm]
                · simp [g3, hemb_other _ _ _ _ _ j hj0 hj1 hj2 hj3 hj4, hj0, hj1, hj4])⟩

  let p0 := emb 0 0 1 1 1
  let p1 := emb 0 1 1 0 1
  let p2 := emb 1 0 1 0 1
  let p3 := emb 1 1 0 0 1
  have hp0_mem : p0 ∈ U0 ∧ p0 ∉ U1 ∧ p0 ∉ U2 ∧ p0 ∉ U3 := by
    refine ⟨Finset.mem_image.mpr ⟨(1, 1, 1), Finset.mem_univ _, rfl⟩, ?_, ?_, ?_⟩
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.2.2.1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.2.2.1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.2.2.1; exact zero_ne_one h'
  have hp1_mem : p1 ∉ U0 ∧ p1 ∈ U1 ∧ p1 ∉ U2 ∧ p1 ∉ U3 := by
    refine ⟨?_, Finset.mem_image.mpr ⟨(1, 1, 1), Finset.mem_univ _, rfl⟩, ?_, ?_⟩
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.2.1; exact zero_ne_one h'
  have hp2_mem : p2 ∉ U0 ∧ p2 ∉ U1 ∧ p2 ∈ U2 ∧ p2 ∉ U3 := by
    refine ⟨?_, ?_, Finset.mem_image.mpr ⟨(1, 1, 1), Finset.mem_univ _, rfl⟩, ?_⟩
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.2.1; exact zero_ne_one h'
  have hp3_mem : p3 ∉ U0 ∧ p3 ∉ U1 ∧ p3 ∉ U2 ∧ p3 ∈ U3 := by
    refine ⟨?_, ?_, ?_, Finset.mem_image.mpr ⟨(1, 1, 1), Finset.mem_univ _, rfl⟩⟩
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).1; exact zero_ne_one h'
    · intro h; obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      have h' := (hemb_inj _ _ _ _ _ _ _ _ _ _ ht).2.1; exact zero_ne_one h'

  have hrel_card : (relSet E).card = 16 := by
    let u0 : orth (quadSub E) := relEquiv E ⟨U0, hU0_rel⟩
    let u1 : orth (quadSub E) := relEquiv E ⟨U1, hU1_rel⟩
    let u2 : orth (quadSub E) := relEquiv E ⟨U2, hU2_rel⟩
    let u3 : orth (quadSub E) := relEquiv E ⟨U3, hU3_rel⟩
    let comb : (Fin 4 → F2) → orth (quadSub E) :=
      fun c => c 0 • u0 + c 1 • u1 + c 2 • u2 + c 3 • u3
    have hp0E : p0 ∈ E := ((mem_relSet_iff E U0).mp hU0_rel).1 hp0_mem.1
    have hp1E : p1 ∈ E := ((mem_relSet_iff E U1).mp hU1_rel).1 hp1_mem.2.1
    have hp2E : p2 ∈ E := ((mem_relSet_iff E U2).mp hU2_rel).1 hp2_mem.2.2.1
    have hp3E : p3 ∈ E := ((mem_relSet_iff E U3).mp hU3_rel).1 hp3_mem.2.2.2
    have hcomb_eval : ∀ c : Fin 4 → F2,
        (comb c).1 ⟨p0, hp0E⟩ = c 0 ∧ (comb c).1 ⟨p1, hp1E⟩ = c 1 ∧
        (comb c).1 ⟨p2, hp2E⟩ = c 2 ∧ (comb c).1 ⟨p3, hp3E⟩ = c 3 := by
      intro c
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [comb, u0, u1, u2, u3, relEquiv, indE, hp0_mem.1, hp0_mem.2.1, hp0_mem.2.2.1, hp0_mem.2.2.2]
      · simp [comb, u0, u1, u2, u3, relEquiv, indE, hp1_mem.1, hp1_mem.2.1, hp1_mem.2.2.1, hp1_mem.2.2.2]
      · simp [comb, u0, u1, u2, u3, relEquiv, indE, hp2_mem.1, hp2_mem.2.1, hp2_mem.2.2.1, hp2_mem.2.2.2]
      · simp [comb, u0, u1, u2, u3, relEquiv, indE, hp3_mem.1, hp3_mem.2.1, hp3_mem.2.2.1, hp3_mem.2.2.2]
    have hcomb_inj : Function.Injective comb := by
      intro c d hEq
      ext r
      fin_cases r
      · have h1 := (hcomb_eval c).1; have h2 := (hcomb_eval d).1
        rw [hEq] at h1; exact h1.symm.trans h2
      · have h1 := (hcomb_eval c).2.1; have h2 := (hcomb_eval d).2.1
        rw [hEq] at h1; exact h1.symm.trans h2
      · have h1 := (hcomb_eval c).2.2.1; have h2 := (hcomb_eval d).2.2.1
        rw [hEq] at h1; exact h1.symm.trans h2
      · have h1 := (hcomb_eval c).2.2.2; have h2 := (hcomb_eval d).2.2.2
        rw [hEq] at h1; exact h1.symm.trans h2
    have hcomb_surj : Function.Surjective comb := by
      intro w
      let c : Fin 4 → F2 := ![w.1 ⟨p0, hp0E⟩, w.1 ⟨p1, hp1E⟩, w.1 ⟨p2, hp2E⟩, w.1 ⟨p3, hp3E⟩]
      refine ⟨c, ?_⟩
      let d : orth (quadSub E) := w + comb c
      let V : Finset (Fin k → F2) := suppE E d.1
      have hVrel : V ∈ relSet E := (suppE_mem_relSet_iff E d.1).mpr d.2
      have hVsub : V ⊆ E := ((mem_relSet_iff E V).mp hVrel).1
      have hVquad : ∀ f : (Fin k → F2) → F2, Quad f → ∑ s ∈ V, f s = 0 :=
        ((mem_relSet_iff E V).mp hVrel).2
      have hV_not_p : p0 ∉ V ∧ p1 ∉ V ∧ p2 ∉ V ∧ p3 ∉ V := by
        have hv0 : d.1 ⟨p0, hp0E⟩ = 0 := by
          change w.1 ⟨p0, hp0E⟩ + (comb c).1 ⟨p0, hp0E⟩ = 0
          rw [(hcomb_eval c).1]; exact zmod2_add_self _
        have hv1 : d.1 ⟨p1, hp1E⟩ = 0 := by
          change w.1 ⟨p1, hp1E⟩ + (comb c).1 ⟨p1, hp1E⟩ = 0
          rw [(hcomb_eval c).2.1]; exact zmod2_add_self _
        have hv2 : d.1 ⟨p2, hp2E⟩ = 0 := by
          change w.1 ⟨p2, hp2E⟩ + (comb c).1 ⟨p2, hp2E⟩ = 0
          rw [(hcomb_eval c).2.2.1]; exact zmod2_add_self _
        have hv3 : d.1 ⟨p3, hp3E⟩ = 0 := by
          change w.1 ⟨p3, hp3E⟩ + (comb c).1 ⟨p3, hp3E⟩ = 0
          rw [(hcomb_eval c).2.2.2]; exact zmod2_add_self _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [show p0 = (⟨p0, hp0E⟩ : E).1 from rfl, mem_suppE_iff, hv0]; exact zero_ne_one
        · rw [show p1 = (⟨p1, hp1E⟩ : E).1 from rfl, mem_suppE_iff, hv1]; exact zero_ne_one
        · rw [show p2 = (⟨p2, hp2E⟩ : E).1 from rfl, mem_suppE_iff, hv2]; exact zero_ne_one
        · rw [show p3 = (⟨p3, hp3E⟩ : E).1 from rfl, mem_suppE_iff, hv3]; exact zero_ne_one

      have helim : ∀ (x : Fin k → F2) (f : (Fin k → F2) → F2),
          Quad f → f x = 1 → (∀ s ∈ V, s ≠ x → f s = 0) → x ∉ V := by
        intro x f hf hfx hother hxV
        have hsum1 : ∑ s ∈ V, f s = 1 := by
          rw [Finset.sum_eq_single x]
          · exact hfx
          · intro s hs hne; exact hother s hs hne
          · intro h; exact (h hxV).elim
        rw [hVquad f hf] at hsum1
        exact zero_ne_one hsum1

      have hE_char : ∀ s ∈ E, ∃ b0 b1 b2 b3 b4 : F2, s = emb b0 b1 b2 b3 b4 ∧
          ((b0 = 0 ∧ b1 = 0) ∨ (b0 = 0 ∧ b3 = 0) ∨ (b1 = 0 ∧ b3 = 0) ∨ (b2 = 0 ∧ b3 = 0)) := by
        intro s hs
        simp only [E, Finset.mem_union] at hs
        rcases hs with ((h0 | h1) | h2) | h3
        · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h0
          exact ⟨0, 0, t.1, t.2.1, t.2.2, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h1
          exact ⟨0, t.1, t.2.1, 0, t.2.2, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h2
          exact ⟨t.1, 0, t.2.1, 0, t.2.2, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
        · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h3
          exact ⟨t.1, t.2.1, 0, 0, t.2.2, rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

      have hne_23 : emb 0 0 1 1 0 ∉ V := helim _ (fun s => s i2 * s i3) (quad_coord_mul i2 i3)
        (by simp [hemb_i2, hemb_i3]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, hpat⟩ := hE_char s (hVsub hs)
          rw [hemb_i2, hemb_i3]
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b3 with rfl | rfl; · simp
          rcases hpat with ⟨rfl, rfl⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hV_not_p.1 hs).elim
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero)
      have hne_12 : emb 0 1 1 0 0 ∉ V := helim _ (fun s => s i1 * s i2) (quad_coord_mul i1 i2)
        (by simp [hemb_i1, hemb_i2]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, hpat⟩ := hE_char s (hVsub hs)
          rw [hemb_i1, hemb_i2]
          rcases zmod2_eq_zero_or_one b1 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · simp
          rcases hpat with ⟨_, h⟩ | ⟨rfl, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hV_not_p.2.1 hs).elim
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero)
      have hne_02 : emb 1 0 1 0 0 ∉ V := helim _ (fun s => s i0 * s i2) (quad_coord_mul i0 i2)
        (by simp [hemb_i0, hemb_i2]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, hpat⟩ := hE_char s (hVsub hs)
          rw [hemb_i0, hemb_i2]
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · simp
          rcases hpat with ⟨h, _⟩ | ⟨h, _⟩ | ⟨rfl, rfl⟩ | ⟨h, _⟩
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hV_not_p.2.2.1 hs).elim
          · exact absurd h one_ne_zero)
      have hne_01 : emb 1 1 0 0 0 ∉ V := helim _ (fun s => s i0 * s i1) (quad_coord_mul i0 i1)
        (by simp [hemb_i0, hemb_i1]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, hpat⟩ := hE_char s (hVsub hs)
          rw [hemb_i0, hemb_i1]
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b1 with rfl | rfl; · simp
          rcases hpat with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨rfl, rfl⟩
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hV_not_p.2.2.2 hs).elim)

      have hV_wt1 : ∀ s ∈ V, ∃ b0 b1 b2 b3 b4 : F2, s = emb b0 b1 b2 b3 b4 ∧
          (b0 = 0 ∨ (b1 = 0 ∧ b2 = 0 ∧ b3 = 0)) ∧
          (b1 = 0 ∨ (b0 = 0 ∧ b2 = 0 ∧ b3 = 0)) ∧
          (b2 = 0 ∨ (b0 = 0 ∧ b1 = 0 ∧ b3 = 0)) ∧
          (b3 = 0 ∨ (b0 = 0 ∧ b1 = 0 ∧ b2 = 0)) := by
        intro s hs
        obtain ⟨b0, b1, b2, b3, b4, rfl, hpat⟩ := hE_char s (hVsub hs)
        have h01' : b0 = 0 ∨ b1 = 0 := by
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl; · exact Or.inl rfl
          rcases zmod2_eq_zero_or_one b1 with rfl | rfl; · exact Or.inr rfl
          rcases hpat with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨rfl, rfl⟩
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne_01 hs).elim
            · exact (hV_not_p.2.2.2 hs).elim
        have h02' : b0 = 0 ∨ b2 = 0 := by
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl; · exact Or.inl rfl
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · exact Or.inr rfl
          rcases hpat with ⟨h, _⟩ | ⟨h, _⟩ | ⟨rfl, rfl⟩ | ⟨h, _⟩
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne_02 hs).elim
            · exact (hV_not_p.2.2.1 hs).elim
          · exact absurd h one_ne_zero
        have h12' : b1 = 0 ∨ b2 = 0 := by
          rcases zmod2_eq_zero_or_one b1 with rfl | rfl; · exact Or.inl rfl
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · exact Or.inr rfl
          rcases hpat with ⟨_, h⟩ | ⟨rfl, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne_12 hs).elim
            · exact (hV_not_p.2.1 hs).elim
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
        have h23' : b2 = 0 ∨ b3 = 0 := by
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · exact Or.inl rfl
          rcases zmod2_eq_zero_or_one b3 with rfl | rfl; · exact Or.inr rfl
          rcases hpat with ⟨rfl, rfl⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne_23 hs).elim
            · exact (hV_not_p.1 hs).elim
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
          · exact absurd h one_ne_zero
        have h03' : b0 = 0 ∨ b3 = 0 := by
          rcases hpat with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
          · exact Or.inl h
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inr h
        have h13' : b1 = 0 ∨ b3 = 0 := by
          rcases hpat with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl h
          · exact Or.inr h
        refine ⟨b0, b1, b2, b3, b4, rfl, ?_, ?_, ?_, ?_⟩
        · rcases zmod2_eq_zero_or_one b0 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ⟨h01'.resolve_left one_ne_zero, h02'.resolve_left one_ne_zero,
              h03'.resolve_left one_ne_zero⟩
        · rcases zmod2_eq_zero_or_one b1 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ⟨h01'.resolve_right one_ne_zero, h12'.resolve_left one_ne_zero,
              h13'.resolve_left one_ne_zero⟩
        · rcases zmod2_eq_zero_or_one b2 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ⟨h02'.resolve_right one_ne_zero, h12'.resolve_right one_ne_zero,
              h23'.resolve_left one_ne_zero⟩
        · rcases zmod2_eq_zero_or_one b3 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ⟨h03'.resolve_right one_ne_zero, h13'.resolve_right one_ne_zero,
              h23'.resolve_right one_ne_zero⟩

      have hne_04 : emb 1 0 0 0 1 ∉ V := helim _ (fun s => s i0 * s i4) (quad_coord_mul i0 i4)
        (by simp [hemb_i0, hemb_i4]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, h0, _, _, _⟩ := hV_wt1 s hs
          rw [hemb_i0, hemb_i4]
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b4 with rfl | rfl; · simp
          rcases h0 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · exact (hne rfl).elim)
      have hne_14 : emb 0 1 0 0 1 ∉ V := helim _ (fun s => s i1 * s i4) (quad_coord_mul i1 i4)
        (by simp [hemb_i1, hemb_i4]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, _, h1, _, _⟩ := hV_wt1 s hs
          rw [hemb_i1, hemb_i4]
          rcases zmod2_eq_zero_or_one b1 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b4 with rfl | rfl; · simp
          rcases h1 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · exact (hne rfl).elim)
      have hne_24 : emb 0 0 1 0 1 ∉ V := helim _ (fun s => s i2 * s i4) (quad_coord_mul i2 i4)
        (by simp [hemb_i2, hemb_i4]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, _, _, h2, _⟩ := hV_wt1 s hs
          rw [hemb_i2, hemb_i4]
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b4 with rfl | rfl; · simp
          rcases h2 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · exact (hne rfl).elim)
      have hne_34 : emb 0 0 0 1 1 ∉ V := helim _ (fun s => s i3 * s i4) (quad_coord_mul i3 i4)
        (by simp [hemb_i3, hemb_i4]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, _, _, _, h3⟩ := hV_wt1 s hs
          rw [hemb_i3, hemb_i4]
          rcases zmod2_eq_zero_or_one b3 with rfl | rfl; · simp
          rcases zmod2_eq_zero_or_one b4 with rfl | rfl; · simp
          rcases h3 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · exact (hne rfl).elim)

      have hne_e0 : emb 1 0 0 0 0 ∉ V := helim _ (fun s => s i0) (quad_coord i0)
        (by simp [hemb_i0]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, h0, _, _, _⟩ := hV_wt1 s hs
          rw [hemb_i0]
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl; · rfl
          rcases h0 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hne_04 hs).elim)
      have hne_e1 : emb 0 1 0 0 0 ∉ V := helim _ (fun s => s i1) (quad_coord i1)
        (by simp [hemb_i1]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, _, h1, _, _⟩ := hV_wt1 s hs
          rw [hemb_i1]
          rcases zmod2_eq_zero_or_one b1 with rfl | rfl; · rfl
          rcases h1 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hne_14 hs).elim)
      have hne_e2 : emb 0 0 1 0 0 ∉ V := helim _ (fun s => s i2) (quad_coord i2)
        (by simp [hemb_i2]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, _, _, h2, _⟩ := hV_wt1 s hs
          rw [hemb_i2]
          rcases zmod2_eq_zero_or_one b2 with rfl | rfl; · rfl
          rcases h2 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hne_24 hs).elim)
      have hne_e3 : emb 0 0 0 1 0 ∉ V := helim _ (fun s => s i3) (quad_coord i3)
        (by simp [hemb_i3]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, _, _, _, h3⟩ := hV_wt1 s hs
          rw [hemb_i3]
          rcases zmod2_eq_zero_or_one b3 with rfl | rfl; · rfl
          rcases h3 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne rfl).elim
            · exact (hne_34 hs).elim)

      have hne_e4 : emb 0 0 0 0 1 ∉ V := helim _ (fun s => s i4) (quad_coord i4)
        (by simp [hemb_i4]) (fun s hs hne => by
          obtain ⟨b0, b1, b2, b3, b4, rfl, h0, h1, h2, _⟩ := hV_wt1 s hs
          rw [hemb_i4]
          rcases zmod2_eq_zero_or_one b4 with rfl | rfl; · rfl
          rcases zmod2_eq_zero_or_one b0 with rfl | rfl
          · rcases zmod2_eq_zero_or_one b1 with rfl | rfl
            · rcases zmod2_eq_zero_or_one b2 with rfl | rfl
              · rcases zmod2_eq_zero_or_one b3 with rfl | rfl
                · exact (hne rfl).elim
                · exact (hne_34 hs).elim
              · rcases h2 with h | ⟨_, _, rfl⟩
                · exact absurd h one_ne_zero
                · exact (hne_24 hs).elim
            · rcases h1 with h | ⟨_, rfl, rfl⟩
              · exact absurd h one_ne_zero
              · exact (hne_14 hs).elim
          · rcases h0 with h | ⟨rfl, rfl, rfl⟩
            · exact absurd h one_ne_zero
            · exact (hne_04 hs).elim)
      have hne_0 : emb 0 0 0 0 0 ∉ V := helim _ (fun _ => 1) (quad_const 1) rfl (fun s hs hne => by
        obtain ⟨b0, b1, b2, b3, b4, rfl, h0, h1, h2, _⟩ := hV_wt1 s hs
        rcases zmod2_eq_zero_or_one b0 with rfl | rfl
        · rcases zmod2_eq_zero_or_one b1 with rfl | rfl
          · rcases zmod2_eq_zero_or_one b2 with rfl | rfl
            · rcases zmod2_eq_zero_or_one b3 with rfl | rfl
              · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
                · exact (hne rfl).elim
                · exact (hne_e4 hs).elim
              · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
                · exact (hne_e3 hs).elim
                · exact (hne_34 hs).elim
            · rcases h2 with h | ⟨_, _, rfl⟩
              · exact absurd h one_ne_zero
              · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
                · exact (hne_e2 hs).elim
                · exact (hne_24 hs).elim
          · rcases h1 with h | ⟨_, rfl, rfl⟩
            · exact absurd h one_ne_zero
            · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
              · exact (hne_e1 hs).elim
              · exact (hne_14 hs).elim
        · rcases h0 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact (hne_e0 hs).elim
            · exact (hne_04 hs).elim)
      have hVempty : V = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro s hs
        obtain ⟨b0, b1, b2, b3, b4, rfl, h0, h1, h2, _⟩ := hV_wt1 s hs
        rcases zmod2_eq_zero_or_one b0 with rfl | rfl
        · rcases zmod2_eq_zero_or_one b1 with rfl | rfl
          · rcases zmod2_eq_zero_or_one b2 with rfl | rfl
            · rcases zmod2_eq_zero_or_one b3 with rfl | rfl
              · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
                · exact hne_0 hs
                · exact hne_e4 hs
              · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
                · exact hne_e3 hs
                · exact hne_34 hs
            · rcases h2 with h | ⟨_, _, rfl⟩
              · exact absurd h one_ne_zero
              · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
                · exact hne_e2 hs
                · exact hne_24 hs
          · rcases h1 with h | ⟨_, rfl, rfl⟩
            · exact absurd h one_ne_zero
            · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
              · exact hne_e1 hs
              · exact hne_14 hs
        · rcases h0 with h | ⟨rfl, rfl, rfl⟩
          · exact absurd h one_ne_zero
          · rcases zmod2_eq_zero_or_one b4 with rfl | rfl
            · exact hne_e0 hs
            · exact hne_04 hs
      have hd0 : d = 0 := by
        apply Subtype.ext
        rw [← indE_suppE E d.1]
        change indE E V = 0
        rw [hVempty]
        ext x; simp [indE]
      apply Subtype.ext
      ext x
      have hx : w.1 x + (comb c).1 x = 0 := congrFun (congrArg Subtype.val hd0) x
      exact ((zmod2_eq_iff_add_eq_zero _ _).mpr hx).symm
    have hbij : Function.Bijective comb := ⟨hcomb_inj, hcomb_surj⟩
    let _ : Fintype (orth (quadSub E)) := Fintype.ofFinite _
    have hcard_orth : Fintype.card (orth (quadSub E)) = 16 := by
      rw [← Fintype.card_of_bijective hbij, card_fin_f2]
      norm_num
    rw [← Fintype.card_coe, Fintype.card_congr (relEquiv E), hcard_orth]

  let h : (Fin k → F2) → F2 := fun s => if s = p0 ∨ s = p3 then 1 else 0
  have hsum_h : (∑ s ∈ U0, h s = 1) ∧ (∑ s ∈ U1, h s = 0) ∧
      (∑ s ∈ U2, h s = 0) ∧ (∑ s ∈ U3, h s = 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_eq_single p0]
      · simp [h]
      · intro s hs hne; simp [h, hne, show s ≠ p3 from fun heq => hp3_mem.1 (heq ▸ hs)]
      · intro hn; exact (hn hp0_mem.1).elim
    · exact Finset.sum_eq_zero fun s hs => by
        simp [h, show s ≠ p0 from fun heq => hp0_mem.2.1 (heq ▸ hs),
          show s ≠ p3 from fun heq => hp3_mem.2.1 (heq ▸ hs)]
    · exact Finset.sum_eq_zero fun s hs => by
        simp [h, show s ≠ p0 from fun heq => hp0_mem.2.2.1 (heq ▸ hs),
          show s ≠ p3 from fun heq => hp3_mem.2.2.1 (heq ▸ hs)]
    · rw [Finset.sum_eq_single p3]
      · simp [h]
      · intro s hs hne; simp [h, hne, show s ≠ p0 from fun heq => hp0_mem.2.2.2 (heq ▸ hs)]
      · intro hn; exact (hn hp3_mem.2.2.2).elim
  refine ⟨E, h, hrel_card, fun a b hfit => ?_⟩
  rcases hfit with ⟨c, f, hf, hfeq⟩
  have hsig_eq : ∀ U ∈ relSet E, sigF U a b c = ∑ s ∈ U, h s := by
    intro U hU
    have hsub := ((mem_relSet_iff E U).mp hU).1
    have hf0 := ((mem_relSet_iff E U).mp hU).2 f hf
    have hsum : ∑ s ∈ U, h s = (∑ s ∈ U, f s) + sigF U a b c := by
      simp only [sigF, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s hs => hfeq s (hsub hs)
    rw [hsum, hf0, zero_add]
  have hs0 : sigF U0 a b c = det3 (a i2) (b i2) (c i2) (a i3) (b i3) (c i3) (a i4) (b i4) (c i4) := by
    simp only [sigF, U0, mkCube, Finset.sum_image (fun x _ y _ h => hg0_inj h), tripleF, g0, hdot_emb]
    simpa only [mul_zero, zero_add] using
      sum_cube3_triple_eval (a i2) (a i3) (a i4) (b i2) (b i3) (b i4) (c i2) (c i3) (c i4)
  have hs1 : sigF U1 a b c = det3 (a i1) (b i1) (c i1) (a i2) (b i2) (c i2) (a i4) (b i4) (c i4) := by
    simp only [sigF, U1, mkCube, Finset.sum_image (fun x _ y _ h => hg1_inj h), tripleF, g1, hdot_emb]
    simpa only [mul_zero, zero_add, add_zero] using
      sum_cube3_triple_eval (a i1) (a i2) (a i4) (b i1) (b i2) (b i4) (c i1) (c i2) (c i4)
  have hs2 : sigF U2 a b c = det3 (a i0) (b i0) (c i0) (a i2) (b i2) (c i2) (a i4) (b i4) (c i4) := by
    simp only [sigF, U2, mkCube, Finset.sum_image (fun x _ y _ h => hg2_inj h), tripleF, g2, hdot_emb]
    simpa only [mul_zero, zero_add, add_zero] using
      sum_cube3_triple_eval (a i0) (a i2) (a i4) (b i0) (b i2) (b i4) (c i0) (c i2) (c i4)
  have hs3 : sigF U3 a b c = det3 (a i0) (b i0) (c i0) (a i1) (b i1) (c i1) (a i4) (b i4) (c i4) := by
    simp only [sigF, U3, mkCube, Finset.sum_image (fun x _ y _ h => hg3_inj h), tripleF, g3, hdot_emb]
    simpa only [mul_zero, zero_add, add_zero] using
      sum_cube3_triple_eval (a i0) (a i1) (a i4) (b i0) (b i1) (b i4) (c i0) (c i1) (c i4)
  have hd0 : det3 (a i2) (b i2) (c i2) (a i3) (b i3) (c i3) (a i4) (b i4) (c i4) = 1 := by
    rw [← hs0, hsig_eq U0 hU0_rel, hsum_h.1]
  have hd1 : det3 (a i1) (b i1) (c i1) (a i2) (b i2) (c i2) (a i4) (b i4) (c i4) = 0 := by
    rw [← hs1, hsig_eq U1 hU1_rel, hsum_h.2.1]
  have hd2 : det3 (a i0) (b i0) (c i0) (a i2) (b i2) (c i2) (a i4) (b i4) (c i4) = 0 := by
    rw [← hs2, hsig_eq U2 hU2_rel, hsum_h.2.2.1]
  have hd3 : det3 (a i0) (b i0) (c i0) (a i1) (b i1) (c i1) (a i4) (b i4) (c i4) = 1 := by
    rw [← hs3, hsig_eq U3 hU3_rel, hsum_h.2.2.2]
  have hpl := plucker_det3 (a i0) (b i0) (c i0) (a i1) (b i1) (c i1) (a i2) (b i2) (c i2)
    (a i3) (b i3) (c i3) (a i4) (b i4) (c i4)
  rw [hd0, hd3, hd2, hd1] at hpl
  simp at hpl

end PEqualNP.Outside.L_lib_1003_aux

open PEqualNP.Outside.L_lib_1003_aux in
theorem PEqualNP.Outside.L_lib_1003 : (∀ k : ℕ,
  let F := ZMod 2
  let S := Fin k → F
  let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
  let rel := fun (E : Finset S) => E.powerset.filter (fun U => @decide
    (∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0) (Classical.propDecidable _))
  let triple := fun (a b c s : S) => dotProduct a s * dotProduct b s * dotProduct c s
  let sig := fun (U : Finset S) (a b c : S) => ∑ s ∈ U, triple a b c s
  let fit := fun (E : Finset S) (h : S → F) (a b : S) =>
    ∃ (c : S) (f : S → F), quad f ∧ ∀ s ∈ E, h s = f s + triple a b c s
  (∀ (E : Finset S) (h : S → F),
    let odd := (rel E).filter (fun U => (∑ s ∈ U, h s) = 1)
    let forms := odd.image sig
    (∀ a b : S, fit E h a b ↔ ∀ U ∈ odd, ∃ c : S, sig U a b c = 1) ∧
    ((rel E).card ≤ 8 ∨ (forms.card ≤ 4 ∧ ∀ U ∈ odd, ∃ a b c : S, sig U a b c = 1) →
      let pairs := (Finset.univ : Finset (S × S)).filter
        (fun v => @decide (fit E h v.1 v.2) (Classical.propDecidable _))
      3 * 2^(2*k) ≤ 32 * pairs.card)) ∧
  (5 ≤ k → ∃ (E : Finset S) (h : S → F), (rel E).card = 16 ∧
    ∀ a b : S, ¬ fit E h a b)) := by
  intro k F S quad rel triple sig fit
  constructor
  · intro E h odd forms
    refine ⟨fun a b => fitF_iff E h a b, fun hcond => ?_⟩
    rcases hcond with hrel8 | ⟨hforms4, hnonz⟩
    · by_cases hodd_empty : odd = ∅
      · refine bound_from_four_forms E h ?_ ?_
        · change (odd.image sigF).card ≤ 4
          rw [hodd_empty]; simp
        · intro U hU
          change U ∈ odd at hU
          rw [hodd_empty] at hU
          exact (Finset.notMem_empty U hU).elim
      · have hodd_ne : odd.Nonempty := Finset.nonempty_iff_ne_empty.mpr hodd_empty
        have hodd4 : odd.card ≤ 4 := by
          have h2 : 2 * odd.card = (rel E).card := odd_card_le_half_rel E h hodd_ne
          omega
        have hforms4 : (odd.image sigF).card ≤ 4 := le_trans Finset.card_image_le hodd4
        have hnonz : ∀ U ∈ odd, ∃ a b c : S, sigF U a b c = 1 := by
          intro U hU
          by_contra hall
          have hzero : ∀ a b c : S, sigF U a b c = 0 := by
            intro a b c
            rcases zmod2_eq_zero_or_one (sigF U a b c) with h0 | h1
            · exact h0
            · exact (hall ⟨a, b, c, h1⟩).elim
          have hUne : U.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hUe
            have h1 : (∑ s ∈ U, h s) = 1 := (Finset.mem_filter.mp hU).2
            rw [hUe, Finset.sum_empty] at h1
            exact zero_ne_one h1
          have h16 : 16 ≤ (rel E).card := zero_sig_gives_many_rels (Finset.mem_filter.mp hU).1 hUne hzero
          omega
        exact bound_from_four_forms E h hforms4 hnonz
    · exact bound_from_four_forms E h hforms4 hnonz
  · exact fun hk => paw_counterexample hk


import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_547

def wordMap {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) : List (Fin q) → (V →ₗ[K] V)
  | [] => LinearMap.id
  | a :: w => (wordMap A w).comp (A a)

lemma wordMap_apply {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (w : List (Fin q)) (x : V) :
    wordMap A w x = w.foldl (fun y a => A a y) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a ws ih => exact ih (A a x)

def obsMap {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (f : V →ₗ[K] K) : V →ₗ[K] (List (Fin q) → K) where
  toFun x w := f (w.foldl (fun y a => A a y) x)
  map_add' x y := by
    funext w
    simp only [← wordMap_apply, map_add, Pi.add_apply]
  map_smul' c x := by
    funext w
    simp only [← wordMap_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

lemma foldl_conj {K : Type} [Field K] {W W' : Type*} [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] {q : ℕ}
    (e : W ≃ₗ[K] W') (C : Fin q → W →ₗ[K] W) (w : List (Fin q)) (x : W) :
    w.foldl (fun y a => (e.toLinearMap.comp ((C a).comp e.symm.toLinearMap)) y) (e x) =
      e (w.foldl (fun y a => C a y) x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a ws ih =>
    simp only [List.foldl_cons, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact ih (C a x)

lemma realize_of_module {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Finite K W] {q : ℕ} (C : Fin q → W →ₗ[K] W) (t0 : W) (h : W →ₗ[K] K) :
    ∃ (t : Fin (Module.finrank K W) → K)
      (B : Fin q → (Fin (Module.finrank K W) → K) →ₗ[K] (Fin (Module.finrank K W) → K))
      (g : (Fin (Module.finrank K W) → K) →ₗ[K] K),
      ∀ w : List (Fin q), g (w.foldl (fun y a => B a y) t) = h (w.foldl (fun y a => C a y) t0) := by
  let e : W ≃ₗ[K] (Fin (Module.finrank K W) → K) := (Module.finBasis K W).equivFun
  refine ⟨e t0, fun a => e.toLinearMap.comp ((C a).comp e.symm.toLinearMap),
    h.comp e.symm.toLinearMap, fun w => ?_⟩
  rw [foldl_conj]
  simp

lemma foldl_restrict {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (R : Submodule K V) (hinv : ∀ a, ∀ x ∈ R, A a x ∈ R)
    (w : List (Fin q)) (x : R) :
    ((w.foldl (fun y a => (A a).restrict (hinv a) y) x : R) : V) =
      w.foldl (fun y a => A a y) (x : V) := by
  induction w generalizing x with
  | nil => rfl
  | cons a ws ih => exact ih ((A a).restrict (hinv a) x)

lemma foldl_quotient {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {q : ℕ}
    (A : Fin q → V →ₗ[K] V) (O : Submodule K V) (hinv : ∀ a, O ≤ O.comap (A a))
    (w : List (Fin q)) (x : V) :
    w.foldl (fun y a => Submodule.mapQ O O (A a) (hinv a) y) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (w.foldl (fun y a => A a y) x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a ws ih =>
    simp only [List.foldl_cons, Submodule.mapQ_apply]
    exact ih (A a x)

end PEqualNP.Outside.L_lib_547

theorem PEqualNP.Outside.L_lib_547 : ∀ (K : Type) [Field K] (q d : ℕ),
  let V := Fin d → K
  ∀ (s : V) (A : Fin q → V →ₗ[K] V),
    let run := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    ∀ f : V →ₗ[K] K,
      let smaller := fun e : ℕ => ∃ (t : Fin e → K)
        (B : Fin q → (Fin e → K) →ₗ[K] (Fin e → K)) (g : (Fin e → K) →ₗ[K] K),
        ∀ w : List (Fin q), g (w.foldl (fun y a => B a y) t) = f (run w)
      (∀ e < d, ¬ smaller e) ↔
        Submodule.span K (Set.range run) = ⊤ ∧
        ∀ x : V, (∀ w : List (Fin q), f (w.foldl (fun y a => A a y) x) = 0) → x = 0 := by
  intro K _ q d V s A run f smaller
  constructor
  · intro hmin
    constructor
    · by_contra hR
      let R : Submodule K V := Submodule.span K (Set.range run)
      have hinv : ∀ a, ∀ x ∈ R, A a x ∈ R := by
        intro a x hx
        have hle : R ≤ R.comap (A a) := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨w, rfl⟩
          change A a (run w) ∈ R
          have hstep : A a (run w) = run (w ++ [a]) := by
            simp [run, List.foldl_append]
          rw [hstep]
          exact Submodule.subset_span ⟨w ++ [a], rfl⟩
        exact hle hx
      have hlt : Module.finrank K R < d := by
        have h1 : Module.finrank K R < Module.finrank K V :=
          Submodule.finrank_lt hR
        simpa [V, Module.finrank_fin_fun] using h1
      let t0 : R := ⟨s, Submodule.subset_span ⟨[], rfl⟩⟩
      obtain ⟨t, B, g, hg⟩ :=
        PEqualNP.Outside.L_lib_547.realize_of_module
          (fun a => (A a).restrict (hinv a)) t0 (f.comp R.subtype)
      refine hmin (Module.finrank K R) hlt ⟨t, B, g, fun w => ?_⟩
      rw [hg w]
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [PEqualNP.Outside.L_lib_547.foldl_restrict]
    · intro x hx
      by_contra hx0
      let O : Submodule K V := LinearMap.ker (PEqualNP.Outside.L_lib_547.obsMap A f)
      have hxO : x ∈ O := by
        rw [LinearMap.mem_ker]
        funext w
        exact hx w
      have hOne : O ≠ ⊥ := by
        intro hbot
        rw [hbot, Submodule.mem_bot] at hxO
        exact hx0 hxO
      have hpos : 0 < Module.finrank K O := by
        exact Nat.pos_of_ne_zero (mt Submodule.finrank_eq_zero.mp hOne)
      have hlt : Module.finrank K (V ⧸ O) < d := by
        have hsum := Submodule.finrank_quotient_add_finrank O
        have hv : Module.finrank K V = d := Module.finrank_fin_fun K
        omega
      have hinv : ∀ a, O ≤ O.comap (A a) := by
        intro a y hy
        rw [Submodule.mem_comap, LinearMap.mem_ker]
        rw [LinearMap.mem_ker] at hy
        funext w
        exact congrFun hy (a :: w)
      have hker : O ≤ LinearMap.ker f := by
        intro y hy
        rw [LinearMap.mem_ker] at hy ⊢
        exact congrFun hy []
      obtain ⟨t, B, g, hg⟩ :=
        PEqualNP.Outside.L_lib_547.realize_of_module
          (fun a => Submodule.mapQ O O (A a) (hinv a))
          (Submodule.Quotient.mk s)
          (Submodule.liftQ O f hker)
      refine hmin (Module.finrank K (V ⧸ O)) hlt ⟨t, B, g, fun w => ?_⟩
      rw [hg w, PEqualNP.Outside.L_lib_547.foldl_quotient]
      rfl
  · rintro ⟨hreach, hobs⟩ e he ⟨t, B, g, hfg⟩
    let phiA := PEqualNP.Outside.L_lib_547.obsMap A f
    let phiB := PEqualNP.Outside.L_lib_547.obsMap B g
    have hmem : ∀ x : V, phiA x ∈ LinearMap.range phiB := by
      have hle : Submodule.span K (Set.range run) ≤ (LinearMap.range phiB).comap phiA := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨u, rfl⟩
        refine ⟨u.foldl (fun y a => B a y) t, ?_⟩
        funext w
        change g (w.foldl (fun y a => B a y) (u.foldl (fun y a => B a y) t)) =
          f (w.foldl (fun y a => A a y) (u.foldl (fun y a => A a y) s))
        rw [← List.foldl_append, ← List.foldl_append]
        exact hfg (u ++ w)
      intro x
      have hx : x ∈ Submodule.span K (Set.range run) := by
        rw [hreach]
        trivial
      exact hle hx
    let psi : V →ₗ[K] LinearMap.range phiB := phiA.codRestrict (LinearMap.range phiB) hmem
    have hinj : Function.Injective psi := by
      intro x y hxy
      have hsub : phiA (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val hxy
      have hzero : x - y = 0 := hobs (x - y) (fun w => congrFun hsub w)
      exact sub_eq_zero.mp hzero
    have h1 : Module.finrank K V ≤ Module.finrank K (LinearMap.range phiB) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have h2 : Module.finrank K (LinearMap.range phiB) ≤ Module.finrank K (Fin e → K) := by
      have hsum := LinearMap.finrank_range_add_finrank_ker phiB
      omega
    have hv : Module.finrank K V = d := Module.finrank_fin_fun K
    have hu : Module.finrank K (Fin e → K) = e := Module.finrank_fin_fun K
    omega

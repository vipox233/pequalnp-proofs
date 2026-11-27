import PEqualNP.Defs

-- L-lib-548: a series has Hankel rank at most d iff it has a d-dimensional linear realization.
-- Forward: the Hankel row space is shift-invariant; transport the shift action into Fin d -> K by a section.
-- Backward: every residual is the observation image of a reachable state, so the row space sits in a range.

namespace PEqualNP.Outside.L_lib_548_aux

section HK
variable {K : Type} [Field K] {q : ℕ}

/-- shift of a word function by one letter -/
def shiftL (a : Fin q) : (List (Fin q) → K) →ₗ[K] (List (Fin q) → K) where
  toFun φ := fun v => φ (a :: v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftL_apply (a : Fin q) (φ : List (Fin q) → K) (v : List (Fin q)) :
    shiftL a φ v = φ (a :: v) := rfl

/-- the Hankel row space of a word function -/
def hank (f : List (Fin q) → K) : Submodule K (List (Fin q) → K) :=
  Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))

theorem self_mem_hank (f : List (Fin q) → K) : f ∈ hank f :=
  Submodule.subset_span ⟨[], by funext v; simp⟩

theorem shiftL_mem_hank (f : List (Fin q) → K) (a : Fin q) {φ : List (Fin q) → K}
    (h : φ ∈ hank f) : shiftL a φ ∈ hank f := by
  have hle : hank f ≤ (hank f).comap (shiftL a) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, rfl⟩
    refine Submodule.subset_span ⟨u ++ [a], ?_⟩
    funext v
    simp [shiftL_apply]
  exact hle h

theorem realize_of_rank (f : List (Fin q) → K) (d : ℕ) (hfin : Module.Finite K (hank f))
    (hd : Module.finrank K (hank f) ≤ d) :
    ∃ (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
      (g : (Fin d → K) →ₗ[K] K),
      ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w := by
  have := hfin
  let e : hank f ≃ₗ[K] (Fin (Module.finrank K (hank f)) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let ψ : (Fin d → K) →ₗ[K] hank f :=
    e.symm.toLinearMap ∘ₗ LinearMap.funLeft K K (Fin.castLE hd)
  have hψ : Function.Surjective ψ :=
    e.symm.surjective.comp (LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective hd))
  obtain ⟨ι, hι⟩ := ψ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hψ)
  have hψι : ∀ φ, ψ (ι φ) = φ := fun φ => by
    simpa using LinearMap.congr_fun hι φ
  let T : Fin q → hank f →ₗ[K] hank f := fun a =>
    (shiftL a).restrict (fun φ h => shiftL_mem_hank f a h)
  refine ⟨ι ⟨f, self_mem_hank f⟩, fun a => ι ∘ₗ T a ∘ₗ ψ,
    LinearMap.proj [] ∘ₗ (hank f).subtype ∘ₗ ψ, ?_⟩
  have key : ∀ (w : List (Fin q)) (φ : hank f),
      (LinearMap.proj [] ∘ₗ (hank f).subtype ∘ₗ ψ)
        (w.foldl (fun x a => (ι ∘ₗ T a ∘ₗ ψ) x) (ι φ)) = (φ : List (Fin q) → K) w := by
    intro w
    induction w with
    | nil => intro φ; simp [hψι]
    | cons a w ih =>
      intro φ
      have h1 : (ι ∘ₗ T a ∘ₗ ψ) (ι φ) = ι (T a φ) := by simp [hψι]
      rw [List.foldl_cons, h1, ih]
      rfl
  intro w
  exact key w ⟨f, self_mem_hank f⟩

variable {V : Type} [AddCommGroup V] [Module K V]

/-- the composite letter map along a word -/
def wordMap (A : Fin q → V →ₗ[K] V) : List (Fin q) → V →ₗ[K] V
  | [] => LinearMap.id
  | a :: v => wordMap A v ∘ₗ A a

theorem wordMap_apply (A : Fin q → V →ₗ[K] V) :
    ∀ (v : List (Fin q)) (x : V), wordMap A v x = v.foldl (fun x a => A a x) x
  | [], _ => rfl
  | a :: v, x => by simp [wordMap, wordMap_apply A v]

/-- observation map: a state goes to its future output word function -/
def obsMap (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) : V →ₗ[K] (List (Fin q) → K) :=
  LinearMap.pi (fun v => g ∘ₗ wordMap A v)

theorem obsMap_apply (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) (x : V) (v : List (Fin q)) :
    obsMap A g x v = g (v.foldl (fun x a => A a x) x) := by
  simp [obsMap, wordMap_apply]

theorem obsMap_run (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) (s : V) (u : List (Fin q)) :
    obsMap A g (u.foldl (fun x a => A a x) s) =
      fun v => g ((u ++ v).foldl (fun x a => A a x) s) := by
  funext v
  rw [obsMap_apply, List.foldl_append]

theorem hank_le_range (f : List (Fin q) → K) (s : V) (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K)
    (h : ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w) :
    hank f ≤ LinearMap.range (obsMap A g) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, rfl⟩
  refine ⟨u.foldl (fun x a => A a x) s, ?_⟩
  rw [obsMap_run]
  funext v
  exact h (u ++ v)

theorem rank_of_realize [FiniteDimensional K V] (f : List (Fin q) → K) (s : V)
    (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K)
    (h : ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w) :
    Module.Finite K (hank f) ∧ Module.finrank K (hank f) ≤ Module.finrank K V := by
  have hle := hank_le_range f s A g h
  have : FiniteDimensional K (hank f) := Submodule.finiteDimensional_of_le hle
  exact ⟨inferInstance, (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le _)⟩

end HK

end PEqualNP.Outside.L_lib_548_aux

open PEqualNP.Outside.L_lib_548_aux in
theorem PEqualNP.Outside.L_lib_548 :
    ∀ (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K),
      let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
      ∀ d : ℕ, (Module.Finite K R ∧ Module.finrank K R ≤ d) ↔
        ∃ (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
          (g : (Fin d → K) →ₗ[K] K),
          ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w
      := by
  intro K _ q f R d
  constructor
  · rintro ⟨hfin, hd⟩
    exact realize_of_rank f d hfin hd
  · rintro ⟨s, A, g, h⟩
    have := rank_of_realize f s A g h
    rw [Module.finrank_fin_fun] at this
    exact this

import PEqualNP.Defs

-- L-lib-550: the observation maps of both automata are injective with the same range, the Hankel row space,
-- so H is the composite of the two range isomorphisms. Any intertwiner preserving outputs commutes with the
-- observation maps, which fixes it by injectivity.

namespace PEqualNP.Outside.L_lib_550_aux

-- toolkit block copied from L_lib_548 (staged in ready/prep_L_lib_548.lean)
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


theorem hank_eq_map (s : V) (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) :
    hank (fun w : List (Fin q) => g (w.foldl (fun x a => A a x) s)) =
      (Submodule.span K (Set.range (fun w : List (Fin q) => w.foldl (fun x a => A a x) s))).map
        (obsMap A g) := by
  rw [Submodule.map_span, ← Set.range_comp]
  unfold hank
  congr 2
  funext u
  exact (obsMap_run A g s u).symm

theorem obsMap_injective (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K)
    (h : ∀ x : V, (∀ w : List (Fin q), g (w.foldl (fun y a => A a y) x) = 0) → x = 0) :
    Function.Injective (obsMap A g) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  apply h x
  intro w
  have := congr_fun (LinearMap.mem_ker.mp hx) w
  rwa [obsMap_apply] at this

theorem finrank_range_lt_of_ker [FiniteDimensional K V] (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K)
    (x : V) (hx : ∀ w : List (Fin q), g (w.foldl (fun y a => A a y) x) = 0) (hx0 : x ≠ 0) :
    Module.finrank K (LinearMap.range (obsMap A g)) < Module.finrank K V := by
  have hk : LinearMap.ker (obsMap A g) ≠ ⊥ := by
    intro hb
    apply hx0
    have hm : x ∈ LinearMap.ker (obsMap A g) := by
      rw [LinearMap.mem_ker]
      funext w
      rw [obsMap_apply]
      exact hx w
    rw [hb] at hm
    exact (Submodule.mem_bot K).mp hm
  have h1 := LinearMap.finrank_range_add_finrank_ker (obsMap A g)
  have h2 : 0 < Module.finrank K (LinearMap.ker (obsMap A g)) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hk (Submodule.finrank_eq_zero.mp h0)
  omega

theorem obsMap_nil (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) (x : V) : obsMap A g x [] = g x := by
  rw [obsMap_apply]
  rfl

theorem obsMap_letter (A : Fin q → V →ₗ[K] V) (g : V →ₗ[K] K) (a : Fin q) (x : V) :
    obsMap A g (A a x) = shiftL a (obsMap A g x) := by
  funext v
  rw [shiftL_apply, obsMap_apply, obsMap_apply]
  rfl

theorem obs_of_intertwine {W : Type} [AddCommGroup W] [Module K W] (A : Fin q → V →ₗ[K] V)
    (B : Fin q → W →ₗ[K] W) (f : V →ₗ[K] K) (g : W →ₗ[K] K) (H : V → W)
    (hg : ∀ x, g (H x) = f x) (hi : ∀ (a : Fin q) (x : V), H (A a x) = B a (H x)) :
    ∀ x, obsMap B g (H x) = obsMap A f x := by
  intro x
  funext v
  rw [obsMap_apply, obsMap_apply]
  induction v generalizing x with
  | nil => exact hg x
  | cons a v ih =>
    simp only [List.foldl_cons]
    rw [← hi]
    exact ih _

end HK

end PEqualNP.Outside.L_lib_550_aux

open PEqualNP.Outside.L_lib_550_aux in
theorem PEqualNP.Outside.L_lib_550 :
    ∀ (K : Type) [Field K] (q d e : ℕ),
      let V := Fin d → K
      let W := Fin e → K
      ∀ (s : V) (t : W) (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W)
        (f : V →ₗ[K] K) (g : W →ₗ[K] K),
        let X := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
        let Y := fun (w : List (Fin q)) => w.foldl (fun y a => B a y) t
        Submodule.span K (Set.range X) = ⊤ →
        Submodule.span K (Set.range Y) = ⊤ →
        (∀ x : V, (∀ w : List (Fin q), f (w.foldl (fun y a => A a y) x) = 0) → x = 0) →
        (∀ y : W, (∀ w : List (Fin q), g (w.foldl (fun x a => B a x) y) = 0) → y = 0) →
        (∀ w, f (X w) = g (Y w)) →
        ∃! H : V ≃ₗ[K] W, H s = t ∧ (∀ x, g (H x) = f x) ∧
          ∀ (a : Fin q) (x : V), H (A a x) = B a (H x)
      := by
  intro K _ q d e
  dsimp only
  intro s t A B f g hX hY hobsA hobsB hagree
  have iA := obsMap_injective A f hobsA
  have iB := obsMap_injective B g hobsB
  have rA : LinearMap.range (obsMap A f) = hank (fun w => f (w.foldl (fun x a => A a x) s)) := by
    rw [hank_eq_map, hX, Submodule.map_top]
  have rB : LinearMap.range (obsMap B g) = hank (fun w => g (w.foldl (fun x a => B a x) t)) := by
    rw [hank_eq_map, hY, Submodule.map_top]
  have hF : (fun w : List (Fin q) => f (w.foldl (fun x a => A a x) s)) = (fun w : List (Fin q) => g (w.foldl (fun x a => B a x) t)) :=
    funext hagree
  have hr : LinearMap.range (obsMap A f) = LinearMap.range (obsMap B g) := by
    rw [rA, rB, hF]
  let H : (Fin d → K) ≃ₗ[K] (Fin e → K) :=
    (LinearEquiv.ofInjective _ iA).trans
      ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective _ iB).symm)
  have hH : ∀ x, obsMap B g (H x) = obsMap A f x := by
    intro x
    have h1 := (LinearEquiv.ofInjective _ iB).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hr) ((LinearEquiv.ofInjective _ iA) x))
    have h2 := congrArg Subtype.val h1
    simp [H] at h2 ⊢
  refine ⟨H, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply iB
    rw [hH]
    funext v
    rw [obsMap_apply, obsMap_apply]
    exact hagree v
  · intro x
    rw [← obsMap_nil B g (H x), hH, obsMap_nil]
  · intro a x
    apply iB
    rw [hH, obsMap_letter B g, hH, obsMap_letter]
  · rintro H' ⟨-, hg', hi'⟩
    refine LinearEquiv.ext fun x => iB ?_
    rw [obs_of_intertwine A B f g H' hg' hi' x, hH]

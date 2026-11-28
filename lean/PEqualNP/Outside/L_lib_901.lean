import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_901_aux

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

private def diff {G : Type*} [AddCommGroup G] (f : G → ZMod 2) (a x : G) : ZMod 2 :=
  f (x + a) - f x

private def diff3 {G : Type*} [AddCommGroup G] (f : G → ZMod 2) (a b c : G) : ZMod 2 :=
  diff (diff (diff f a) b) c 0

private lemma diff_add {G : Type*} [AddCommGroup G] (f g : G → ZMod 2) (a x : G) :
    diff (fun z => f z + g z) a x = diff f a x + diff g a x := by
  simp only [diff]
  ring

private lemma diff_sum {G ι : Type*} [AddCommGroup G] (s : Finset ι)
    (F : ι → G → ZMod 2) (a x : G) :
    diff (fun z => ∑ i ∈ s, F i z) a x = ∑ i ∈ s, diff (F i) a x := by
  simp only [diff, Finset.sum_sub_distrib]

private lemma diff3_add {G : Type*} [AddCommGroup G] (f g : G → ZMod 2) (a b c : G) :
    diff3 (fun z => f z + g z) a b c = diff3 f a b c + diff3 g a b c := by
  have h1 : diff (fun z => f z + g z) a = fun z => diff f a z + diff g a z := by
    funext z; exact diff_add f g a z
  have h2 : diff (diff (fun z => f z + g z) a) b =
      fun z => diff (diff f a) b z + diff (diff g a) b z := by
    rw [h1]; funext z; exact diff_add _ _ b z
  rw [diff3, h2]
  exact diff_add _ _ c 0

private lemma diff3_sum {G ι : Type*} [AddCommGroup G] (s : Finset ι)
    (F : ι → G → ZMod 2) (a b c : G) :
    diff3 (fun z => ∑ i ∈ s, F i z) a b c = ∑ i ∈ s, diff3 (F i) a b c := by
  have h1 : diff (fun z => ∑ i ∈ s, F i z) a = fun z => ∑ i ∈ s, diff (F i) a z := by
    funext z; exact diff_sum s F a z
  have h2 : diff (diff (fun z => ∑ i ∈ s, F i z) a) b =
      fun z => ∑ i ∈ s, diff (diff (F i) a) b z := by
    rw [h1]; funext z; exact diff_sum s _ b z
  rw [diff3, h2]
  exact diff_sum s _ c 0

private lemma diff3_trilinear {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    (L₁ L₂ L₃ : G →ₗ[ZMod 2] ZMod 2) (a b c : G) :
    diff3 (fun z => L₁ z * L₂ z * L₃ z) a b c =
      L₁ a * (L₂ b * L₃ c + L₂ c * L₃ b) +
      L₁ b * (L₂ a * L₃ c + L₂ c * L₃ a) +
      L₁ c * (L₂ a * L₃ b + L₂ b * L₃ a) := by
  simp only [diff3, diff, map_add, map_zero, zero_add]
  ring

private lemma diff3_zero_left {G : Type*} [AddCommGroup G] (f : G → ZMod 2) (b c : G) :
    diff3 f 0 b c = 0 := by
  simp [diff3, diff]

private lemma diff3_zero_right {G : Type*} [AddCommGroup G] (f : G → ZMod 2) (a b : G) :
    diff3 f a b 0 = 0 := by
  simp [diff3, diff]

private def tsLin {k : ℕ} (h : (Fin k → ZMod 2) → ZMod 2)
    (hh : ∀ a b c d x, diff (diff (diff (diff h a) b) c) d x = 0)
    (s a : Fin k → ZMod 2) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun b => diff3 h s a b
  map_add' := by
    intro b₁ b₂
    set q := diff (diff h s) a
    have hconst : diff q b₂ b₁ = diff q b₂ 0 := by
      have h0 : diff q b₂ (0 + b₁) - diff q b₂ 0 = 0 := hh s a b₂ b₁ 0
      rw [zero_add, sub_eq_zero] at h0
      exact h0
    change diff q (b₁ + b₂) 0 = diff q b₁ 0 + diff q b₂ 0
    rw [← hconst]
    simp only [diff, zero_add]
    ring
  map_smul' := by
    intro c b
    rcases zmod2_cases c with rfl | rfl
    · simp [diff3_zero_right]
    · simp

private def dotLin {k : ℕ} (v : Fin k → ZMod 2) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun x => dotProduct v x
  map_add' := fun x y => dotProduct_add v x y
  map_smul' := fun c x => by simp [dotProduct_smul]

private def dotEquiv (k : ℕ) : (Fin k → ZMod 2) ≃ₗ[ZMod 2] ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) where
  toFun := dotLin
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro x
    exact add_dotProduct u v x
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro x
    simp [dotLin, smul_dotProduct]
  invFun := fun ℓ j => ℓ (Pi.single j 1)
  left_inv := by
    intro v; funext j; simp [dotLin]
  right_inv := by
    intro ℓ
    apply LinearMap.ext
    intro x
    change ∑ j : Fin k, ℓ (Pi.single j 1) * x j = ℓ x
    have hx : x = ∑ j : Fin k, x j • Pi.single j (1 : ZMod 2) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]

private def annSub {k : ℕ} (W : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Submodule (ZMod 2) ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
  { carrier := {ℓ | ∀ x ∈ W, ℓ x = 0}
    zero_mem' := by intro x _; rfl
    , add_mem' := by intro ℓ₁ ℓ₂ h1 h2 x hx; simp [h1 x hx, h2 x hx]
    smul_mem' := by intro c ℓ h1 x hx; simp [h1 x hx] }

private lemma finrank_ann {k : ℕ} (W : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Module.finrank (ZMod 2) (annSub W) = k - Module.finrank (ZMod 2) W := by
  let res : ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2] (↥W →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun ℓ => ℓ.comp W.subtype
      map_add' := fun ℓ₁ ℓ₂ => by apply LinearMap.ext; intro x; rfl
      map_smul' := fun c ℓ => by apply LinearMap.ext; intro x; rfl }
  have hker : LinearMap.ker res = annSub W := by
    ext ℓ
    simp only [LinearMap.mem_ker]
    constructor
    · intro h x hx
      exact LinearMap.congr_fun h ⟨x, hx⟩
    · intro h
      apply LinearMap.ext
      intro ⟨x, hx⟩
      exact h x hx
  have hsurj : Function.Surjective res := by
    intro f
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    let p : (Fin k → ZMod 2) →ₗ[ZMod 2] ↥W := W.projectionOnto W' hW'
    refine ⟨f.comp p, ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg f (Submodule.projectionOnto_apply_left hW' x)
  have hrange : LinearMap.range res = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker res
  rw [hrange, finrank_top, hker] at hrn
  have hdom : Module.finrank (ZMod 2) ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) = k := by
    rw [← (dotEquiv k).finrank_eq, Module.finrank_fin_fun]
  have hcod : Module.finrank (ZMod 2) (↥W →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) W := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  rw [hdom, hcod] at hrn
  omega

private lemma nat_card_subspace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (U : Submodule (ZMod 2) W) :
    Nat.card ↥U = 2 ^ Module.finrank (ZMod 2) U := by
  classical
  have : Fintype ↥U := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥U)
  rw [ZMod.card 2] at h
  exact h

private lemma tv_form_expand {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (h : (Fin k → ZMod 2) → ZMod 2)
    (s a b : Fin k → ZMod 2) (u v p q r t : Fin m → ZMod 2) :
    diff3 (fun x : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) =>
        h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i)
        (s, (u, v)) (a, (p, q)) (b, (r, t)) =
      diff3 h s a b +
      ∑ i : Fin m,
        (dotProduct (A i) s * (p i * t i + r i * q i) +
         dotProduct (A i) a * (u i * t i + r i * v i) +
         dotProduct (A i) b * (u i * q i + p i * v i)) := by
  let V := (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))
  have h1 : diff3 (fun x : V => h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i)
        (s, (u, v)) (a, (p, q)) (b, (r, t)) =
      diff3 (fun x : V => h x.1) (s, (u, v)) (a, (p, q)) (b, (r, t)) +
      ∑ i : Fin m, diff3 (fun x : V => dotProduct (A i) x.1 * x.2.1 i * x.2.2 i)
        (s, (u, v)) (a, (p, q)) (b, (r, t)) := by
    rw [diff3_add, diff3_sum]
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  let L₁ : V →ₗ[ZMod 2] ZMod 2 := (dotLin (A i)).comp (LinearMap.fst (ZMod 2) _ _)
  let L₂ : V →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj i).comp ((LinearMap.fst (ZMod 2) _ _).comp (LinearMap.snd (ZMod 2) _ _))
  let L₃ : V →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj i).comp ((LinearMap.snd (ZMod 2) _ _).comp (LinearMap.snd (ZMod 2) _ _))
  exact diff3_trilinear L₁ L₂ L₃ (s, (u, v)) (a, (p, q)) (b, (r, t))

private lemma main_proof (k m : ℕ) (A : Fin m → Fin k → ZMod 2)
    (h : (Fin k → ZMod 2) → ZMod 2)
    (hh : ∀ a b c d x, diff (diff (diff (diff h a) b) c) d x = 0)
    (w : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) :
    let F := ZMod 2
    let S := Fin k → F
    let D := Fin m → F
    let V := S × (D × D)
    let form := fun x : V => h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
    let wt := fun s : S => ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card
    let good := (∀ i, A i ≠ 0) ∧ (∀ s : S, s ≠ 0 → 2 ≤ wt s)
    let J := (Finset.univ : Finset (Fin m)).filter (fun i =>
      dotProduct (A i) w.1 = 0 ∧ (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0))
    let K := (Finset.univ : Finset S).filter (fun a => ∀ i ∈ J, dotProduct (A i) a = 0)
    let inner := (K.filter (fun a => ∀ b ∈ K, diff3 h w.1 a b = 0)).card
    let rad := ((Finset.univ : Finset V).filter (fun x => ∀ y, diff3 form w x y = 0)).card
    rad * 2 ^ k = 2 ^ (2 * (m - wt w.1)) * K.card * inner ∧
      (good → (4 * rad = Fintype.card V ↔ w.1 = 0 ∧
        ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧ ∀ j : Fin m,
          (w.2.1 j ≠ 0 ∨ w.2.2 j ≠ 0) → A j = A i)) := by
  classical
  rcases w with ⟨s, u, v⟩
  dsimp only
  let form : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) → ZMod 2 :=
    fun x => h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
  let I₁ : Finset (Fin m) := Finset.univ.filter (fun i => dotProduct (A i) s ≠ 0)
  let I₀ : Finset (Fin m) := Finset.univ.filter (fun i => dotProduct (A i) s = 0)
  let J : Finset (Fin m) := Finset.univ.filter (fun i =>
    dotProduct (A i) s = 0 ∧ (u i ≠ 0 ∨ v i ≠ 0))
  let K : Finset (Fin k → ZMod 2) := Finset.univ.filter (fun a => ∀ i ∈ J, dotProduct (A i) a = 0)
  let innerSet : Finset (Fin k → ZMod 2) := K.filter (fun a => ∀ b ∈ K, diff3 h s a b = 0)
  let radSet : Finset ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) :=
    Finset.univ.filter (fun x => ∀ y, diff3 form (s, (u, v)) x y = 0)
  have hI₀_card : I₀.card = m - I₁.card := by
    have hsum : I₁.card + I₀.card = (Finset.univ : Finset (Fin m)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext i
        simp only [I₁, I₀, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (ne_or_eq (dotProduct (A i) s) 0)
      · rw [Finset.disjoint_left]
        intro i hi1 hi0
        simp only [I₁, I₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi0
        exact hi1 hi0
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  let U : Submodule (ZMod 2) (Fin k → ZMod 2) := Submodule.span (ZMod 2) (Set.image A (J : Set (Fin m)))
  let Ksub : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    { carrier := {a | ∀ i ∈ J, dotProduct (A i) a = 0}
      zero_mem' := by intro i _; simp
      , add_mem' := by
        intro a b ha hb i hi
        rw [dotProduct_add, ha i hi, hb i hi, zero_add]
      smul_mem' := by
        intro c a ha i hi
        rw [dotProduct_smul, ha i hi, smul_zero] }
  have hK_mem : ∀ a : Fin k → ZMod 2, a ∈ K ↔ a ∈ Ksub := by
    intro a; simp [K, Ksub]
  have hKsub_eq_ann : Ksub = Submodule.comap (dotEquiv k).toLinearMap (annSub U) := by
    ext b
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe]
    constructor
    · intro hb x hx
      change dotProduct b x = 0
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, hi, rfl⟩
        rw [dotProduct_comm]
        exact hb i hi
      · simp
      · intro x1 x2 _ _ h1 h2
        rw [dotProduct_add, h1, h2, zero_add]
      · intro c x1 _ h1
        rw [dotProduct_smul, h1, smul_zero]
    · intro hb i hi
      rw [dotProduct_comm]
      exact hb (A i) (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hfinrank_Ksub : Module.finrank (ZMod 2) Ksub = k - Module.finrank (ZMod 2) U := by
    have h1 := finrank_ann U
    have heq : Module.finrank (ZMod 2) Ksub = Module.finrank (ZMod 2) (annSub U) := by
      rw [hKsub_eq_ann]
      let e : ↥(Submodule.comap (dotEquiv k).toLinearMap (annSub U)) ≃ₗ[ZMod 2] ↥(annSub U) :=
        { toFun := fun x => ⟨dotEquiv k x.1, x.2⟩
          map_add' := fun x y => Subtype.ext (map_add (dotEquiv k) x.1 y.1)
          map_smul' := fun c x => Subtype.ext (map_smul (dotEquiv k) c x.1)
          invFun := fun y => ⟨(dotEquiv k).symm y.1, by
            change dotEquiv k ((dotEquiv k).symm y.1) ∈ annSub U
            rw [(dotEquiv k).apply_symm_apply]
            exact y.2⟩
          left_inv := fun x => Subtype.ext ((dotEquiv k).symm_apply_apply x.1)
          right_inv := fun y => Subtype.ext ((dotEquiv k).apply_symm_apply y.1) }
      exact e.finrank_eq
    rw [heq, h1]
  have hfinrank_AnnK : Module.finrank (ZMod 2) (annSub Ksub) = Module.finrank (ZMod 2) U := by
    have h1 : Module.finrank (ZMod 2) (annSub Ksub) = k - Module.finrank (ZMod 2) Ksub := finrank_ann Ksub
    have hUle : Module.finrank (ZMod 2) U ≤ k := by
      have hle := Submodule.finrank_le U
      rw [Module.finrank_fin_fun] at hle
      exact hle
    rw [h1, hfinrank_Ksub]
    omega
  let Ψ : ({i : Fin m // i ∈ I₀} → ZMod 2 × ZMod 2) →ₗ[ZMod 2] ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun pq =>
        { toFun := fun b =>
            ∑ i : {i : Fin m // i ∈ I₀},
              dotProduct (A i.1) b * (u i.1 * (pq i).2 + (pq i).1 * v i.1)
          map_add' := by
            intro b₁ b₂
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [dotProduct_add]; ring
          map_smul' := by
            intro c b
            change (∑ i : {i : Fin m // i ∈ I₀},
                dotProduct (A i.1) (c • b) * (u i.1 * (pq i).2 + (pq i).1 * v i.1)) =
              c * ∑ i : {i : Fin m // i ∈ I₀},
                dotProduct (A i.1) b * (u i.1 * (pq i).2 + (pq i).1 * v i.1)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [dotProduct_smul, smul_eq_mul]
            ring }
      map_add' := by
        intro pq₁ pq₂
        apply LinearMap.ext
        intro b
        change ∑ i : {i : Fin m // i ∈ I₀},
            dotProduct (A i.1) b * (u i.1 * ((pq₁ i).2 + (pq₂ i).2) + ((pq₁ i).1 + (pq₂ i).1) * v i.1) =
          (∑ i : {i : Fin m // i ∈ I₀},
            dotProduct (A i.1) b * (u i.1 * (pq₁ i).2 + (pq₁ i).1 * v i.1)) +
          (∑ i : {i : Fin m // i ∈ I₀},
            dotProduct (A i.1) b * (u i.1 * (pq₂ i).2 + (pq₂ i).1 * v i.1))
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      map_smul' := by
        intro c pq
        apply LinearMap.ext
        intro b
        change ∑ i : {i : Fin m // i ∈ I₀},
            dotProduct (A i.1) b * (u i.1 * (c * (pq i).2) + (c * (pq i).1) * v i.1) =
          c * ∑ i : {i : Fin m // i ∈ I₀},
            dotProduct (A i.1) b * (u i.1 * (pq i).2 + (pq i).1 * v i.1)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring) }
  have hrange_le : LinearMap.range Ψ ≤ annSub Ksub := by
    rintro _ ⟨pq, rfl⟩ b hb
    change ∑ i : {i : Fin m // i ∈ I₀},
      dotProduct (A i.1) b * (u i.1 * (pq i).2 + (pq i).1 * v i.1) = 0
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hJ : i.1 ∈ J
    · rw [hb i.1 hJ, zero_mul]
    · have hi0 : dotProduct (A i.1) s = 0 := (Finset.mem_filter.mp i.2).2
      have huv0 : u i.1 = 0 ∧ v i.1 = 0 := by
        by_contra hne
        apply hJ
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, ?_⟩
        by_cases hu : u i.1 = 0
        · exact Or.inr (fun hv => hne ⟨hu, hv⟩)
        · exact Or.inl hu
      rw [huv0.1, huv0.2]
      ring
  have hspan_le : Submodule.map (dotEquiv k).toLinearMap U ≤ LinearMap.range Ψ := by
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, hiJ, rfl⟩
      have hiJ' := (Finset.mem_filter.mp hiJ).2
      have hi₀ : i ∈ I₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiJ'.1⟩
      rcases hiJ'.2 with hu | hv
      · have hu1 : u i = 1 := zmod2_eq_one_of_ne_zero hu
        let pq0 : {j : Fin m // j ∈ I₀} → ZMod 2 × ZMod 2 := Pi.single ⟨i, hi₀⟩ (0, 1)
        refine ⟨pq0, ?_⟩
        apply LinearMap.ext
        intro b
        change ∑ j : {j : Fin m // j ∈ I₀},
          dotProduct (A j.1) b * (u j.1 * (pq0 j).2 + (pq0 j).1 * v j.1) = dotProduct (A i) b
        rw [Finset.sum_eq_single ⟨i, hi₀⟩]
        · simp [pq0, hu1]
        · intro j _ hjne
          simp [pq0, Pi.single_eq_of_ne hjne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · have hv1 : v i = 1 := zmod2_eq_one_of_ne_zero hv
        let pq0 : {j : Fin m // j ∈ I₀} → ZMod 2 × ZMod 2 := Pi.single ⟨i, hi₀⟩ (1, 0)
        refine ⟨pq0, ?_⟩
        apply LinearMap.ext
        intro b
        change ∑ j : {j : Fin m // j ∈ I₀},
          dotProduct (A j.1) b * (u j.1 * (pq0 j).2 + (pq0 j).1 * v j.1) = dotProduct (A i) b
        rw [Finset.sum_eq_single ⟨i, hi₀⟩]
        · simp [pq0, hv1]
        · intro j _ hjne
          simp [pq0, Pi.single_eq_of_ne hjne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x1 x2 _ _ h1 h2
      rw [map_add]
      exact Submodule.add_mem _ h1 h2
    · intro c x1 _ h1
      rw [map_smul]
      exact Submodule.smul_mem _ c h1
  have hrange_eq : LinearMap.range Ψ = annSub Ksub := by
    apply Submodule.eq_of_le_of_finrank_eq hrange_le
    apply le_antisymm (Submodule.finrank_mono hrange_le)
    rw [hfinrank_AnnK]
    have hmap : Module.finrank (ZMod 2) (Submodule.map (dotEquiv k).toLinearMap U) =
        Module.finrank (ZMod 2) U :=
      (Submodule.equivMapOfInjective (dotEquiv k).toLinearMap (dotEquiv k).injective U).finrank_eq.symm
    rw [← hmap]
    exact Submodule.finrank_mono hspan_le
  have hrad_iff : ∀ (a : Fin k → ZMod 2) (p q : Fin m → ZMod 2),
      (a, (p, q)) ∈ radSet ↔
        a ∈ K ∧
        (∀ i ∈ I₁, p i = dotProduct (A i) a * u i ∧ q i = dotProduct (A i) a * v i) ∧
        Ψ (fun i => (p i.1, q i.1)) = tsLin h hh s a := by
    intro a p q
    simp only [radSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hall
      have h1 : ∀ i : Fin m, dotProduct (A i) s * q i + dotProduct (A i) a * v i = 0 := by
        intro i
        have hy := hall (0, (Pi.single i (1 : ZMod 2), 0))
        rw [tv_form_expand, diff3_zero_right, zero_add] at hy
        have hsum : (∑ j : Fin m,
            (dotProduct (A j) s * (p j * (0 : Fin m → ZMod 2) j + (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j * q j) +
             dotProduct (A j) a * (u j * (0 : Fin m → ZMod 2) j + (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j * v j) +
             dotProduct (A j) 0 * (u j * q j + p j * v j))) =
            dotProduct (A i) s * q i + dotProduct (A i) a * v i := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hjne
            simp [Pi.single_eq_of_ne hjne]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hsum] at hy
        exact hy
      have h2 : ∀ i : Fin m, dotProduct (A i) s * p i + dotProduct (A i) a * u i = 0 := by
        intro i
        have hy := hall (0, (0, Pi.single i (1 : ZMod 2)))
        rw [tv_form_expand, diff3_zero_right, zero_add] at hy
        have hsum : (∑ j : Fin m,
            (dotProduct (A j) s * (p j * (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j + (0 : Fin m → ZMod 2) j * q j) +
             dotProduct (A j) a * (u j * (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j + (0 : Fin m → ZMod 2) j * v j) +
             dotProduct (A j) 0 * (u j * q j + p j * v j))) =
            dotProduct (A i) s * p i + dotProduct (A i) a * u i := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hjne
            simp [Pi.single_eq_of_ne hjne]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hsum] at hy
        exact hy
      have haK : a ∈ K := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hiJ => ?_⟩
        have hiJ' := (Finset.mem_filter.mp hiJ).2
        have h1i := h1 i
        have h2i := h2 i
        rw [hiJ'.1, zero_mul, zero_add] at h1i h2i
        rcases hiJ'.2 with hu | hv
        · exact (mul_eq_zero.mp h2i).resolve_right hu
        · exact (mul_eq_zero.mp h1i).resolve_right hv
      have hI1 : ∀ i ∈ I₁, p i = dotProduct (A i) a * u i ∧ q i = dotProduct (A i) a * v i := by
        intro i hi1
        have hs1 : dotProduct (A i) s = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi1).2
        have h1i := h1 i
        have h2i := h2 i
        rw [hs1, one_mul] at h1i h2i
        constructor
        · have e : p i + (dotProduct (A i) a * u i) + (dotProduct (A i) a * u i) =
              0 + (dotProduct (A i) a * u i) := congrArg (· + dotProduct (A i) a * u i) h2i
          rw [add_assoc, zmod2_add_self, add_zero, zero_add] at e
          exact e
        · have e : q i + (dotProduct (A i) a * v i) + (dotProduct (A i) a * v i) =
              0 + (dotProduct (A i) a * v i) := congrArg (· + dotProduct (A i) a * v i) h1i
          rw [add_assoc, zmod2_add_self, add_zero, zero_add] at e
          exact e
      have hΨ : Ψ (fun i => (p i.1, q i.1)) = tsLin h hh s a := by
        apply LinearMap.ext
        intro b
        have hy := hall (b, (0, 0))
        rw [tv_form_expand] at hy
        have hsum_all : (∑ i : Fin m,
            (dotProduct (A i) s * (p i * (0 : Fin m → ZMod 2) i + (0 : Fin m → ZMod 2) i * q i) +
             dotProduct (A i) a * (u i * (0 : Fin m → ZMod 2) i + (0 : Fin m → ZMod 2) i * v i) +
             dotProduct (A i) b * (u i * q i + p i * v i))) =
            ∑ i : {i : Fin m // i ∈ I₀},
              dotProduct (A i.1) b * (u i.1 * q i.1 + p i.1 * v i.1) := by
          have hsimp : ∀ i : Fin m,
              dotProduct (A i) s * (p i * (0 : Fin m → ZMod 2) i + (0 : Fin m → ZMod 2) i * q i) +
              dotProduct (A i) a * (u i * (0 : Fin m → ZMod 2) i + (0 : Fin m → ZMod 2) i * v i) +
              dotProduct (A i) b * (u i * q i + p i * v i) =
              dotProduct (A i) b * (u i * q i + p i * v i) := fun i => by simp
          simp_rw [hsimp]
          rw [Finset.sum_coe_sort I₀ (fun i => dotProduct (A i) b * (u i * q i + p i * v i))]
          symm
          refine Finset.sum_subset (Finset.subset_univ I₀) (fun i _ hi0 => ?_)
          have hi1 : i ∈ I₁ := by
            simp only [I₀, I₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi0 ⊢
            exact hi0
          obtain ⟨hp, hq⟩ := hI1 i hi1
          rw [hp, hq]
          have hc : u i * (dotProduct (A i) a * v i) + dotProduct (A i) a * u i * v i =
              (dotProduct (A i) a * u i * v i) + (dotProduct (A i) a * u i * v i) := by ring
          rw [hc, zmod2_add_self, mul_zero]
        rw [hsum_all] at hy
        change (∑ i : {i : Fin m // i ∈ I₀},
          dotProduct (A i.1) b * (u i.1 * q i.1 + p i.1 * v i.1)) = diff3 h s a b
        have e := congrArg (diff3 h s a b + ·) hy
        rw [← add_assoc, zmod2_add_self, zero_add, add_zero] at e
        exact e
      exact ⟨haK, hI1, hΨ⟩
    · rintro ⟨haK, hI1, hΨ⟩ ⟨b, r, t⟩
      rw [tv_form_expand]
      have h1 : ∀ i : Fin m, dotProduct (A i) s * q i + dotProduct (A i) a * v i = 0 := by
        intro i
        by_cases hs0 : dotProduct (A i) s = 0
        · rw [hs0, zero_mul, zero_add]
          by_cases hv0 : v i = 0
          · rw [hv0, mul_zero]
          · have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0, Or.inr hv0⟩
            rw [(Finset.mem_filter.mp haK).2 i hiJ, zero_mul]
        · have hi1 : i ∈ I₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0⟩
          rw [zmod2_eq_one_of_ne_zero hs0, one_mul, (hI1 i hi1).2, zmod2_add_self]
      have h2 : ∀ i : Fin m, dotProduct (A i) s * p i + dotProduct (A i) a * u i = 0 := by
        intro i
        by_cases hs0 : dotProduct (A i) s = 0
        · rw [hs0, zero_mul, zero_add]
          by_cases hu0 : u i = 0
          · rw [hu0, mul_zero]
          · have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0, Or.inl hu0⟩
            rw [(Finset.mem_filter.mp haK).2 i hiJ, zero_mul]
        · have hi1 : i ∈ I₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0⟩
          rw [zmod2_eq_one_of_ne_zero hs0, one_mul, (hI1 i hi1).1, zmod2_add_self]
      have h3 : (∑ i : Fin m, dotProduct (A i) b * (u i * q i + p i * v i)) = diff3 h s a b := by
        have hb := LinearMap.congr_fun hΨ b
        change (∑ i : Fin m, dotProduct (A i) b * (u i * q i + p i * v i)) = (tsLin h hh s a) b
        rw [← hb]
        change (∑ i : Fin m, dotProduct (A i) b * (u i * q i + p i * v i)) =
          ∑ i : {i : Fin m // i ∈ I₀}, dotProduct (A i.1) b * (u i.1 * q i.1 + p i.1 * v i.1)
        rw [Finset.sum_coe_sort I₀ (fun i => dotProduct (A i) b * (u i * q i + p i * v i))]
        symm
        refine Finset.sum_subset (Finset.subset_univ I₀) (fun i _ hi0 => ?_)
        have hi1 : i ∈ I₁ := by
          simp only [I₀, I₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi0 ⊢
          exact hi0
        obtain ⟨hp, hq⟩ := hI1 i hi1
        rw [hp, hq]
        have hc : u i * (dotProduct (A i) a * v i) + dotProduct (A i) a * u i * v i =
            (dotProduct (A i) a * u i * v i) + (dotProduct (A i) a * u i * v i) := by ring
        rw [hc, zmod2_add_self, mul_zero]
      have hrearr : (∑ i : Fin m,
          (dotProduct (A i) s * (p i * t i + r i * q i) +
           dotProduct (A i) a * (u i * t i + r i * v i) +
           dotProduct (A i) b * (u i * q i + p i * v i))) =
          (∑ i : Fin m, ((dotProduct (A i) s * q i + dotProduct (A i) a * v i) * r i +
            (dotProduct (A i) s * p i + dotProduct (A i) a * u i) * t i)) +
          (∑ i : Fin m, dotProduct (A i) b * (u i * q i + p i * v i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hrearr]
      have hz : (∑ i : Fin m, ((dotProduct (A i) s * q i + dotProduct (A i) a * v i) * r i +
          (dotProduct (A i) s * p i + dotProduct (A i) a * u i) * t i)) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [h1 i, h2 i]; ring
      rw [hz, zero_add, h3, zmod2_add_self]
  have hfiber_card : ∀ a : Fin k → ZMod 2,
      ((Finset.univ : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2))).filter
        (fun pq => (a, pq) ∈ radSet)).card =
        if a ∈ innerSet then 2 ^ Module.finrank (ZMod 2) (LinearMap.ker Ψ) else 0 := by
    intro a
    by_cases ha : a ∈ innerSet
    · simp only [ha, ↓reduceIte]
      have haK : a ∈ K := (Finset.mem_filter.mp ha).1
      have haAnn : tsLin h hh s a ∈ annSub Ksub := by
        intro b hb
        exact (Finset.mem_filter.mp ha).2 b ((hK_mem b).mpr hb)
      rw [← hrange_eq] at haAnn
      rcases haAnn with ⟨pq₁, hpq₁⟩
      let e : {pq : (Fin m → ZMod 2) × (Fin m → ZMod 2) // (a, pq) ∈ radSet} ≃
          ↥(LinearMap.ker Ψ) :=
        { toFun := fun x =>
            ⟨(fun i => (x.1.1 i.1, x.1.2 i.1)) - pq₁, by
              rw [LinearMap.mem_ker, map_sub, ((hrad_iff a x.1.1 x.1.2).mp x.2).2.2, hpq₁, sub_self]⟩
          invFun := fun z =>
            ⟨(fun i => if hi0 : i ∈ I₀ then (z.1 ⟨i, hi0⟩ + pq₁ ⟨i, hi0⟩).1 else dotProduct (A i) a * u i,
              fun i => if hi0 : i ∈ I₀ then (z.1 ⟨i, hi0⟩ + pq₁ ⟨i, hi0⟩).2 else dotProduct (A i) a * v i),
             by
              rw [hrad_iff]
              refine ⟨haK, ?_, ?_⟩
              · intro i hi1
                have hnot : i ∉ I₀ := by
                  simp only [I₁, I₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 ⊢
                  exact hi1
                simp [hnot]
              · have hfun : (fun i : {i : Fin m // i ∈ I₀} =>
                    ((if hi0 : i.1 ∈ I₀ then (z.1 ⟨i.1, hi0⟩ + pq₁ ⟨i.1, hi0⟩).1 else dotProduct (A i.1) a * u i.1),
                     (if hi0 : i.1 ∈ I₀ then (z.1 ⟨i.1, hi0⟩ + pq₁ ⟨i.1, hi0⟩).2 else dotProduct (A i.1) a * v i.1))) =
                    z.1 + pq₁ := by
                  funext i
                  simp only [i.2, ↓reduceDIte, Pi.add_apply]
                rw [hfun, map_add, LinearMap.mem_ker.mp z.2, zero_add, hpq₁]⟩
          left_inv := by
            intro x
            ext i
            · by_cases hi0 : i ∈ I₀
              · simp [hi0]
              · have hi1 : i ∈ I₁ := by
                  simp only [I₀, I₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi0 ⊢
                  exact hi0
                simp only [hi0, ↓reduceDIte]
                exact (((hrad_iff a x.1.1 x.1.2).mp x.2).2.1 i hi1).1.symm
            · by_cases hi0 : i ∈ I₀
              · simp [hi0]
              · have hi1 : i ∈ I₁ := by
                  simp only [I₀, I₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi0 ⊢
                  exact hi0
                simp only [hi0, ↓reduceDIte]
                exact (((hrad_iff a x.1.1 x.1.2).mp x.2).2.1 i hi1).2.symm
          right_inv := by
            intro z
            apply Subtype.ext
            funext i
            ext <;> simp }
      have hcard1 : ((Finset.univ : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2))).filter
          (fun pq => (a, pq) ∈ radSet)).card =
          Nat.card {pq : (Fin m → ZMod 2) × (Fin m → ZMod 2) // (a, pq) ∈ radSet} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hcard1, Nat.card_congr e, nat_card_subspace]
    · simp only [ha, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pq _ hmem
      have hx := (hrad_iff a pq.1 pq.2).mp hmem
      apply ha
      refine Finset.mem_filter.mpr ⟨hx.1, fun b hbK => ?_⟩
      have hmemR : tsLin h hh s a ∈ annSub Ksub := by
        rw [← hrange_eq]
        exact ⟨_, hx.2.2⟩
      exact hmemR b ((hK_mem b).mp hbK)
  have hrad_eq : radSet.card = innerSet.card * 2 ^ Module.finrank (ZMod 2) (LinearMap.ker Ψ) := by
    have hsplit : radSet.card =
        ∑ a : Fin k → ZMod 2,
          ((Finset.univ : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2))).filter
            (fun pq => (a, pq) ∈ radSet)).card := by
      have hprod : radSet =
          ((Finset.univ : Finset (Fin k → ZMod 2)) ×ˢ
            (Finset.univ : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2)))).filter
            (fun x => x ∈ radSet) := by
        ext x; simp
      conv_lhs => rw [hprod]
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.card_filter]
    rw [hsplit]
    simp_rw [hfiber_card]
    simp
  have hK_card : K.card = 2 ^ Module.finrank (ZMod 2) Ksub := by
    have : Fintype ↥Ksub := Fintype.ofFinite _
    have h1 : K.card = Nat.card ↥Ksub := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext a
      simp [K, Ksub]
    rw [h1, nat_card_subspace]
  have hdom_Ψ : Module.finrank (ZMod 2) ({i : Fin m // i ∈ I₀} → ZMod 2 × ZMod 2) =
      2 * (m - I₁.card) := by
    rw [Module.finrank_pi_fintype]
    have hf : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by
      rw [Module.finrank_prod, Module.finrank_self]
    simp only [hf, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm,
      hI₀_card]
  have hrn_Ψ := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hrange_eq, hfinrank_AnnK, hdom_Ψ] at hrn_Ψ
  have hU_plus_K : Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) Ksub = k := by
    have hUle : Module.finrank (ZMod 2) U ≤ k := by
      have hle := Submodule.finrank_le U
      rw [Module.finrank_fin_fun] at hle
      exact hle
    rw [hfinrank_Ksub]
    omega
  have hexp : Module.finrank (ZMod 2) (LinearMap.ker Ψ) + k =
      2 * (m - I₁.card) + Module.finrank (ZMod 2) Ksub := by
    omega
  have hpart1 : radSet.card * 2 ^ k = 2 ^ (2 * (m - I₁.card)) * K.card * innerSet.card := by
    rw [hrad_eq, hK_card]
    calc innerSet.card * 2 ^ Module.finrank (ZMod 2) (LinearMap.ker Ψ) * 2 ^ k
        = innerSet.card * (2 ^ Module.finrank (ZMod 2) (LinearMap.ker Ψ) * 2 ^ k) := by ring
      _ = innerSet.card * 2 ^ (Module.finrank (ZMod 2) (LinearMap.ker Ψ) + k) := by rw [pow_add]
      _ = innerSet.card * 2 ^ (2 * (m - I₁.card) + Module.finrank (ZMod 2) Ksub) := by rw [hexp]
      _ = innerSet.card * (2 ^ (2 * (m - I₁.card)) * 2 ^ Module.finrank (ZMod 2) Ksub) := by rw [pow_add]
      _ = 2 ^ (2 * (m - I₁.card)) * 2 ^ Module.finrank (ZMod 2) Ksub * innerSet.card := by ring
  refine ⟨hpart1, ?_⟩
  intro hgood
  have hcardV : Fintype.card ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) =
      2 ^ k * 2 ^ (2 * m) := by
    simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card 2,
      Finset.prod_const, Finset.card_univ]
    rw [← pow_add, two_mul]
  have hI1_le : I₁.card ≤ m := by
    calc I₁.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
      _ = m := by simp
  have h4rad_iff : 4 * radSet.card =
        Fintype.card ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) ↔
      4 * K.card * innerSet.card = 2 ^ (2 * I₁.card) * 2 ^ k * 2 ^ k := by
    have hposk : 0 < 2 ^ k := by positivity
    have hposm : 0 < 2 ^ (2 * (m - I₁.card)) := by positivity
    have hpowm : 2 ^ (2 * m) = 2 ^ (2 * (m - I₁.card)) * 2 ^ (2 * I₁.card) := by
      rw [← pow_add]
      congr 1
      omega
    constructor
    · intro h4
      have hmul : 4 * (radSet.card * 2 ^ k) =
          Fintype.card ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) * 2 ^ k := by
        calc 4 * (radSet.card * 2 ^ k) = (4 * radSet.card) * 2 ^ k := by ring
          _ = _ := by rw [h4]
      rw [hpart1, hcardV, hpowm] at hmul
      have hmul' : 2 ^ (2 * (m - I₁.card)) * (4 * K.card * innerSet.card) =
          2 ^ (2 * (m - I₁.card)) * (2 ^ (2 * I₁.card) * 2 ^ k * 2 ^ k) := by
        linarith
      exact Nat.eq_of_mul_eq_mul_left hposm hmul'
    · intro h4
      have hmul : (4 * radSet.card) * 2 ^ k =
          Fintype.card ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) * 2 ^ k := by
        calc (4 * radSet.card) * 2 ^ k = 4 * (radSet.card * 2 ^ k) := by ring
          _ = 4 * (2 ^ (2 * (m - I₁.card)) * K.card * innerSet.card) := by rw [hpart1]
          _ = 2 ^ (2 * (m - I₁.card)) * (4 * K.card * innerSet.card) := by ring
          _ = 2 ^ (2 * (m - I₁.card)) * (2 ^ (2 * I₁.card) * 2 ^ k * 2 ^ k) := by rw [h4]
          _ = 2 ^ k * (2 ^ (2 * (m - I₁.card)) * 2 ^ (2 * I₁.card)) * 2 ^ k := by ring
          _ = 2 ^ k * 2 ^ (2 * m) * 2 ^ k := by rw [← hpowm]
          _ = _ := by rw [hcardV]
      exact Nat.eq_of_mul_eq_mul_right hposk hmul
  rw [h4rad_iff]
  constructor
  · intro h4
    have hK_le : K.card ≤ 2 ^ k := by
      calc K.card ≤ (Finset.univ : Finset (Fin k → ZMod 2)).card := Finset.card_le_univ _
        _ = 2 ^ k := by simp [ZMod.card 2]
    have hinner_le : innerSet.card ≤ K.card := Finset.card_filter_le _ _
    have hs0 : s = 0 := by
      by_contra hsne
      have hwt2 : 2 ≤ I₁.card := hgood.2 s hsne
      have hpow16 : 16 ≤ 2 ^ (2 * I₁.card) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * I₁.card) := Nat.pow_le_pow_right (by omega) (by omega)
      have hpos : 0 < 2 ^ k * 2 ^ k := by positivity
      have hprod_le : K.card * innerSet.card ≤ 2 ^ k * 2 ^ k :=
        Nat.mul_le_mul hK_le (le_trans hinner_le hK_le)
      have h1 : 4 * (K.card * innerSet.card) ≤ 4 * (2 ^ k * 2 ^ k) :=
        Nat.mul_le_mul_left 4 hprod_le
      have h2 : 4 * (2 ^ k * 2 ^ k) < 16 * (2 ^ k * 2 ^ k) := by omega
      have h3 : 16 * (2 ^ k * 2 ^ k) ≤ 2 ^ (2 * I₁.card) * (2 ^ k * 2 ^ k) :=
        Nat.mul_le_mul_right _ hpow16
      have h4' : 4 * (K.card * innerSet.card) = 2 ^ (2 * I₁.card) * (2 ^ k * 2 ^ k) := by
        calc 4 * (K.card * innerSet.card) = 4 * K.card * innerSet.card := by ring
          _ = 2 ^ (2 * I₁.card) * 2 ^ k * 2 ^ k := h4
          _ = 2 ^ (2 * I₁.card) * (2 ^ k * 2 ^ k) := by ring
      omega
    have hI1_0 : I₁.card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; simp [hs0]
    have hinner_eq : innerSet.card = K.card := by
      congr 1
      ext a
      simp only [innerSet, Finset.mem_filter, and_iff_left_iff_imp]
      intro _ b _
      rw [hs0]
      exact diff3_zero_left h a b
    rw [hI1_0, hinner_eq, mul_zero, pow_zero, one_mul] at h4
    have h2K : 2 * K.card = 2 ^ k := by
      have hsq : (2 * K.card) ^ 2 = (2 ^ k) ^ 2 := by
        calc (2 * K.card) ^ 2 = 4 * K.card * K.card := by ring
          _ = 2 ^ k * 2 ^ k := h4
          _ = (2 ^ k) ^ 2 := by ring
      exact Nat.pow_left_injective (by omega : 2 ≠ 0) hsq
    have hU1 : Module.finrank (ZMod 2) U = 1 := by
      rw [hK_card] at h2K
      have hpow : 2 ^ (Module.finrank (ZMod 2) Ksub + 1) = 2 ^ k := by
        rw [pow_succ, mul_comm]; exact h2K
      have heq : Module.finrank (ZMod 2) Ksub + 1 = k :=
        Nat.pow_right_injective (by omega : 2 ≤ 2) hpow
      omega
    have hJ_nonempty : J.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hU0 : U = ⊥ := by simp [U, hempty]
      rw [hU0, finrank_bot] at hU1
      omega
    rcases hJ_nonempty with ⟨i, hiJ⟩
    have hiJ' := (Finset.mem_filter.mp hiJ).2
    refine ⟨hs0, i, hiJ'.2, fun j hj => ?_⟩
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hs0], hj⟩
    have hAi_in : A i ∈ U := Submodule.subset_span ⟨i, hiJ, rfl⟩
    have hAj_in : A j ∈ U := Submodule.subset_span ⟨j, hjJ, rfl⟩
    have hUeq : Submodule.span (ZMod 2) ({A i} : Set (Fin k → ZMod 2)) = U := by
      apply Submodule.eq_of_le_of_finrank_eq
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hAi_in)
      · rw [finrank_span_singleton (hgood.1 i), hU1]
    rw [← hUeq] at hAj_in
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hAj_in
    rcases zmod2_cases c with rfl | rfl
    · simp only [zero_smul] at hc
      exact absurd hc.symm (hgood.1 j)
    · simp only [one_smul] at hc
      exact hc.symm
  · rintro ⟨hs0, i, hi_occ, hall_eq⟩
    have hI1_0 : I₁.card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _; simp [hs0]
    have hinner_eq : innerSet.card = K.card := by
      congr 1
      ext a
      simp only [innerSet, Finset.mem_filter, and_iff_left_iff_imp]
      intro _ b _
      rw [hs0]
      exact diff3_zero_left h a b
    have himg : Set.image A (J : Set (Fin m)) = {A i} := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, hjJ, rfl⟩
        exact hall_eq j (Finset.mem_filter.mp hjJ).2.2
      · rintro rfl
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hs0], hi_occ⟩, rfl⟩
    have hUeq : U = Submodule.span (ZMod 2) {A i} := by
      dsimp only [U]
      rw [himg]
    have hU1 : Module.finrank (ZMod 2) U = 1 := by
      rw [hUeq]
      exact finrank_span_singleton (hgood.1 i)
    have h2K : 2 * K.card = 2 ^ k := by
      rw [hK_card]
      calc 2 * 2 ^ Module.finrank (ZMod 2) Ksub
          = 2 ^ (Module.finrank (ZMod 2) Ksub + 1) := by rw [pow_succ, mul_comm]
        _ = 2 ^ k := by congr 1; omega
    rw [hI1_0, hinner_eq, mul_zero, pow_zero, one_mul]
    calc 4 * K.card * K.card = (2 * K.card) * (2 * K.card) := by ring
      _ = 2 ^ k * 2 ^ k := by rw [h2K]

end PEqualNP.Outside.L_lib_901_aux

theorem PEqualNP.Outside.L_lib_901 :
  ∀ k m : ℕ,
    let F := ZMod 2
    let S := Fin k → F
    let D := Fin m → F
    let V := S × (D × D)
    let diffS := fun (f : S → F) (a x : S) => f (x+a) - f x
    let cubic := fun (h : S → F) => ∀ a b c d x, diffS (diffS (diffS (diffS h a) b) c) d x = 0
    let ts := fun (h : S → F) (a b c : S) => diffS (diffS (diffS h a) b) c 0
    let diffV := fun (f : V → F) (a x : V) => f (x+a) - f x
    let tv := fun (f : V → F) (a b c : V) => diffV (diffV (diffV f a) b) c 0
    let form := fun (A : Fin m → S) (h : S → F) (x : V) =>
      h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
    let wt := fun (A : Fin m → S) (s : S) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card
    let good := fun (A : Fin m → S) => (∀ i, A i ≠ 0) ∧ (∀ s : S, s ≠ 0 → 2 ≤ wt A s)
    ∀ (A : Fin m → S) (h : S → F), cubic h → ∀ w : V,
      let J := (Finset.univ : Finset (Fin m)).filter (fun i =>
        dotProduct (A i) w.1 = 0 ∧ (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0))
      let K := (Finset.univ : Finset S).filter (fun a => ∀ i ∈ J, dotProduct (A i) a = 0)
      let inner := (K.filter (fun a => ∀ b ∈ K, ts h w.1 a b = 0)).card
      let rad := ((Finset.univ : Finset V).filter (fun x => ∀ y, tv (form A h) w x y = 0)).card
      rad * 2^k = 2^(2*(m-wt A w.1)) * K.card * inner ∧
        (good A → (4*rad = Fintype.card V ↔ w.1 = 0 ∧
          ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧ ∀ j : Fin m,
            (w.2.1 j ≠ 0 ∨ w.2.2 j ≠ 0) → A j = A i)) := by
  intro k m
  dsimp only
  intro A h hh w
  exact PEqualNP.Outside.L_lib_901_aux.main_proof k m A h hh w

import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_902_aux

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

private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have e := congrArg (· + b) h
  rw [add_assoc, zmod2_add_self, add_zero, zero_add] at e
  exact e

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

private lemma rank_two_char {k m : ℕ} (A : Fin m → Fin k → ZMod 2)
    (h : (Fin k → ZMod 2) → ZMod 2)
    (hgood : (∀ i, A i ≠ 0) ∧
      ∀ s : Fin k → ZMod 2, s ≠ 0 →
        2 ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card)
    (hh : ∀ a b c d x, diff (diff (diff (diff h a) b) c) d x = 0)
    (w : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) :
    let V := (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))
    let form := fun x : V => h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
    let rad := ((Finset.univ : Finset V).filter (fun x => ∀ y, diff3 form w x y = 0)).card
    4 * rad = Fintype.card V ↔ w.1 = 0 ∧
      ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧ ∀ j : Fin m,
        (w.2.1 j ≠ 0 ∨ w.2.2 j ≠ 0) → A j = A i := by
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
        exact ⟨zmod2_eq_of_add_eq_zero h2i, zmod2_eq_of_add_eq_zero h1i⟩
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
        exact (zmod2_eq_of_add_eq_zero hy).symm
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

private def classSub {k m : ℕ} (C : Fin m → Fin k → ZMod 2) (α : Fin k → ZMod 2) :
    Submodule (ZMod 2) ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) :=
  { carrier := {w | w.1 = 0 ∧ ∀ r : Fin m, (w.2.1 r ≠ 0 ∨ w.2.2 r ≠ 0) → C r = α}
    zero_mem' := by
      refine ⟨rfl, fun r hr => ?_⟩
      simp at hr
    , add_mem' := by
      intro x y hx hy
      refine ⟨by simp [hx.1, hy.1], fun r hr => ?_⟩
      by_cases hx0 : x.2.1 r = 0 ∧ x.2.2 r = 0
      · apply hy.2 r
        rcases hr with h1 | h2
        · left; intro hy1; apply h1; change x.2.1 r + y.2.1 r = 0; rw [hx0.1, hy1, zero_add]
        · right; intro hy2; apply h2; change x.2.2 r + y.2.2 r = 0; rw [hx0.2, hy2, zero_add]
      · apply hx.2 r
        by_cases h1 : x.2.1 r = 0
        · exact Or.inr (fun h2 => hx0 ⟨h1, h2⟩)
        · exact Or.inl h1
    smul_mem' := by
      intro c x hx
      rcases zmod2_cases c with rfl | rfl
      · simp only [zero_smul]
        exact ⟨rfl, fun r hr => by simp at hr⟩
      · simpa only [one_smul] using hx }

private lemma finrank_classSub {k m : ℕ} (C : Fin m → Fin k → ZMod 2) (α : Fin k → ZMod 2) :
    Module.finrank (ZMod 2) (classSub C α) =
      2 * ((Finset.univ : Finset (Fin m)).filter (fun r => C r = α)).card := by
  classical
  let S := (Finset.univ : Finset (Fin m)).filter (fun r => C r = α)
  let e : ↥(classSub C α) ≃ₗ[ZMod 2] ({r : Fin m // r ∈ S} → ZMod 2 × ZMod 2) :=
    { toFun := fun w r => (w.1.2.1 r.1, w.1.2.2 r.1)
      map_add' := fun x y => by funext r; rfl
      map_smul' := fun c x => by funext r; rfl
      invFun := fun f =>
        ⟨(0, (fun r => if hr : r ∈ S then (f ⟨r, hr⟩).1 else 0,
              fun r => if hr : r ∈ S then (f ⟨r, hr⟩).2 else 0)),
         by
          refine ⟨rfl, fun r hr => ?_⟩
          by_cases hmem : r ∈ S
          · exact (Finset.mem_filter.mp hmem).2
          · simp [hmem] at hr⟩
      left_inv := by
        intro ⟨⟨s, u, v⟩, hw⟩
        apply Subtype.ext
        rcases hw with ⟨hs, hC⟩
        refine Prod.ext hs.symm (Prod.ext ?_ ?_)
        · funext r
          by_cases hr : r ∈ S
          · simp [hr]
          · simp only [hr, ↓reduceDIte]
            by_contra hu
            apply hr
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC r (Or.inl (Ne.symm hu))⟩
        · funext r
          by_cases hr : r ∈ S
          · simp [hr]
          · simp only [hr, ↓reduceDIte]
            by_contra hv
            apply hr
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC r (Or.inr (Ne.symm hv))⟩
      right_inv := by
        intro f
        funext r
        ext <;> simp [r.2] }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  have hf : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  simp only [hf, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]
  rfl

private lemma exists_dot_one {k : ℕ} {v : Fin k → ZMod 2} (hv : v ≠ 0) :
    ∃ s : Fin k → ZMod 2, dotProduct v s = 1 := by
  have hne : ∃ i : Fin k, v i ≠ 0 := by
    by_contra hall
    apply hv
    funext i
    by_contra hi
    exact hall ⟨i, hi⟩
  rcases hne with ⟨i, hi⟩
  refine ⟨Pi.single i 1, ?_⟩
  simp [zmod2_eq_one_of_ne_zero hi]

private lemma main_proof (k m : ℕ) (A B : Fin m → Fin k → ZMod 2)
    (h j : (Fin k → ZMod 2) → ZMod 2)
    (hgA : (∀ i, A i ≠ 0) ∧
      ∀ s : Fin k → ZMod 2, s ≠ 0 →
        2 ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card)
    (hgB : (∀ i, B i ≠ 0) ∧
      ∀ s : Fin k → ZMod 2, s ≠ 0 →
        2 ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (B i) s ≠ 0)).card)
    (hh : ∀ a b c d x, diff (diff (diff (diff h a) b) c) d x = 0)
    (hj : ∀ a b c d x, diff (diff (diff (diff j a) b) c) d x = 0) :
    let F := ZMod 2
    let S := Fin k → F
    let D := Fin m → F
    let V := S × (D × D)
    let formA := fun x : V => h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
    let formB := fun x : V => j x.1 + ∑ i : Fin m, dotProduct (B i) x.1 * x.2.1 i * x.2.2 i
    (∃ e : V ≃ₗ[F] V, ∀ u v w : V, diff3 formA u v w = diff3 formB (e u) (e v) (e w)) ↔
      ∃ (l : S ≃ₗ[F] S) (p : Equiv.Perm (Fin m)),
        (∀ i s, dotProduct (A i) s = dotProduct (B (p i)) (l s)) ∧
        (∀ a b c : S, diff3 h a b c = diff3 j (l a) (l b) (l c)) := by
  classical
  dsimp only
  let formA : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) → ZMod 2 :=
    fun x => h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
  let formB : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) → ZMod 2 :=
    fun x => j x.1 + ∑ i : Fin m, dotProduct (B i) x.1 * x.2.1 i * x.2.2 i
  constructor
  · rintro ⟨e, he⟩
    let R2A : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) → Prop := fun w =>
      w.1 = 0 ∧ ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧
        ∀ r : Fin m, (w.2.1 r ≠ 0 ∨ w.2.2 r ≠ 0) → A r = A i
    let R2B : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) → Prop := fun w =>
      w.1 = 0 ∧ ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧
        ∀ r : Fin m, (w.2.1 r ≠ 0 ∨ w.2.2 r ≠ 0) → B r = B i
    have he_R2 : ∀ w, R2A w ↔ R2B (e w) := by
      intro w
      have hA := rank_two_char A h hgA hh w
      have hB := rank_two_char B j hgB hj (e w)
      dsimp only at hA hB
      change (w.1 = 0 ∧ ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧
          ∀ r : Fin m, (w.2.1 r ≠ 0 ∨ w.2.2 r ≠ 0) → A r = A i) ↔
        ((e w).1 = 0 ∧ ∃ i : Fin m, ((e w).2.1 i ≠ 0 ∨ (e w).2.2 i ≠ 0) ∧
          ∀ r : Fin m, ((e w).2.1 r ≠ 0 ∨ (e w).2.2 r ≠ 0) → B r = B i)
      rw [← hA, ← hB]
      have hcard :
          ((Finset.univ : Finset ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)))).filter
            (fun x => ∀ y, diff3 formA w x y = 0)).card =
          ((Finset.univ : Finset ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)))).filter
            (fun x => ∀ y, diff3 formB (e w) x y = 0)).card := by
        refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          intro y
          have hy := hx (e.symm y)
          rw [he w x (e.symm y), e.apply_symm_apply] at hy
          exact hy
        · intro x₁ _ x₂ _ hxy
          exact e.injective hxy
        · intro x' hx'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
          refine ⟨e.symm x', ?_, e.apply_symm_apply x'⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro y
          rw [he w (e.symm x') y, e.apply_symm_apply]
          exact hx' (e y)
      rw [hcard]
    have hclass_iff : ∀ (C : Fin m → Fin k → ZMod 2) (α : Fin k → ZMod 2)
        (d₀ : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))),
        let R2C := fun w : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) =>
          w.1 = 0 ∧ ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧
            ∀ r : Fin m, (w.2.1 r ≠ 0 ∨ w.2.2 r ≠ 0) → C r = C i
        (d₀ ∈ classSub C α ∧ d₀ ≠ 0) →
        ∀ w, w ∈ classSub C α ↔ w = 0 ∨ (R2C w ∧ (w = d₀ ∨ R2C (w + d₀))) := by
      intro C α d₀ R2C ⟨hd0_mem, hd0_ne⟩ w
      have hd0_occ : ∃ i₀ : Fin m, d₀.2.1 i₀ ≠ 0 ∨ d₀.2.2 i₀ ≠ 0 := by
        by_contra hall
        apply hd0_ne
        refine Prod.ext hd0_mem.1 (Prod.ext ?_ ?_)
        · funext r
          by_contra h1
          exact hall ⟨r, Or.inl h1⟩
        · funext r
          by_contra h2
          exact hall ⟨r, Or.inr h2⟩
      rcases hd0_occ with ⟨i₀, hi₀⟩
      have hCi0 : C i₀ = α := hd0_mem.2 i₀ hi₀
      constructor
      · intro hw
        by_cases hw0 : w = 0
        · exact Or.inl hw0
        · right
          have hw_occ : ∃ i₁ : Fin m, w.2.1 i₁ ≠ 0 ∨ w.2.2 i₁ ≠ 0 := by
            by_contra hall
            apply hw0
            refine Prod.ext hw.1 (Prod.ext ?_ ?_)
            · funext r; by_contra h1; exact hall ⟨r, Or.inl h1⟩
            · funext r; by_contra h2; exact hall ⟨r, Or.inr h2⟩
          rcases hw_occ with ⟨i₁, hi₁⟩
          have hw_R2 : R2C w := ⟨hw.1, i₁, hi₁, fun r hr => by rw [hw.2 r hr, hw.2 i₁ hi₁]⟩
          refine ⟨hw_R2, ?_⟩
          by_cases hwd : w = d₀
          · exact Or.inl hwd
          · right
            have hsum_mem : w + d₀ ∈ classSub C α := Submodule.add_mem _ hw hd0_mem
            have hsum_ne : w + d₀ ≠ 0 := by
              intro h0
              apply hwd
              refine Prod.ext ?_ (Prod.ext ?_ ?_)
              · rw [hw.1, hd0_mem.1]
              · funext r
                have h0r : w.2.1 r + d₀.2.1 r = 0 := congrFun (congrArg (fun z => z.2.1) h0) r
                exact zmod2_eq_of_add_eq_zero h0r
              · funext r
                have h0r : w.2.2 r + d₀.2.2 r = 0 := congrFun (congrArg (fun z => z.2.2) h0) r
                exact zmod2_eq_of_add_eq_zero h0r
            have hsum_occ : ∃ i₂ : Fin m, (w + d₀).2.1 i₂ ≠ 0 ∨ (w + d₀).2.2 i₂ ≠ 0 := by
              by_contra hall
              apply hsum_ne
              refine Prod.ext hsum_mem.1 (Prod.ext ?_ ?_)
              · funext r; by_contra h1; exact hall ⟨r, Or.inl h1⟩
              · funext r; by_contra h2; exact hall ⟨r, Or.inr h2⟩
            rcases hsum_occ with ⟨i₂, hi₂⟩
            exact ⟨hsum_mem.1, i₂, hi₂, fun r hr => by rw [hsum_mem.2 r hr, hsum_mem.2 i₂ hi₂]⟩
      · rintro (rfl | ⟨⟨hw1, i₁, hi₁, hCw⟩, rfl | ⟨_, i₂, hi₂, hCsum⟩⟩)
        · exact Submodule.zero_mem _
        · exact hd0_mem
        · refine ⟨hw1, fun r hr => ?_⟩
          rw [hCw r hr]
          by_contra hne
          have hd0_i1 : d₀.2.1 i₁ = 0 ∧ d₀.2.2 i₁ = 0 := by
            constructor
            · by_contra h1; exact hne (hd0_mem.2 i₁ (Or.inl h1))
            · by_contra h2; exact hne (hd0_mem.2 i₁ (Or.inr h2))
          have hw_i0 : w.2.1 i₀ = 0 ∧ w.2.2 i₀ = 0 := by
            constructor
            · by_contra h1; exact hne (hCi0 ▸ hCw i₀ (Or.inl h1)).symm
            · by_contra h2; exact hne (hCi0 ▸ hCw i₀ (Or.inr h2)).symm
          have hsum_i1 : (w + d₀).2.1 i₁ ≠ 0 ∨ (w + d₀).2.2 i₁ ≠ 0 := by
            rcases hi₁ with h1 | h2
            · left; change w.2.1 i₁ + d₀.2.1 i₁ ≠ 0; rw [hd0_i1.1, add_zero]; exact h1
            · right; change w.2.2 i₁ + d₀.2.2 i₁ ≠ 0; rw [hd0_i1.2, add_zero]; exact h2
          have hsum_i0 : (w + d₀).2.1 i₀ ≠ 0 ∨ (w + d₀).2.2 i₀ ≠ 0 := by
            rcases hi₀ with h1 | h2
            · left; change w.2.1 i₀ + d₀.2.1 i₀ ≠ 0; rw [hw_i0.1, zero_add]; exact h1
            · right; change w.2.2 i₀ + d₀.2.2 i₀ ≠ 0; rw [hw_i0.2, zero_add]; exact h2
          have e1 := hCsum i₁ hsum_i1
          have e0 := hCsum i₀ hsum_i0
          exact hne (e1.trans (e0.symm.trans hCi0))
    have hdata_decomp : ∀ p q : Fin m → ZMod 2,
        ((0 : Fin k → ZMod 2), (p, q)) =
          ∑ i : Fin m,
            (p i • (((0 : Fin k → ZMod 2), (Pi.single i (1 : ZMod 2), (0 : Fin m → ZMod 2))) :
                (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) +
             q i • (((0 : Fin k → ZMod 2), ((0 : Fin m → ZMod 2), Pi.single i (1 : ZMod 2))) :
                (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)))) := by
      intro p q
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · rw [Prod.fst_sum]; simp
      · funext r
        rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
        rw [Finset.sum_eq_single r]
        · simp
        · intro i _ hir; simp [Pi.single_eq_of_ne (Ne.symm hir)]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · funext r
        rw [Prod.snd_sum, Prod.snd_sum, Finset.sum_apply]
        rw [Finset.sum_eq_single r]
        · simp
        · intro i _ hir; simp [Pi.single_eq_of_ne (Ne.symm hir)]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have he_data : ∀ p q : Fin m → ZMod 2, (e (0, (p, q))).1 = 0 := by
      intro p q
      rw [hdata_decomp p q, map_sum, Prod.fst_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [map_add, map_smul, map_smul]
      have h1R : R2A (0, (Pi.single i (1 : ZMod 2), 0)) := by
        refine ⟨rfl, i, Or.inl (by simp), fun r hr => ?_⟩
        rcases hr with hr1 | hr2
        · by_cases hri : r = i
          · rw [hri]
          · exfalso; apply hr1; simp [Pi.single_eq_of_ne hri]
        · simp at hr2
      have h2R : R2A (0, (0, Pi.single i (1 : ZMod 2))) := by
        refine ⟨rfl, i, Or.inr (by simp), fun r hr => ?_⟩
        rcases hr with hr1 | hr2
        · simp at hr1
        · by_cases hri : r = i
          · rw [hri]
          · exfalso; apply hr2; simp [Pi.single_eq_of_ne hri]
      have h10 : (e (0, (Pi.single i (1 : ZMod 2), 0))).1 = 0 := ((he_R2 _).mp h1R).1
      have h20 : (e (0, (0, Pi.single i (1 : ZMod 2)))).1 = 0 := ((he_R2 _).mp h2R).1
      change p i • (e (0, (Pi.single i (1 : ZMod 2), 0))).1 +
          q i • (e (0, (0, Pi.single i (1 : ZMod 2)))).1 = 0
      rw [h10, h20, smul_zero, smul_zero, add_zero]
    have hesymm_data : ∀ p q : Fin m → ZMod 2, (e.symm (0, (p, q))).1 = 0 := by
      intro p q
      rw [hdata_decomp p q, map_sum, Prod.fst_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [map_add, map_smul, map_smul]
      have h1R : R2B (0, (Pi.single i (1 : ZMod 2), 0)) := by
        refine ⟨rfl, i, Or.inl (by simp), fun r hr => ?_⟩
        rcases hr with hr1 | hr2
        · by_cases hri : r = i
          · rw [hri]
          · exfalso; apply hr1; simp [Pi.single_eq_of_ne hri]
        · simp at hr2
      have h2R : R2B (0, (0, Pi.single i (1 : ZMod 2))) := by
        refine ⟨rfl, i, Or.inr (by simp), fun r hr => ?_⟩
        rcases hr with hr1 | hr2
        · simp at hr1
        · by_cases hri : r = i
          · rw [hri]
          · exfalso; apply hr2; simp [Pi.single_eq_of_ne hri]
      have h10 : (e.symm (0, (Pi.single i (1 : ZMod 2), 0))).1 = 0 := by
        have h' := (he_R2 (e.symm (0, (Pi.single i (1 : ZMod 2), 0)))).mpr (by rwa [e.apply_symm_apply])
        exact h'.1
      have h20 : (e.symm (0, (0, Pi.single i (1 : ZMod 2)))).1 = 0 := by
        have h' := (he_R2 (e.symm (0, (0, Pi.single i (1 : ZMod 2))))).mpr (by rwa [e.apply_symm_apply])
        exact h'.1
      change p i • (e.symm (0, (Pi.single i (1 : ZMod 2), 0))).1 +
          q i • (e.symm (0, (0, Pi.single i (1 : ZMod 2)))).1 = 0
      rw [h10, h20, smul_zero, smul_zero, add_zero]
    let lMap : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      { toFun := fun s => (e (s, (0, 0))).1
        map_add' := fun s₁ s₂ => by
          have h1 : ((s₁ + s₂), ((0 : Fin m → ZMod 2), (0 : Fin m → ZMod 2))) =
              (s₁, (0, 0)) + (s₂, (0, 0)) := by simp
          rw [h1, map_add]; rfl
        map_smul' := fun c s => by
          have h1 : (c • s, ((0 : Fin m → ZMod 2), (0 : Fin m → ZMod 2))) =
              c • (s, (0, 0)) := by simp
          rw [h1, map_smul]; rfl }
    have hl_inj : Function.Injective lMap := by
      intro s₁ s₂ h12
      have h0 : lMap (s₁ - s₂) = 0 := by rw [map_sub, h12, sub_self]
      have he0 : e (s₁ - s₂, (0, 0)) = (0, ((e (s₁ - s₂, (0, 0))).2.1, (e (s₁ - s₂, (0, 0))).2.2)) :=
        Prod.ext h0 rfl
      have hback := congrArg (fun z => (e.symm z).1) he0
      rw [e.symm_apply_apply] at hback
      have hsub : s₁ - s₂ = 0 := hback.trans (hesymm_data _ _)
      exact sub_eq_zero.mp hsub
    have hl_bij : Function.Bijective lMap := Finite.injective_iff_bijective.mp hl_inj
    let l : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) := LinearEquiv.ofBijective lMap hl_bij
    let imgA : Finset (Fin k → ZMod 2) := Finset.univ.image A
    let imgB : Finset (Fin k → ZMod 2) := Finset.univ.image B
    have hmatch_exists : ∀ α ∈ imgA, ∃ β ∈ imgB, ∀ w, w ∈ classSub A α ↔ e w ∈ classSub B β := by
      intro α hα
      rcases Finset.mem_image.mp hα with ⟨i₀, _, rfl⟩
      let d₀ : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        (0, (Pi.single i₀ (1 : ZMod 2), 0))
      have hd0_mem : d₀ ∈ classSub A (A i₀) := by
        refine ⟨rfl, fun r hr => ?_⟩
        rcases hr with h1 | h2
        · by_cases hri : r = i₀
          · rw [hri]
          · exfalso; apply h1; simp [d₀, Pi.single_eq_of_ne hri]
        · simp [d₀] at h2
      have hd0_ne : d₀ ≠ 0 := by
        intro h0
        have h1 := congrFun (congrArg (fun z => z.2.1) h0) i₀
        simp [d₀] at h1
      have hd0_R2 : R2A d₀ := ⟨rfl, i₀, Or.inl (by simp [d₀]), fun r hr => hd0_mem.2 r hr⟩
      have hed0_R2 : R2B (e d₀) := (he_R2 d₀).mp hd0_R2
      rcases hed0_R2 with ⟨hed0_1, r₀, hr₀, hB_ed0⟩
      refine ⟨B r₀, Finset.mem_image_of_mem B (Finset.mem_univ r₀), fun w => ?_⟩
      have hed0_mem : e d₀ ∈ classSub B (B r₀) := ⟨hed0_1, hB_ed0⟩
      have hed0_ne : e d₀ ≠ 0 := fun h0 => hd0_ne (e.injective (by rw [h0, map_zero]))
      rw [hclass_iff A (A i₀) d₀ ⟨hd0_mem, hd0_ne⟩ w,
          hclass_iff B (B r₀) (e d₀) ⟨hed0_mem, hed0_ne⟩ (e w)]
      have hzero : w = 0 ↔ e w = 0 := ⟨fun h => by rw [h, map_zero], fun h => e.injective (by rw [h, map_zero])⟩
      have heq : w = d₀ ↔ e w = e d₀ := ⟨fun h => by rw [h], fun h => e.injective h⟩
      have hsum : R2A (w + d₀) ↔ R2B (e w + e d₀) := by
        rw [← map_add]
        exact he_R2 (w + d₀)
      change (w = 0 ∨ R2A w ∧ (w = d₀ ∨ R2A (w + d₀))) ↔
        (e w = 0 ∨ R2B (e w) ∧ (e w = e d₀ ∨ R2B (e w + e d₀)))
      rw [hzero, he_R2 w, heq, hsum]
    let φ : {α : Fin k → ZMod 2 // α ∈ imgA} → {β : Fin k → ZMod 2 // β ∈ imgB} :=
      fun α => ⟨Classical.choose (hmatch_exists α.1 α.2), (Classical.choose_spec (hmatch_exists α.1 α.2)).1⟩
    have hφ_spec : ∀ α : {α : Fin k → ZMod 2 // α ∈ imgA},
        ∀ w, w ∈ classSub A α.1 ↔ e w ∈ classSub B (φ α).1 :=
      fun α => (Classical.choose_spec (hmatch_exists α.1 α.2)).2
    have hφ_inj : Function.Injective φ := by
      intro α₁ α₂ h12
      apply Subtype.ext
      rcases Finset.mem_image.mp α₁.2 with ⟨i₁, _, hi₁⟩
      let d₁ : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        (0, (Pi.single i₁ (1 : ZMod 2), 0))
      have hd1_in : d₁ ∈ classSub A α₁.1 := by
        refine ⟨rfl, fun r hr => ?_⟩
        rcases hr with h1 | h2
        · by_cases hri : r = i₁
          · rw [hri, hi₁]
          · exfalso; apply h1; simp [d₁, Pi.single_eq_of_ne hri]
        · simp [d₁] at h2
      have hed1 : e d₁ ∈ classSub B (φ α₁).1 := (hφ_spec α₁ d₁).mp hd1_in
      rw [h12] at hed1
      have hd1_in2 : d₁ ∈ classSub A α₂.1 := (hφ_spec α₂ d₁).mpr hed1
      have hAi1 : A i₁ = α₂.1 := hd1_in2.2 i₁ (Or.inl (by simp [d₁]))
      rw [← hi₁, hAi1]
    have hφ_surj : Function.Surjective φ := by
      intro β
      rcases Finset.mem_image.mp β.2 with ⟨r₀, _, hr₀⟩
      let d₀ : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        (0, (Pi.single r₀ (1 : ZMod 2), 0))
      have hd0_R2 : R2B d₀ := by
        refine ⟨rfl, r₀, Or.inl (by simp [d₀]), fun r hr => ?_⟩
        rcases hr with h1 | h2
        · by_cases hrr : r = r₀
          · rw [hrr]
          · exfalso; apply h1; simp [d₀, Pi.single_eq_of_ne hrr]
        · simp [d₀] at h2
      have hpre_R2 : R2A (e.symm d₀) := (he_R2 (e.symm d₀)).mpr (by rwa [e.apply_symm_apply])
      rcases hpre_R2 with ⟨hpre1, i₀, _, hA_pre⟩
      let α : {α : Fin k → ZMod 2 // α ∈ imgA} :=
        ⟨A i₀, Finset.mem_image_of_mem A (Finset.mem_univ i₀)⟩
      have hpre_in : e.symm d₀ ∈ classSub A α.1 := ⟨hpre1, hA_pre⟩
      have hd0_in : d₀ ∈ classSub B (φ α).1 := by
        have h' := (hφ_spec α (e.symm d₀)).mp hpre_in
        rwa [e.apply_symm_apply] at h'
      refine ⟨α, Subtype.ext ?_⟩
      have hBr0 : B r₀ = (φ α).1 := hd0_in.2 r₀ (Or.inl (by simp [d₀]))
      rw [← hr₀, hBr0]
    let φEquiv : {α : Fin k → ZMod 2 // α ∈ imgA} ≃ {β : Fin k → ZMod 2 // β ∈ imgB} :=
      Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hfiber_card : ∀ α : {α : Fin k → ZMod 2 // α ∈ imgA},
        Fintype.card {i : Fin m // A i = α.1} = Fintype.card {r : Fin m // B r = (φ α).1} := by
      intro α
      let eSub : ↥(classSub A α.1) ≃ₗ[ZMod 2] ↥(classSub B (φ α).1) :=
        { toFun := fun w => ⟨e w.1, (hφ_spec α w.1).mp w.2⟩
          map_add' := fun x y => Subtype.ext (map_add e x.1 y.1)
          map_smul' := fun c x => Subtype.ext (map_smul e c x.1)
          invFun := fun w => ⟨e.symm w.1, (hφ_spec α (e.symm w.1)).mpr (by
            rw [e.apply_symm_apply]; exact w.2)⟩
          left_inv := fun w => Subtype.ext (e.symm_apply_apply w.1)
          right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
      have hfr := eSub.finrank_eq
      rw [finrank_classSub, finrank_classSub] at hfr
      have hcardEq : ((Finset.univ : Finset (Fin m)).filter (fun r => A r = α.1)).card =
          ((Finset.univ : Finset (Fin m)).filter (fun r => B r = (φ α).1)).card := by omega
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact hcardEq
    let fibEquiv : ∀ α : {α : Fin k → ZMod 2 // α ∈ imgA},
        {i : Fin m // A i = α.1} ≃ {r : Fin m // B r = (φ α).1} :=
      fun α => Fintype.equivOfCardEq (hfiber_card α)
    let splitA : Fin m ≃ Σ α : {α : Fin k → ZMod 2 // α ∈ imgA}, {i : Fin m // A i = α.1} :=
      { toFun := fun i => ⟨⟨A i, Finset.mem_image_of_mem A (Finset.mem_univ i)⟩, ⟨i, rfl⟩⟩
        invFun := fun x => x.2.1
        left_inv := fun _ => rfl
        right_inv := fun x => by
          rcases x with ⟨⟨α, hα⟩, ⟨i, hi⟩⟩
          simp only [Sigma.mk.inj_iff, Subtype.mk.injEq]
          refine ⟨hi, ?_⟩
          cases hi
          rfl }
    let splitB : Fin m ≃ Σ β : {β : Fin k → ZMod 2 // β ∈ imgB}, {r : Fin m // B r = β.1} :=
      { toFun := fun r => ⟨⟨B r, Finset.mem_image_of_mem B (Finset.mem_univ r)⟩, ⟨r, rfl⟩⟩
        invFun := fun x => x.2.1
        left_inv := fun _ => rfl
        right_inv := fun x => by
          rcases x with ⟨⟨β, hβ⟩, ⟨r, hr⟩⟩
          simp only [Sigma.mk.inj_iff, Subtype.mk.injEq]
          refine ⟨hr, ?_⟩
          cases hr
          rfl }
    let p : Equiv.Perm (Fin m) :=
      splitA.trans ((Equiv.sigmaCongr φEquiv (fun α => fibEquiv α)).trans splitB.symm)
    have hBp : ∀ i : Fin m, B (p i) = (φ ⟨A i, Finset.mem_image_of_mem A (Finset.mem_univ i)⟩).1 := by
      intro i
      change B (fibEquiv ⟨A i, Finset.mem_image_of_mem A (Finset.mem_univ i)⟩ ⟨i, rfl⟩).1 = _
      exact (fibEquiv ⟨A i, Finset.mem_image_of_mem A (Finset.mem_univ i)⟩ ⟨i, rfl⟩).2
    have hdot_eq : ∀ (i : Fin m) (s : Fin k → ZMod 2), dotProduct (A i) s = dotProduct (B (p i)) (l s) := by
      intro i
      let α : {α : Fin k → ZMod 2 // α ∈ imgA} :=
        ⟨A i, Finset.mem_image_of_mem A (Finset.mem_univ i)⟩
      let d₁ : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        (0, (Pi.single i (1 : ZMod 2), 0))
      let d₂ : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        (0, (0, Pi.single i (1 : ZMod 2)))
      have hd1_in : d₁ ∈ classSub A α.1 := by
        refine ⟨rfl, fun r hr => ?_⟩
        rcases hr with h1 | h2
        · by_cases hri : r = i
          · rw [hri]
          · exfalso; apply h1; simp [d₁, Pi.single_eq_of_ne hri]
        · simp [d₁] at h2
      have hd2_in : d₂ ∈ classSub A α.1 := by
        refine ⟨rfl, fun r hr => ?_⟩
        rcases hr with h1 | h2
        · simp [d₂] at h1
        · by_cases hri : r = i
          · rw [hri]
          · exfalso; apply h2; simp [d₂, Pi.single_eq_of_ne hri]
      have hed1_in : e d₁ ∈ classSub B (B (p i)) := by
        rw [hBp i]; exact (hφ_spec α d₁).mp hd1_in
      have hed2_in : e d₂ ∈ classSub B (B (p i)) := by
        rw [hBp i]; exact (hφ_spec α d₂).mp hd2_in
      set p' := (e d₁).2.1
      set q' := (e d₁).2.2
      set r' := (e d₂).2.1
      set t' := (e d₂).2.2
      let c : ZMod 2 := ∑ r : Fin m, (p' r * t' r + r' r * q' r)
      have hmul_c : ∀ s : Fin k → ZMod 2, dotProduct (A i) s = dotProduct (B (p i)) (l s) * c := by
        intro s
        have heq := he (s, (0, 0)) d₁ d₂
        have hlhs : diff3 formA (s, (0, 0)) d₁ d₂ = dotProduct (A i) s := by
          dsimp only [d₁, d₂]
          rw [tv_form_expand, diff3_zero_right, zero_add]
          rw [Finset.sum_eq_single i]
          · simp
          · intro r _ hri; simp [Pi.single_eq_of_ne hri]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        have hed1_eq : e d₁ = (0, (p', q')) := Prod.ext hed1_in.1 rfl
        have hed2_eq : e d₂ = (0, (r', t')) := Prod.ext hed2_in.1 rfl
        have hes_eq : e (s, (0, 0)) = (l s, ((e (s, (0, 0))).2.1, (e (s, (0, 0))).2.2)) := rfl
        have hrhs : diff3 formB (e (s, (0, 0))) (e d₁) (e d₂) =
            dotProduct (B (p i)) (l s) * c := by
          rw [hes_eq, hed1_eq, hed2_eq, tv_form_expand, diff3_zero_right, zero_add]
          dsimp only [c]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          simp only [dotProduct_zero, zero_mul, add_zero]
          by_cases hBr : B r = B (p i)
          · rw [hBr]
          · have hp0 : p' r = 0 := by
              by_contra hne; exact hBr (hed1_in.2 r (Or.inl hne))
            have hq0 : q' r = 0 := by
              by_contra hne; exact hBr (hed1_in.2 r (Or.inr hne))
            have hr0 : r' r = 0 := by
              by_contra hne; exact hBr (hed2_in.2 r (Or.inl hne))
            have ht0 : t' r = 0 := by
              by_contra hne; exact hBr (hed2_in.2 r (Or.inr hne))
            simp [hp0, hq0, hr0, ht0]
        rw [hlhs, hrhs] at heq
        exact heq
      obtain ⟨s₀, hs₀⟩ := exists_dot_one (hgA.1 i)
      have hc1 : c = 1 := by
        have h1 := hmul_c s₀
        rw [hs₀] at h1
        rcases zmod2_cases c with hc0 | hc1
        · rw [hc0, mul_zero] at h1; exact absurd h1 one_ne_zero
        · exact hc1
      intro s
      rw [hmul_c s, hc1, mul_one]
    have hts_eq : ∀ a b c : Fin k → ZMod 2, diff3 h a b c = diff3 j (l a) (l b) (l c) := by
      let σ₁ : (Fin k → ZMod 2) → (Fin m → ZMod 2) := fun a => (e (a, (0, 0))).2.1
      let σ₂ : (Fin k → ZMod 2) → (Fin m → ZMod 2) := fun a => (e (a, (0, 0))).2.2
      have hrel1 : ∀ (r : Fin m) (a b : Fin k → ZMod 2),
          dotProduct (B r) (l a) * σ₁ b r + dotProduct (B r) (l b) * σ₁ a r = 0 := by
        intro r a b
        let d : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
          (0, (0, Pi.single r (1 : ZMod 2)))
        have heq := he (a, (0, 0)) (b, (0, 0)) (e.symm d)
        rw [e.apply_symm_apply] at heq
        have hpre0 : (e.symm d).1 = 0 := hesymm_data 0 (Pi.single r 1)
        have hlhs : diff3 formA (a, (0, 0)) (b, (0, 0)) (e.symm d) = 0 := by
          have hpre_eq : e.symm d = (0, ((e.symm d).2.1, (e.symm d).2.2)) := Prod.ext hpre0 rfl
          rw [hpre_eq, tv_form_expand, diff3_zero_right]
          simp
        have hrhs : diff3 formB (e (a, (0, 0))) (e (b, (0, 0))) d =
            dotProduct (B r) (l a) * σ₁ b r + dotProduct (B r) (l b) * σ₁ a r := by
          have ha_eq : e (a, (0, 0)) = (l a, (σ₁ a, σ₂ a)) := rfl
          have hb_eq : e (b, (0, 0)) = (l b, (σ₁ b, σ₂ b)) := rfl
          rw [ha_eq, hb_eq]
          dsimp only [d]
          rw [tv_form_expand, diff3_zero_right, zero_add]
          rw [Finset.sum_eq_single r]
          · simp
          · intro r' _ hrr'; simp [Pi.single_eq_of_ne hrr']
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hlhs, hrhs] at heq
        exact heq.symm
      have hrel2 : ∀ (r : Fin m) (a b : Fin k → ZMod 2),
          dotProduct (B r) (l a) * σ₂ b r + dotProduct (B r) (l b) * σ₂ a r = 0 := by
        intro r a b
        let d : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
          (0, (Pi.single r (1 : ZMod 2), 0))
        have heq := he (a, (0, 0)) (b, (0, 0)) (e.symm d)
        rw [e.apply_symm_apply] at heq
        have hpre0 : (e.symm d).1 = 0 := hesymm_data (Pi.single r 1) 0
        have hlhs : diff3 formA (a, (0, 0)) (b, (0, 0)) (e.symm d) = 0 := by
          have hpre_eq : e.symm d = (0, ((e.symm d).2.1, (e.symm d).2.2)) := Prod.ext hpre0 rfl
          rw [hpre_eq, tv_form_expand, diff3_zero_right]
          simp
        have hrhs : diff3 formB (e (a, (0, 0))) (e (b, (0, 0))) d =
            dotProduct (B r) (l a) * σ₂ b r + dotProduct (B r) (l b) * σ₂ a r := by
          have ha_eq : e (a, (0, 0)) = (l a, (σ₁ a, σ₂ a)) := rfl
          have hb_eq : e (b, (0, 0)) = (l b, (σ₁ b, σ₂ b)) := rfl
          rw [ha_eq, hb_eq]
          dsimp only [d]
          rw [tv_form_expand, diff3_zero_right, zero_add]
          rw [Finset.sum_eq_single r]
          · simp
          · intro r' _ hrr'; simp [Pi.single_eq_of_ne hrr']
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hlhs, hrhs] at heq
        exact heq.symm
      have hcross_zero : ∀ (r : Fin m) (x y : Fin k → ZMod 2),
          σ₁ x r * σ₂ y r + σ₁ y r * σ₂ x r = 0 := by
        intro r x y
        obtain ⟨s₁, hs₁⟩ := exists_dot_one (hgB.1 r)
        let a₀ := l.symm s₁
        have ha0 : dotProduct (B r) (l a₀) = 1 := by
          dsimp only [a₀]; rw [l.apply_symm_apply]; exact hs₁
        have h1x : σ₁ x r = dotProduct (B r) (l x) * σ₁ a₀ r := by
          have h' := hrel1 r a₀ x; rw [ha0, one_mul] at h'; exact zmod2_eq_of_add_eq_zero h'
        have h1y : σ₁ y r = dotProduct (B r) (l y) * σ₁ a₀ r := by
          have h' := hrel1 r a₀ y; rw [ha0, one_mul] at h'; exact zmod2_eq_of_add_eq_zero h'
        have h2x : σ₂ x r = dotProduct (B r) (l x) * σ₂ a₀ r := by
          have h' := hrel2 r a₀ x; rw [ha0, one_mul] at h'; exact zmod2_eq_of_add_eq_zero h'
        have h2y : σ₂ y r = dotProduct (B r) (l y) * σ₂ a₀ r := by
          have h' := hrel2 r a₀ y; rw [ha0, one_mul] at h'; exact zmod2_eq_of_add_eq_zero h'
        rw [h1x, h1y, h2x, h2y]
        have hsame : dotProduct (B r) (l x) * σ₁ a₀ r * (dotProduct (B r) (l y) * σ₂ a₀ r) +
            dotProduct (B r) (l y) * σ₁ a₀ r * (dotProduct (B r) (l x) * σ₂ a₀ r) =
            (dotProduct (B r) (l x) * dotProduct (B r) (l y) * σ₁ a₀ r * σ₂ a₀ r) +
            (dotProduct (B r) (l x) * dotProduct (B r) (l y) * σ₁ a₀ r * σ₂ a₀ r) := by ring
        rw [hsame, zmod2_add_self]
      intro a b c
      have heq := he (a, (0, 0)) (b, (0, 0)) (c, (0, 0))
      have hlhs : diff3 formA (a, (0, 0)) (b, (0, 0)) (c, (0, 0)) = diff3 h a b c := by
        rw [tv_form_expand]; simp
      have hrhs : diff3 formB (e (a, (0, 0))) (e (b, (0, 0))) (e (c, (0, 0))) =
          diff3 j (l a) (l b) (l c) := by
        have ha_eq : e (a, (0, 0)) = (l a, (σ₁ a, σ₂ a)) := rfl
        have hb_eq : e (b, (0, 0)) = (l b, (σ₁ b, σ₂ b)) := rfl
        have hc_eq : e (c, (0, 0)) = (l c, (σ₁ c, σ₂ c)) := rfl
        rw [ha_eq, hb_eq, hc_eq, tv_form_expand]
        have hsum0 : (∑ r : Fin m,
            (dotProduct (B r) (l a) * (σ₁ b r * σ₂ c r + σ₁ c r * σ₂ b r) +
             dotProduct (B r) (l b) * (σ₁ a r * σ₂ c r + σ₁ c r * σ₂ a r) +
             dotProduct (B r) (l c) * (σ₁ a r * σ₂ b r + σ₁ b r * σ₂ a r))) = 0 := by
          refine Finset.sum_eq_zero (fun r _ => ?_)
          rw [hcross_zero r b c, hcross_zero r a c, hcross_zero r a b]
          ring
        rw [hsum0, add_zero]
      rw [hlhs, hrhs] at heq
      exact heq
    exact ⟨l, p, hdot_eq, hts_eq⟩
  · rintro ⟨l, p, hdot_eq, hts_eq⟩
    let e : ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) ≃ₗ[ZMod 2]
        ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) :=
      { toFun := fun x => (l x.1, (fun r => x.2.1 (p.symm r), fun r => x.2.2 (p.symm r)))
        map_add' := fun x y => by
          refine Prod.ext (map_add l x.1 y.1) (Prod.ext ?_ ?_)
          · funext r; rfl
          · funext r; rfl
        map_smul' := fun c x => by
          refine Prod.ext (map_smul l c x.1) (Prod.ext ?_ ?_)
          · funext r; rfl
          · funext r; rfl
        invFun := fun y => (l.symm y.1, (fun i => y.2.1 (p i), fun i => y.2.2 (p i)))
        left_inv := fun ⟨s, u, v⟩ => by
          refine Prod.ext (l.symm_apply_apply s) (Prod.ext ?_ ?_)
          · funext i; simp
          · funext i; simp
        right_inv := fun ⟨s, u, v⟩ => by
          refine Prod.ext (l.apply_symm_apply s) (Prod.ext ?_ ?_)
          · funext r; simp
          · funext r; simp }
    refine ⟨e, ?_⟩
    rintro ⟨s, u, v⟩ ⟨a, p1, q1⟩ ⟨b, r1, t1⟩
    change diff3 formA (s, (u, v)) (a, (p1, q1)) (b, (r1, t1)) =
      diff3 formB (l s, (fun r => u (p.symm r), fun r => v (p.symm r)))
        (l a, (fun r => p1 (p.symm r), fun r => q1 (p.symm r)))
        (l b, (fun r => r1 (p.symm r), fun r => t1 (p.symm r)))
    rw [tv_form_expand, tv_form_expand, hts_eq s a b]
    congr 1
    conv_rhs => rw [← Equiv.sum_comp p]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Equiv.symm_apply_apply]
    rw [← hdot_eq i s, ← hdot_eq i a, ← hdot_eq i b]

end PEqualNP.Outside.L_lib_902_aux

theorem PEqualNP.Outside.L_lib_902 :
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
    ∀ (A B : Fin m → S) (h j : S → F), good A → good B → cubic h → cubic j →
      ((∃ e : V ≃ₗ[F] V, ∀ u v w : V, tv (form A h) u v w = tv (form B j) (e u) (e v) (e w)) ↔
        ∃ (l : S ≃ₗ[F] S) (p : Equiv.Perm (Fin m)),
          (∀ i s, dotProduct (A i) s = dotProduct (B (p i)) (l s)) ∧
          (∀ a b c : S, ts h a b c = ts j (l a) (l b) (l c))) := by
  intro k m
  dsimp only
  intro A B h j hgA hgB hh hj
  exact PEqualNP.Outside.L_lib_902_aux.main_proof k m A B h j hgA hgB hh hj

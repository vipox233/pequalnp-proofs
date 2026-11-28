import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_445_aux

abbrev F := ZMod 2
abbrev X (n : ℕ) := Fin n → F

lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by
  have h1 := congrArg (fun t => t + b) h
  rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h1
  exact h1

lemma zmod2_ne_zero_eq_one {a : F} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma zmod2_vec_add_self {n : ℕ} (u : X n) : u + u = 0 := by
  ext i
  exact zmod2_add_self (u i)

def signZ (a : F) : ℤ := if a = 0 then 1 else -1

lemma signZ_add (a b : F) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma signZ_sq (a : F) : signZ a * signZ a = 1 := by
  fin_cases a <;> decide

lemma zmod2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma sum_signZ_linear {V : Type} [AddCommGroup V] [Module F V] [Fintype V]
    (ℓ : V →ₗ[F] F) :
    (∑ v : V, signZ (ℓ v)) = if ℓ = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with h0
  · simp [h0, signZ]
  · have hex : ∃ w : V, ℓ w = 1 := by
      by_contra hall
      push Not at hall
      apply h0
      ext v
      rcases zmod2_eq_zero_or_one (ℓ v) with h | h
      · exact h
      · exact absurd h (hall v)
    obtain ⟨w, hw⟩ := hex
    have hshift : (∑ v : V, signZ (ℓ v)) = ∑ v : V, signZ (ℓ (v + w)) := by
      symm
      refine Fintype.sum_equiv (Equiv.addRight w) _ _ (fun v => rfl)
    have hneg : (∑ v : V, signZ (ℓ (v + w))) = -(∑ v : V, signZ (ℓ v)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro v _
      rw [map_add, hw, signZ_add]
      have : signZ (1 : F) = -1 := rfl
      rw [this]
      ring
    linarith

lemma B_symm {n : ℕ} (f : X n → F) (u v : X n) :
    f (u + v) + f u + f v + f 0 = f (v + u) + f v + f u + f 0 := by
  rw [add_comm u v]
  ring

lemma B_self {n : ℕ} (f : X n → F) (u : X n) :
    f (u + u) + f u + f u + f 0 = 0 := by
  rw [zmod2_vec_add_self u]
  have h1 := zmod2_add_self (f 0)
  have h2 := zmod2_add_self (f u)
  calc
    f 0 + f u + f u + f 0 = (f 0 + f 0) + (f u + f u) := by ring
    _ = 0 := by rw [h1, h2, add_zero]

lemma B_add_right {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (u v w : X n) :
    (f (u + (v + w)) + f u + f (v + w) + f 0) =
      (f (u + v) + f u + f v + f 0) + (f (u + w) + f u + f w + f 0) := by
  have hq := hquad v u w
  have h1 : v + u + w = u + (v + w) := by abel
  have h2 : v + u = u + v := add_comm v u
  rw [h1, h2] at hq
  have hcancel : ∀ a b c d e g : F,
      a + b + c + d = e → (b + g + d + f 0) + e = a + g + c + f 0 := by
    intro a b c d e g he
    rw [← he]
    have hb := zmod2_add_self b
    have hd := zmod2_add_self d
    calc
      b + g + d + f 0 + (a + b + c + d) = (b + b) + (d + d) + (a + g + c + f 0) := by ring
      _ = a + g + c + f 0 := by rw [hb, hd, zero_add, zero_add]
  exact (hcancel (f (u + (v + w))) (f (u + v)) (f (v + w)) (f v)
    (f (u + w) + f u + f w + f 0) (f u) hq).symm

def Blin {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0) :
    X n →ₗ[F] (X n →ₗ[F] F) where
  toFun u :=
    { toFun := fun v => f (u + v) + f u + f v + f 0
      map_add' := fun v w => B_add_right f hquad u v w
      map_smul' := fun c v => by
        fin_cases c
        · change f (u + (0 : F) • v) + f u + f ((0 : F) • v) + f 0 =
            (0 : F) * (f (u + v) + f u + f v + f 0)
          rw [zero_smul, add_zero, zero_mul]
          calc
            f u + f u + f 0 + f 0 = (f u + f u) + (f 0 + f 0) := by ring
            _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]
        · change f (u + (1 : F) • v) + f u + f ((1 : F) • v) + f 0 =
            (1 : F) * (f (u + v) + f u + f v + f 0)
          rw [one_smul, one_mul] }
  map_add' u1 u2 := by
    apply LinearMap.ext
    intro v
    change f (u1 + u2 + v) + f (u1 + u2) + f v + f 0 =
      (f (u1 + v) + f u1 + f v + f 0) + (f (u2 + v) + f u2 + f v + f 0)
    rw [B_symm f (u1 + u2) v, B_symm f u1 v, B_symm f u2 v]
    exact B_add_right f hquad v u1 u2
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    fin_cases c
    · change f ((0 : F) • u + v) + f ((0 : F) • u) + f v + f 0 =
        (0 : F) * (f (u + v) + f u + f v + f 0)
      rw [zero_smul, zero_add, zero_mul]
      calc
        f v + f 0 + f v + f 0 = (f v + f v) + (f 0 + f 0) := by ring
        _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]
    · change f ((1 : F) • u + v) + f ((1 : F) • u) + f v + f 0 =
        (1 : F) * (f (u + v) + f u + f v + f 0)
      rw [one_smul, one_mul]

lemma Blin_symm {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0) (u v : X n) :
    Blin f hquad u v = Blin f hquad v u := B_symm f u v

def orthSub {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (W : Submodule F (X n)) : Submodule F (X n) :=
  LinearMap.ker ((LinearMap.lcomp F F W.subtype).comp (Blin f hquad))

lemma mem_orthSub {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (W : Submodule F (X n)) (u : X n) :
    u ∈ orthSub f hquad W ↔ ∀ v ∈ W, f (u + v) + f u + f v + f 0 = 0 := by
  simp only [orthSub, LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h v hv
    exact LinearMap.congr_fun h ⟨v, hv⟩
  · intro h
    ext ⟨v, hv⟩
    exact h v hv

def radSub {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (W : Submodule F (X n)) : Submodule F (X n) :=
  W ⊓ orthSub f hquad W

lemma card_sub_eq_pow {n : ℕ} (W : Submodule F (X n)) [Fintype W] :
    Fintype.card W = 2 ^ Module.finrank F W := by
  have h1 := Module.card_eq_pow_finrank (K := F) (V := W)
  have h2 : Fintype.card F = 2 := ZMod.card 2
  rw [h2] at h1
  exact h1

lemma even_finrank_sub_rad {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0) :
    ∀ (d : ℕ) (W : Submodule F (X n)), Module.finrank F W ≤ d →
      Even (Module.finrank F W - Module.finrank F (radSub f hquad W)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro W hWd
    by_cases heq : radSub f hquad W = W
    · rw [heq, Nat.sub_self]
      exact ⟨0, rfl⟩
    · have hex : ∃ u ∈ W, ∃ v ∈ W, Blin f hquad u v ≠ 0 := by
        by_contra hall
        push Not at hall
        apply heq
        apply le_antisymm inf_le_left
        intro u hu
        refine ⟨hu, (mem_orthSub f hquad W u).mpr ?_⟩
        intro v hv
        exact hall u hu v hv
      obtain ⟨u, huW, v, hvW, huv_ne⟩ := hex
      have huv : Blin f hquad u v = 1 := zmod2_ne_zero_eq_one huv_ne
      have hvu : Blin f hquad v u = 1 := by
        show f (v + u) + f v + f u + f 0 = 1
        rw [B_symm f v u]
        exact huv
      have huu : Blin f hquad u u = 0 := B_self f u
      have hvv : Blin f hquad v v = 0 := B_self f v
      let ψ : W →ₗ[F] (F × F) :=
        { toFun := fun x => (Blin f hquad u x.1, Blin f hquad v x.1)
          map_add' := fun a b => by
            ext
            · exact map_add (Blin f hquad u) a.1 b.1
            · exact map_add (Blin f hquad v) a.1 b.1
          map_smul' := fun c a => by
            ext
            · exact map_smul (Blin f hquad u) c a.1
            · exact map_smul (Blin f hquad v) c a.1 }
      have hsurj : Function.Surjective ψ := by
        rintro ⟨a, b⟩
        refine ⟨⟨b • u + a • v, W.add_mem (W.smul_mem b huW) (W.smul_mem a hvW)⟩, ?_⟩
        ext
        · show Blin f hquad u (b • u + a • v) = a
          rw [map_add, map_smul, map_smul, huu, huv]
          simp
        · show Blin f hquad v (b • u + a • v) = b
          rw [map_add, map_smul, map_smul, hvu, hvv]
          simp
      let W' : Submodule F (X n) := (LinearMap.ker ψ).map W.subtype
      have hW'_le : W' ≤ W := by
        rintro _ ⟨x, _, rfl⟩
        exact x.2
      have hdim_W' : Module.finrank F W' + 2 = Module.finrank F W := by
        have hrn := LinearMap.finrank_range_add_finrank_ker ψ
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn
        have hff : Module.finrank F (F × F) = 2 := by
          rw [Module.finrank_prod, Module.finrank_self]
        rw [hff] at hrn
        have hinj : Function.Injective W.subtype := Subtype.val_injective
        have hmap : Module.finrank F W' = Module.finrank F (LinearMap.ker ψ) :=
          (Submodule.equivMapOfInjective W.subtype hinj (LinearMap.ker ψ)).finrank_eq.symm
        omega
      have hrad_eq : radSub f hquad W' = radSub f hquad W := by
        apply le_antisymm
        · intro w hw
          rcases hw with ⟨hwW', hw_orth⟩
          have hwW : w ∈ W := hW'_le hwW'
          rcases hwW' with ⟨⟨w0, hw0W⟩, hw0ker, rfl⟩
          have hw_u : Blin f hquad u w0 = 0 := congrArg Prod.fst hw0ker
          have hw_v : Blin f hquad v w0 = 0 := congrArg Prod.snd hw0ker
          refine ⟨hwW, (mem_orthSub f hquad W w0).mpr ?_⟩
          intro x hxW
          let x' : X n := x + Blin f hquad v x • u + Blin f hquad u x • v
          have hx'W : x' ∈ W :=
            W.add_mem (W.add_mem hxW (W.smul_mem _ huW)) (W.smul_mem _ hvW)
          have hx'ker : ⟨x', hx'W⟩ ∈ LinearMap.ker ψ := by
            rw [LinearMap.mem_ker]
            ext
            · show Blin f hquad u x' = 0
              simp only [x', map_add, map_smul, huu, huv, smul_eq_mul, mul_zero, mul_one, add_zero]
              exact zmod2_add_self (Blin f hquad u x)
            · show Blin f hquad v x' = 0
              simp only [x', map_add, map_smul, hvu, hvv, smul_eq_mul, mul_zero, mul_one, add_zero]
              exact zmod2_add_self (Blin f hquad v x)
          have hx'W' : x' ∈ W' := ⟨⟨x', hx'W⟩, hx'ker, rfl⟩
          have h0 : Blin f hquad w0 x' = 0 := (mem_orthSub f hquad W' w0).mp hw_orth x' hx'W'
          have hwu0 : Blin f hquad w0 u = 0 := by
            show f (w0 + u) + f w0 + f u + f 0 = 0
            rw [B_symm f w0 u]
            exact hw_u
          have hwv0 : Blin f hquad w0 v = 0 := by
            show f (w0 + v) + f w0 + f v + f 0 = 0
            rw [B_symm f w0 v]
            exact hw_v
          simp only [x', map_add, map_smul, hwu0, hwv0, smul_eq_mul, mul_zero, add_zero] at h0
          exact h0
        · intro w hw
          rcases hw with ⟨hwW, hw_orth⟩
          have hwker : ⟨w, hwW⟩ ∈ LinearMap.ker ψ := by
            rw [LinearMap.mem_ker]
            ext
            · show f (u + w) + f u + f w + f 0 = 0
              rw [B_symm f u w]
              exact (mem_orthSub f hquad W w).mp hw_orth u huW
            · show f (v + w) + f v + f w + f 0 = 0
              rw [B_symm f v w]
              exact (mem_orthSub f hquad W w).mp hw_orth v hvW
          refine ⟨⟨⟨w, hwW⟩, hwker, rfl⟩, (mem_orthSub f hquad W' w).mpr ?_⟩
          intro x hxW'
          exact (mem_orthSub f hquad W w).mp hw_orth x (hW'_le hxW')
      have hW'_lt : Module.finrank F W' < d := by omega
      have hih := ih (Module.finrank F W') hW'_lt W' le_rfl
      rw [hrad_eq] at hih
      have hle_rad : Module.finrank F (radSub f hquad W) ≤ Module.finrank F W' := by
        rw [← hrad_eq]
        exact Submodule.finrank_mono inf_le_left
      have hstep : Module.finrank F W - Module.finrank F (radSub f hquad W) =
          (Module.finrank F W' - Module.finrank F (radSub f hquad W)) + 2 := by omega
      rw [hstep]
      exact Even.add hih ⟨1, rfl⟩

lemma finrank_orthSub_le {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (W : Submodule F (X n)) :
    let R0 := LinearMap.ker (Blin f hquad)
    Module.finrank F (orthSub f hquad W) ≤
      Module.finrank F R0 + (n - Module.finrank F W) ∧
    (Module.finrank F (orthSub f hquad W) = Module.finrank F R0 + (n - Module.finrank F W) →
      ∀ ℓ : X n →ₗ[F] F, (∀ v ∈ W, ℓ v = 0) → ∃ u ∈ orthSub f hquad W, Blin f hquad u = ℓ) := by
  dsimp only
  let R0 := LinearMap.ker (Blin f hquad)
  let res : (X n →ₗ[F] F) →ₗ[F] (W →ₗ[F] F) := LinearMap.lcomp F F W.subtype
  have hres_surj : Function.Surjective res := by
    intro g
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
    let proj : X n →ₗ[F] W := Submodule.projectionOnto W C hC
    refine ⟨g.comp proj, ?_⟩
    ext v
    show g (proj v.1) = g v
    rw [Submodule.projectionOnto_apply_left hC v]
  have hann_dim : Module.finrank F (LinearMap.ker res) = n - Module.finrank F W := by
    have hrn := LinearMap.finrank_range_add_finrank_ker res
    rw [LinearMap.range_eq_top.mpr hres_surj, finrank_top, Subspace.dual_finrank_eq,
      Subspace.dual_finrank_eq, Module.finrank_fin_fun] at hrn
    have hle : Module.finrank F W ≤ n := by
      have := Submodule.finrank_le W
      rwa [Module.finrank_fin_fun] at this
    omega
  let φ : orthSub f hquad W →ₗ[F] (X n →ₗ[F] F) := (Blin f hquad).comp (orthSub f hquad W).subtype
  have hrange_sub : LinearMap.range φ ≤ LinearMap.ker res := by
    rintro _ ⟨u, rfl⟩
    exact u.2
  have hkerφ : Module.finrank F (LinearMap.ker φ) = Module.finrank F R0 := by
    let e : LinearMap.ker φ ≃ₗ[F] R0 :=
      { toFun := fun u => ⟨u.1.1, u.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun u => ⟨⟨u.1, by
          rw [orthSub, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp u.2, map_zero]⟩,
          u.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hrnφ : Module.finrank F (LinearMap.range φ) + Module.finrank F (LinearMap.ker (Blin f hquad)) =
      Module.finrank F (orthSub f hquad W) := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hkerφ] at h
    exact h
  have hrange_le : Module.finrank F (LinearMap.range φ) ≤ n - Module.finrank F W := by
    rw [← hann_dim]
    exact Submodule.finrank_mono hrange_sub
  refine ⟨by omega, ?_⟩
  intro heq ℓ hℓ
  have hℓker : ℓ ∈ LinearMap.ker res := by
    rw [LinearMap.mem_ker]
    ext ⟨v, hv⟩
    exact hℓ v hv
  have hrange_eq : LinearMap.range φ = LinearMap.ker res :=
    Submodule.eq_of_le_of_finrank_eq hrange_sub (by rw [hann_dim]; omega)
  have hmem : ℓ ∈ LinearMap.range φ := by
    rw [hrange_eq]
    exact hℓker
  obtain ⟨⟨u, hu⟩, hφu⟩ := hmem
  exact ⟨u, hu, hφu⟩

lemma sum_signZ_coset_sq {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (U : Submodule F (X n)) [Fintype U] (x0 : X n) :
    let R := radSub f hquad U
    have : Fintype R := Fintype.ofFinite _
    (∑ u : U, signZ (f (x0 + u.1))) ^ 2 =
      if (∀ w : R, f (x0 + w.1) = f x0) then
        (2 : ℤ) ^ (Module.finrank F U + Module.finrank F R)
      else 0 := by
  dsimp only
  let R := radSub f hquad U
  haveI : Fintype R := Fintype.ofFinite _
  have hsq : (∑ u : U, signZ (f (x0 + u.1))) ^ 2 =
      ∑ w : U, signZ (f (x0 + w.1) + f x0) * ∑ u : U, signZ (Blin f hquad w.1 u.1) := by
    rw [sq, Finset.sum_mul]
    calc
      ∑ u : U, signZ (f (x0 + u.1)) * ∑ v : U, signZ (f (x0 + v.1))
          = ∑ u : U, ∑ v : U, signZ (f (x0 + u.1) + f (x0 + v.1)) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro v _
            rw [signZ_add]
      _ = ∑ u : U, ∑ w : U, signZ (f (x0 + u.1) + f (x0 + (u.1 + w.1))) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            symm
            refine Fintype.sum_equiv (Equiv.addLeft u) _ _ ?_
            intro w
            rfl
      _ = ∑ w : U, ∑ u : U, signZ ((f (x0 + w.1) + f x0) + Blin f hquad w.1 u.1) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro w _
            refine Finset.sum_congr rfl ?_
            intro u _
            congr 1
            have hq := hquad x0 u.1 w.1
            have h1 : x0 + (u.1 + w.1) = x0 + u.1 + w.1 := (add_assoc x0 u.1 w.1).symm
            rw [h1]
            have hsym : Blin f hquad w.1 u.1 = Blin f hquad u.1 w.1 := B_symm f w.1 u.1
            rw [hsym]
            change f (x0 + u.1) + f (x0 + u.1 + w.1) =
              f (x0 + w.1) + f x0 + (f (u.1 + w.1) + f u.1 + f w.1 + f 0)
            rw [← hq]
            have ha := zmod2_add_self (f (x0 + u.1))
            have hb := zmod2_add_self (f (x0 + w.1))
            have hc := zmod2_add_self (f x0)
            calc
              f (x0 + u.1) + f (x0 + u.1 + w.1)
                  = (f (x0 + w.1) + f (x0 + w.1)) + (f x0 + f x0) +
                      (f (x0 + u.1) + f (x0 + u.1 + w.1)) := by rw [hb, hc, zero_add, zero_add]
              _ = f (x0 + w.1) + f x0 +
                    (f (x0 + u.1 + w.1) + f (x0 + u.1) + f (x0 + w.1) + f x0) := by ring
      _ = ∑ w : U, signZ (f (x0 + w.1) + f x0) * ∑ u : U, signZ (Blin f hquad w.1 u.1) := by
            refine Finset.sum_congr rfl ?_
            intro w _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro u _
            rw [signZ_add]
  rw [hsq]
  have hinner : ∀ w : U, (∑ u : U, signZ (Blin f hquad w.1 u.1)) =
      letI : Decidable (w.1 ∈ R) := Classical.propDecidable _
      if w.1 ∈ R then (Fintype.card U : ℤ) else 0 := by
    intro w
    let ℓw : U →ₗ[F] F := (Blin f hquad w.1).comp U.subtype
    have h1 := sum_signZ_linear ℓw
    have hiff : ℓw = 0 ↔ w.1 ∈ R := by
      constructor
      · intro h0
        refine ⟨w.2, (mem_orthSub f hquad U w.1).mpr ?_⟩
        intro v hv
        exact LinearMap.congr_fun h0 ⟨v, hv⟩
      · intro hwR
        apply LinearMap.ext
        intro v
        exact (mem_orthSub f hquad U w.1).mp hwR.2 v.1 v.2
    by_cases hwR : w.1 ∈ R
    · rw [if_pos hwR]
      rw [if_pos (hiff.mpr hwR)] at h1
      exact h1
    · rw [if_neg hwR]
      rw [if_neg (fun h => hwR (hiff.mp h))] at h1
      exact h1
  have hsum_R : (∑ w : U, signZ (f (x0 + w.1) + f x0) * ∑ u : U, signZ (Blin f hquad w.1 u.1)) =
      (Fintype.card U : ℤ) * ∑ w : R, signZ (f (x0 + w.1) + f x0) := by
    classical
    simp_rw [hinner]
    rw [Finset.mul_sum]
    have hfilt : (∑ w : U, signZ (f (x0 + w.1) + f x0) * if w.1 ∈ R then (Fintype.card U : ℤ) else 0) =
        ∑ w ∈ Finset.univ.filter (fun w : U => w.1 ∈ R),
          (Fintype.card U : ℤ) * signZ (f (x0 + w.1) + f x0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro w _
      split_ifs <;> ring
    rw [hfilt]
    refine Finset.sum_bij (fun w hw => ⟨w.1, (Finset.mem_filter.mp hw).2⟩) ?_ ?_ ?_ ?_
    · intro w _; exact Finset.mem_univ _
    · intro w1 _ w2 _ h
      exact Subtype.ext (congrArg (fun r : R => r.1) h)
    · intro r _
      exact ⟨⟨r.1, r.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩, rfl⟩
    · intro w _; rfl
  rw [hsum_R]
  let ℓR : R →ₗ[F] F :=
    { toFun := fun w => f (x0 + w.1) + f x0
      map_add' := fun a b => by
        have hq := hquad x0 a.1 b.1
        have hB0 : Blin f hquad a.1 b.1 = 0 := (mem_orthSub f hquad U a.1).mp a.2.2 b.1 b.2.1
        have h1 : x0 + (a.1 + b.1) = x0 + a.1 + b.1 := (add_assoc x0 a.1 b.1).symm
        change f (x0 + (a.1 + b.1)) + f x0 = (f (x0 + a.1) + f x0) + (f (x0 + b.1) + f x0)
        rw [h1]
        have h2 : f (x0 + a.1 + b.1) + f (x0 + a.1) + f (x0 + b.1) + f x0 = 0 := hq.trans hB0
        have h3 := zmod2_add_eq_zero (a := f (x0 + a.1 + b.1) + f x0)
          (b := (f (x0 + a.1) + f x0) + (f (x0 + b.1) + f x0))
          (by
            have h00 := zmod2_add_self (f x0)
            calc
              f (x0 + a.1 + b.1) + f x0 + ((f (x0 + a.1) + f x0) + (f (x0 + b.1) + f x0))
                  = (f (x0 + a.1 + b.1) + f (x0 + a.1) + f (x0 + b.1) + f x0) + (f x0 + f x0) := by ring
              _ = 0 := by rw [h2, h00, add_zero])
        exact h3
      map_smul' := fun c a => by
        fin_cases c
        · change f (x0 + (0 : F) • a.1) + f x0 = (0 : F) * (f (x0 + a.1) + f x0)
          rw [zero_smul, add_zero, zero_mul, zmod2_add_self]
        · change f (x0 + (1 : F) • a.1) + f x0 = (1 : F) * (f (x0 + a.1) + f x0)
          rw [one_smul, one_mul] }
  have hℓR := sum_signZ_linear ℓR
  have hiffR : ℓR = 0 ↔ ∀ w : R, f (x0 + w.1) = f x0 := by
    constructor
    · intro h0 w
      have := LinearMap.congr_fun h0 w
      exact zmod2_add_eq_zero this
    · intro hall
      apply LinearMap.ext
      intro w
      change f (x0 + w.1) + f x0 = 0
      rw [hall w, zmod2_add_self]
  rw [show (∑ w : R, signZ (f (x0 + w.1) + f x0)) = ∑ w : R, signZ (ℓR w) from rfl, hℓR]
  split_ifs with h1 h2 h2
  · rw [card_sub_eq_pow U, card_sub_eq_pow R]
    push_cast
    rw [← pow_add]
  · exact absurd (hiffR.mp h1) h2
  · exact absurd (hiffR.mpr h2) h1
  · simp

open scoped Classical in
lemma abs_sum_signZ_coset_le {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (U : Submodule F (X n)) [Fintype U] (x0 : X n) :
    let R := radSub f hquad U
    let q := (Module.finrank F U - Module.finrank F R) / 2
    |∑ u : U, signZ (f (x0 + u.1))| ≤
      if (∀ w : R, f (x0 + w.1) = f x0) then (2 : ℤ) ^ (Module.finrank F U - q) else 0 := by
  dsimp only
  let R := radSub f hquad U
  have : Fintype R := Fintype.ofFinite _
  have hsq := sum_signZ_coset_sq f hquad U x0
  dsimp only at hsq
  have hU_le : Module.finrank F U ≤ n := by
    have := Submodule.finrank_le U
    rwa [Module.finrank_fin_fun] at this
  have hR_le : Module.finrank F R ≤ Module.finrank F U := Submodule.finrank_mono inf_le_left
  have hev := even_finrank_sub_rad f hquad n U hU_le
  rcases hev with ⟨t, ht⟩
  have ht' : Module.finrank F U - Module.finrank F R = t + t := ht
  split_ifs with hall
  · rw [if_pos hall] at hsq
    have hexp : Module.finrank F U + Module.finrank F R =
        2 * (Module.finrank F U - (Module.finrank F U - Module.finrank F R) / 2) := by omega
    rw [hexp, pow_mul'] at hsq
    have hsq2 : |∑ u : U, signZ (f (x0 + u.1))| ^ 2 =
        ((2 : ℤ) ^ (Module.finrank F U - (Module.finrank F U - Module.finrank F R) / 2)) ^ 2 := by
      rw [sq_abs, hsq, pow_two]
    have hnonneg : 0 ≤ (2 : ℤ) ^ (Module.finrank F U - (Module.finrank F U - Module.finrank F R) / 2) :=
      pow_nonneg (by norm_num) _
    have habs : |∑ u : U, signZ (f (x0 + u.1))| =
        (2 : ℤ) ^ (Module.finrank F U - (Module.finrank F U - Module.finrank F R) / 2) := by
      nlinarith [abs_nonneg (∑ u : U, signZ (f (x0 + u.1)))]
    exact le_of_eq habs
  · rw [if_neg hall] at hsq
    have h0 : (∑ u : U, signZ (f (x0 + u.1))) = 0 := sq_eq_zero_iff.mp hsq
    simp [h0]

open scoped Classical in
lemma cell_tail_excess_bound {n e : ℕ} (he : 0 < e) (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (W : Submodule F (X n)) [Fintype W] (x0 : X n)
    (L : X n →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F) :
    let p := (Module.finrank F W - Module.finrank F (radSub f hquad W)) / 2
    let hits := ((Finset.univ : Finset W).filter (fun w => out (L (x0 + w.1)) = f (x0 + w.1))).card
    (2 * hits : ℤ) - (2 : ℤ) ^ Module.finrank F W ≤
      (2 : ℤ) ^ (Module.finrank F W - p +
        min p (if ∀ u ∈ radSub f hquad W, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2)) := by
  classical
  dsimp only
  let p := (Module.finrank F W - Module.finrank F (radSub f hquad W)) / 2
  let LW : W →ₗ[F] (Fin e → F) := L.comp W.subtype
  let U : Submodule F (X n) := (LinearMap.ker LW).map W.subtype
  haveI : Fintype U := Fintype.ofFinite _
  have hU_le_W : U ≤ W := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  have hU_mem : ∀ w : W, w.1 ∈ U ↔ L w.1 = 0 := by
    intro w
    constructor
    · rintro ⟨w', hw', heq⟩
      have : w' = w := Subtype.ext heq
      rw [← this]
      exact hw'
    · intro h0
      exact ⟨w, h0, rfl⟩
  let d := Module.finrank F W - Module.finrank F U
  have hd_le_e : d ≤ e := by
    have hrn := LinearMap.finrank_range_add_finrank_ker LW
    have hrange : Module.finrank F (LinearMap.range LW) ≤ e := by
      have := Submodule.finrank_le (LinearMap.range LW)
      rwa [Module.finrank_fin_fun] at this
    have hmap : Module.finrank F U = Module.finrank F (LinearMap.ker LW) :=
      (Submodule.equivMapOfInjective W.subtype Subtype.val_injective (LinearMap.ker LW)).finrank_eq.symm
    omega
  have hhits_eq :
      (2 * ((Finset.univ : Finset W).filter (fun w => out (L (x0 + w.1)) = f (x0 + w.1))).card : ℤ) -
        (2 : ℤ) ^ Module.finrank F W =
      ∑ w : W, signZ (out (L (x0 + w.1)) + f (x0 + w.1)) := by
    have hcardW : (Fintype.card W : ℤ) = (2 : ℤ) ^ Module.finrank F W := by
      rw [card_sub_eq_pow W]; push_cast; rfl
    rw [← hcardW]
    have hterm : ∀ w : W, signZ (out (L (x0 + w.1)) + f (x0 + w.1)) =
        (if out (L (x0 + w.1)) = f (x0 + w.1) then 2 else 0) - 1 := by
      intro w
      by_cases h : out (L (x0 + w.1)) = f (x0 + w.1)
      · rw [if_pos h, h, zmod2_add_self]
        rfl
      · rw [if_neg h]
        have hne : out (L (x0 + w.1)) + f (x0 + w.1) ≠ 0 := fun h0 => h (zmod2_add_eq_zero h0)
        rw [zmod2_ne_zero_eq_one hne]
        rfl
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_comm _ (2 : ℤ)]
  rw [hhits_eq]
  let RU := radSub f hquad U
  let RW := radSub f hquad W
  haveI : Fintype RU := Fintype.ofFinite _
  haveI : Fintype RW := Fintype.ofFinite _
  let q := (Module.finrank F U - Module.finrank F RU) / 2
  have hfib : (∑ w : W, signZ (out (L (x0 + w.1)) + f (x0 + w.1))) =
      ∑ t : Fin e → F, ∑ w ∈ Finset.univ.filter (fun w : W => L w.1 = t),
        signZ (out (L x0 + t) + f (x0 + w.1)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : W => L w.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl ?_
    intro t _
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [map_add, (Finset.mem_filter.mp hw).2]
  rw [hfib]
  let goodT : Finset (Fin e → F) := Finset.univ.filter (fun t =>
    ∃ w0 : W, L w0.1 = t ∧ ∀ u : RU, f (x0 + w0.1 + u.1) = f (x0 + w0.1))
  have hfib_le : ∀ t : Fin e → F,
      (∑ w ∈ Finset.univ.filter (fun w : W => L w.1 = t),
        signZ (out (L x0 + t) + f (x0 + w.1))) ≤
      if t ∈ goodT then (2 : ℤ) ^ (Module.finrank F U - q) else 0 := by
    intro t
    by_cases hne : (Finset.univ.filter (fun w : W => L w.1 = t)).Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      have hw0t : L w0.1 = t := (Finset.mem_filter.mp hw0).2
      have hshift :
          (∑ w ∈ Finset.univ.filter (fun w : W => L w.1 = t),
            signZ (out (L x0 + t) + f (x0 + w.1))) =
          signZ (out (L x0 + t)) * ∑ u : U, signZ (f ((x0 + w0.1) + u.1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun w hw => ⟨w.1 + w0.1, (hU_mem ⟨w.1 + w0.1, W.add_mem w.2 w0.2⟩).mpr
          (by rw [map_add, (Finset.mem_filter.mp hw).2, hw0t, zmod2_vec_add_self])⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro w1 _ w2 _ h
          have h1 : w1.1 + w0.1 = w2.1 + w0.1 := congrArg Subtype.val h
          exact Subtype.ext (add_right_cancel h1)
        · intro u _
          have huW : u.1 ∈ W := hU_le_W u.2
          refine ⟨⟨u.1 + w0.1, W.add_mem huW w0.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              rw [map_add, (hU_mem ⟨u.1, huW⟩).mp u.2, hw0t, zero_add]⟩, ?_⟩
          apply Subtype.ext
          dsimp only
          rw [add_assoc, zmod2_vec_add_self w0.1, add_zero]
        · intro w _
          rw [← signZ_add]
          congr 2
          have h1 : x0 + w0.1 + (w.1 + w0.1) = x0 + w.1 := by
            calc
              x0 + w0.1 + (w.1 + w0.1) = x0 + w.1 + (w0.1 + w0.1) := by abel
              _ = x0 + w.1 := by rw [zmod2_vec_add_self w0.1, add_zero]
          rw [h1]
      rw [hshift]
      have habs := abs_sum_signZ_coset_le f hquad U (x0 + w0.1)
      dsimp only at habs
      have hsign : |signZ (out (L x0 + t)) * ∑ u : U, signZ (f (x0 + w0.1 + u.1))| =
          |∑ u : U, signZ (f (x0 + w0.1 + u.1))| := by
        rw [abs_mul]
        have : |signZ (out (L x0 + t))| = 1 := by
          rcases zmod2_eq_zero_or_one (out (L x0 + t)) with h | h <;> rw [h] <;> norm_num [signZ]
        rw [this, one_mul]
      have hle_abs : signZ (out (L x0 + t)) * ∑ u : U, signZ (f (x0 + w0.1 + u.1)) ≤
          |∑ u : U, signZ (f (x0 + w0.1 + u.1))| := by
        rw [← hsign]
        exact le_abs_self _
      split_ifs with ht_good
      · by_cases hall : ∀ u : RU, f (x0 + w0.1 + u.1) = f (x0 + w0.1)
        · rw [if_pos hall] at habs
          exact le_trans hle_abs habs
        · rw [if_neg hall] at habs
          exact le_trans (le_trans hle_abs habs) (pow_nonneg (by norm_num) _)
      · have hnot : ¬ ∀ u : RU, f (x0 + w0.1 + u.1) = f (x0 + w0.1) := by
          intro hall
          apply ht_good
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, w0, hw0t, hall⟩
        rw [if_neg hnot] at habs
        exact le_trans hle_abs habs
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]
      split_ifs
      · exact pow_nonneg (by norm_num) _
      · exact le_refl 0
  have hsum_le : (∑ t : Fin e → F, ∑ w ∈ Finset.univ.filter (fun w : W => L w.1 = t),
      signZ (out (L x0 + t) + f (x0 + w.1))) ≤
      (goodT.card : ℤ) * (2 : ℤ) ^ (Module.finrank F U - q) := by
    calc
      (∑ t : Fin e → F, ∑ w ∈ Finset.univ.filter (fun w : W => L w.1 = t),
          signZ (out (L x0 + t) + f (x0 + w.1)))
          ≤ ∑ t : Fin e → F, if t ∈ goodT then (2 : ℤ) ^ (Module.finrank F U - q) else 0 :=
            Finset.sum_le_sum (fun t _ => hfib_le t)
      _ = (goodT.card : ℤ) * (2 : ℤ) ^ (Module.finrank F U - q) := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  refine le_trans hsum_le ?_
  by_cases hgood_empty : goodT = ∅
  · rw [hgood_empty, Finset.card_empty]
    simp only [Nat.cast_zero, zero_mul]
    exact pow_nonneg (by norm_num) _
  · obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.mpr hgood_empty
    obtain ⟨w0, hw0t, hw0all⟩ := (Finset.mem_filter.mp ht0).2
    let Ψ : W →ₗ[F] (RU →ₗ[F] F) := (LinearMap.lcomp F F RU.subtype).comp ((Blin f hquad).comp W.subtype)
    have hkerΨ_ge_U : LinearMap.ker LW ≤ LinearMap.ker Ψ := by
      intro w hw
      rw [LinearMap.mem_ker]
      ext u
      show Blin f hquad w.1 u.1 = 0
      rw [Blin_symm f hquad w.1 u.1]
      exact (mem_orthSub f hquad U u.1).mp u.2.2 w.1 ((hU_mem w).mpr hw)
    have hcard_goodT : goodT.card ≤ 2 ^ (Module.finrank F (LinearMap.ker Ψ) - Module.finrank F U) := by
      let K : Submodule F W := LinearMap.ker Ψ
      haveI : Fintype K := Fintype.ofFinite _
      let imgK : Finset (Fin e → F) := Finset.univ.image (fun w : K => L (w0.1 + w.1.1))
      have hsub : goodT ⊆ imgK := by
        intro t ht
        obtain ⟨w1, hw1t, hw1all⟩ := (Finset.mem_filter.mp ht).2
        have hwdiff : w1 + w0 ∈ K := by
          rw [LinearMap.mem_ker]
          ext u
          show Blin f hquad (w1.1 + w0.1) u.1 = 0
          have h1 : f (x0 + w1.1 + u.1) = f (x0 + w1.1) := hw1all u
          have h2 : f (x0 + w0.1 + u.1) = f (x0 + w0.1) := hw0all u
          have hq1 := hquad x0 w1.1 u.1
          have hq2 := hquad x0 w0.1 u.1
          have hB1 : Blin f hquad w1.1 u.1 = f (x0 + u.1) + f x0 := by
            change f (w1.1 + u.1) + f w1.1 + f u.1 + f 0 = f (x0 + u.1) + f x0
            rw [← hq1, h1]
            have ha := zmod2_add_self (f (x0 + w1.1))
            calc
              f (x0 + w1.1) + f (x0 + w1.1) + f (x0 + u.1) + f x0
                  = (f (x0 + w1.1) + f (x0 + w1.1)) + (f (x0 + u.1) + f x0) := by ring
              _ = f (x0 + u.1) + f x0 := by rw [ha, zero_add]
          have hB2 : Blin f hquad w0.1 u.1 = f (x0 + u.1) + f x0 := by
            change f (w0.1 + u.1) + f w0.1 + f u.1 + f 0 = f (x0 + u.1) + f x0
            rw [← hq2, h2]
            have ha := zmod2_add_self (f (x0 + w0.1))
            calc
              f (x0 + w0.1) + f (x0 + w0.1) + f (x0 + u.1) + f x0
                  = (f (x0 + w0.1) + f (x0 + w0.1)) + (f (x0 + u.1) + f x0) := by ring
              _ = f (x0 + u.1) + f x0 := by rw [ha, zero_add]
          rw [map_add, LinearMap.add_apply, hB1, hB2, zmod2_add_self]
        refine Finset.mem_image.mpr ⟨⟨w1 + w0, hwdiff⟩, Finset.mem_univ _, ?_⟩
        show L (w0.1 + (w1.1 + w0.1)) = t
        have : w0.1 + (w1.1 + w0.1) = w1.1 := by
          calc
            w0.1 + (w1.1 + w0.1) = w1.1 + (w0.1 + w0.1) := by abel
            _ = w1.1 := by rw [zmod2_vec_add_self w0.1, add_zero]
        rw [this, hw1t]
      have hcard_img : imgK.card ≤ 2 ^ (Module.finrank F K - Module.finrank F U) := by
        let K0 : Submodule F (X n) := Submodule.map W.subtype K
        have hK0_dim : Module.finrank F K0 = Module.finrank F K :=
          (Submodule.equivMapOfInjective W.subtype W.injective_subtype K).finrank_eq.symm
        let LWK : K0 →ₗ[F] (Fin e → F) := L.comp K0.subtype
        have hkerLWK : Module.finrank F (LinearMap.ker LWK) = Module.finrank F U := by
          let eK : LinearMap.ker LWK ≃ₗ[F] U :=
            { toFun := fun x => ⟨x.1.1, by
                rcases x.1.2 with ⟨w, _, hw_eq⟩
                rw [← hw_eq]
                exact (hU_mem w).mpr (by change L (W.subtype w) = 0; rw [hw_eq]; exact x.2)⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              invFun := fun u => ⟨⟨u.1, ⟨⟨u.1, hU_le_W u.2⟩,
                hkerΨ_ge_U ((hU_mem ⟨u.1, hU_le_W u.2⟩).mp u.2), rfl⟩⟩,
                (hU_mem ⟨u.1, hU_le_W u.2⟩).mp u.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          exact eK.finrank_eq
        have hrnK := LinearMap.finrank_range_add_finrank_ker LWK
        rw [hkerLWK, hK0_dim] at hrnK
        have hrangeK : Module.finrank F (LinearMap.range LWK) =
            Module.finrank F K - Module.finrank F U := by omega
        haveI : Fintype (LinearMap.range LWK) := Fintype.ofFinite _
        have hcardR : Fintype.card (LinearMap.range LWK) =
            2 ^ (Module.finrank F K - Module.finrank F U) := by
          have h1 := Module.card_eq_pow_finrank (K := F) (V := LinearMap.range LWK)
          have h2 : Fintype.card F = 2 := ZMod.card 2
          rw [h2, hrangeK] at h1
          exact h1
        rw [← hcardR]
        have himg_eq : imgK = Finset.univ.image (fun y : LinearMap.range LWK => L w0.1 + y.1) := by
          ext t
          simp only [imgK, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨w, rfl⟩
            exact ⟨⟨LWK ⟨w.1.1, ⟨w.1, w.2, rfl⟩⟩, ⟨⟨w.1.1, ⟨w.1, w.2, rfl⟩⟩, rfl⟩⟩,
              (map_add L w0.1 w.1.1).symm⟩
          · rintro ⟨⟨_, ⟨_, w, hwK, rfl⟩, rfl⟩, rfl⟩
            exact ⟨⟨w, hwK⟩, map_add L w0.1 w.1⟩
        rw [himg_eq]
        exact le_trans Finset.card_image_le (by simp)
      exact le_trans (Finset.card_le_card hsub) hcard_img
    have hdim_kerΨ : Module.finrank F (LinearMap.ker Ψ) + Module.finrank F RU =
        Module.finrank F W + Module.finrank F ((RU ⊓ RW : Submodule F (X n))) := by
      let Ψ' : RU →ₗ[F] (W →ₗ[F] F) := (LinearMap.lcomp F F W.subtype).comp ((Blin f hquad).comp RU.subtype)
      have hkerΨ' : Module.finrank F (LinearMap.ker Ψ') =
          Module.finrank F ((RU ⊓ RW : Submodule F (X n))) := by
        let eR : LinearMap.ker Ψ' ≃ₗ[F] ((RU ⊓ RW : Submodule F (X n))) :=
          { toFun := fun u => ⟨u.1.1, ⟨u.1.2, ⟨hU_le_W u.1.2.1, (mem_orthSub f hquad W u.1.1).mpr
              (fun v hv => LinearMap.congr_fun u.2 ⟨v, hv⟩)⟩⟩⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun u => ⟨⟨u.1, u.2.1⟩, by
              rw [LinearMap.mem_ker]
              ext v
              exact (mem_orthSub f hquad W u.1).mp u.2.2.2 v.1 v.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        exact eR.finrank_eq
      have hrange_eq : Module.finrank F (LinearMap.range Ψ) = Module.finrank F (LinearMap.range Ψ') := by
        let bW := Module.finBasis F W
        let bR := Module.finBasis F RU
        let M : Matrix (Fin (Module.finrank F RU)) (Fin (Module.finrank F W)) F :=
          fun i j => Blin f hquad (bW j).1 (bR i).1
        have hΨ_rank : Module.finrank F (LinearMap.range Ψ) = Matrix.rank M := by
          let eW : W ≃ₗ[F] (Fin (Module.finrank F W) → F) := bW.equivFun
          let eR : (RU →ₗ[F] F) ≃ₗ[F] (Fin (Module.finrank F RU) → F) :=
            { toFun := fun φ i => φ (bR i)
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              invFun := fun v => bR.constr F v
              left_inv := fun φ => by
                apply bR.ext
                intro i
                simp
              right_inv := fun v => by
                ext i
                simp }
          have hcomm : eR.toLinearMap.comp (Ψ.comp eW.symm.toLinearMap) = M.mulVecLin := by
            apply LinearMap.ext
            intro v
            ext i
            simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, eR, eW, Ψ,
              LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M,
              LinearMap.lcomp_apply, Submodule.coe_subtype]
            have hv : bW.equivFun.symm v = ∑ j : Fin (Module.finrank F W), v j • bW j := by
              rw [Module.Basis.equivFun_symm_apply]
            rw [hv]
            simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul,
              LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [mul_comm]
          have h1 : Module.finrank F (LinearMap.range M.mulVecLin) = Matrix.rank M := rfl
          have heW_top : LinearMap.range eW.symm.toLinearMap = ⊤ :=
            LinearMap.range_eq_top.mpr eW.symm.surjective
          have hr : LinearMap.range (eR.toLinearMap.comp (Ψ.comp eW.symm.toLinearMap)) =
              Submodule.map eR.toLinearMap (LinearMap.range Ψ) := by
            rw [LinearMap.range_comp, LinearMap.range_comp, heW_top, Submodule.map_top]
          rw [← h1, ← hcomm, hr]
          exact (Submodule.equivMapOfInjective eR.toLinearMap eR.injective _).finrank_eq
        have hΨ'_rank : Module.finrank F (LinearMap.range Ψ') = Matrix.rank M.transpose := by
          let eR : RU ≃ₗ[F] (Fin (Module.finrank F RU) → F) := bR.equivFun
          let eW : (W →ₗ[F] F) ≃ₗ[F] (Fin (Module.finrank F W) → F) :=
            { toFun := fun φ j => φ (bW j)
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              invFun := fun v => bW.constr F v
              left_inv := fun φ => by
                apply bW.ext
                intro j
                simp
              right_inv := fun v => by
                ext j
                simp }
          have hcomm : eW.toLinearMap.comp (Ψ'.comp eR.symm.toLinearMap) = M.transpose.mulVecLin := by
            apply LinearMap.ext
            intro v
            ext j
            simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, eR, eW, Ψ',
              LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
              Matrix.transpose_apply, M, LinearMap.lcomp_apply, Submodule.coe_subtype]
            have hv : bR.equivFun.symm v = ∑ i : Fin (Module.finrank F RU), v i • bR i := by
              rw [Module.Basis.equivFun_symm_apply]
            rw [hv]
            simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul,
              LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            show v i * Blin f hquad (bR i).1 (bW j).1 = Blin f hquad (bW j).1 (bR i).1 * v i
            rw [Blin_symm f hquad (bR i).1 (bW j).1, mul_comm]
          have h1 : Module.finrank F (LinearMap.range M.transpose.mulVecLin) = Matrix.rank M.transpose := rfl
          have heR_top : LinearMap.range eR.symm.toLinearMap = ⊤ :=
            LinearMap.range_eq_top.mpr eR.symm.surjective
          have hr : LinearMap.range (eW.toLinearMap.comp (Ψ'.comp eR.symm.toLinearMap)) =
              Submodule.map eW.toLinearMap (LinearMap.range Ψ') := by
            rw [LinearMap.range_comp, LinearMap.range_comp, heR_top, Submodule.map_top]
          rw [← h1, ← hcomm, hr]
          exact (Submodule.equivMapOfInjective eW.toLinearMap eW.injective _).finrank_eq
        rw [hΨ_rank, hΨ'_rank, Matrix.rank_transpose]
      have hrn1 := LinearMap.finrank_range_add_finrank_ker Ψ
      have hrn2 := LinearMap.finrank_range_add_finrank_ker Ψ'
      rw [hkerΨ'] at hrn2
      omega
    have hU_le_W_dim : Module.finrank F U ≤ Module.finrank F W := Submodule.finrank_mono hU_le_W
    have hRU_le_U : Module.finrank F RU ≤ Module.finrank F U := Submodule.finrank_mono inf_le_left
    have hRW_le_W : Module.finrank F RW ≤ Module.finrank F W := Submodule.finrank_mono inf_le_left
    have hinf_le_RU : Module.finrank F ((RU ⊓ RW : Submodule F (X n))) ≤ Module.finrank F RU :=
      Submodule.finrank_mono inf_le_left
    have hinf_le_RW : Module.finrank F ((RU ⊓ RW : Submodule F (X n))) ≤ Module.finrank F RW :=
      Submodule.finrank_mono inf_le_right
    have hW_le_n : Module.finrank F W ≤ n := by
      have := Submodule.finrank_le W
      rwa [Module.finrank_fin_fun] at this
    have hevW := even_finrank_sub_rad f hquad n W hW_le_n
    have hevU := even_finrank_sub_rad f hquad n U (le_trans hU_le_W_dim hW_le_n)
    rcases hevW with ⟨tw, htw⟩
    rcases hevU with ⟨tu, htu⟩
    have htw' : Module.finrank F W - Module.finrank F RW = tw + tw := htw
    have htu' : Module.finrank F U - Module.finrank F RU = tu + tu := htu
    have hkerΨ_ge_U_dim : Module.finrank F U ≤ Module.finrank F (LinearMap.ker Ψ) := by
      have h1 := Submodule.finrank_mono hkerΨ_ge_U
      have hmap : Module.finrank F U = Module.finrank F (LinearMap.ker LW) :=
        (Submodule.equivMapOfInjective W.subtype Subtype.val_injective (LinearMap.ker LW)).finrank_eq.symm
      omega
    have hexp_bound :
        (Module.finrank F (LinearMap.ker Ψ) - Module.finrank F U) + (Module.finrank F U - q) ≤
          Module.finrank F W - p +
            min p (if ∀ u ∈ RW, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2) := by
      split_ifs with hclearW
      · omega
      · have hne_inf : Module.finrank F ((RU ⊓ RW : Submodule F (X n))) < Module.finrank F RW := by
          by_contra hge
          have heq_inf : (RU ⊓ RW : Submodule F (X n)) = RW :=
            Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
          have hRW_le_RU : RW ≤ RU := by rw [← heq_inf]; exact inf_le_left
          apply hclearW
          intro u huRW
          have huRU : u ∈ RU := hRW_le_RU huRW
          have h1 : f (x0 + w0.1 + u) = f (x0 + w0.1) := hw0all ⟨u, huRU⟩
          have hq := hquad x0 w0.1 u
          have hB0 : Blin f hquad w0.1 u = 0 := by
            rw [Blin_symm f hquad w0.1 u]
            exact (mem_orthSub f hquad W u).mp huRW.2 w0.1 w0.2
          have h2 : f (x0 + w0.1 + u) + f (x0 + w0.1) + f (x0 + u) + f x0 = 0 := hq.trans hB0
          rw [h1] at h2
          have h3 : f (x0 + u) + f x0 = 0 := by
            have ha := zmod2_add_self (f (x0 + w0.1))
            calc
              f (x0 + u) + f x0 = (f (x0 + w0.1) + f (x0 + w0.1)) + (f (x0 + u) + f x0) := by
                rw [ha, zero_add]
              _ = f (x0 + w0.1) + f (x0 + w0.1) + f (x0 + u) + f x0 := by ring
              _ = 0 := h2
          exact zmod2_add_eq_zero h3
        omega
    calc
      (goodT.card : ℤ) * (2 : ℤ) ^ (Module.finrank F U - q)
          ≤ ((2 : ℤ) ^ (Module.finrank F (LinearMap.ker Ψ) - Module.finrank F U)) *
              (2 : ℤ) ^ (Module.finrank F U - q) := by
            have h1 : (goodT.card : ℤ) ≤
                (2 : ℤ) ^ (Module.finrank F (LinearMap.ker Ψ) - Module.finrank F U) := by
              exact_mod_cast hcard_goodT
            exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (by norm_num) _)
      _ = (2 : ℤ) ^ ((Module.finrank F (LinearMap.ker Ψ) - Module.finrank F U) +
            (Module.finrank F U - q)) := (pow_add _ _ _).symm
      _ ≤ (2 : ℤ) ^ (Module.finrank F W - p +
            min p (if ∀ u ∈ RW, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2)) :=
            pow_le_pow_right₀ (by norm_num) hexp_bound

lemma exists_symplectic_normal_form {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0) :
    let R0 := LinearMap.ker (Blin f hquad)
    ∃ (m : ℕ) (α β : Fin m → (X n →ₗ[F] F)) (c d : Fin m → F) (ℓ0 : X n →ₗ[F] F) (c0 : F),
      (2 * m = n - Module.finrank F R0) ∧
      (Function.Surjective (fun x : X n => (fun i => α i x, fun i => β i x))) ∧
      (∀ u ∈ R0, ∀ i : Fin m, α i u = 0 ∧ β i u = 0) ∧
      (∀ u ∈ R0, ℓ0 u = f u + f 0) ∧
      ((∀ u ∈ R0, f u = f 0) → ℓ0 = 0) ∧
      (∀ x : X n, f x = c0 + ℓ0 x + ∑ i : Fin m, (α i x + c i) * (β i x + d i)) := by
  dsimp only
  have hbuild : ∀ (k : ℕ) (W : Submodule F (X n)),
      Module.finrank F W - Module.finrank F (radSub f hquad W) = 2 * k →
      ∃ (u v : Fin k → X n),
        (∀ i, u i ∈ W ∧ v i ∈ W) ∧
        (∀ i j, Blin f hquad (u i) (u j) = 0 ∧ Blin f hquad (v i) (v j) = 0 ∧
          Blin f hquad (u i) (v j) = if i = j then 1 else 0) := by
    intro k
    induction k with
    | zero =>
      intro W _
      exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro W hdim
      have hne : radSub f hquad W ≠ W := by
        intro heq
        rw [heq, Nat.sub_self] at hdim
        omega
      have hex : ∃ u0 ∈ W, ∃ v0 ∈ W, Blin f hquad u0 v0 ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne
        apply le_antisymm inf_le_left
        intro u hu
        refine ⟨hu, (mem_orthSub f hquad W u).mpr ?_⟩
        intro v hv
        exact hall u hu v hv
      obtain ⟨u0, hu0W, v0, hv0W, huv_ne⟩ := hex
      have huv : Blin f hquad u0 v0 = 1 := zmod2_ne_zero_eq_one huv_ne
      have hvu : Blin f hquad v0 u0 = 1 := by
        show f (v0 + u0) + f v0 + f u0 + f 0 = 1
        rw [B_symm f v0 u0]
        exact huv
      have huu : Blin f hquad u0 u0 = 0 := B_self f u0
      have hvv : Blin f hquad v0 v0 = 0 := B_self f v0
      let ψ : W →ₗ[F] (F × F) :=
        { toFun := fun x => (Blin f hquad u0 x.1, Blin f hquad v0 x.1)
          map_add' := fun a b => by
            ext
            · exact map_add (Blin f hquad u0) a.1 b.1
            · exact map_add (Blin f hquad v0) a.1 b.1
          map_smul' := fun c a => by
            ext
            · exact map_smul (Blin f hquad u0) c a.1
            · exact map_smul (Blin f hquad v0) c a.1 }
      have hsurj : Function.Surjective ψ := by
        rintro ⟨a, b⟩
        refine ⟨⟨b • u0 + a • v0, W.add_mem (W.smul_mem b hu0W) (W.smul_mem a hv0W)⟩, ?_⟩
        ext
        · show Blin f hquad u0 (b • u0 + a • v0) = a
          rw [map_add, map_smul, map_smul, huu, huv]; simp
        · show Blin f hquad v0 (b • u0 + a • v0) = b
          rw [map_add, map_smul, map_smul, hvu, hvv]; simp
      let W' : Submodule F (X n) := (LinearMap.ker ψ).map W.subtype
      have hW'_le : W' ≤ W := by rintro _ ⟨x, _, rfl⟩; exact x.2
      have hdim_W' : Module.finrank F W' + 2 = Module.finrank F W := by
        have hrn := LinearMap.finrank_range_add_finrank_ker ψ
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn
        have hff : Module.finrank F (F × F) = 2 := by rw [Module.finrank_prod, Module.finrank_self]
        rw [hff] at hrn
        have hmap : Module.finrank F W' = Module.finrank F (LinearMap.ker ψ) :=
          (Submodule.equivMapOfInjective W.subtype Subtype.val_injective (LinearMap.ker ψ)).finrank_eq.symm
        omega
      have hrad_eq : radSub f hquad W' = radSub f hquad W := by
        apply le_antisymm
        · intro w hw
          rcases hw with ⟨hwW', hw_orth⟩
          have hwW : w ∈ W := hW'_le hwW'
          rcases hwW' with ⟨⟨w1, hw1W⟩, hw1ker, rfl⟩
          have hw_u : Blin f hquad u0 w1 = 0 := congrArg Prod.fst hw1ker
          have hw_v : Blin f hquad v0 w1 = 0 := congrArg Prod.snd hw1ker
          refine ⟨hwW, (mem_orthSub f hquad W w1).mpr ?_⟩
          intro x hxW
          let x' : X n := x + Blin f hquad v0 x • u0 + Blin f hquad u0 x • v0
          have hx'W : x' ∈ W := W.add_mem (W.add_mem hxW (W.smul_mem _ hu0W)) (W.smul_mem _ hv0W)
          have hx'ker : ⟨x', hx'W⟩ ∈ LinearMap.ker ψ := by
            rw [LinearMap.mem_ker]; ext
            · show Blin f hquad u0 x' = 0
              simp only [x', map_add, map_smul, huu, huv, smul_eq_mul, mul_zero, mul_one, add_zero]
              exact zmod2_add_self (Blin f hquad u0 x)
            · show Blin f hquad v0 x' = 0
              simp only [x', map_add, map_smul, hvu, hvv, smul_eq_mul, mul_zero, mul_one, add_zero]
              exact zmod2_add_self (Blin f hquad v0 x)
          have h0 : Blin f hquad w1 x' = 0 :=
            (mem_orthSub f hquad W' w1).mp hw_orth x' ⟨⟨x', hx'W⟩, hx'ker, rfl⟩
          have hwu0 : Blin f hquad w1 u0 = 0 := by rw [Blin_symm f hquad w1 u0]; exact hw_u
          have hwv0 : Blin f hquad w1 v0 = 0 := by rw [Blin_symm f hquad w1 v0]; exact hw_v
          simp only [x', map_add, map_smul, hwu0, hwv0, smul_eq_mul, mul_zero, add_zero] at h0
          exact h0
        · intro w hw
          rcases hw with ⟨hwW, hw_orth⟩
          have hwker : ⟨w, hwW⟩ ∈ LinearMap.ker ψ := by
            rw [LinearMap.mem_ker]; ext
            · show f (u0 + w) + f u0 + f w + f 0 = 0
              rw [B_symm f u0 w]; exact (mem_orthSub f hquad W w).mp hw_orth u0 hu0W
            · show f (v0 + w) + f v0 + f w + f 0 = 0
              rw [B_symm f v0 w]; exact (mem_orthSub f hquad W w).mp hw_orth v0 hv0W
          refine ⟨⟨⟨w, hwW⟩, hwker, rfl⟩, (mem_orthSub f hquad W' w).mpr ?_⟩
          intro x hxW'
          exact (mem_orthSub f hquad W w).mp hw_orth x (hW'_le hxW')
      have hdim' : Module.finrank F W' - Module.finrank F (radSub f hquad W') = 2 * k := by
        rw [hrad_eq]
        have hle : Module.finrank F (radSub f hquad W) ≤ Module.finrank F W' := by
          rw [← hrad_eq]; exact Submodule.finrank_mono inf_le_left
        omega
      obtain ⟨u', v', hmem', hsymp'⟩ := ih W' hdim'
      refine ⟨Fin.cons u0 u', Fin.cons v0 v', ?_, ?_⟩
      · intro i
        refine Fin.cases ⟨hu0W, hv0W⟩ (fun j => ⟨hW'_le (hmem' j).1, hW'_le (hmem' j).2⟩) i
      · intro i j
        refine Fin.cases ?_ ?_ i
        · refine Fin.cases ?_ ?_ j
          · exact ⟨huu, hvv, by simp [huv]⟩
          · intro j'
            rcases (hmem' j').1 with ⟨⟨_, _⟩, hju, hju_eq⟩
            rcases (hmem' j').2 with ⟨⟨_, _⟩, hjv, hjv_eq⟩
            have h1 : Blin f hquad u0 (u' j') = 0 := by rw [← hju_eq]; exact congrArg Prod.fst hju
            have h2 : Blin f hquad v0 (v' j') = 0 := by rw [← hjv_eq]; exact congrArg Prod.snd hjv
            have h3 : Blin f hquad u0 (v' j') = 0 := by rw [← hjv_eq]; exact congrArg Prod.fst hjv
            exact ⟨h1, h2, by simp [h3, (Fin.succ_ne_zero j').symm]⟩
        · intro i'
          refine Fin.cases ?_ ?_ j
          · rcases (hmem' i').1 with ⟨⟨_, _⟩, hiu, hiu_eq⟩
            rcases (hmem' i').2 with ⟨⟨_, _⟩, hiv, hiv_eq⟩
            have h1 : Blin f hquad (u' i') u0 = 0 := by
              rw [Blin_symm f hquad (u' i') u0, ← hiu_eq]; exact congrArg Prod.fst hiu
            have h2 : Blin f hquad (v' i') v0 = 0 := by
              rw [Blin_symm f hquad (v' i') v0, ← hiv_eq]; exact congrArg Prod.snd hiv
            have h3 : Blin f hquad (u' i') v0 = 0 := by
              rw [Blin_symm f hquad (u' i') v0, ← hiu_eq]; exact congrArg Prod.snd hiu
            exact ⟨h1, h2, by simp [h3]⟩
          · intro j'
            simpa [Fin.cons_succ] using hsymp' i' j'
  have hrad_top : radSub f hquad ⊤ = LinearMap.ker (Blin f hquad) := by
    ext u
    rw [radSub, Submodule.mem_inf, mem_orthSub, LinearMap.mem_ker]
    simp only [Submodule.mem_top, true_and, true_imp_iff]
    constructor
    · intro h; apply LinearMap.ext; intro v; exact h v
    · intro h v; exact LinearMap.congr_fun h v
  have hm_even := even_finrank_sub_rad f hquad n ⊤ (by rw [finrank_top, Module.finrank_fin_fun])
  rw [finrank_top, Module.finrank_fin_fun, hrad_top] at hm_even
  rcases hm_even with ⟨t, ht⟩
  have h2m : Module.finrank F (⊤ : Submodule F (X n)) -
      Module.finrank F (radSub f hquad ⊤) =
      2 * ((n - Module.finrank F (LinearMap.ker (Blin f hquad))) / 2) := by
    rw [finrank_top, Module.finrank_fin_fun, hrad_top]
    omega
  obtain ⟨u, v, _, hsymp⟩ := hbuild _ ⊤ h2m
  let m := (n - Module.finrank F (LinearMap.ker (Blin f hquad))) / 2
  let α : Fin m → (X n →ₗ[F] F) := fun i => Blin f hquad (v i)
  let β : Fin m → (X n →ₗ[F] F) := fun i => Blin f hquad (u i)
  have hαu : ∀ i j, α i (u j) = if i = j then 1 else 0 := by
    intro i j
    show Blin f hquad (v i) (u j) = if i = j then 1 else 0
    rw [Blin_symm f hquad (v i) (u j), (hsymp j i).2.2]
    by_cases h : i = j <;> simp [h, eq_comm]
  have hαv : ∀ i j, α i (v j) = 0 := fun i j => (hsymp i j).2.1
  have hβu : ∀ i j, β i (u j) = 0 := fun i j => (hsymp i j).1
  have hβv : ∀ i j, β i (v j) = if i = j then 1 else 0 := fun i j => (hsymp i j).2.2
  let c : Fin m → F := fun i => f (v i) + f 0
  let d : Fin m → F := fun i => f (u i) + f 0
  let c0 : F := f 0 + ∑ i : Fin m, c i * d i
  let π : X n →ₗ[F] X n :=
    { toFun := fun x => x + ∑ i : Fin m, (α i x • u i + β i x • v i)
      map_add' := fun x y => by
        simp only [map_add, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := fun s x => by
        simp [map_smul, mul_smul, smul_add, Finset.smul_sum] }
  have hπR0 : ∀ x : X n, π x ∈ LinearMap.ker (Blin f hquad) := by
    intro x
    have hproj_ker : ∀ i : Fin m, α i (π x) = 0 ∧ β i (π x) = 0 := by
      intro i
      constructor
      · simp only [π, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul, hαu, hαv,
          smul_eq_mul, mul_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte, zmod2_add_self]
      · simp only [π, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul, hβu, hβv,
          smul_eq_mul, mul_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte, zmod2_add_self]
    have hsurj_ab : Function.Surjective (fun y : X n => (fun i => α i y, fun i => β i y)) := by
      rintro ⟨a, b⟩
      refine ⟨∑ i : Fin m, (a i • u i + b i • v i), ?_⟩
      ext i
      · simp [map_sum, map_add, map_smul, hαu, hαv]
      · simp [map_sum, map_add, map_smul, hβu, hβv]
    let ab : X n →ₗ[F] ((Fin m → F) × (Fin m → F)) :=
      { toFun := fun y => (fun i => α i y, fun i => β i y)
        map_add' := fun y1 y2 => by ext i <;> simp [map_add]
        map_smul' := fun s y => by ext i <;> simp [map_smul] }
    have hker_le : LinearMap.ker (Blin f hquad) ≤ LinearMap.ker ab := by
      intro y hy
      rw [LinearMap.mem_ker]
      ext i
      · show Blin f hquad (v i) y = 0
        rw [Blin_symm f hquad (v i) y]; exact LinearMap.congr_fun hy (v i)
      · show Blin f hquad (u i) y = 0
        rw [Blin_symm f hquad (u i) y]; exact LinearMap.congr_fun hy (u i)
    have hdim_ker : Module.finrank F (LinearMap.ker ab) =
        Module.finrank F (LinearMap.ker (Blin f hquad)) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker ab
      rw [LinearMap.range_eq_top.mpr hsurj_ab, finrank_top, Module.finrank_prod,
        Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
      have hR0_le : Module.finrank F (LinearMap.ker (Blin f hquad)) ≤ n := by
        have := Submodule.finrank_le (LinearMap.ker (Blin f hquad))
        rwa [Module.finrank_fin_fun] at this
      omega
    have hker_eq : LinearMap.ker (Blin f hquad) = LinearMap.ker ab :=
      Submodule.eq_of_le_of_finrank_eq hker_le hdim_ker.symm
    rw [hker_eq, LinearMap.mem_ker]
    ext i
    · exact (hproj_ker i).1
    · exact (hproj_ker i).2
  let ℓ0 : X n →ₗ[F] F :=
    { toFun := fun x => f (π x) + f 0
      map_add' := fun x y => by
        rw [map_add]
        have hB0 : Blin f hquad (π x) (π y) = 0 := LinearMap.congr_fun (hπR0 x) (π y)
        change f (π x + π y) + f 0 = (f (π x) + f 0) + (f (π y) + f 0)
        have h1 : f (π x + π y) + f (π x) + f (π y) + f 0 = 0 := hB0
        exact zmod2_add_eq_zero (by
          have h00 := zmod2_add_self (f 0)
          calc
            f (π x + π y) + f 0 + ((f (π x) + f 0) + (f (π y) + f 0))
                = (f (π x + π y) + f (π x) + f (π y) + f 0) + (f 0 + f 0) := by ring
            _ = 0 := by rw [h1, h00, add_zero])
      map_smul' := fun s x => by
        fin_cases s
        · change f (π ((0 : F) • x)) + f 0 = (0 : F) * (f (π x) + f 0)
          rw [zero_smul, map_zero, zero_mul, zmod2_add_self]
        · change f (π ((1 : F) • x)) + f 0 = (1 : F) * (f (π x) + f 0)
          rw [one_smul, one_mul] }
  refine ⟨m, α, β, c, d, ℓ0, c0, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩
    refine ⟨∑ i : Fin m, (a i • u i + b i • v i), ?_⟩
    ext i
    · simp [map_sum, map_add, map_smul, hαu, hαv]
    · simp [map_sum, map_add, map_smul, hβu, hβv]
  · intro w hw i
    constructor
    · show Blin f hquad (v i) w = 0
      rw [Blin_symm f hquad (v i) w]; exact LinearMap.congr_fun hw (v i)
    · show Blin f hquad (u i) w = 0
      rw [Blin_symm f hquad (u i) w]; exact LinearMap.congr_fun hw (u i)
  · intro w hw
    show f (π w) + f 0 = f w + f 0
    have hπw : π w = w := by
      have hα0 : ∀ i, α i w = 0 := fun i => by
        show Blin f hquad (v i) w = 0; rw [Blin_symm f hquad (v i) w]; exact LinearMap.congr_fun hw (v i)
      have hβ0 : ∀ i, β i w = 0 := fun i => by
        show Blin f hquad (u i) w = 0; rw [Blin_symm f hquad (u i) w]; exact LinearMap.congr_fun hw (u i)
      simp [π, hα0, hβ0]
    rw [hπw]
  · intro hclear
    apply LinearMap.ext
    intro x
    show f (π x) + f 0 = 0
    rw [hclear (π x) (hπR0 x), zmod2_add_self]
  · intro x
    let S : X n := ∑ i : Fin m, (α i x • u i + β i x • v i)
    have hx_eq : x = π x + S := by
      simp only [π, S, LinearMap.coe_mk, AddHom.coe_mk]
      rw [add_assoc, zmod2_vec_add_self, add_zero]
    have hfS : f S + f 0 = ∑ i : Fin m, (α i x * d i + β i x * c i + α i x * β i x) := by
      have hind : ∀ (s : Finset (Fin m)),
          f (∑ i ∈ s, (α i x • u i + β i x • v i)) + f 0 =
            ∑ i ∈ s, (α i x * d i + β i x * c i + α i x * β i x) := by
        intro s
        induction s using Finset.induction with
        | empty => simp [zmod2_add_self]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          let T := ∑ i ∈ s, (α i x • u i + β i x • v i)
          let P := α a x • u a + β a x • v a
          have hBPT : Blin f hquad P T = 0 := by
            simp only [P, T, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
              smul_eq_mul]
            refine Finset.sum_eq_zero ?_
            intro j hj
            have haj : a ≠ j := fun h => ha (h ▸ hj)
            have h1 := (hsymp a j).1
            have h2 := (hsymp a j).2.1
            have h3 : Blin f hquad (u a) (v j) = 0 := by rw [(hsymp a j).2.2, if_neg haj]
            have h4 : Blin f hquad (v a) (u j) = 0 := by
              rw [Blin_symm f hquad (v a) (u j), (hsymp j a).2.2, if_neg haj.symm]
            simp [h1, h2, h3, h4]
          have hstep : f (P + T) + f 0 = (f P + f 0) + (f T + f 0) := by
            have h1 : f (P + T) + f P + f T + f 0 = 0 := hBPT
            exact zmod2_add_eq_zero (by
              have h00 := zmod2_add_self (f 0)
              calc
                f (P + T) + f 0 + ((f P + f 0) + (f T + f 0))
                    = (f (P + T) + f P + f T + f 0) + (f 0 + f 0) := by ring
                _ = 0 := by rw [h1, h00, add_zero])
          have hfP : f P + f 0 = α a x * d a + β a x * c a + α a x * β a x := by
            have h1 : f (α a x • u a + β a x • v a) + f (α a x • u a) + f (β a x • v a) + f 0 =
                Blin f hquad (α a x • u a) (β a x • v a) := rfl
            have h2 : Blin f hquad (α a x • u a) (β a x • v a) = α a x * β a x := by
              rw [map_smul, map_smul, LinearMap.smul_apply, (hsymp a a).2.2, if_pos rfl]
              simp [smul_eq_mul, mul_comm]
            have hu_eval : f (α a x • u a) + f 0 = α a x * d a := by
              rcases zmod2_eq_zero_or_one (α a x) with h | h <;> rw [h] <;> simp [d, zmod2_add_self]
            have hv_eval : f (β a x • v a) + f 0 = β a x * c a := by
              rcases zmod2_eq_zero_or_one (β a x) with h | h <;> rw [h] <;> simp [c, zmod2_add_self]
            rw [h2] at h1
            have h3 : (f P + f 0) + (α a x * d a + β a x * c a + α a x * β a x) = 0 := by
              rw [← hu_eval, ← hv_eval]
              have h00 := zmod2_add_self (f 0)
              have haa := zmod2_add_self (α a x * β a x)
              calc
                f P + f 0 + (f (α a x • u a) + f 0 + (f (β a x • v a) + f 0) + α a x * β a x)
                    = (f P + f (α a x • u a) + f (β a x • v a) + f 0) + (f 0 + f 0) + α a x * β a x := by ring
                _ = α a x * β a x + 0 + α a x * β a x := by rw [h1, h00]
                _ = α a x * β a x + α a x * β a x := by ring
                _ = 0 := haa
            exact zmod2_add_eq_zero h3
          rw [hstep, hfP, ih]
      exact hind Finset.univ
    have hBπS : Blin f hquad (π x) S = 0 := LinearMap.congr_fun (hπR0 x) S
    have hfx_split : f x + f 0 = ℓ0 x + (f S + f 0) := by
      conv_lhs => rw [hx_eq]
      have h1 : f (π x + S) + f (π x) + f S + f 0 = 0 := hBπS
      exact zmod2_add_eq_zero (by
        have h00 := zmod2_add_self (f 0)
        change f (π x + S) + f 0 + (f (π x) + f 0 + (f S + f 0)) = 0
        calc
          f (π x + S) + f 0 + (f (π x) + f 0 + (f S + f 0))
              = (f (π x + S) + f (π x) + f S + f 0) + (f 0 + f 0) := by ring
          _ = 0 := by rw [h1, h00, add_zero])
    have hsum_expand :
        ∑ i : Fin m, (α i x + c i) * (β i x + d i) =
          (∑ i : Fin m, (α i x * d i + β i x * c i + α i x * β i x)) + ∑ i : Fin m, c i * d i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hsum_expand]
    have hfinal : f x + (c0 + ℓ0 x + ((∑ i : Fin m, (α i x * d i + β i x * c i + α i x * β i x)) +
        ∑ i : Fin m, c i * d i)) = 0 := by
      rw [← hfS]
      simp only [c0]
      have h00 := zmod2_add_self (f 0)
      have hss := zmod2_add_self (∑ i : Fin m, c i * d i)
      calc
        f x + (f 0 + ∑ i : Fin m, c i * d i + ℓ0 x + (f S + f 0 + ∑ i : Fin m, c i * d i))
            = (f x + f 0) + (ℓ0 x + (f S + f 0)) + ((∑ i : Fin m, c i * d i) + ∑ i : Fin m, c i * d i) := by ring
        _ = (f x + f 0) + (f x + f 0) + 0 := by rw [← hfx_split, hss]
        _ = 0 := by rw [add_zero, zmod2_add_self]
    exact zmod2_add_eq_zero hfinal

lemma sum_signZ_symp_form : ∀ k : ℕ,
    (∑ p : (Fin k → F) × (Fin k → F), signZ (∑ i : Fin k, p.1 i * p.2 i)) = (2 : ℤ) ^ k
  | 0 => by simp [signZ]
  | k + 1 => by
      have heq : (∑ p : (Fin (k + 1) → F) × (Fin (k + 1) → F),
          signZ (∑ i : Fin (k + 1), p.1 i * p.2 i)) =
          (∑ ab : F × F, signZ (ab.1 * ab.2)) *
            (∑ p : (Fin k → F) × (Fin k → F), signZ (∑ i : Fin k, p.1 i * p.2 i)) := by
        let e : ((F × F) × ((Fin k → F) × (Fin k → F))) ≃
            ((Fin (k + 1) → F) × (Fin (k + 1) → F)) :=
          { toFun := fun q => (Fin.cons q.1.1 q.2.1, Fin.cons q.1.2 q.2.2)
            invFun := fun p => ((p.1 0, p.2 0), (Fin.tail p.1, Fin.tail p.2))
            left_inv := fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ => by ext <;> simp
            right_inv := fun ⟨u, v⟩ => by ext i <;> simp [Fin.cons_self_tail] }
        rw [← Fintype.sum_equiv e _ _ (fun _ => rfl)]
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro ab _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p _
        change signZ (∑ i : Fin (k + 1),
            (Fin.cons (α := fun _ => F) ab.1 p.1 i) * (Fin.cons (α := fun _ => F) ab.2 p.2 i)) =
          signZ (ab.1 * ab.2) * signZ (∑ i : Fin k, p.1 i * p.2 i)
        rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [signZ_add]
      rw [heq, sum_signZ_symp_form k]
      have h1 : (∑ ab : F × F, signZ (ab.1 * ab.2)) = 2 := by decide
      rw [h1, pow_succ']

end PEqualNP.Outside.L_pcx_445_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_pcx_445 : ∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ (f : X → F),
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) →
    ∀ D : ℕ,
      let A := Fin D → F
      let past := fun (b : A) (stage : Fin D) (j : Fin stage.val) =>
        b ⟨j.val, Nat.lt_trans j.isLt stage.isLt⟩
      ∃ first : X →ₗ[F] A, ∀ e : ℕ, 0<e →
        let T := Fin e → F
        ∀ (ask : (step : Fin D) → (Fin step.val → F) → X →ₗ[F] F)
          (last : A → X →ₗ[F] T) (out : A → T → F),
          ∃ (tail : A → X →ₗ[F] T) (guess : A → T → F),
            Nat.card {x : X // ∃ b : A,
              (∀ turn, ask turn (past b turn) x=b turn) ∧ out b (last b x)=f x} ≤
            Nat.card {x : X // guess (first x) (tail (first x) x)=f x} := by
  intro n
  dsimp only
  intro f hquad D
  let F := PEqualNP.Outside.L_pcx_445_aux.F
  let X := PEqualNP.Outside.L_pcx_445_aux.X n
  let A := Fin D → F
  let past := fun (b : A) (stage : Fin D) (j : Fin stage.val) =>
    b ⟨j.val, Nat.lt_trans j.isLt stage.isLt⟩
  let R0 : Submodule F X := LinearMap.ker (PEqualNP.Outside.L_pcx_445_aux.Blin f hquad)
  obtain ⟨m, α, β, c, d, ℓ0, c0, h2m, hsurj_ab, hR0_ab, hℓ0_R0, hℓ0_clear, hf_nf⟩ :=
    PEqualNP.Outside.L_pcx_445_aux.exists_symplectic_normal_form f hquad
  let first : X →ₗ[F] A :=
    { toFun := fun x j => if hj : j.val < m then α ⟨j.val, hj⟩ x else 0
      map_add' := fun u v => by
        ext j
        change (if hj : j.val < m then α ⟨j.val, hj⟩ (u + v) else 0) =
          (if hj : j.val < m then α ⟨j.val, hj⟩ u else 0) +
            (if hj : j.val < m then α ⟨j.val, hj⟩ v else 0)
        split_ifs with hj
        · exact map_add (α ⟨j.val, hj⟩) u v
        · simp
      map_smul' := fun s u => by
        ext j
        change (if hj : j.val < m then α ⟨j.val, hj⟩ (s • u) else 0) =
          s * (if hj : j.val < m then α ⟨j.val, hj⟩ u else 0)
        split_ifs with hj
        · exact map_smul (α ⟨j.val, hj⟩) s u
        · simp }
  refine ⟨first, ?_⟩
  intro e he ask last out
  let T := Fin e → F
  by_cases hDm : m ≤ D
  · let L_b : A → (X →ₗ[F] F) := fun b =>
      ℓ0 + ∑ i : Fin m, (b ⟨i.val, lt_of_lt_of_le i.isLt hDm⟩ + c i) • β i
    let const_b : A → F := fun b =>
      c0 + ∑ i : Fin m, (b ⟨i.val, lt_of_lt_of_le i.isLt hDm⟩ + c i) * d i
    let tail : A → (X →ₗ[F] T) := fun b =>
      { toFun := fun x _ => L_b b x
        map_add' := fun u v => by ext _; exact map_add (L_b b) u v
        map_smul' := fun s u => by ext _; exact map_smul (L_b b) s u }
    let guess : A → T → F := fun b t => const_b b + t ⟨0, he⟩
    refine ⟨tail, guess, ?_⟩
    have hall : ∀ x : X, guess (first x) (tail (first x) x) = f x := by
      intro x
      rw [hf_nf x]
      simp only [guess, tail, const_b, L_b, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      have hfirst : ∀ i : Fin m, first x ⟨i.val, lt_of_lt_of_le i.isLt hDm⟩ = α i x := by
        intro i
        simp [first, i.isLt]
      simp_rw [hfirst]
      have hsum : ∑ i : Fin m, (α i x + c i) * (β i x + d i) =
          (∑ i : Fin m, (α i x + c i) * d i) + ∑ i : Fin m, (α i x + c i) * β i x := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hsum]
      ring
    have hcard_rhs : Nat.card {x : X // guess (first x) (tail (first x) x) = f x} = Nat.card X := by
      apply Nat.card_congr
      exact
        { toFun := Subtype.val
          invFun := fun x => ⟨x, hall x⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hcard_rhs, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  · push Not at hDm
    let r := m - D
    have hr_pos : 0 < r := by omega
    let clearP : Prop := ∀ u ∈ R0, f u = f 0
    classical
    let bGood : A := fun j => c ⟨j.val, lt_trans j.isLt hDm⟩
    let sOf : A → ℕ := fun b =>
      if clearP ∧ b = bGood then min r (e / 2) else min r ((e - 1) / 2)
    let L_b : A → (X →ₗ[F] F) := fun b =>
      ℓ0 + ∑ j : Fin D, (b j + c ⟨j.val, lt_trans j.isLt hDm⟩) • β ⟨j.val, lt_trans j.isLt hDm⟩
    let const_b : A → F := fun b =>
      c0 + ∑ j : Fin D, (b j + c ⟨j.val, lt_trans j.isLt hDm⟩) * d ⟨j.val, lt_trans j.isLt hDm⟩
    let tail : A → (X →ₗ[F] T) := fun b =>
      if clearP ∧ b = bGood then
        { toFun := fun x idx =>
            if hidx : idx.val / 2 < min r (e / 2) then
              if idx.val % 2 = 0 then α ⟨D + idx.val / 2, by omega⟩ x
              else β ⟨D + idx.val / 2, by omega⟩ x
            else 0
          map_add' := fun u v => by
            ext idx
            rw [Pi.add_apply]
            split_ifs with h1 h2
            · exact map_add (α ⟨D + idx.val / 2, by omega⟩) u v
            · exact map_add (β ⟨D + idx.val / 2, by omega⟩) u v
            · simp
          map_smul' := fun s u => by
            ext idx
            simp only [RingHom.id_apply]
            rw [Pi.smul_apply]
            split_ifs with h1 h2
            · exact map_smul (α ⟨D + idx.val / 2, by omega⟩) s u
            · exact map_smul (β ⟨D + idx.val / 2, by omega⟩) s u
            · simp }
      else
        { toFun := fun x idx =>
            if idx.val = 0 then L_b b x
            else if hidx : (idx.val - 1) / 2 < min r ((e - 1) / 2) then
              if (idx.val - 1) % 2 = 0 then α ⟨D + (idx.val - 1) / 2, by omega⟩ x
              else β ⟨D + (idx.val - 1) / 2, by omega⟩ x
            else 0
          map_add' := fun u v => by
            ext idx
            rw [Pi.add_apply]
            split_ifs with h0 h1 h2
            · exact map_add (L_b b) u v
            · exact map_add (α ⟨D + (idx.val - 1) / 2, by omega⟩) u v
            · exact map_add (β ⟨D + (idx.val - 1) / 2, by omega⟩) u v
            · simp
          map_smul' := fun s u => by
            ext idx
            simp only [RingHom.id_apply]
            rw [Pi.smul_apply]
            split_ifs with h0 h1 h2
            · exact map_smul (L_b b) s u
            · exact map_smul (α ⟨D + (idx.val - 1) / 2, by omega⟩) s u
            · exact map_smul (β ⟨D + (idx.val - 1) / 2, by omega⟩) s u
            · simp }
    let guess : A → T → F := fun b t =>
      if clearP ∧ b = bGood then
        const_b b + ∑ j : Fin (min r (e / 2)),
          (t ⟨2 * j.val, by omega⟩ + c ⟨D + j.val, by omega⟩) *
            (t ⟨2 * j.val + 1, by omega⟩ + d ⟨D + j.val, by omega⟩)
      else
        const_b b + t ⟨0, he⟩ + ∑ j : Fin (min r ((e - 1) / 2)),
          (t ⟨2 * j.val + 1, by omega⟩ + c ⟨D + j.val, by omega⟩) *
            (t ⟨2 * j.val + 2, by omega⟩ + d ⟨D + j.val, by omega⟩)
    refine ⟨tail, guess, ?_⟩
    have hsOf_le : ∀ b : A, sOf b ≤ r := by
      intro b
      dsimp only [sOf]
      split_ifs <;> exact min_le_left _ _
    have hrem : ∀ (x : X),
        guess (first x) (tail (first x) x) + f x =
          ∑ j : Fin (r - sOf (first x)),
            (α ⟨D + sOf (first x) + j.val, by have := hsOf_le (first x); omega⟩ x +
                c ⟨D + sOf (first x) + j.val, by have := hsOf_le (first x); omega⟩) *
              (β ⟨D + sOf (first x) + j.val, by have := hsOf_le (first x); omega⟩ x +
                d ⟨D + sOf (first x) + j.val, by have := hsOf_le (first x); omega⟩) := by
      intro x
      set b := first x
      have hsb_le : sOf b ≤ r := hsOf_le b
      have hfirst : ∀ j : Fin D, b j = α ⟨j.val, lt_trans j.isLt hDm⟩ x := by
        intro j
        simp [b, first, lt_trans j.isLt hDm]
      have hsplit_m : ∀ (g : Fin m → F),
          (∑ i : Fin m, g i) =
            (∑ j : Fin D, g ⟨j.val, lt_trans j.isLt hDm⟩) +
            (∑ j : Fin (sOf b), g ⟨D + j.val, by omega⟩) +
            (∑ j : Fin (r - sOf b), g ⟨D + sOf b + j.val, by omega⟩) := by
        intro g
        have h1 : (∑ i : Fin m, g i) =
            (∑ j : Fin D, g ⟨j.val, lt_trans j.isLt hDm⟩) +
            (∑ j : Fin r, g ⟨D + j.val, by omega⟩) := by
          have hm_eq : m = D + r := by omega
          let e1 : Fin D ⊕ Fin r ≃ Fin m :=
            finSumFinEquiv.trans (finCongr hm_eq.symm)
          rw [← Fintype.sum_equiv e1 _ _ (fun _ => rfl), Fintype.sum_sum_type]
          rfl
        have h2 : (∑ j : Fin r, g ⟨D + j.val, by omega⟩) =
            (∑ j : Fin (sOf b), g ⟨D + j.val, by omega⟩) +
            (∑ j : Fin (r - sOf b), g ⟨D + sOf b + j.val, by omega⟩) := by
          have hr_eq : r = sOf b + (r - sOf b) := by
            have : sOf b ≤ r := by
              dsimp only [sOf]
              split_ifs <;> exact min_le_left _ _
            omega
          let e2 : Fin (sOf b) ⊕ Fin (r - sOf b) ≃ Fin r :=
            finSumFinEquiv.trans (finCongr hr_eq.symm)
          rw [← Fintype.sum_equiv e2 _ _ (fun _ => rfl), Fintype.sum_sum_type]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j _
          congr 1
          ext
          simp [e2, add_assoc]
        rw [h1, h2, add_assoc]
      rw [hf_nf x, hsplit_m (fun i => (α i x + c i) * (β i x + d i))]
      by_cases hcb : clearP ∧ b = bGood
      · have hsOf : sOf b = min r (e / 2) := if_pos hcb
        have hℓ0z : ℓ0 = 0 := hℓ0_clear hcb.1
        have hDsum : (∑ j : Fin D,
            (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
              (β ⟨j.val, lt_trans j.isLt hDm⟩ x + d ⟨j.val, lt_trans j.isLt hDm⟩)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro j _
          rw [← hfirst j, hcb.2]
          simp [bGood, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self]
        have hconst : const_b b = c0 := by
          dsimp only [const_b]
          rw [hcb.2]
          have h0 : (∑ j : Fin D,
              (bGood j + c ⟨j.val, lt_trans j.isLt hDm⟩) * d ⟨j.val, lt_trans j.isLt hDm⟩) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro j _
            rw [show bGood j = c ⟨j.val, lt_trans j.isLt hDm⟩ from rfl,
              PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self, zero_mul]
          rw [h0, add_zero]
        have hguess_eq : guess b (tail b x) =
            c0 + ∑ j : Fin (sOf b),
              (α ⟨D + j.val, by omega⟩ x + c ⟨D + j.val, by omega⟩) *
                (β ⟨D + j.val, by omega⟩ x + d ⟨D + j.val, by omega⟩) := by
          simp only [guess, tail, if_pos hcb, hconst]
          congr 1
          refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b' _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro j _; exact ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩
          · intro j _
            have h1 : (2 * j.val) / 2 = j.val := by omega
            have h2 : (2 * j.val) % 2 = 0 := by omega
            have h3 : (2 * j.val + 1) / 2 = j.val := by omega
            have h4 : (2 * j.val + 1) % 2 ≠ 0 := by omega
            simp only [LinearMap.coe_mk, AddHom.coe_mk, h1, h2, h3, h4, j.isLt, ↓reduceDIte,
              ↓reduceIte]
        rw [hguess_eq, hℓ0z, LinearMap.zero_apply, add_zero, hDsum, zero_add]
        set S1 := ∑ j : Fin (sOf b), (α ⟨D + j.val, by omega⟩ x + c ⟨D + j.val, by omega⟩) *
            (β ⟨D + j.val, by omega⟩ x + d ⟨D + j.val, by omega⟩)
        set S2 := ∑ j : Fin (r - sOf b),
            (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
              (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩)
        have hc00 := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self c0
        have hS11 := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self S1
        calc
          c0 + S1 + (c0 + (S1 + S2)) = (c0 + c0) + (S1 + S1) + S2 := by ring
          _ = S2 := by rw [hc00, hS11, add_zero, zero_add]
      · have hsOf : sOf b = min r ((e - 1) / 2) := if_neg hcb
        have hguess_eq : guess b (tail b x) =
            const_b b + L_b b x + ∑ j : Fin (sOf b),
              (α ⟨D + j.val, by omega⟩ x + c ⟨D + j.val, by omega⟩) *
                (β ⟨D + j.val, by omega⟩ x + d ⟨D + j.val, by omega⟩) := by
          simp only [guess, tail, if_neg hcb, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte]
          congr 1
          refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b' _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro j _; exact ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩
          · intro j _
            have h0a : 2 * j.val + 1 ≠ 0 := by omega
            have h0b : 2 * j.val + 2 ≠ 0 := by omega
            have h1 : (2 * j.val + 1 - 1) / 2 = j.val := by omega
            have h2 : (2 * j.val + 1 - 1) % 2 = 0 := by omega
            have h3 : (2 * j.val + 2 - 1) / 2 = j.val := by omega
            have h4 : (2 * j.val + 2 - 1) % 2 ≠ 0 := by omega
            simp only [h0a, h0b, h1, h2, h3, h4, j.isLt, ↓reduceIte, ↓reduceDIte]
        have hDpart : const_b b + L_b b x =
            c0 + ℓ0 x + ∑ j : Fin D,
              (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
                (β ⟨j.val, lt_trans j.isLt hDm⟩ x + d ⟨j.val, lt_trans j.isLt hDm⟩) := by
          simp only [const_b, L_b, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
            smul_eq_mul]
          simp_rw [hfirst]
          have hsum : ∑ j : Fin D,
              (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
                (β ⟨j.val, lt_trans j.isLt hDm⟩ x + d ⟨j.val, lt_trans j.isLt hDm⟩) =
              (∑ j : Fin D, (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
                d ⟨j.val, lt_trans j.isLt hDm⟩) +
              (∑ j : Fin D, (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
                β ⟨j.val, lt_trans j.isLt hDm⟩ x) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
          rw [hsum]
          ring
        rw [hguess_eq, hDpart]
        set P0 := c0 + ℓ0 x + ∑ j : Fin D,
            (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
              (β ⟨j.val, lt_trans j.isLt hDm⟩ x + d ⟨j.val, lt_trans j.isLt hDm⟩)
        set S1 := ∑ j : Fin (sOf b), (α ⟨D + j.val, by omega⟩ x + c ⟨D + j.val, by omega⟩) *
            (β ⟨D + j.val, by omega⟩ x + d ⟨D + j.val, by omega⟩)
        set S2 := ∑ j : Fin (r - sOf b),
            (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
              (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩)
        have hP00 := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self P0
        have hS11 := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self S1
        calc
          P0 + S1 + (c0 + ℓ0 x + ((∑ j : Fin D,
              (α ⟨j.val, lt_trans j.isLt hDm⟩ x + c ⟨j.val, lt_trans j.isLt hDm⟩) *
                (β ⟨j.val, lt_trans j.isLt hDm⟩ x + d ⟨j.val, lt_trans j.isLt hDm⟩)) + S1 + S2))
              = (P0 + P0) + (S1 + S1) + S2 := by ring
          _ = S2 := by rw [hP00, hS11, add_zero, zero_add]
    have hrhs_exact :
        (2 * Nat.card {x : X // guess (first x) (tail (first x) x) = f x} : ℤ) - (2 : ℤ) ^ n =
          ∑ b : A, (2 : ℤ) ^ (n - D - (r - sOf b)) := by
      have hcardX : (Fintype.card X : ℤ) = (2 : ℤ) ^ n := by
        simp [X, ZMod.card]
      rw [Nat.card_eq_fintype_card, ← hcardX]
      have hsum_sign :
          (2 * (Fintype.card {x : X // guess (first x) (tail (first x) x) = f x}) : ℤ) -
            (Fintype.card X : ℤ) =
          ∑ x : X, PEqualNP.Outside.L_pcx_445_aux.signZ (guess (first x) (tail (first x) x) + f x) := by
        have hterm : ∀ x : X,
            PEqualNP.Outside.L_pcx_445_aux.signZ (guess (first x) (tail (first x) x) + f x) =
              (if guess (first x) (tail (first x) x) = f x then 2 else 0) - 1 := by
          intro x
          by_cases h : guess (first x) (tail (first x) x) = f x
          · rw [if_pos h, h, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self]; rfl
          · rw [if_neg h]
            have hne : guess (first x) (tail (first x) x) + f x ≠ 0 :=
              fun h0 => h (PEqualNP.Outside.L_pcx_445_aux.zmod2_add_eq_zero h0)
            rw [PEqualNP.Outside.L_pcx_445_aux.zmod2_ne_zero_eq_one hne]; rfl
        simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm _ (2 : ℤ), Fintype.card_subtype]
      rw [hsum_sign]
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : X => first x) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl ?_
      intro b _
      let ab : X →ₗ[F] ((Fin m → F) × (Fin m → F)) :=
        { toFun := fun y => (fun i => α i y, fun i => β i y)
          map_add' := fun y1 y2 => by ext i <;> simp [map_add]
          map_smul' := fun s y => by ext i <;> simp [map_smul] }
      have hfib_ab : ∀ y : (Fin m → F) × (Fin m → F),
          (Finset.univ.filter (fun x : X => ab x = y)).card = 2 ^ (n - 2 * m) := by
        intro y
        obtain ⟨x0, hx0⟩ := hsurj_ab y
        have hker_dim : Module.finrank F (LinearMap.ker ab) = n - 2 * m := by
          have hrn := LinearMap.finrank_range_add_finrank_ker ab
          rw [LinearMap.range_eq_top.mpr hsurj_ab, finrank_top, Module.finrank_prod,
            Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
          omega
        haveI : Fintype (LinearMap.ker ab) := Fintype.ofFinite _
        have hcardK : Fintype.card (LinearMap.ker ab) = 2 ^ (n - 2 * m) := by
          rw [PEqualNP.Outside.L_pcx_445_aux.card_sub_eq_pow, hker_dim]
        rw [← hcardK]
        have heq : Finset.univ.filter (fun x : X => ab x = y) =
            Finset.univ.image (fun k : LinearMap.ker ab => k.1 + x0) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hx
            refine ⟨⟨x + x0, by
              have hx0' : ab x0 = y := hx0
              rw [LinearMap.mem_ker, map_add, hx, hx0']
              ext i <;> exact PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self _⟩, ?_⟩
            rw [add_assoc, PEqualNP.Outside.L_pcx_445_aux.zmod2_vec_add_self, add_zero]
          · rintro ⟨⟨k, hk⟩, rfl⟩
            have hx0' : ab x0 = y := hx0
            rw [map_add, LinearMap.mem_ker.mp hk, zero_add, hx0']
        rw [heq, Finset.card_image_of_injective]
        · simp
        · intro a1 a2 h
          exact Subtype.ext (add_right_cancel h)
      have hsb_le : sOf b ≤ r := hsOf_le b
      have hsum_b :
          (∑ x ∈ Finset.univ.filter (fun x : X => first x = b),
            PEqualNP.Outside.L_pcx_445_aux.signZ (guess (first x) (tail (first x) x) + f x)) =
          ∑ x ∈ Finset.univ.filter (fun x : X => first x = b),
            PEqualNP.Outside.L_pcx_445_aux.signZ
              (∑ j : Fin (r - sOf b),
                (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
                  (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxb : first x = b := (Finset.mem_filter.mp hx).2
        rw [hrem x]
        have hsubst : ∀ b' : A, b' = b →
            PEqualNP.Outside.L_pcx_445_aux.signZ
              (∑ j : Fin (r - sOf b'),
                (α ⟨D + sOf b' + j.val, by have := hsOf_le b'; omega⟩ x +
                    c ⟨D + sOf b' + j.val, by have := hsOf_le b'; omega⟩) *
                  (β ⟨D + sOf b' + j.val, by have := hsOf_le b'; omega⟩ x +
                    d ⟨D + sOf b' + j.val, by have := hsOf_le b'; omega⟩)) =
            PEqualNP.Outside.L_pcx_445_aux.signZ
              (∑ j : Fin (r - sOf b),
                (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
                  (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩)) := by
          rintro _ rfl; rfl
        exact hsubst (first x) hxb
      rw [hsum_b]
      have h2m_le_n : 2 * m ≤ n := by omega
      let P := {y : (Fin m → F) × (Fin m → F) // ∀ j : Fin D, y.1 ⟨j.val, lt_trans j.isLt hDm⟩ = b j}
      have hgroup :
          (∑ x ∈ Finset.univ.filter (fun x : X => first x = b),
            PEqualNP.Outside.L_pcx_445_aux.signZ
              (∑ j : Fin (r - sOf b),
                (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
                  (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩))) =
          (2 : ℤ) ^ (n - 2 * m) *
            ∑ y : P, PEqualNP.Outside.L_pcx_445_aux.signZ
              (∑ j : Fin (r - sOf b),
                (y.1.1 ⟨D + sOf b + j.val, by omega⟩ + c ⟨D + sOf b + j.val, by omega⟩) *
                  (y.1.2 ⟨D + sOf b + j.val, by omega⟩ + d ⟨D + sOf b + j.val, by omega⟩)) := by
        rw [Finset.mul_sum]
        let gP : X → (Fin m → F) × (Fin m → F) := ab
        rw [← Finset.sum_fiberwise_of_maps_to (g := gP) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)]
        have hfiltP :
            (∑ y : (Fin m → F) × (Fin m → F),
              ∑ x ∈ (Finset.univ.filter (fun x : X => first x = b)).filter (fun x => gP x = y),
                PEqualNP.Outside.L_pcx_445_aux.signZ
                  (∑ j : Fin (r - sOf b),
                    (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
                      (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩))) =
            ∑ y ∈ Finset.univ.filter (fun y : (Fin m → F) × (Fin m → F) =>
              ∀ j : Fin D, y.1 ⟨j.val, lt_trans j.isLt hDm⟩ = b j),
              (2 : ℤ) ^ (n - 2 * m) *
                PEqualNP.Outside.L_pcx_445_aux.signZ
                  (∑ j : Fin (r - sOf b),
                    (y.1 ⟨D + sOf b + j.val, by omega⟩ + c ⟨D + sOf b + j.val, by omega⟩) *
                      (y.2 ⟨D + sOf b + j.val, by omega⟩ + d ⟨D + sOf b + j.val, by omega⟩)) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro y _
          split_ifs with hy
          · have hsubeq : (Finset.univ.filter (fun x : X => first x = b)).filter (fun x => gP x = y) =
                Finset.univ.filter (fun x : X => ab x = y) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, gP]
              constructor
              · exact And.right
              · intro hxy
                refine ⟨?_, hxy⟩
                ext j
                have hj := hy j
                have h1 : α ⟨j.val, lt_trans j.isLt hDm⟩ x = y.1 ⟨j.val, lt_trans j.isLt hDm⟩ :=
                  congrFun (congrArg Prod.fst hxy) ⟨j.val, lt_trans j.isLt hDm⟩
                simp [first, lt_trans j.isLt hDm, h1, hj]
            rw [hsubeq]
            have hconst_x : ∀ x ∈ Finset.univ.filter (fun x : X => ab x = y),
                PEqualNP.Outside.L_pcx_445_aux.signZ
                  (∑ j : Fin (r - sOf b),
                    (α ⟨D + sOf b + j.val, by omega⟩ x + c ⟨D + sOf b + j.val, by omega⟩) *
                      (β ⟨D + sOf b + j.val, by omega⟩ x + d ⟨D + sOf b + j.val, by omega⟩)) =
                PEqualNP.Outside.L_pcx_445_aux.signZ
                  (∑ j : Fin (r - sOf b),
                    (y.1 ⟨D + sOf b + j.val, by omega⟩ + c ⟨D + sOf b + j.val, by omega⟩) *
                      (y.2 ⟨D + sOf b + j.val, by omega⟩ + d ⟨D + sOf b + j.val, by omega⟩)) := by
              intro x hx
              have hxy : ab x = y := (Finset.mem_filter.mp hx).2
              congr 1
              refine Finset.sum_congr rfl ?_
              intro j _
              have h1 : α ⟨D + sOf b + j.val, by omega⟩ x = y.1 ⟨D + sOf b + j.val, by omega⟩ :=
                congrFun (congrArg Prod.fst hxy) _
              have h2 : β ⟨D + sOf b + j.val, by omega⟩ x = y.2 ⟨D + sOf b + j.val, by omega⟩ :=
                congrFun (congrArg Prod.snd hxy) _
              rw [h1, h2]
            rw [Finset.sum_congr rfl hconst_x, Finset.sum_const, nsmul_eq_mul, hfib_ab y]
            push_cast
            rfl
          · apply Finset.sum_eq_zero
            intro x hx
            exfalso
            apply hy
            intro j
            have h1 := congrFun (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2 j
            have h2 := congrFun (congrArg Prod.fst (Finset.mem_filter.mp hx).2) ⟨j.val, lt_trans j.isLt hDm⟩
            have h1' : α ⟨j.val, lt_trans j.isLt hDm⟩ x = b j := by
              simpa [first, lt_trans j.isLt hDm] using h1
            have h2' : α ⟨j.val, lt_trans j.isLt hDm⟩ x = y.1 ⟨j.val, lt_trans j.isLt hDm⟩ := h2
            rw [← h2', h1']
        rw [hfiltP]
        refine Finset.sum_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).2⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro y1 _ y2 _ h; exact congrArg Subtype.val h
        · intro y _; exact ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩
        · intro _ _; rfl
      rw [hgroup]
      let k := r - sOf b
      let remA := Fin (sOf b) → F
      let remB := Fin (D + sOf b) → F
      let eP : P ≃ (remA × remB) × ((Fin k → F) × (Fin k → F)) :=
        { toFun := fun y =>
            ((fun j => y.1.1 ⟨D + j.val, by omega⟩,
              fun j => y.1.2 ⟨j.val, by omega⟩),
             (fun j => y.1.1 ⟨D + sOf b + j.val, by omega⟩ + c ⟨D + sOf b + j.val, by omega⟩,
              fun j => y.1.2 ⟨D + sOf b + j.val, by omega⟩ + d ⟨D + sOf b + j.val, by omega⟩))
          invFun := fun q =>
            ⟨(fun i =>
                if hi1 : i.val < D then b ⟨i.val, hi1⟩
                else if hi2 : i.val < D + sOf b then q.1.1 ⟨i.val - D, by omega⟩
                else q.2.1 ⟨i.val - (D + sOf b), by omega⟩ + c i,
              fun i =>
                if hi2 : i.val < D + sOf b then q.1.2 ⟨i.val, hi2⟩
                else q.2.2 ⟨i.val - (D + sOf b), by omega⟩ + d i),
             fun j => by simp [j.isLt]⟩
          left_inv := fun y => by
            apply Subtype.ext
            ext i
            · dsimp only
              split_ifs with h1 h2
              · exact (y.2 ⟨i.val, h1⟩).symm
              · exact congrArg y.1.1 (Fin.ext (by dsimp only; omega))
              · have hidx : (⟨D + sOf b + (i.val - (D + sOf b)), by omega⟩ : Fin m) = i :=
                  Fin.ext (by dsimp only; omega)
                rw [hidx, add_assoc, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self, add_zero]
            · dsimp only
              split_ifs with h2
              · rfl
              · have hidx : (⟨D + sOf b + (i.val - (D + sOf b)), by omega⟩ : Fin m) = i :=
                  Fin.ext (by dsimp only; omega)
                rw [hidx, add_assoc, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self, add_zero]
          right_inv := fun q => by
            ext j
            · dsimp only
              have h1 : ¬ D + j.val < D := by omega
              have h2 : D + j.val < D + sOf b := by omega
              simp [h1, h2]
            · dsimp only
              have h2 : j.val < D + sOf b := j.isLt
              simp [h2]
            · dsimp only
              have h1 : ¬ D + sOf b + j.val < D := by omega
              have h2 : ¬ D + sOf b + j.val < D + sOf b := by omega
              simp only [h1, h2, ↓reduceDIte]
              rw [add_assoc, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self, add_zero]
              exact congrArg q.2.1 (Fin.ext (by dsimp only; omega))
            · dsimp only
              have h2 : ¬ D + sOf b + j.val < D + sOf b := by omega
              simp only [h2, ↓reduceDIte]
              rw [add_assoc, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self, add_zero]
              exact congrArg q.2.2 (Fin.ext (by dsimp only; omega)) }
      have hsumP :
          (∑ y : P, PEqualNP.Outside.L_pcx_445_aux.signZ
            (∑ j : Fin k,
              (y.1.1 ⟨D + sOf b + j.val, by omega⟩ + c ⟨D + sOf b + j.val, by omega⟩) *
                (y.1.2 ⟨D + sOf b + j.val, by omega⟩ + d ⟨D + sOf b + j.val, by omega⟩))) =
          (2 : ℤ) ^ (D + 2 * sOf b) * (2 : ℤ) ^ k := by
        rw [← Fintype.sum_equiv eP.symm _ _ (fun _ => rfl)]
        rw [Fintype.sum_prod_type]
        have hconst_q : ∀ q1 : remA × remB,
            (∑ q2 : (Fin k → F) × (Fin k → F),
              PEqualNP.Outside.L_pcx_445_aux.signZ
                (∑ j : Fin k,
                  ((eP.symm (q1, q2)).1.1 ⟨D + sOf b + j.val, by omega⟩ +
                      c ⟨D + sOf b + j.val, by omega⟩) *
                    ((eP.symm (q1, q2)).1.2 ⟨D + sOf b + j.val, by omega⟩ +
                      d ⟨D + sOf b + j.val, by omega⟩))) =
            (2 : ℤ) ^ k := by
          intro q1
          have hsimp : ∀ q2 : (Fin k → F) × (Fin k → F),
              (∑ j : Fin k,
                ((eP.symm (q1, q2)).1.1 ⟨D + sOf b + j.val, by omega⟩ +
                    c ⟨D + sOf b + j.val, by omega⟩) *
                  ((eP.symm (q1, q2)).1.2 ⟨D + sOf b + j.val, by omega⟩ +
                    d ⟨D + sOf b + j.val, by omega⟩)) =
              ∑ j : Fin k, q2.1 j * q2.2 j := by
            intro q2
            refine Finset.sum_congr rfl ?_
            intro j _
            have h1 : (eP.symm (q1, q2)).1.1 ⟨D + sOf b + j.val, by omega⟩ +
                c ⟨D + sOf b + j.val, by omega⟩ = q2.1 j := by
              have := congrFun (congrArg Prod.fst (congrArg Prod.snd (eP.right_inv (q1, q2)))) j
              exact this
            have h2 : (eP.symm (q1, q2)).1.2 ⟨D + sOf b + j.val, by omega⟩ +
                d ⟨D + sOf b + j.val, by omega⟩ = q2.2 j := by
              have := congrFun (congrArg Prod.snd (congrArg Prod.snd (eP.right_inv (q1, q2)))) j
              exact this
            rw [h1, h2]
          simp_rw [hsimp]
          exact PEqualNP.Outside.L_pcx_445_aux.sum_signZ_symp_form k
        simp_rw [hconst_q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard_rem : (Fintype.card (remA × remB) : ℤ) = (2 : ℤ) ^ (D + 2 * sOf b) := by
          simp only [remA, remB, Fintype.card_prod, Fintype.card_pi, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, F, ZMod.card, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_ofNat]
          rw [← pow_add]
          congr 1
          omega
        rw [hcard_rem]
      rw [hsumP, ← pow_add, ← pow_add]
      congr 1
      have hsle : sOf b ≤ r := by
        dsimp only [sOf]
        split_ifs <;> exact min_le_left _ _
      omega
    let cell := fun (b : A) (x : X) => ∀ turn, ask turn (past b turn) x = b turn
    let Lb : A → (X →ₗ[F] A) := fun b =>
      { toFun := fun x turn => ask turn (past b turn) x
        map_add' := fun u v => by ext turn; exact map_add (ask turn (past b turn)) u v
        map_smul' := fun s u => by ext turn; exact map_smul (ask turn (past b turn)) s u }
    let Wb : A → Submodule F X := fun b => LinearMap.ker (Lb b)
    have hcell_uniq : ∀ x : X, ∃! b : A, cell b x := by
      intro x
      have hrec : ∀ (k : ℕ) (hk : k ≤ D),
          ∃! (g : Fin k → F), ∀ (j : Fin k),
            ask ⟨j.val, lt_of_lt_of_le j.isLt hk⟩
              (fun i : Fin j.val => g ⟨i.val, lt_trans i.isLt j.isLt⟩) x = g j := by
        intro k
        induction k with
        | zero =>
          intro _
          refine ⟨Fin.elim0, fun j => j.elim0, fun g _ => funext (fun j => j.elim0)⟩
        | succ k ih =>
          intro hk
          obtain ⟨g, hg, huniq⟩ := ih (Nat.le_of_succ_le hk)
          let lastVal : F := ask ⟨k, hk⟩ (fun i : Fin k => g i) x
          let g' : Fin (k + 1) → F := Fin.snoc (α := fun _ => F) g lastVal
          refine ⟨g', ?_, ?_⟩
          · intro j
            refine Fin.lastCases ?_ ?_ j
            · simp only [g', Fin.val_last, Fin.snoc_last]
              have hfun : (fun i : Fin k => Fin.snoc (α := fun _ => F) g lastVal ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = g := by
                ext i
                exact Fin.snoc_castSucc (α := fun _ => F) lastVal g i
              rw [hfun]
            · intro j0
              simp only [g', Fin.val_castSucc, Fin.snoc_castSucc]
              have hfun : (fun i : Fin j0.val =>
                  Fin.snoc (α := fun _ => F) g lastVal ⟨i.val, lt_trans i.isLt (Nat.lt_succ_of_lt j0.isLt)⟩) =
                  fun i : Fin j0.val => g ⟨i.val, lt_trans i.isLt j0.isLt⟩ := by
                ext i
                exact Fin.snoc_castSucc (α := fun _ => F) lastVal g ⟨i.val, lt_trans i.isLt j0.isLt⟩
              rw [hfun]
              exact hg j0
          · intro g2 hg2
            have hinit : (fun j : Fin k => g2 j.castSucc) = g := by
              apply huniq
              intro j
              exact hg2 j.castSucc
            ext j
            refine Fin.lastCases ?_ ?_ j
            · simp only [g', Fin.snoc_last, lastVal]
              have h2 := hg2 (Fin.last k)
              simp only [Fin.val_last] at h2
              have hfun : (fun i : Fin k => g2 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = g := by
                rw [← hinit]; rfl
              rw [← h2, hfun]
            · intro j0
              simp only [g', Fin.snoc_castSucc]
              exact congrFun hinit j0
      exact hrec D le_rfl
    let trace : X → A := fun x => Classical.choose (hcell_uniq x)
    have htrace_cell : ∀ x : X, cell (trace x) x := fun x => (Classical.choose_spec (hcell_uniq x)).1
    have htrace_eq : ∀ x b, cell b x ↔ trace x = b := by
      intro x b
      constructor
      · intro h
        exact ((Classical.choose_spec (hcell_uniq x)).2 b h).symm
      · rintro rfl
        exact htrace_cell x
    have hlhs_split :
        (2 * Nat.card {x : X // ∃ b : A, cell b x ∧ out b (last b x) = f x} : ℤ) - (2 : ℤ) ^ n =
          ∑ b : A,
            ((2 * (Finset.univ.filter (fun x : X => cell b x ∧ out b (last b x) = f x)).card : ℤ) -
              ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hcardX : (2 : ℤ) ^ n = ∑ b : A, ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ) := by
        have h1 : (Finset.univ : Finset X).card = ∑ b : A, (Finset.univ.filter (fun x : X => cell b x)).card := by
          have h2 := Finset.card_eq_sum_card_fiberwise (f := trace) (s := Finset.univ)
            (t := (Finset.univ : Finset A)) (fun _ _ => Finset.mem_univ _)
          rw [h2]
          refine Finset.sum_congr rfl ?_
          intro b _
          congr 1
          ext x
          simp [htrace_eq]
        have hX : (Finset.univ : Finset X).card = 2 ^ n := by simp [X, F, ZMod.card]
        rw [hX] at h1
        exact_mod_cast h1
      have hhits : (Finset.univ.filter (fun x : X => ∃ b : A, cell b x ∧ out b (last b x) = f x)).card =
          ∑ b : A, (Finset.univ.filter (fun x : X => cell b x ∧ out b (last b x) = f x)).card := by
        have h2 := Finset.card_eq_sum_card_fiberwise (f := trace)
          (s := Finset.univ.filter (fun x : X => ∃ b : A, cell b x ∧ out b (last b x) = f x))
          (t := (Finset.univ : Finset A)) (fun _ _ => Finset.mem_univ _)
        rw [h2]
        refine Finset.sum_congr rfl ?_
        intro b _
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨b', hb', hout⟩, rfl⟩
          have : b' = trace x := ((htrace_eq x b').mp hb').symm
          rw [← this]
          exact ⟨hb', hout⟩
        · rintro ⟨hb, hout⟩
          exact ⟨⟨b, hb, hout⟩, (htrace_eq x b).mp hb⟩
      rw [hhits, hcardX, Finset.sum_sub_distrib, Nat.cast_sum, Finset.mul_sum]
    let radb : A → Submodule F X := fun b => PEqualNP.Outside.L_pcx_445_aux.radSub f hquad (Wb b)
    let pb : A → ℕ := fun b => (Module.finrank F (Wb b) - Module.finrank F (radb b)) / 2
    let goodb : A → Prop := fun b =>
      pb b = r ∧ ∃ x : X, cell b x ∧ ∀ u ∈ radb b, f (x + u) = f x
    have hWb_codim : ∀ b, n - Module.finrank F (Wb b) ≤ D := by
      intro b
      have hrn := LinearMap.finrank_range_add_finrank_ker (Lb b)
      rw [Module.finrank_fin_fun] at hrn
      have hker : Module.finrank F (LinearMap.ker (Lb b)) = Module.finrank F (Wb b) := rfl
      rw [hker] at hrn
      have hr : Module.finrank F (LinearMap.range (Lb b)) ≤ D := by
        have := Submodule.finrank_le (LinearMap.range (Lb b))
        rwa [Module.finrank_fin_fun] at this
      omega
    have h2pb : ∀ b, 2 * pb b = Module.finrank F (Wb b) - Module.finrank F (radb b) := by
      intro b
      have hle : Module.finrank F (Wb b) ≤ n := by
        have := Submodule.finrank_le (Wb b)
        rwa [Module.finrank_fin_fun] at this
      have hev := PEqualNP.Outside.L_pcx_445_aux.even_finrank_sub_rad f hquad n (Wb b) hle
      rcases hev with ⟨t, ht⟩
      have ht' : Module.finrank F (Wb b) - Module.finrank F (radb b) = t + t := ht
      dsimp only [pb]
      omega
    have hpb_ge : ∀ b, r ≤ pb b := by
      intro b
      have h1 : Module.finrank F (PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b)) ≤
          Module.finrank F R0 + (n - Module.finrank F (Wb b)) :=
        (PEqualNP.Outside.L_pcx_445_aux.finrank_orthSub_le f hquad (Wb b)).1
      have h2 : Module.finrank F (radb b) ≤
          Module.finrank F (PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b)) :=
        Submodule.finrank_mono inf_le_right
      have h3 := hWb_codim b
      have h4 := h2pb b
      have hWb_le : Module.finrank F (Wb b) ≤ n := by
        have := Submodule.finrank_le (Wb b)
        rwa [Module.finrank_fin_fun] at this
      have hR0_le : Module.finrank F R0 ≤ n := by
        have := Submodule.finrank_le R0
        rwa [Module.finrank_fin_fun] at this
      have hm_eq' : 2 * m = n - Module.finrank F R0 := h2m
      have hr_def : r = m - D := rfl
      omega
    have htight : ∀ b, pb b = r →
        Module.finrank F (Wb b) + D = n ∧
        (∀ u ∈ R0, u ∈ radb b) ∧
        (∀ ℓ : X →ₗ[F] F, (∀ v ∈ Wb b, ℓ v = 0) →
          ∃ u ∈ radb b, PEqualNP.Outside.L_pcx_445_aux.Blin f hquad u = ℓ) := by
      intro b hpb
      have hfb := PEqualNP.Outside.L_pcx_445_aux.finrank_orthSub_le f hquad (Wb b)
      have h1 : Module.finrank F (PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b)) ≤
          Module.finrank F R0 + (n - Module.finrank F (Wb b)) := hfb.1
      have h2 : Module.finrank F (radb b) ≤
          Module.finrank F (PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b)) :=
        Submodule.finrank_mono inf_le_right
      have h3 := hWb_codim b
      have h4 := h2pb b
      have hWb_le : Module.finrank F (Wb b) ≤ n := by
        have := Submodule.finrank_le (Wb b)
        rwa [Module.finrank_fin_fun] at this
      have hR0_le : Module.finrank F R0 ≤ n := by
        have := Submodule.finrank_le R0
        rwa [Module.finrank_fin_fun] at this
      have hm_eq' : 2 * m = n - Module.finrank F R0 := h2m
      have hr_def : r = m - D := rfl
      have hcodim_eq : Module.finrank F (Wb b) + D = n := by omega
      have horth_eq : Module.finrank F (PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b)) =
          Module.finrank F R0 + (n - Module.finrank F (Wb b)) := by omega
      have hrad_eq_dim : Module.finrank F (radb b) =
          Module.finrank F (PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b)) := by omega
      have hrad_eq_orth : radb b = PEqualNP.Outside.L_pcx_445_aux.orthSub f hquad (Wb b) :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right hrad_eq_dim
      refine ⟨hcodim_eq, ?_, ?_⟩
      · intro u huR0
        rw [hrad_eq_orth, PEqualNP.Outside.L_pcx_445_aux.mem_orthSub]
        intro v _
        exact LinearMap.congr_fun huR0 v
      · intro ℓ hℓ
        obtain ⟨u, hu_orth, hu_eq⟩ := hfb.2 horth_eq ℓ hℓ
        exact ⟨u, hrad_eq_orth ▸ hu_orth, hu_eq⟩
    have hgood_clear : ∀ b, goodb b → clearP := by
      intro b ⟨hpb, x, _, hfx⟩ u huR0
      have hru : u ∈ radb b := (htight b hpb).2.1 u huR0
      have h1 : f (x + u) = f x := hfx u hru
      have h2 : PEqualNP.Outside.L_pcx_445_aux.Blin f hquad u x = 0 := LinearMap.congr_fun huR0 x
      have h3 : f (x + u) + f x + f u + f 0 = 0 := by
        have := PEqualNP.Outside.L_pcx_445_aux.B_symm f u x
        rw [← this]
        exact h2
      rw [h1] at h3
      have h4 : f u + f 0 = 0 := by
        have hxx := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self (f x)
        calc
          f u + f 0 = (f x + f x) + (f u + f 0) := by rw [hxx, zero_add]
          _ = f x + f x + f u + f 0 := by ring
          _ = 0 := h3
      exact PEqualNP.Outside.L_pcx_445_aux.zmod2_add_eq_zero h4
    have hgood_uniq : ∀ b1 b2, goodb b1 → goodb b2 → b1 = b2 := by
      intro b1 b2 hg1 hg2
      by_contra hne
      have hex : ∃ k : ℕ, ∃ hk : k < D, b1 ⟨k, hk⟩ ≠ b2 ⟨k, hk⟩ := by
        by_contra hall
        push Not at hall
        apply hne
        ext t
        exact hall t.val t.isLt
      let k0 := Nat.find hex
      obtain ⟨hk0_lt, hb_ne⟩ := Nat.find_spec hex
      let t : Fin D := ⟨k0, hk0_lt⟩
      have hpast_eq : past b1 t = past b2 t := by
        ext j
        have hnot := Nat.find_min hex j.isLt
        push Not at hnot
        exact hnot (Nat.lt_trans j.isLt hk0_lt)
      let ℓ : X →ₗ[F] F := ask t (past b1 t)
      have hℓ1 : ∀ v ∈ Wb b1, ℓ v = 0 := fun v hv => congrFun hv t
      have hℓ2 : ∀ v ∈ Wb b2, ℓ v = 0 := fun v hv => by
        have h : ask t (past b2 t) v = 0 := congrFun hv t
        rwa [← hpast_eq] at h
      obtain ⟨hpb1, x1, hx1_cell, hx1_rad⟩ := hg1
      obtain ⟨hpb2, x2, hx2_cell, hx2_rad⟩ := hg2
      obtain ⟨u1, hu1_rad, hu1_B⟩ := (htight b1 hpb1).2.2 ℓ hℓ1
      obtain ⟨u2, hu2_rad, hu2_B⟩ := (htight b2 hpb2).2.2 ℓ hℓ2
      have hu12_R0 : u1 + u2 ∈ R0 := by
        rw [LinearMap.mem_ker]
        apply LinearMap.ext
        intro v
        rw [map_add, LinearMap.add_apply, hu1_B, hu2_B]
        exact PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self (ℓ v)
      have hfu12 : f (u1 + u2) = f 0 := hgood_clear b1 ⟨hpb1, x1, hx1_cell, hx1_rad⟩ (u1 + u2) hu12_R0
      have hBu1u2 : PEqualNP.Outside.L_pcx_445_aux.Blin f hquad u1 u2 = 0 := by
        have h1 := LinearMap.congr_fun hu12_R0 u2
        have hBself : PEqualNP.Outside.L_pcx_445_aux.Blin f hquad u2 u2 = 0 :=
          PEqualNP.Outside.L_pcx_445_aux.B_self f u2
        rw [map_add, LinearMap.add_apply, hBself, add_zero] at h1
        exact h1
      have hfu_eq : f u1 = f u2 := by
        have h1 : f (u1 + u2) + f u1 + f u2 + f 0 = 0 := hBu1u2
        rw [hfu12] at h1
        have h2 : f u1 + f u2 = 0 := by
          have h00 := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self (f 0)
          calc
            f u1 + f u2 = (f 0 + f 0) + (f u1 + f u2) := by rw [h00, zero_add]
            _ = f 0 + f u1 + f u2 + f 0 := by ring
            _ = 0 := h1
        exact PEqualNP.Outside.L_pcx_445_aux.zmod2_add_eq_zero h2
      have hval1 : f u1 + f 0 = b1 t := by
        have h1 : f (x1 + u1) = f x1 := hx1_rad u1 hu1_rad
        have h2 : f (u1 + x1) + f u1 + f x1 + f 0 = ℓ x1 := LinearMap.congr_fun hu1_B x1
        rw [add_comm u1 x1, h1] at h2
        have h3 : f x1 + f u1 + f x1 + f 0 = f u1 + f 0 := by
          have hxx := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self (f x1)
          calc
            f x1 + f u1 + f x1 + f 0 = (f x1 + f x1) + (f u1 + f 0) := by ring
            _ = f u1 + f 0 := by rw [hxx, zero_add]
        rw [h3] at h2
        rw [h2]
        exact hx1_cell t
      have hval2 : f u2 + f 0 = b2 t := by
        have h1 : f (x2 + u2) = f x2 := hx2_rad u2 hu2_rad
        have h2 : f (u2 + x2) + f u2 + f x2 + f 0 = ℓ x2 := LinearMap.congr_fun hu2_B x2
        rw [add_comm u2 x2, h1] at h2
        have h3 : f x2 + f u2 + f x2 + f 0 = f u2 + f 0 := by
          have hxx := PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self (f x2)
          calc
            f x2 + f u2 + f x2 + f 0 = (f x2 + f x2) + (f u2 + f 0) := by ring
            _ = f u2 + f 0 := by rw [hxx, zero_add]
        rw [h3] at h2
        rw [h2]
        simpa [ℓ, hpast_eq] using hx2_cell t
      apply hb_ne
      rw [← hval1, ← hval2, hfu_eq]
    let k0 := r - min r ((e - 1) / 2)
    let k1 := r - min r (e / 2)
    have hcell_ex : ∀ b : A,
        (2 : ℤ) ^ k0 *
          ((2 * (Finset.univ.filter (fun x : X => cell b x ∧ out b (last b x) = f x)).card : ℤ) -
            ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ)) ≤
        if goodb b then (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - k1)
        else ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ) := by
      intro b
      by_cases hne : ∃ x0 : X, cell b x0
      · obtain ⟨x0, hx0⟩ := hne
        haveI : Fintype (Wb b) := Fintype.ofFinite _
        have hbij_cell : (Finset.univ.filter (fun x : X => cell b x)).card = 2 ^ Module.finrank F (Wb b) := by
          rw [← PEqualNP.Outside.L_pcx_445_aux.card_sub_eq_pow (Wb b)]
          have heq : Finset.univ.filter (fun x : X => cell b x) =
              Finset.univ.image (fun w : Wb b => x0 + w.1) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hx
              refine ⟨⟨x + x0, by
                rw [LinearMap.mem_ker]
                ext turn
                show ask turn (past b turn) (x + x0) = 0
                rw [map_add, hx turn, hx0 turn, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self]⟩, ?_⟩
              calc
                x0 + (x + x0) = x + (x0 + x0) := by abel
                _ = x := by rw [PEqualNP.Outside.L_pcx_445_aux.zmod2_vec_add_self, add_zero]
            · rintro ⟨w, rfl⟩ turn
              have hw : ask turn (past b turn) w.1 = 0 := congrFun w.2 turn
              rw [map_add, hx0 turn, hw, add_zero]
          rw [heq, Finset.card_image_of_injective]
          · simp only [Finset.card_univ]; exact Fintype.card_congr (Equiv.refl _)
          · intro w1 w2 h
            exact Subtype.ext (add_left_cancel h)
        have hbij_hits :
            (Finset.univ.filter (fun x : X => cell b x ∧ out b (last b x) = f x)).card =
            ((Finset.univ : Finset (Wb b)).filter (fun w => out b (last b (x0 + w.1)) = f (x0 + w.1))).card := by
          refine Finset.card_bij (fun x hx => ⟨x + x0, by
            rw [LinearMap.mem_ker]
            ext turn
            show ask turn (past b turn) (x + x0) = 0
            rw [map_add, (Finset.mem_filter.mp hx).2.1 turn, hx0 turn,
              PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self]⟩) ?_ ?_ ?_
          · intro x hx
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have h1 : x0 + (x + x0) = x := by
              calc
                x0 + (x + x0) = x + (x0 + x0) := by abel
                _ = x := by rw [PEqualNP.Outside.L_pcx_445_aux.zmod2_vec_add_self, add_zero]
            rw [h1]
            exact (Finset.mem_filter.mp hx).2.2
          · intro x1 _ x2 _ h
            exact add_right_cancel (congrArg Subtype.val h)
          · intro w hw
            refine ⟨x0 + w.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hw).2⟩, ?_⟩
            · intro turn
              have hw0 : ask turn (past b turn) w.1 = 0 := congrFun w.2 turn
              rw [map_add, hx0 turn, hw0, add_zero]
            · apply Subtype.ext
              calc
                x0 + w.1 + x0 = w.1 + (x0 + x0) := by abel
                _ = w.1 := by rw [PEqualNP.Outside.L_pcx_445_aux.zmod2_vec_add_self, add_zero]
        have hbound := PEqualNP.Outside.L_pcx_445_aux.cell_tail_excess_bound he f hquad (Wb b) x0
          (last b) (out b)
        change (2 * ((Finset.univ : Finset (Wb b)).filter
            (fun w => out b (last b (x0 + w.1)) = f (x0 + w.1))).card : ℤ) -
            (2 : ℤ) ^ Module.finrank F (Wb b) ≤
          (2 : ℤ) ^ (Module.finrank F (Wb b) - pb b +
            min (pb b) (if ∀ u ∈ radb b, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2)) at hbound
        rw [hbij_cell, hbij_hits]
        push_cast
        have hpb_ge_r := hpb_ge b
        have hpb_le_W : pb b ≤ Module.finrank F (Wb b) := by
          have := h2pb b
          omega
        split_ifs with hgb
        · have hcodim := (htight b hgb.1).1
          have hexp : Module.finrank F (Wb b) - pb b +
              min (pb b) (if ∀ u ∈ radb b, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2) ≤
              n - D - k1 := by
            have hpb_eq : pb b = r := hgb.1
            have : ∀ u ∈ radb b, f (x0 + u) = f x0 → True := fun _ _ _ => trivial
            split_ifs <;> omega
          have hle1 : (2 * ((Finset.univ : Finset (Wb b)).filter
              (fun w => out b (last b (x0 + w.1)) = f (x0 + w.1))).card : ℤ) -
              (2 : ℤ) ^ Module.finrank F (Wb b) ≤ (2 : ℤ) ^ (n - D - k1) :=
            le_trans hbound (pow_le_pow_right₀ (by decide) hexp)
          exact mul_le_mul_of_nonneg_left hle1 (pow_nonneg (by decide) _)
        · have hexp : k0 + (Module.finrank F (Wb b) - pb b +
              min (pb b) (if ∀ u ∈ radb b, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2)) ≤
              Module.finrank F (Wb b) := by
            split_ifs with hconst
            · have hpb_gt : r + 1 ≤ pb b := by
                by_contra hle
                apply hgb
                exact ⟨by omega, x0, hx0, hconst⟩
              omega
            · omega
          calc
            (2 : ℤ) ^ k0 *
                ((2 * ((Finset.univ : Finset (Wb b)).filter
                    (fun w => out b (last b (x0 + w.1)) = f (x0 + w.1))).card : ℤ) -
                  (2 : ℤ) ^ Module.finrank F (Wb b))
                ≤ (2 : ℤ) ^ k0 *
                    (2 : ℤ) ^ (Module.finrank F (Wb b) - pb b +
                      min (pb b) (if ∀ u ∈ radb b, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2)) :=
                  mul_le_mul_of_nonneg_left hbound (pow_nonneg (by decide) _)
            _ = (2 : ℤ) ^ (k0 + (Module.finrank F (Wb b) - pb b +
                  min (pb b) (if ∀ u ∈ radb b, f (x0 + u) = f x0 then e / 2 else (e - 1) / 2))) :=
                  (pow_add _ _ _).symm
            _ ≤ (2 : ℤ) ^ Module.finrank F (Wb b) := pow_le_pow_right₀ (by decide) hexp
      · have hemp1 : Finset.univ.filter (fun x : X => cell b x) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x _ hx
          exact hne ⟨x, hx⟩
        have hemp2 : Finset.univ.filter (fun x : X => cell b x ∧ out b (last b x) = f x) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x _ hx
          exact hne ⟨x, hx.1⟩
        rw [hemp1, hemp2]
        simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_self]
        split_ifs
        · exact mul_nonneg (pow_nonneg (by decide) _) (pow_nonneg (by decide) _)
        · exact le_refl 0
    have hcard_good_cell : ∀ b : A, goodb b →
        (Finset.univ.filter (fun x : X => cell b x)).card = 2 ^ (n - D) := by
      intro b hgb
      obtain ⟨x0, hx0, _⟩ := hgb.2
      haveI : Fintype (Wb b) := Fintype.ofFinite _
      have hcodim := (htight b hgb.1).1
      have hdim : Module.finrank F (Wb b) = n - D := by omega
      rw [← hdim, ← PEqualNP.Outside.L_pcx_445_aux.card_sub_eq_pow (Wb b)]
      have heq : Finset.univ.filter (fun x : X => cell b x) =
          Finset.univ.image (fun w : Wb b => x0 + w.1) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hx
          refine ⟨⟨x + x0, by
            rw [LinearMap.mem_ker]
            ext turn
            show ask turn (past b turn) (x + x0) = 0
            rw [map_add, hx turn, hx0 turn, PEqualNP.Outside.L_pcx_445_aux.zmod2_add_self]⟩, ?_⟩
          calc
            x0 + (x + x0) = x + (x0 + x0) := by abel
            _ = x := by rw [PEqualNP.Outside.L_pcx_445_aux.zmod2_vec_add_self, add_zero]
        · rintro ⟨w, rfl⟩ turn
          have hw : ask turn (past b turn) w.1 = 0 := congrFun w.2 turn
          rw [map_add, hx0 turn, hw, add_zero]
      rw [heq, Finset.card_image_of_injective]
      · simp only [Finset.card_univ]; exact Fintype.card_congr (Equiv.refl _)
      · intro w1 w2 h
        exact Subtype.ext (add_left_cancel h)
    have hcard_sum : (∑ b : A, ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ)) = (2 : ℤ) ^ n := by
      have h1 : (Finset.univ : Finset X).card = ∑ b : A, (Finset.univ.filter (fun x : X => cell b x)).card := by
        have h2 := Finset.card_eq_sum_card_fiberwise (f := trace) (s := Finset.univ)
          (t := (Finset.univ : Finset A)) (fun _ _ => Finset.mem_univ _)
        rw [h2]
        refine Finset.sum_congr rfl ?_
        intro b _
        congr 1
        ext x
        simp [htrace_eq]
      have hX : (Finset.univ : Finset X).card = 2 ^ n := by simp [X, F, ZMod.card]
      rw [hX] at h1
      exact_mod_cast h1.symm
    have hmain_int :
        (2 : ℤ) ^ k0 *
          ((2 * Nat.card {x : X // ∃ b : A, cell b x ∧ out b (last b x) = f x} : ℤ) - (2 : ℤ) ^ n) ≤
        (2 : ℤ) ^ k0 *
          ((2 * Nat.card {x : X // guess (first x) (tail (first x) x) = f x} : ℤ) - (2 : ℤ) ^ n) := by
      rw [hlhs_split, hrhs_exact, Finset.mul_sum, Finset.mul_sum]
      have hsum_ex := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun b _ => hcell_ex b)
      refine le_trans hsum_ex ?_
      have h2m_le_n : 2 * m ≤ n := by omega
      have hk1_le_k0 : k1 ≤ k0 := by omega
      have hk0_le_nD : k0 ≤ n - D := by omega
      have hcardA : (Fintype.card A : ℤ) = (2 : ℤ) ^ D := by simp [A, F, ZMod.card]
      have hrhs_eval :
          (∑ b : A, (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - (r - sOf b))) =
          if clearP then
            ((2 : ℤ) ^ D - 1) * (2 : ℤ) ^ (n - D) + (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - k1)
          else (2 : ℤ) ^ n := by
        split_ifs with hcl
        · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ bGood)]
          have hbG : sOf bGood = min r (e / 2) := if_pos ⟨hcl, rfl⟩
          have hother : ∀ b ∈ Finset.univ.erase bGood,
              (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - (r - sOf b)) = (2 : ℤ) ^ (n - D) := by
            intro b hb
            have hne : b ≠ bGood := (Finset.mem_erase.mp hb).1
            have hs : sOf b = min r ((e - 1) / 2) := if_neg (fun h => hne h.2)
            rw [hs, ← pow_add]
            congr 1
            omega
          rw [hbG, Finset.sum_congr rfl hother, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ bGood),
            Finset.card_univ, nsmul_eq_mul]
          have hcardA_nat : Fintype.card A = 2 ^ D := by simp [A, F, ZMod.card]
          rw [hcardA_nat]
          have h1le : 1 ≤ 2 ^ D := Nat.one_le_pow D 2 (by decide)
          have hcast : ((2 ^ D - 1 : ℕ) : ℤ) = (2 : ℤ) ^ D - 1 := by
            rw [Nat.cast_sub h1le]; push_cast; rfl
          rw [hcast]
          ring
        · have hall : ∀ b : A, (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - (r - sOf b)) = (2 : ℤ) ^ (n - D) := by
            intro b
            have hs : sOf b = min r ((e - 1) / 2) := if_neg (fun h => hcl h.1)
            rw [hs, ← pow_add]
            congr 1
            omega
          rw [Finset.sum_congr rfl (fun b _ => hall b), Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, hcardA, ← pow_add]
          congr 1
          omega
      rw [hrhs_eval]
      by_cases hex_good : ∃ b0 : A, goodb b0
      · obtain ⟨b0, hb0⟩ := hex_good
        have hcl : clearP := hgood_clear b0 hb0
        rw [if_pos hcl]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
        rw [if_pos hb0]
        have hother : ∀ b ∈ Finset.univ.erase b0,
            (if goodb b then (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - k1)
             else ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ)) =
            ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ) := by
          intro b hb
          have hne : b ≠ b0 := (Finset.mem_erase.mp hb).1
          rw [if_neg (fun hgb => hne (hgood_uniq b b0 hgb hb0))]
        rw [Finset.sum_congr rfl hother]
        have hrest_sum : (∑ b ∈ Finset.univ.erase b0,
            ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ)) =
            ((2 : ℤ) ^ D - 1) * (2 : ℤ) ^ (n - D) := by
          have hsplit := Finset.add_sum_erase (s := (Finset.univ : Finset A))
            (f := fun b : A => ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ))
            (Finset.mem_univ b0)
          rw [hcard_sum, hcard_good_cell b0 hb0] at hsplit
          have hpow : (2 : ℤ) ^ n = (2 : ℤ) ^ D * (2 : ℤ) ^ (n - D) := by
            rw [← pow_add]; congr 1; omega
          push_cast at hsplit
          linarith
        rw [hrest_sum]
        linarith
      · have hnone : ∀ b : A,
            (if goodb b then (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - k1)
             else ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ)) =
            ((Finset.univ.filter (fun x : X => cell b x)).card : ℤ) := by
          intro b
          rw [if_neg (fun hgb => hex_good ⟨b, hgb⟩)]
        rw [Finset.sum_congr rfl (fun b _ => hnone b), hcard_sum]
        split_ifs with hcl
        · have hpow : (2 : ℤ) ^ n = (2 : ℤ) ^ D * (2 : ℤ) ^ (n - D) := by
            rw [← pow_add]; congr 1; omega
          have hle_pow : (2 : ℤ) ^ (n - D) ≤ (2 : ℤ) ^ k0 * (2 : ℤ) ^ (n - D - k1) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by decide) (by omega)
          rw [hpow]
          linarith
        · exact le_refl _
    have hpos : (0 : ℤ) < (2 : ℤ) ^ k0 := pow_pos (by decide) k0
    have hcancel :
        (2 * Nat.card {x : X // ∃ b : A, cell b x ∧ out b (last b x) = f x} : ℤ) - (2 : ℤ) ^ n ≤
        (2 * Nat.card {x : X // guess (first x) (tail (first x) x) = f x} : ℤ) - (2 : ℤ) ^ n :=
      le_of_mul_le_mul_left hmain_int hpos
    change Nat.card {x : X // ∃ b : A, cell b x ∧ out b (last b x) = f x} ≤
      Nat.card {x : X // guess (first x) (tail (first x) x) = f x}
    omega

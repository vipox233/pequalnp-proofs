import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_444_aux

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
    have := LinearMap.congr_fun h ⟨v, hv⟩
    exact this
  · intro h
    ext ⟨v, hv⟩
    exact h v hv

def radSub {n : ℕ} (f : X n → F)
    (hquad : ∀ p u v : X n, f (p + u + v) + f (p + u) + f (p + v) + f p =
      f (u + v) + f u + f v + f 0)
    (W : Submodule F (X n)) : Submodule F (X n) :=
  W ⊓ orthSub f hquad W

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
            · show Blin f hquad u w = 0
              show f (u + w) + f u + f w + f 0 = 0
              rw [B_symm f u w]
              exact (mem_orthSub f hquad W w).mp hw_orth u huW
            · show Blin f hquad v w = 0
              show f (v + w) + f v + f w + f 0 = 0
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

lemma natCard_sub_eq_pow {n : ℕ} (W : Submodule F (X n)) :
    Nat.card {u : X n // u ∈ W} = 2 ^ Module.finrank F W := by
  have : Fintype W := Fintype.ofFinite _
  have h1 := Module.card_eq_pow_finrank (K := F) (V := W)
  have h3 : Fintype.card F = 2 := ZMod.card 2
  rw [Nat.card_eq_fintype_card, h1, h3]

lemma log2_natCard_sub {n : ℕ} (W : Submodule F (X n)) :
    (Nat.card {u : X n // u ∈ W}).log2 = Module.finrank F W := by
  rw [natCard_sub_eq_pow W, Nat.log2_two_pow]

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

end PEqualNP.Outside.L_pcx_444_aux

theorem PEqualNP.Outside.L_pcx_444 : ∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ (f : X → F),
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) →
    let m := (n - (Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let clear := ∀ u : X, (∀ v : X, B u v=0) → f u=f 0
    ∀ D : ℕ, D ≤ m →
      let A := Fin D → F
      let past := fun (b : A) (stage : Fin D) (j : Fin stage.val) =>
        b ⟨j.val, Nat.lt_trans j.isLt stage.isLt⟩
      ∀ (ask : (step : Fin D) → (Fin step.val → F) → X →ₗ[F] F),
        let cell := fun (b : A) (x : X) => ∀ turn, ask turn (past b turn) x=b turn
        let dir := fun (b : A) (u : X) => ∀ turn, ask turn (past b turn) u=0
        let rad := fun (b : A) (u : X) => dir b u ∧ ∀ v, dir b v → B u v=0
        let pairs := fun b : A =>
          ((Nat.card {u : X // dir b u}).log2 - (Nat.card {u : X // rad b u}).log2)/2
        let good := fun b : A => pairs b=m-D ∧
          ∃ x : X, cell b x ∧ ∀ u, rad b u → f (x+u)=f x
        (∀ b : A, (∃ x, cell b x) → m-D ≤ pairs b) ∧
        (∀ b : A, (∃ x, cell b x) → pairs b=m-D →
          2^D * Nat.card {x : X // cell b x} = Nat.card X) ∧
        Nat.card {b : A // good b} ≤ 1 ∧
        (¬ clear → Nat.card {b : A // good b} = 0) := by
  intro n
  dsimp only
  intro f hquad D hDm ask
  let F := PEqualNP.Outside.L_pcx_444_aux.F
  let X := PEqualNP.Outside.L_pcx_444_aux.X n
  let B := fun u v : X => f (u + v) + f u + f v + f 0
  let R0 : Submodule F X := LinearMap.ker (PEqualNP.Outside.L_pcx_444_aux.Blin f hquad)
  have hR0_mem : ∀ u : X, u ∈ R0 ↔ ∀ v : X, B u v = 0 := by
    intro u
    simp only [R0, LinearMap.mem_ker]
    constructor
    · intro h v
      exact LinearMap.congr_fun h v
    · intro h
      apply LinearMap.ext
      intro v
      exact h v
  have hR0_card : Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card {u : X // u ∈ R0} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun u => (hR0_mem u).symm)
  have hR0_log2 : (Nat.card {u : X // ∀ v : X, B u v = 0}).log2 = Module.finrank F R0 := by
    rw [hR0_card, PEqualNP.Outside.L_pcx_444_aux.log2_natCard_sub R0]
  have hrad_top : PEqualNP.Outside.L_pcx_444_aux.radSub f hquad ⊤ = R0 := by
    ext u
    rw [PEqualNP.Outside.L_pcx_444_aux.radSub, Submodule.mem_inf,
      PEqualNP.Outside.L_pcx_444_aux.mem_orthSub, hR0_mem]
    simp only [Submodule.mem_top, true_and, true_imp_iff]
    rfl
  have hm_even : Even (n - Module.finrank F R0) := by
    have h1 := PEqualNP.Outside.L_pcx_444_aux.even_finrank_sub_rad f hquad n ⊤
      (by rw [finrank_top, Module.finrank_fin_fun])
    rw [finrank_top, Module.finrank_fin_fun, hrad_top] at h1
    exact h1
  let m := (n - (Nat.card {u : X // ∀ v : X, B u v = 0}).log2) / 2
  have h2m : 2 * m = n - Module.finrank F R0 := by
    rcases hm_even with ⟨t, ht⟩
    have hm_eq : m = (n - Module.finrank F R0) / 2 := by rw [← hR0_log2]
    omega
  let A := Fin D → F
  let past := fun (b : A) (stage : Fin D) (j : Fin stage.val) =>
    b ⟨j.val, Nat.lt_trans j.isLt stage.isLt⟩
  let cell := fun (b : A) (x : X) => ∀ turn, ask turn (past b turn) x = b turn
  let dir := fun (b : A) (u : X) => ∀ turn, ask turn (past b turn) u = 0
  let rad := fun (b : A) (u : X) => dir b u ∧ ∀ v, dir b v → B u v = 0
  let pairs := fun b : A =>
    ((Nat.card {u : X // dir b u}).log2 - (Nat.card {u : X // rad b u}).log2) / 2
  let good := fun b : A => pairs b = m - D ∧
    ∃ x : X, cell b x ∧ ∀ u, rad b u → f (x + u) = f x
  let Lb : A → (X →ₗ[F] A) := fun b =>
    { toFun := fun x turn => ask turn (past b turn) x
      map_add' := fun u v => by ext turn; exact map_add (ask turn (past b turn)) u v
      map_smul' := fun c u => by ext turn; exact map_smul (ask turn (past b turn)) c u }
  let Wb : A → Submodule F X := fun b => LinearMap.ker (Lb b)
  have hWb_mem : ∀ b u, u ∈ Wb b ↔ dir b u := by
    intro b u
    simp only [Wb, LinearMap.mem_ker]
    constructor
    · intro h turn
      exact congrFun h turn
    · intro h
      ext turn
      exact h turn
  have hradb_mem : ∀ b u, u ∈ PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b) ↔ rad b u := by
    intro b u
    rw [PEqualNP.Outside.L_pcx_444_aux.radSub, Submodule.mem_inf,
      PEqualNP.Outside.L_pcx_444_aux.mem_orthSub, hWb_mem]
    simp only [rad, hWb_mem, B]
    rfl
  have hWb_log2 : ∀ b, (Nat.card {u : X // dir b u}).log2 = Module.finrank F (Wb b) := by
    intro b
    have hc : Nat.card {u : X // dir b u} = Nat.card {u : X // u ∈ Wb b} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun u => (hWb_mem b u).symm))
    rw [hc, PEqualNP.Outside.L_pcx_444_aux.log2_natCard_sub]
  have hradb_log2 : ∀ b, (Nat.card {u : X // rad b u}).log2 =
      Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)) := by
    intro b
    have hc : Nat.card {u : X // rad b u} =
        Nat.card {u : X // u ∈ PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun u => (hradb_mem b u).symm))
    rw [hc, PEqualNP.Outside.L_pcx_444_aux.log2_natCard_sub]
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
  have hDm' : D ≤ m := hDm
  have h2pairs : ∀ b, 2 * pairs b =
      Module.finrank F (Wb b) -
        Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)) := by
    intro b
    have hle : Module.finrank F (Wb b) ≤ n := by
      have := Submodule.finrank_le (Wb b)
      rwa [Module.finrank_fin_fun] at this
    have hev := PEqualNP.Outside.L_pcx_444_aux.even_finrank_sub_rad f hquad n (Wb b) hle
    rcases hev with ⟨t, ht⟩
    have ht' : Module.finrank F (Wb b) -
        Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)) = t + t := ht
    have hp : pairs b = (Module.finrank F (Wb b) -
        Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b))) / 2 := by
      show ((Nat.card {u : X // dir b u}).log2 - (Nat.card {u : X // rad b u}).log2) / 2 = _
      rw [hWb_log2 b, hradb_log2 b]
    omega
  have hpairs_ge : ∀ b, m - D ≤ pairs b := by
    intro b
    have h1 : Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b)) ≤
        Module.finrank F R0 + (n - Module.finrank F (Wb b)) :=
      (PEqualNP.Outside.L_pcx_444_aux.finrank_orthSub_le f hquad (Wb b)).1
    have h2 : Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)) ≤
        Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b)) :=
      Submodule.finrank_mono inf_le_right
    have h3 := hWb_codim b
    have h4 := h2pairs b
    have hWb_le : Module.finrank F (Wb b) ≤ n := by
      have := Submodule.finrank_le (Wb b)
      rwa [Module.finrank_fin_fun] at this
    have hR0_le : Module.finrank F R0 ≤ n := by
      have := Submodule.finrank_le R0
      rwa [Module.finrank_fin_fun] at this
    omega
  have htight : ∀ b, pairs b = m - D →
      Module.finrank F (Wb b) + D = n ∧
      (∀ u ∈ R0, rad b u) ∧
      (∀ ℓ : X →ₗ[F] F, (∀ v ∈ Wb b, ℓ v = 0) →
        ∃ u, rad b u ∧ PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u = ℓ) := by
    intro b hpb
    have hfb := PEqualNP.Outside.L_pcx_444_aux.finrank_orthSub_le f hquad (Wb b)
    have h1 : Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b)) ≤
        Module.finrank F R0 + (n - Module.finrank F (Wb b)) := hfb.1
    have h2 : Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)) ≤
        Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b)) :=
      Submodule.finrank_mono inf_le_right
    have h3 := hWb_codim b
    have h4 := h2pairs b
    have hWb_le : Module.finrank F (Wb b) ≤ n := by
      have := Submodule.finrank_le (Wb b)
      rwa [Module.finrank_fin_fun] at this
    have hR0_le : Module.finrank F R0 ≤ n := by
      have := Submodule.finrank_le R0
      rwa [Module.finrank_fin_fun] at this
    have hcodim_eq : Module.finrank F (Wb b) + D = n := by omega
    have horth_eq : Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b)) =
        Module.finrank F R0 + (n - Module.finrank F (Wb b)) := by omega
    have hrad_eq_dim : Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b)) =
        Module.finrank F (PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b)) := by omega
    have hrad_eq_orth : PEqualNP.Outside.L_pcx_444_aux.radSub f hquad (Wb b) =
        PEqualNP.Outside.L_pcx_444_aux.orthSub f hquad (Wb b) :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right hrad_eq_dim
    refine ⟨hcodim_eq, ?_, ?_⟩
    · intro u huR0
      rw [← hradb_mem b u, hrad_eq_orth, PEqualNP.Outside.L_pcx_444_aux.mem_orthSub]
      intro v _
      exact (hR0_mem u).mp huR0 v
    · intro ℓ hℓ
      obtain ⟨u, hu_orth, hu_eq⟩ := hfb.2 horth_eq ℓ hℓ
      refine ⟨u, ?_, hu_eq⟩
      rw [← hradb_mem b u, hrad_eq_orth]
      exact hu_orth
  have hgood_clear : ∀ b, good b → ∀ u : X, (∀ v : X, B u v = 0) → f u = f 0 := by
    intro b ⟨hpb, x, _, hfx⟩ u hu
    have hru : rad b u := (htight b hpb).2.1 u ((hR0_mem u).mpr hu)
    have h1 : f (x + u) = f x := hfx u hru
    have h2 : B u x = 0 := hu x
    have h3 : f (x + u) + f x + f u + f 0 = 0 := by
      have := PEqualNP.Outside.L_pcx_444_aux.B_symm f u x
      rw [← this]
      exact h2
    rw [h1] at h3
    have h4 : f u + f 0 = 0 := by
      have hxx := PEqualNP.Outside.L_pcx_444_aux.zmod2_add_self (f x)
      calc
        f u + f 0 = (f x + f x) + (f u + f 0) := by rw [hxx, zero_add]
        _ = f x + f x + f u + f 0 := by ring
        _ = 0 := h3
    exact PEqualNP.Outside.L_pcx_444_aux.zmod2_add_eq_zero h4
  refine ⟨fun b _ => hpairs_ge b, ?_, ?_, ?_⟩
  · intro b ⟨x0, hx0⟩ hpb
    have hcodim_eq := (htight b hpb).1
    have hcard_cell : Nat.card {x : X // cell b x} = Nat.card {u : X // u ∈ Wb b} := by
      apply Nat.card_congr
      refine
        { toFun := fun x => ⟨x.1 + x0, (hWb_mem b _).mpr (fun turn => by
            rw [map_add, x.2 turn, hx0 turn]
            exact PEqualNP.Outside.L_pcx_444_aux.zmod2_add_self (b turn))⟩
          invFun := fun u => ⟨u.1 + x0, fun turn => by
            rw [map_add, (hWb_mem b u.1).mp u.2 turn, hx0 turn, zero_add]⟩
          left_inv := fun x => by
            apply Subtype.ext
            dsimp only
            rw [add_assoc, PEqualNP.Outside.L_pcx_444_aux.zmod2_vec_add_self x0, add_zero]
          right_inv := fun u => by
            apply Subtype.ext
            dsimp only
            rw [add_assoc, PEqualNP.Outside.L_pcx_444_aux.zmod2_vec_add_self x0, add_zero] }
    rw [hcard_cell, PEqualNP.Outside.L_pcx_444_aux.natCard_sub_eq_pow (Wb b), ← pow_add, add_comm D,
      hcodim_eq]
    have hcardX : Nat.card X = 2 ^ n := by
      rw [Nat.card_eq_fintype_card]
      simp [X, ZMod.card]
    rw [hcardX]
  · have hsub : Subsingleton {b : A // good b} := by
      constructor
      rintro ⟨b1, hg1⟩ ⟨b2, hg2⟩
      apply Subtype.ext
      by_contra hne
      have hex : ∃ k : ℕ, ∃ hk : k < D, b1 ⟨k, hk⟩ ≠ b2 ⟨k, hk⟩ := by
        by_contra hall
        push Not at hall
        apply hne
        ext t
        exact hall t.val t.isLt
      classical
      let k0 := Nat.find hex
      have hk0_spec := Nat.find_spec hex
      obtain ⟨hk0_lt, hb_ne⟩ := hk0_spec
      let t : Fin D := ⟨k0, hk0_lt⟩
      have hpast_eq : past b1 t = past b2 t := by
        ext j
        have hj_lt : j.val < k0 := j.isLt
        have hnot := Nat.find_min hex hj_lt
        push Not at hnot
        exact hnot (Nat.lt_trans j.isLt hk0_lt)
      let ℓ : X →ₗ[F] F := ask t (past b1 t)
      have hℓ1 : ∀ v ∈ Wb b1, ℓ v = 0 := fun v hv => (hWb_mem b1 v).mp hv t
      have hℓ2 : ∀ v ∈ Wb b2, ℓ v = 0 := fun v hv => by
        have h := (hWb_mem b2 v).mp hv t
        simpa [ℓ, hpast_eq] using h
      obtain ⟨hpb1, x1, hx1_cell, hx1_rad⟩ := hg1
      obtain ⟨hpb2, x2, hx2_cell, hx2_rad⟩ := hg2
      obtain ⟨u1, hu1_rad, hu1_B⟩ := (htight b1 hpb1).2.2 ℓ hℓ1
      obtain ⟨u2, hu2_rad, hu2_B⟩ := (htight b2 hpb2).2.2 ℓ hℓ2
      have hu12_R0 : ∀ v : X, B (u1 + u2) v = 0 := by
        intro v
        have h1 : PEqualNP.Outside.L_pcx_444_aux.Blin f hquad (u1 + u2) v =
            PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u1 v +
              PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u2 v := by
          rw [map_add, LinearMap.add_apply]
        change PEqualNP.Outside.L_pcx_444_aux.Blin f hquad (u1 + u2) v = 0
        rw [h1, hu1_B, hu2_B]
        exact PEqualNP.Outside.L_pcx_444_aux.zmod2_add_self (ℓ v)
      have hfu12 : f (u1 + u2) = f 0 := hgood_clear b1 ⟨hpb1, x1, hx1_cell, hx1_rad⟩ (u1 + u2) hu12_R0
      have hBu1u2 : B u1 u2 = 0 := by
        have h1 : B (u1 + u2) u2 = 0 := hu12_R0 u2
        have h2 : PEqualNP.Outside.L_pcx_444_aux.Blin f hquad (u1 + u2) u2 =
            PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u1 u2 +
              PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u2 u2 := by
          rw [map_add, LinearMap.add_apply]
        have h3 : PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u2 u2 = 0 :=
          PEqualNP.Outside.L_pcx_444_aux.B_self f u2
        change PEqualNP.Outside.L_pcx_444_aux.Blin f hquad u1 u2 = 0
        have h4 : PEqualNP.Outside.L_pcx_444_aux.Blin f hquad (u1 + u2) u2 = 0 := h1
        rw [h2, h3, add_zero] at h4
        exact h4
      have hfu_eq : f u1 = f u2 := by
        have h1 : f (u1 + u2) + f u1 + f u2 + f 0 = 0 := hBu1u2
        rw [hfu12] at h1
        have h2 : f u1 + f u2 = 0 := by
          have h00 := PEqualNP.Outside.L_pcx_444_aux.zmod2_add_self (f 0)
          calc
            f u1 + f u2 = (f 0 + f 0) + (f u1 + f u2) := by rw [h00, zero_add]
            _ = f 0 + f u1 + f u2 + f 0 := by ring
            _ = 0 := h1
        exact PEqualNP.Outside.L_pcx_444_aux.zmod2_add_eq_zero h2
      have hval1 : f u1 + f 0 = b1 t := by
        have h1 : f (x1 + u1) = f x1 := hx1_rad u1 hu1_rad
        have h2 : f (u1 + x1) + f u1 + f x1 + f 0 = ℓ x1 := LinearMap.congr_fun hu1_B x1
        rw [add_comm u1 x1, h1] at h2
        have h3 : f (x1) + f u1 + f x1 + f 0 = f u1 + f 0 := by
          have hxx := PEqualNP.Outside.L_pcx_444_aux.zmod2_add_self (f x1)
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
        have h3 : f (x2) + f u2 + f x2 + f 0 = f u2 + f 0 := by
          have hxx := PEqualNP.Outside.L_pcx_444_aux.zmod2_add_self (f x2)
          calc
            f x2 + f u2 + f x2 + f 0 = (f x2 + f x2) + (f u2 + f 0) := by ring
            _ = f u2 + f 0 := by rw [hxx, zero_add]
        rw [h3] at h2
        rw [h2]
        have hx2t := hx2_cell t
        simpa [ℓ, hpast_eq] using hx2t
      apply hb_ne
      rw [← hval1, ← hval2, hfu_eq]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  · intro hnclear
    have : IsEmpty {b : A // good b} := by
      constructor
      rintro ⟨b, hgb⟩
      exact hnclear (hgood_clear b hgb)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero

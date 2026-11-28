import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_461_aux
namespace Pcx461Generic
open scoped BigOperators
abbrev F := ZMod 2
abbrev X (n : ℕ) := Fin n → F
variable {j : ℕ} {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]

def Polar (f : V → F) := ∀ p u v : V,
  f (p+u+v)+f (p+u)+f (p+v)+f p=f (u+v)+f u+f v+f 0

private lemma xx (x : V) : x+x=0 := by exact ZModModule.add_self _

def Aff (e : Equiv.Perm (V)) := ∃ L : V →ₗ[F] V, ∀ z, e z = L z + e 0

lemma fiber_equiv (f : V → F) (hq : Polar f) (x y : V) (hxy : f x = f y) :
    ∃ e : Equiv.Perm (V), Aff e ∧ (∀ z, f (e z) = f z) ∧ e x = y := by
  let t := x+y
  let d := fun z : V => f (z+t)+f z
  let l : V →ₗ[F] F := {
    toFun := fun z => d z+d 0
    map_add' := by
      intro a b
      have h := hq a b t
      simp only [d, zero_add]
      have aux : ∀ A B C D E G H : F,
          A+B+C+D = E+G+H+f 0 → A+B+(H+f 0) = C+D+(H+f 0)+(E+G+(H+f 0)) := by
        generalize f 0 = k
        revert k
        decide +kernel
      exact aux _ _ _ _ _ _ _ h
    map_smul' := by
      intro c a
      have hb : ∀ v : F, v=0 ∨ v=1 := by decide
      rcases hb c with rfl|rfl <;> simp [ZModModule.add_self] }
  let T := fun z : V => z + (1+d z) • t
  let L : V →ₗ[F] V := LinearMap.id + l.smulRight t
  have ha : ∀ z, T z = L z + T 0 := by
    intro z
    simp only [T, L, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, zero_add]
    change z+(1+d z) • t = z+(d z+d 0) • t + (1+d 0) • t
    rw [add_assoc, ← add_smul]
    congr 2
    have aux : ∀ a b : F, 1+a=a+b+(1+b) := by decide
    exact aux _ _
  have hstep : ∀ z : V, T z = if f (z+t) = f z then z+t else z := by
    intro z
    have aux : ∀ a b : F, 1+(a+b) = if a=b then 1 else 0 := by decide
    simp only [T,d,aux]
    split <;> simp
  have inv : Function.Involutive T := by
    intro z
    rw [hstep z]; split
    · rename_i h
      rw [hstep, add_assoc, xx, add_zero, if_pos h.symm]
    · exact hstep z |>.trans (if_neg ‹_›)
  refine ⟨⟨T,T,inv,inv⟩, ⟨L,ha⟩, ?_, ?_⟩
  · intro z; change f (T z) = f z; rw [hstep]; split <;> simp_all
  · change T x = y
    have ht : x+t=y := by dsimp [t]; rw [← add_assoc, xx, zero_add]
    simp [hstep,ht,hxy]

abbrev G (f : V → F) := {e : Equiv.Perm (V) // Aff e ∧ ∀ z, f (e z) = f z}

noncomputable instance (f : V → F) : Fintype (G f) := Fintype.ofFinite _

instance (f : V → F) : Nonempty (G f) :=
  ⟨⟨Equiv.refl _, ⟨LinearMap.id, by simp⟩, by simp⟩⟩

private def pre {f : V → F} (h e : G f) : G f :=
  ⟨h.val.trans e.val, by
    obtain ⟨l,hl⟩ := h.property.1
    obtain ⟨k,hk⟩ := e.property.1
    refine ⟨⟨k.comp l, fun z => ?_⟩, fun z => (e.property.2 _).trans (h.property.2 _)⟩
    change e.val (h.val z) = k (l z) + e.val (h.val 0)
    rw [hk (h.val z), hl z, map_add, hk (h.val 0), add_assoc]⟩

private lemma pre_bij {f : V → F} (h : G f) : Function.Bijective (pre h) := by
  classical
  apply Finite.injective_iff_bijective.mp
  intro e d he
  apply Subtype.ext; apply Equiv.ext; intro z
  obtain ⟨y,rfl⟩ := h.val.surjective z
  exact congrArg (fun a : G f => a.val y) he

private lemma equal_on_fiber {f : V → F} (hq : Polar f) (v : V → ℚ) (x y : V)
    (h : f x = f y) :
    ∑ e : G f, v (e.val x) = ∑ e : G f, v (e.val y) := by
  classical
  obtain ⟨e,ha,hf,hxy⟩ := fiber_equiv f hq x y h
  let k : G f := ⟨e,ha,hf⟩
  let b := Equiv.ofBijective _ (pre_bij k)
  apply (Fintype.sum_equiv b.symm _ _ ?_)
  intro d
  have hb := b.apply_symm_apply d
  have hh := congrArg (fun a : G f => v (a.val x)) hb
  change v ((b.symm d).val (e x)) = v (d.val x) at hh
  rwa [hxy,eq_comm] at hh

private def classEquiv {f : V → F} (e : G f) (c : F) :
    {x // f x = c} ≃ {x // f x = c} where
  toFun := fun x => ⟨e.val x, (e.property.2 _).trans x.2⟩
  invFun := fun x => ⟨e.val.symm x, by rw [← e.property.2 (e.val.symm x),e.val.apply_symm_apply]; exact x.2⟩
  left_inv := by intro x; apply Subtype.ext; exact e.val.left_inv _
  right_inv := by intro x; apply Subtype.ext; exact e.val.right_inv _

private lemma class_sum {f : V → F} (e : G f) (c : F) (v : V → ℚ) :
    ∑ y : {x // f x = c}, v (e.val y) = ∑ y : {x // f x = c}, v y := by
  classical
  exact Fintype.sum_equiv (classEquiv e c) _ _ (fun _ => rfl)

lemma orbit_ge {f : V → F} (hq : Polar f) (v : V → ℚ) (p : ℚ)
    (hc : ∀ c : F, p * Fintype.card {x // f x = c} ≤ ∑ y : {x // f x = c}, v y)
    (x : V) : p * Fintype.card (G f) ≤ ∑ e : G f, v (e.val x) := by
  classical
  let B := {y : V // f y = f x}
  letI : Nonempty B := ⟨⟨x,rfl⟩⟩
  have hb : 0 < (Fintype.card B : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  apply le_of_mul_le_mul_left (a := (Fintype.card B : ℚ)) _ hb
  calc
    _ = (Fintype.card (G f):ℚ) * (p * Fintype.card B) := by ring
    _ ≤ (Fintype.card (G f):ℚ) * (∑ y : B, v y) := by gcongr; exact hc _
    _ = ∑ _e : G f, ∑ y : B, v y := by simp
    _ = ∑ e : G f, ∑ y : B, v (e.val y) := by
      apply Finset.sum_congr rfl; intro e _; exact (class_sum e (f x) v).symm
    _ = ∑ y : B, ∑ e : G f, v (e.val y) := Finset.sum_comm
    _ = ∑ _y : B, ∑ e : G f, v (e.val x) := by
      apply Finset.sum_congr rfl; intro y _; apply equal_on_fiber hq; exact y.2
    _ = _ := by simp

private lemma sum_div_rat {K : Type*} [Fintype K] (v : K → ℚ) (N : ℚ) :
    (∑ i, v i) / N = ∑ i, v i / N := by simp [div_eq_mul_inv, Finset.sum_mul]

lemma lift_classes {f : V → F} (hq : Polar f) {I : Type*} [Fintype I]
    (w : I → ℚ) (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (Q : I → V →ₗ[F] X j) (d : I → X j → F) (p : ℚ)
    (hc : ∀ c : F, p * Fintype.card {x // f x = c} ≤
      ∑ y : {x // f x = c}, ∑ i, if d i (Q i y) = f y then w i else 0) :
    ∃ (r : ℕ) (w : Fin r → ℚ) (q : Fin r → V →ₗ[F] X j) (d : Fin r → X j → F),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ x, p ≤ ∑ i, if d i (q i x) = f x then w i else 0 := by
  classical
  let N : ℚ := Fintype.card (G f)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  let K := G f × I
  let E : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let L (e : G f) := e.property.1.choose
  let W (k : K) := w k.2 / N
  let A (k : K) := (Q k.2).comp (L k.1)
  let D (k : K) (z : X j) := d k.2 (z + Q k.2 (k.1.val 0))
  refine ⟨Fintype.card K, W ∘ E, A ∘ E, D ∘ E, fun i => div_nonneg (hw _) hN.le, ?_, ?_⟩
  · change ∑ i, W (E i) = 1
    rw [E.sum_comp]; change (∑ k : G f × I, w k.2 / N) = 1
    rw [Fintype.sum_prod_type]
    simp only [← sum_div_rat, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change N * (1/N) = 1
    field_simp
  · intro x
    let v (z : V) := ∑ i, if d i (Q i z) = f z then w i else 0
    have hg := (le_div_iff₀ hN).mpr (orbit_ge hq v p hc x)
    refine hg.trans_eq ?_
    let val (k : K) := if D k (A k x) = f x then W k else 0
    change (∑ e : G f, v (e.val x)) / N = ∑ i, val (E i)
    rw [E.sum_comp]; change _ = ∑ k : G f × I, val k
    rw [Fintype.sum_prod_type, sum_div_rat]
    apply Finset.sum_congr rfl; intro e _
    dsimp only [v]; rw [sum_div_rat]
    apply Finset.sum_congr rfl; intro i _
    have hh := e.property.1.choose_spec x
    change e.val x = L e x + e.val 0 at hh
    simp only [val, D,A,W,LinearMap.comp_apply, ← map_add, ← hh, e.property.2]
    split <;> simp

def sign (c : F) : ℚ := if c=0 then 1 else -1

abbrev Succ (f : V → F) (j : ℕ) (p : ℚ) :=
    ∃ (r : ℕ) (w : Fin r → ℚ) (q : Fin r → V →ₗ[F] X j) (d : Fin r → X j → F),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ x, p ≤ ∑ i, if d i (q i x) = f x then w i else 0

lemma lift_moments {f : V → F} (hq : Polar f) {I : Type*} [Fintype I]
    (w : I → ℚ) (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (Q : I → V →ₗ[F] X j) (d : I → X j → F) (A : ℚ)
    (H : V → ℚ) (hH : ∀ x, H x = ∑ i, w i * sign (d i (Q i x)))
    (hC : ∑ x, sign (f x) * H x = A * Fintype.card (V))
    (hD : ∑ x, H x = A * ∑ x, sign (f x)) : Succ f j ((1+A)/2) := by
  classical
  apply lift_classes hq w hw h1 Q d
  intro c
  let v (x : V) := ∑ i, if d i (Q i x) = f x then w i else 0
  let g (x : V) := sign (f x) * H x - A
  have hv (x : V) : 2*v x = 1 + sign (f x) * H x := by
    have aux : ∀ a b : F, (if a=b then (2:ℚ) else 0) = 1+sign b*sign a := by
      intro a b; have f01 : ∀ a : F, a=0 ∨ a=1 := by decide
      rcases f01 a with rfl|rfl <;> rcases f01 b with rfl|rfl <;> norm_num [sign]
    conv_rhs => rw [hH, ←h1, Finset.mul_sum, ← Finset.sum_add_distrib]
    unfold v; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have ha := aux (d i (Q i x)) (f x)
    split <;> (rename_i hh; simp only [hh, ite_true, ite_false] at ha ⊢; linear_combination (w i)*ha)
  have hz : ∑ x, g x = 0 := by
    dsimp only [g]; rw [Finset.sum_sub_distrib,hC]; simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; ring
  have hz' : ∑ x, (H x-A*sign (f x)) = 0 := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hD, sub_self]
  have haux (x : V) : (if f x = c then 2*g x else 0) = g x + sign c * (H x - A*sign (f x)) := by
    have f01 : ∀ a : F, a=0 ∨ a=1 := by decide
    rcases f01 (f x) with t|t <;> rcases f01 c with rfl|rfl <;> simp [g,sign,t] <;> ring
  have hv0 : ∑ y : {x // f x = c}, 2*g y = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x => f x = c)) (by simp) (fun x => 2*g x), Finset.sum_filter]
    simp_rw [haux]; rw [Finset.sum_add_distrib, ← Finset.mul_sum, hz,hz']; simp
  have hgv : ∀ y : {x // f x = c}, 2*g y = 4*v y - (2*(1+A)) := by
    intro y; dsimp only [g]; linarith [hv y]
  simp_rw [hgv] at hv0
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hv0
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hv0
  change _ ≤ ∑ y : {x // f x=c}, v y
  linarith

lemma even_mix (A u b : ℚ) (h : 0 ≤ u-A*b) (hh : u-A*b ≤ 1) :
    let t := (3-2*u+2*A*b)/(3+2*u-2*A*b)
    let C := 3*A/(3+2*u-2*A*b)
    0 ≤ t ∧ t ≤ 1 ∧ t*A+(1-t)*(A/2) = C ∧ t*u+(1-t)*(u/2-3/4) = b*C := by
  dsimp only
  have hpos : 0 < 3+2*u-2*A*b := by linarith
  refine ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith), ?_, ?_⟩ <;>
    field_simp <;> ring

end Pcx461Generic

namespace Donor441

private def restr461 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (W : Submodule K V) : LinearMap.BilinForm K W where
  toFun x := (B x).domRestrict W
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

namespace Phase441SymplecticStep

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def perpendicular (B : LinearMap.BilinForm K V) (e f : V) : Submodule K V :=
  LinearMap.ker (B e) ⊓ LinearMap.ker (B f)

private def remainder (B : LinearMap.BilinForm K V) (e f : V) : V →ₗ[K] V :=
  LinearMap.id - (B f).smulRight e - (B e).smulRight f

private theorem reconstructed (B : LinearMap.BilinForm K V) (e f v : V) :
    B f v • e + B e v • f + remainder B e f v = v := by
  change B f v • e + B e v • f + (v - B f v • e - B e v • f) = v
  abel

private theorem remainder_perpendicular (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) (v : V) :
    remainder B e f v ∈ perpendicular B e f := by
  change B e (v - B f v • e - B e v • f) = 0 ∧
    B f (v - B f v • e - B e v • f) = 0
  simp [map_sub, map_smul, smul_eq_mul, alt, ef, fe]

private theorem split_pair (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) (v w : V) :
    B v w =
      B f v * B e w + B e v * B f w +
        B (remainder B e f v) (remainder B e f w) := by
  have fe : B f e = 1 := (sym _ _).trans ef
  have hv := remainder_perpendicular B e f alt ef fe v
  have hw := remainder_perpendicular B e f alt ef fe w
  change B e (remainder B e f v) = 0 ∧ B f (remainder B e f v) = 0 at hv
  change B e (remainder B e f w) = 0 ∧ B f (remainder B e f w) = 0 at hw
  have he : B (remainder B e f v) e = 0 := (sym _ _).trans hv.1
  have hf : B (remainder B e f v) f = 0 := (sym _ _).trans hv.2
  calc
    B v w = B (B f v • e + B e v • f + remainder B e f v)
             (B f w • e + B e w • f + remainder B e f w) := by
               simp only [reconstructed]
    _ = _ := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, alt, ef, fe, hw.1, hw.2, he, hf] <;> ring

private def coordinates (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) :
    V ≃ₗ[K] (K × K × perpendicular B e f) where
  toFun v := ⟨B f v, B e v, ⟨remainder B e f v, remainder_perpendicular B e f alt ef fe v⟩⟩
  invFun x := x.1 • e + x.2.1 • f + x.2.2.val
  left_inv := reconstructed B e f
  right_inv := by
    rintro ⟨a,b,w⟩
    have hw := w.property
    change B e w.val = 0 ∧ B f w.val = 0 at hw
    have ha : B f (a • e + b • f + w.val) = a := by
      simp [map_add, map_smul, smul_eq_mul, alt, fe, hw.2]
    have hb : B e (a • e + b • f + w.val) = b := by
      simp [map_add, map_smul, smul_eq_mul, alt, ef, hw.1]
    refine Prod.ext ha (Prod.ext hb (Subtype.ext ?_))
    change a • e + b • f + w.val -
      B f (a • e + b • f + w.val) • e - B e (a • e + b • f + w.val) • f = w.val
    rw [ha,hb]
    abel
  map_add' x y := Prod.ext (map_add (B f) x y)
    (Prod.ext (map_add (B e) x y) (Subtype.ext (map_add (remainder B e f) x y)))
  map_smul' c x := Prod.ext (map_smul (B f) c x)
    (Prod.ext (map_smul (B e) c x) (Subtype.ext (map_smul (remainder B e f) c x)))

private theorem dimension_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) [Module.Finite K V] :
    Module.finrank K V = 2 + Module.finrank K (perpendicular B e f) := by
  rw [(coordinates B e f alt ef fe).finrank_eq, Module.finrank_prod, Module.finrank_prod]
  simp <;> omega

private def radicalEquiv (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) :
    LinearMap.ker B ≃ₗ[K] LinearMap.ker (restr461 B (perpendicular B e f)) where
  toFun w := by
    have van (z : V) : B w.val z = 0 := by
      exact congrArg (fun f : V →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have mem : w.val ∈ perpendicular B e f := by
      change B e w.val = 0 ∧ B f w.val = 0
      exact ⟨(sym _ _).trans (van e), (sym _ _).trans (van f)⟩
    refine ⟨⟨w.val,mem⟩,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    exact van z.val
  invFun w := by
    have fe := (sym f e).trans ef
    have van (z : perpendicular B e f) : B w.val.val z.val = 0 := by
      exact congrArg (fun f : perpendicular B e f →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have h := w.val.property
    change B e w.val.val = 0 ∧ B f w.val.val = 0 at h
    have fixed : remainder B e f w.val.val = w.val.val := by
      change w.val.val - B f w.val.val • e - B e w.val.val • f = w.val.val
      simp [h.1,h.2]
    refine ⟨w.val.val,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    have split := split_pair B e f alt sym ef w.val.val z
    have hz := van ⟨remainder B e f z, remainder_perpendicular B e f alt ef fe z⟩
    simpa [h.1,h.2,fixed] using split.trans (by simpa [h.1,h.2,fixed] using hz)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

private theorem rank_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1)
    [Module.Finite K V] :
    Module.finrank K (LinearMap.range B) =
      2 + Module.finrank K (LinearMap.range (restr461 B (perpendicular B e f))) := by
  have ambient := B.finrank_range_add_finrank_ker
  have residual := (restr461 B (perpendicular B e f)).finrank_range_add_finrank_ker
  have ker := (radicalEquiv B e f alt sym ef).finrank_eq
  have dim := dimension_step B e f alt ef ((sym _ _).trans ef)
  omega

end Phase441SymplecticStep

namespace Phase441SymplecticCoordinates
open Phase441SymplecticStep

universe u v
variable {K : Type u} [Field K]

private abbrev Coordinates {V : Type v} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (r : ℕ) :=
  { p : (Fin r → V →ₗ[K] K) × (Fin r → V →ₗ[K] K) //
    (∀ x y, B x y = ∑ i : Fin r, (p.1 i x * p.2 i y + p.2 i x * p.1 i y)) ∧
      Function.Surjective (fun x : V => (fun i => p.1 i x, fun i => p.2 i x)) }

variable {V : Type v} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V} {r : ℕ}

private abbrev Coordinates.left (D : Coordinates B r) := D.val.1
private abbrev Coordinates.right (D : Coordinates B r) := D.val.2
private theorem Coordinates.product (D : Coordinates B r) (x y : V) :
    B x y = ∑ i : Fin r, (D.left i x * D.right i y + D.right i x * D.left i y) := D.property.1 x y
private theorem Coordinates.independent (D : Coordinates B r) :
    Function.Surjective (fun x : V => (fun i => D.left i x, fun i => D.right i x)) := D.property.2

omit [AddCommGroup V] [Module K V] in

private theorem normalForm (r : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V],
      ∀ B : LinearMap.BilinForm K V,
        (∀ x, B x x = 0) → (∀ x y, B x y = B y x) →
          Module.finrank K (LinearMap.range B) = 2*r → Nonempty (Coordinates B r) := by
  induction r with
  | zero =>
    intro V _ _ _ B _ _ rank
    have zr : Module.finrank K (LinearMap.range B) = 0 := by simpa using rank
    have bottom : LinearMap.range B = ⊥ := Submodule.finrank_eq_zero.mp zr
    have van (x y : V) : B x y = 0 := by
      have mem := LinearMap.mem_range_self B x
      rw [bottom] at mem
      have eq : B x = 0 := by simpa using mem
      exact congrArg (fun f : V →ₗ[K] K => f y) eq
    refine ⟨⟨(Fin.elim0, Fin.elim0), ?_, ?_⟩⟩
    · intro x y
      simpa using van x y
    · intro z
      refine ⟨0,Prod.ext ?_ ?_⟩
      · funext i
        exact i.elim0
      · funext i
        exact i.elim0
  | succ r ih =>
    intro V _ _ _ B alt sym rank
    have nn : B ≠ 0 := by
      intro h
      have z : Module.finrank K (LinearMap.range B) = 0 :=
        Submodule.finrank_eq_zero.mpr (LinearMap.range_eq_bot.mpr h)
      omega
    obtain ⟨e,f0,notZero⟩ : ∃ e f, B e f ≠ 0 := by
      by_contra! h
      apply nn
      ext x y
      exact h x y
    let f : V := (B e f0)⁻¹ • f0
    have one : B e f = 1 := by
      simp [f, map_smul, smul_eq_mul, notZero]
    have other : B f e = 1 := (sym _ _).trans one
    let W := perpendicular B e f
    let pr : V →ₗ[K] W := (remainder B e f).codRestrict W
      (remainder_perpendicular B e f alt one other)
    have smaller : Module.finrank K (LinearMap.range (restr461 B W)) = 2*r := by
      have step := rank_step B e f alt sym one
      change Module.finrank K (LinearMap.range B) =
        2 + Module.finrank K (LinearMap.range (restr461 B W)) at step
      omega
    obtain ⟨prev⟩ := ih (restr461 B W) (fun x => alt x.val)
      (fun x y => sym x.val y.val) smaller
    refine ⟨⟨(Fin.cons (B f) (fun i => (prev.left i).comp pr),
      Fin.cons (B e) (fun i => (prev.right i).comp pr)), ?_, ?_⟩⟩
    · intro x y
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply]
      have form := split_pair B e f alt sym one x y
      change B x y = B f x * B e y + B e x * B f y + restr461 B W (pr x) (pr y) at form
      exact form.trans (congrArg (fun t => B f x * B e y + B e x * B f y + t) (prev.product (pr x) (pr y)))
    · rintro ⟨a,b⟩
      obtain ⟨w,hw⟩ := prev.independent (Fin.tail a, Fin.tail b)
      let uv := coordinates B e f alt one other
      let x := uv.symm (a 0,b 0,w)
      have h := uv.apply_symm_apply (a 0,b 0,w)
      have hxL : B f x = a 0 := congrArg Prod.fst h
      have hxR : B e x = b 0 := congrArg (fun p : K × K × W => p.2.1) h
      have hpr : pr x = w := congrArg (fun p : K × K × W => p.2.2) h
      refine ⟨x,Prod.ext ?_ ?_⟩
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxL
        · change prev.left j (pr x) = a j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.fst hw) j
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxR
        · change prev.right j (pr x) = b j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.snd hw) j

end Phase441SymplecticCoordinates

namespace Phase441QuadraticCoordinates
open Phase441SymplecticCoordinates

private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {B : LinearMap.BilinForm F V} {r : ℕ}

private def quadraticPart (D : Coordinates B r) (x : V) : F :=
  ∑ i : Fin r, D.left i x * D.right i x

private theorem crossTerm : ∀ a b c d : F,
    (a+c)*(b+d)+a*b+c*d = a*d+b*c := by
  decide +kernel

private theorem quadratic_polar (D : Coordinates B r) (x y : V) :
    quadraticPart D (x+y) + quadraticPart D x + quadraticPart D y = B x y := by
  rw [D.product]
  simp only [quadraticPart, ← Finset.sum_add_distrib, map_add]
  exact Finset.sum_congr rfl (fun i _ => crossTerm _ _ _ _)

private theorem scalarBalance : ∀ a b c z p q w d : F,
    c+a+b+z=d → w+p+q=d → c+z+w=(a+z+p)+(b+z+q) := by
  decide +kernel

private theorem cancelConstant : ∀ a b c : F, a=b+(a+b+c)+c := by
  decide +kernel

private theorem self_cancel : ∀ a : F, a+a=0 := by decide +kernel

private def affineLinear (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) : V →ₗ[F] F where
  toFun x := q x+q 0+quadraticPart D x
  map_add' x y := scalarBalance _ _ _ _ _ _ _ _ (polar x y) (quadratic_polar D x y)
  map_smul' c x := by
    have bits : ∀ c : F, c = 0 ∨ c = 1 := by decide +kernel
    rcases bits c with rfl | rfl
    · change q ((0 : F) • x) + q 0 + quadraticPart D ((0 : F) • x) =
        (0 : F) * (q x + q 0 + quadraticPart D x)
      simp [zero_smul, quadraticPart, self_cancel]
    · change q ((1 : F) • x) + q 0 + quadraticPart D ((1 : F) • x) =
        (1 : F) * (q x + q 0 + quadraticPart D x)
      rw [one_smul, one_mul]

private theorem exact_decomposition (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) (x : V) :
    q x = q 0 + affineLinear D q polar x + quadraticPart D x := by
  exact cancelConstant _ _ _

end Phase441QuadraticCoordinates

namespace Phase441

private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]

private abbrev IsPhase (q : V → F) (B : LinearMap.BilinForm F V) : Prop :=
  ∀ p u v, q (p+u+v)+q (p+u)+q (p+v)+q p = B u v

private theorem bit : ∀ a : F, a = 0 ∨ a = 1 := by decide
private theorem twice : ∀ a : F, a+a = 0 := by decide
private theorem scalarAdd : ∀ a b c d e f g : F, e+f+b+a = g →
    e+f+c+d = (b+a+c+d)+g := by decide

private def polarMap (q : V → F)
    (h : ∀ p u v, q (p+u+v)+q (p+u)+q (p+v)+q p = q (u+v)+q u+q v+q 0) :
    LinearMap.BilinForm F V := by
  let b (u v : V) := q (u+v)+q u+q v+q 0
  have bs : ∀ u v, b u v = b v u := by
    intro u v
    dsimp [b]
    rw [add_comm u v]
    abel
  have b0 (u : V) : b 0 u = 0 := by
    simp only [b, zero_add]
    rw [show q u + q 0 + q u + q 0 = (q u + q u) + (q 0 + q 0) by abel, twice, twice, zero_add]
  have ba (u w v : V) : b (u+w) v = b u v + b w v :=
    scalarAdd (q u) (q (u+v)) (q v) (q 0) (q (u+w+v)) (q (u+w)) (b w v) (h u w v)
  have bm (c : F) (u v : V) : b (c • u) v = c * b u v := by
    rcases bit c with rfl | rfl <;> simp [b0]
  exact {
    toFun := fun u => {
      toFun := b u
      map_add' := fun v w => by rw [bs u (v+w), ba, bs v u, bs w u]
      map_smul' := fun c v => by rw [bs u (c • v), bm, bs v u]; rfl }
    map_add' := fun u w => LinearMap.ext fun v => ba u w v
    map_smul' := fun c u => LinearMap.ext fun v => bm c u v }

private theorem phase_alt {q : V → F} {B : LinearMap.BilinForm F V} (h : IsPhase q B) :
    ∀ u, B u u = 0 := by
  intro u
  have huu : u + u = 0 := by
    calc
      u + u = (1 + 1 : F) • u := by rw [add_smul, one_smul]
      _ = 0 := by rw [twice, zero_smul]
  have hh := h 0 u u
  simp only [zero_add, huu] at hh
  rw [← hh, show q 0 + q u + q u + q 0 = (q 0 + q 0) + (q u + q u) by abel, twice, twice, zero_add]

private theorem phase_symm {q : V → F} {B : LinearMap.BilinForm F V} (h : IsPhase q B) :
    ∀ u v, B u v = B v u := by
  intro u v
  rw [← h 0 u v, ← h 0 v u]
  simp only [zero_add]
  rw [add_comm u v]
  abel

private theorem rank_even :
    ∀ (j : ℕ) {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W]
      (B : LinearMap.BilinForm F W), (∀ x, B x x = 0) → (∀ x y, B x y = B y x) →
      Module.finrank F (LinearMap.range B) = j → ∃ m, j = 2*m := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro W _ _ _ B alt sym hj
    by_cases hB : B = 0
    · subst B
      have hh : LinearMap.range (0 : LinearMap.BilinForm F W) = ⊥ :=
        LinearMap.range_eq_bot.mpr rfl
      have hzero : j = 0 := by rw [hh, finrank_bot] at hj; exact hj.symm
      exact ⟨0, by simp [hzero]⟩
    · obtain ⟨e,f,hf⟩ : ∃ e f, B e f = 1 := by
        by_contra! hfalse
        apply hB
        ext x y
        exact (bit (B x y)).resolve_right (hfalse x y)
      let U := Phase441SymplecticStep.perpendicular B e f
      let C := restr461 B U
      have hs : j = 2 + Module.finrank F (LinearMap.range C) :=
        hj.symm.trans (Phase441SymplecticStep.rank_step B e f alt sym hf)
      obtain ⟨m, hm⟩ := ih _ (by omega) C (fun x => alt x.val) (fun x y => sym x.val y.val) rfl
      exact ⟨m+1, by omega⟩

end Phase441

open scoped BigOperators
open LinearMap Module

namespace BatchUpper

private abbrev F := ZMod 2

variable {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
variable [AddCommGroup W] [Module F W]

private def sign (z : F) : ℤ := if z = 0 then 1 else -1

private theorem sign_add (x y : F) : sign (x + y) = sign x * sign y := by
  exact (by decide : ∀ x y : F, sign (x+y) = sign x * sign y) x y

private theorem sum_translate {A : Type*} [AddCommGroup A] [Fintype A]
    (g : A → ℤ) (r : A) : (∑ x, g (x+r)) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight r) _ _ fun _ => rfl

private theorem zero_or_one (x : F) : x = 0 ∨ x = 1 :=
  (by decide : ∀ y : F, y = 0 ∨ y = 1) x

private theorem char_sum {A : Type*} [AddCommGroup A] [Fintype A]
    (l : A →+ F) : (∑ x, sign (l x)) = if l = 0 then (Fintype.card A : ℤ) else 0 := by
  classical
  by_cases hz : l = 0
  · simp [hz, sign]
  · obtain ⟨r, hr⟩ : ∃ r, l r ≠ 0 := by
      by_contra! h
      exact hz (AddMonoidHom.ext h)
    have h := sum_translate (fun x => sign (l x)) r
    simp only [l.map_add, sign_add, (zero_or_one (l r)).resolve_left hr,
      show sign 1 = -1 by decide, ← Finset.sum_mul] at h
    rw [ite_eq_right hz]
    linarith

private theorem rearrange (a b c d z : F) (h : a+b+c+d=z) : a+b = c+d+z := by
  exact (by decide : ∀ a b c d z : F, a+b+c+d=z → a+b=c+d+z) a b c d z h

private theorem eq_iff_add_zero (a b : F) : a = b ↔ a+b = 0 :=
  (by decide : ∀ a b : F, a=b ↔ a+b=0) a b

open Classical in
private theorem square {A H : Type*} [AddCommGroup A] [Fintype A] [Zero H]
    (q : A → F) (p : A → H) (b : H → A →+ F) (hb : ∀ h, b h = 0 ↔ h = 0)
    (hq : ∀ x r, q (x+r)+q x+q r+q 0 = b (p r) x) :
    (∑ x, sign (q x)) ^ 2 =
      (Fintype.card A : ℤ) * ∑ r, if p r = 0 then sign (q r+q 0) else 0 := by
  classical
  rw [pow_two]
  calc
    _ = ∑ x : A, ∑ y : A, sign (q x) * sign (q y) := by
      simp only [Finset.mul_sum, mul_comm]
    _ = ∑ x : A, ∑ r : A, sign (q x) * sign (q (r+x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_translate (fun y => sign (q x) * sign (q y)) x).symm
    _ = ∑ r : A, ∑ x : A, sign (q r+q 0)*sign (b (p r) x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      rw [← sign_add, ← sign_add, add_comm r x, add_comm (q x)]
      rw [rearrange _ _ _ _ _ (hq x r)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.mul_sum, char_sum]
      simp only [hb]
      split <;> ring

private theorem card_pow (A : Type*) [AddCommGroup A] [Module F A] [Fintype A] :
    Fintype.card A = 2 ^ Module.finrank F A := by
  rw [Module.card_eq_pow_finrank (K := F), ZMod.card]

omit [Fintype V] in
private theorem derivative (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (x r : V) :
    f (x+r)+f x = f r+f 0+B r x := by
  apply rearrange
  calc
    _ = f (0+r+x)+f (0+r)+f (0+x)+f 0 := by
      simp only [zero_add]
      ac_rfl
    _ = _ := hq 0 r x

omit [Fintype V] in
private theorem period_iff (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (r : V) :
    (∀ x, f (x+r) = f x) ↔ r ∈ B.ker ∧ f r = f 0 := by
  constructor
  · intro h
    have h0 : f r = f 0 := by simpa using h 0
    refine ⟨LinearMap.mem_ker.mpr (LinearMap.ext fun x => ?_), h0⟩
    have hx := derivative f B hq x r
    rw [(eq_iff_add_zero _ _).mp (h x), (eq_iff_add_zero _ _).mp h0, zero_add] at hx
    exact hx.symm
  · rintro ⟨hB, h0⟩ x
    apply (eq_iff_add_zero _ _).mpr
    rw [derivative f B hq, (eq_iff_add_zero _ _).mp h0, zero_add,
      LinearMap.mem_ker.mp hB]
    rfl

private theorem toAddMonoidHom_eq_zero {A : Type*} [AddCommGroup A] [Module F A]
    (l : A →ₗ[F] F) : l.toAddMonoidHom = 0 ↔ l = 0 :=
  ⟨fun h => LinearMap.ext fun t => DFunLike.congr_fun h t, fun h => by subst l; rfl⟩

end BatchUpper
namespace TwoStageSplit

private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]

private abbrev Rad (B : LinearMap.BilinForm F V) := LinearMap.ker B
private noncomputable abbrev polarRank (B : LinearMap.BilinForm F V) := Module.finrank F (LinearMap.range B)

private theorem rad_mem (B : LinearMap.BilinForm F V) (u : V) :
    u ∈ Rad B ↔ ∀ v, B u v = 0 := by
  rw [LinearMap.mem_ker]
  exact ⟨fun h v => congrArg (fun g : V →ₗ[F] F => g v) h,
    fun h => LinearMap.ext h⟩

private theorem zadd (x : F) : x + x = 0 := by
  rw [← two_mul, show (2 : F) = 0 by decide, zero_mul]

private theorem symm (B : LinearMap.BilinForm F V) (alt : ∀ u, B u u = 0)
    (u v : V) : B u v = B v u := by
  have h := alt (u + v)
  simp only [map_add, LinearMap.add_apply, alt, zero_add, add_zero] at h
  linear_combination h - zadd (B v u)
private theorem query_in_range [FiniteDimensional F V] (B : LinearMap.BilinForm F V)
    (alt : ∀ u, B u u = 0) (Q : V →ₗ[F] F) (h : ∀ u : Rad B, Q u = 0) :
    ∃ b, B b = Q := by
  have le : LinearMap.range B ≤ (Rad B).dualAnnihilator := by
    rintro _ ⟨v, rfl⟩
    apply (Submodule.mem_dualAnnihilator (B v)).mpr
    intro x hx
    exact (symm B alt v x).trans ((rad_mem B x).mp hx v)
  have h₁ := B.finrank_range_add_finrank_ker
  have h₂ := Subspace.finrank_add_finrank_dualAnnihilator_eq (Rad B)
  have hfin : Module.finrank F (LinearMap.range B) = Module.finrank F (Rad B).dualAnnihilator :=
    Nat.add_right_cancel (h₁.trans ((add_comm _ _).trans h₂).symm)
  have eq := Submodule.eq_of_le_of_finrank_le le hfin.ge
  apply LinearMap.mem_range.mp
  rw [eq, Submodule.mem_dualAnnihilator]
  exact fun x hx => h ⟨x, hx⟩
private noncomputable def maskOn (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (W : Submodule F V) (van : ∀ u v : W, B u v = 0) (p : V) : W →ₗ[F] F where
  toFun u := f (p + u) + f p
  map_add' u v := by
    change f (p + ((u : V) + v)) + f p = (f (p + u) + f p) + (f (p + v) + f p)
    have h := polar p u v
    rw [van u v, add_assoc p] at h
    linear_combination h - zadd (f (p + u)) - zadd (f (p + v)) - zadd (f p)
  map_smul' c u := by
    have cases : ∀ y : F, y = 0 ∨ y = 1 := by decide
    rcases cases c with rfl | rfl
    · change f (p + (0 : F) • (u : V)) + f p = (0 : F) • _
      simp [zadd]
    · change f (p + (1 : F) • (u : V)) + f p = (1 : F) • _
      simp

private noncomputable def mask (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) : Rad B →ₗ[F] F :=
  maskOn B f polar (Rad B) (fun u v => (rad_mem B u).mp u.property v) 0

private theorem mask_apply (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (u : Rad B) :
    mask B f polar u = f u + f 0 := by
  change f (0 + (u : V)) + f 0 = _
  rw [zero_add]

private theorem translatedDerivative (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (p u : V) :
    f (p+u) + f p = (f u + f 0) + B p u := by
  have h := polar 0 p u
  simp only [zero_add] at h
  linear_combination h - zadd (f u) - zadd (f 0)
end TwoStageSplit
namespace Upper441
open Phase441 TwoStageSplit
private abbrev F := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F V]

private theorem masked_iff (q : V → F) (B : LinearMap.BilinForm F V) (hq : IsPhase q B) :
    (∃ r : B.ker, q r.val ≠ q 0) ↔ mask B q hq ≠ 0 := by
  classical
  have bit : ∀ a b : F, a+b=0 ↔ a=b := by decide
  rw [ne_eq, ← not_iff_not]
  push_neg
  constructor
  · intro h
    ext x
    rw [mask_apply, LinearMap.zero_apply, bit]
    exact h x
  · intro h x
    apply (bit _ _).mp
    rw [← mask_apply B q hq, h, LinearMap.zero_apply]

private theorem rdim [Module.Finite F V] (B : LinearMap.BilinForm F V) :
    Module.finrank F V - Module.finrank F B.ker = polarRank B := by
  have h := B.finrank_range_add_finrank_ker
  change polarRank B + _ = _ at h
  omega

end Upper441

namespace Atlas461
open Phase441 Phase441SymplecticCoordinates Phase441QuadraticCoordinates
open BatchUpper TwoStageSplit Upper441
private abbrev K := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]

theorem signCount (f : V → K) :
    (∑ x, sign (f x)) = (Nat.card {x : V // f x = 0} : ℤ) - Nat.card {x : V // f x = 1} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  simp only [← Finset.sum_boole, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases zero_or_one (f x) with h | h <;> simp [sign,h]

open Classical in
theorem globalSquare (f : V → K) (B : LinearMap.BilinForm K V) (hq : IsPhase f B) :
    (∑ x, sign (f x))^2 = if mask B f hq = 0 then (Fintype.card V : ℤ)*Fintype.card B.ker else 0 := by
  classical
  have hs := square f B LinearMap.toAddMonoidHom toAddMonoidHom_eq_zero
    (fun x r => show f (x+r)+f x+f r+f 0=B r x by rw [phase_symm hq r x]; simpa using hq 0 x r)
  letI : DecidableEq (V →ₗ[K] K) := Classical.decEq _
  have hx : (∑ r : V, if B r = 0 then sign (f r+f 0) else 0) =
      ∑ r : B.ker, sign ((mask B f hq).toAddMonoidHom r) := by
    simp only [LinearMap.toAddMonoidHom_coe, mask_apply]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun r => by simp [LinearMap.mem_ker]) _
  calc
    _ = (Fintype.card V : ℤ) * ∑ r : B.ker, sign ((mask B f hq).toAddMonoidHom r) :=
      hs.trans (congrArg ((Fintype.card V : ℤ) * ·) hx)
    _ = _ := by
      rw [char_sum]
      by_cases h : mask B f hq = 0 <;> simp only [toAddMonoidHom_eq_zero, h, ite_true, ite_false, mul_zero]

theorem balanced_iff_mask (f : V → K) (B : LinearMap.BilinForm K V) (hq : IsPhase f B) :
    Nat.card {x : V // f x = 0} = Nat.card {x : V // f x = 1} ↔ mask B f hq ≠ 0 := by
  classical
  have hs := globalSquare f B hq
  rw [signCount] at hs
  by_cases hm : mask B f hq = 0
  · rw [if_pos hm] at hs
    simp only [hm, ne_self_iff_false, iff_false]
    intro h
    rw [h, sub_self, zero_pow (by decide), eq_comm] at hs
    have hp : (0 : ℤ) < Fintype.card V * (Fintype.card B.ker : ℤ) := by positivity
    omega
  · rw [if_neg hm, sq_eq_zero_iff, sub_eq_zero] at hs
    exact iff_of_true (by exact_mod_cast hs) hm

theorem clearShape (q : V → K) (B : LinearMap.BilinForm K V)
    (hq : IsPhase q B) (m : ℕ) (hr : polarRank B = 2*m) (hm : mask B q hq = 0) :
    ∃ (D : Coordinates B m) (v : V), ∀ x, q (x+v) = q v + quadraticPart D x := by
  classical
  have alt := phase_alt hq
  have sym := phase_symm hq
  obtain ⟨D⟩ := normalForm m B alt sym hr
  have pol (u v : V) : q (u+v)+q u+q v+q 0=B u v := by simpa using hq 0 u v
  let ell := affineLinear D q pol
  have hshape := exact_decomposition D q pol
  have van (r : B.ker) : ell r.val = 0 := by
    have hdiff : q r.val + q 0 = 0 := by rw [← mask_apply B q hq, hm, LinearMap.zero_apply]
    have hpair : quadraticPart D r.val = 0 := by
      have H := LinearMap.mem_ker.mp r.property
      apply Finset.sum_eq_zero
      intro i _
      have hL : D.left i r.val = 0 := by
        obtain ⟨x,hx⟩ := D.independent (0, Pi.single i 1)
        have hl : (fun j => D.left j x) = 0 := congrArg Prod.fst hx
        have hh : (fun j => D.right j x) = Pi.single i 1 := congrArg Prod.snd hx
        have hz : B r.val x = 0 := DFunLike.congr_fun H x
        rw [D.product] at hz
        change (∑ j, (D.left j r.val * (fun k => D.right k x) j +
          D.right j r.val * (fun k => D.left k x) j)) = 0 at hz
        rw [hh, hl] at hz
        simpa [Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using hz
      simp [hL]
    change q r.val + q 0 + quadraticPart D r.val = 0
    rw [hdiff, hpair, zero_add]
  obtain ⟨v, hv⟩ := TwoStageSplit.query_in_range B alt ell van
  let q' (x : V) := q (x+v)
  have hq' (x : V) : q' x = q v + (∑ i : Fin 0, (0 : V →ₗ[K] K) x) + quadraticPart D x := by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have hB : B x v = ell x := (sym x v).trans (DFunLike.congr_fun hv x)
    have h := pol x v
    rw [hB, hshape x] at h
    change q (x+v) = _
    exact (by decide : ∀ a b c d e : K, a+(b+c+d)+e+b=c → a=e+d) _ _ _ _ _ h
  exact ⟨D, v, by simpa [q'] using hq'⟩

theorem rankShape (n : ℕ) (f : (Fin n → K) → K)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = f (u+v)+f u+f v+f 0) :
    let X := Fin n → K
    let g := Nat.card {u : X // ∀ v : X, f (u+v)+f u+f v+f 0=0}
    let m := (n-g.log2)/2
    let n0 := Nat.card {x : X // f x=0}
    let n1 := Nat.card {x : X // f x=1}
    (n0 = n1 → ∃ r : X, ∀ x, f (x+r) = f x + 1) ∧
      (n0 ≠ n1 → |(n0 : ℤ) - n1| = 2^(n-m) ∧
        ∃ (t : X) (A C : Fin m → X →ₗ[K] K),
          Function.Surjective (fun x : X => (fun i => A i x, fun i => C i x)) ∧
          ∀ x, f (x+t) = f t + ∑ i, A i x * C i x) := by
  classical
  intro X g m n0 n1
  let B := polarMap f h
  have hq : IsPhase f B := h
  have hg : g = Nat.card B.ker := by
    change Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card B.ker
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (TwoStageSplit.rad_mem B u).symm)
  have hdim : Module.finrank K X = n := by simp [X]
  have hglog : g.log2 = Module.finrank K B.ker := by
    rw [hg, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ZMod.card, Nat.log2_two_pow]
  have hden := B.finrank_range_add_finrank_ker
  have hdiff : Module.finrank K X - Module.finrank K B.ker = polarRank B := by
    change polarRank B + Module.finrank K B.ker = Module.finrank K X at hden
    omega
  have hm : m = polarRank B/2 := by
    calc
      m = (n - g.log2)/2 := rfl
      _ = (Module.finrank K X - g.log2)/2 := congrArg (fun v => (v-g.log2)/2) hdim.symm
      _ = (Module.finrank K X - Module.finrank K B.ker)/2 :=
        congrArg (fun v => (Module.finrank K X-v)/2) hglog
      _ = polarRank B/2 := congrArg (· / 2) hdiff
  have hr : polarRank B = 2*m := by
    obtain ⟨j,hj⟩ := rank_even (polarRank B) B (phase_alt hq) (phase_symm hq) rfl
    omega
  constructor
  · intro hb
    obtain ⟨r, hr⟩ := (masked_iff f B hq).mpr ((balanced_iff_mask f B hq).mp hb)
    refine ⟨r.val, fun x => ?_⟩
    have hz := derivative f B hq x r.val
    have hbr := (rad_mem B r.val).mp r.property x
    rw [hbr, add_zero] at hz
    exact (by decide : ∀ a b c d : K, a+b=c+d → c≠d → a=b+1) _ _ _ _ hz hr
  · intro hb
    have hmask : mask B f hq = 0 := not_ne_iff.mp (fun h' => hb ((balanced_iff_mask f B hq).mpr h'))
    constructor
    · have hsq := globalSquare f B hq
      rw [if_pos hmask, signCount] at hsq
      change ((n0 : ℤ) - n1)^2 = (Fintype.card X : ℤ) * Fintype.card B.ker at hsq
      rw [card_pow X, card_pow B.ker, Nat.cast_pow, Nat.cast_pow, hdim] at hsq
      norm_num only [Nat.cast_ofNat] at hsq
      rw [← pow_add] at hsq
      change polarRank B + Module.finrank K B.ker = Module.finrank K X at hden
      rw [hr, hdim] at hden
      have he : n + Module.finrank K B.ker = (n-m)*2 := by omega
      rw [he, pow_mul] at hsq
      exact (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp ((sq_abs _).trans hsq)
    · obtain ⟨D,t,hD⟩ := clearShape f B hq m hr hmask
      exact ⟨t,D.left,D.right,D.independent,hD⟩
end Atlas461
namespace Query441

private abbrev K := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module K V]

private noncomputable def score [Fintype V] (q s : V → K) : ℚ :=
  (∑ x : V, if s x = q x then (1 : ℚ) else -1) / Fintype.card V

end Query441
namespace BatchUpper
variable {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
variable [AddCommGroup W] [Module F W]

private theorem dim_ker_inter (B : V →ₗ[F] W) {e : ℕ} (L : V →ₗ[F] (Fin e → F)) :
    finrank F V - finrank F B.ker ≤
      finrank F L.ker - finrank F (B.domRestrict L.ker).ker +
        (e - finrank F (L.domRestrict B.ker).range) := by
  let I := (B.domRestrict L.ker).ker
  let J := (L.domRestrict B.ker).ker
  let E : I ≃ₗ[F] J :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hIJ := E.finrank_eq
  have hK := L.finrank_range_add_finrank_ker
  have hJ := (L.domRestrict B.ker).finrank_range_add_finrank_ker
  have hI := (B.domRestrict L.ker).finrank_range_add_finrank_ker
  have he := Submodule.finrank_le L.range
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  dsimp [I, J] at hIJ
  omega

private theorem square_pow_lower {a : ℤ} {j d : ℕ} (h : a^2 = 2^j) (hd : 2*d ≤ j+1) :
    (2 : ℤ)^d ≤ |a| := by
  have hn : a.natAbs ^ 2 = 2^j := by
    simpa only [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 by decide] using congrArg Int.natAbs h
  have hj : 2 * (a.natAbs.factorization 2) = j := by
    have he := congrArg (fun n : ℕ => n.factorization 2) hn
    rw [Nat.factorization_pow_self Nat.prime_two, Nat.factorization_pow, Finsupp.smul_apply,
      smul_eq_mul] at he
    exact he
  have hpow : (2 : ℤ)^(2*d) ≤ 2^j := pow_le_pow_right₀ (by decide) (by omega)
  apply le_of_sq_le_sq _ (abs_nonneg a)
  rwa [← pow_mul, Nat.mul_comm, sq_abs, h]

private theorem shift_cancel (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {e : ℕ} (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F)
    (r : B.ker) (hr : f r ≠ f 0) (hl : L r = 0) :
    (∑ x, sign (out (L x)+f x)) = 0 := by
  have hs := sum_translate (fun x => sign (out (L x)+f x)) (r : V)
  have hδ (x : V) : f (x+r) = f x+1 := by
    have hz := derivative f B hq x r
    have hbr : B r x = 0 := by
      rw [show B r = 0 from r.property]
      rfl
    rw [hbr, add_zero, (zero_or_one (f r+f 0)).resolve_left
      (fun h => hr ((eq_iff_add_zero _ _).mpr h))] at hz
    exact (by decide : ∀ a b : F, a+b=1 → a=b+1) _ _ hz
  simp only [L.map_add, hl, add_zero, hδ, ← add_assoc, sign_add, ← Finset.sum_mul,
    show sign 1 = -1 by decide] at hs
  simp only [sign_add]
  linarith

private theorem oneBatchInt (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {m w e : ℕ} (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F)
    (hr : 2*m ≤ finrank F L.ker - finrank F (B.domRestrict L.ker).ker + w) :
    (2 : ℤ)^(m-w/2) * (∑ x, sign (out (L x)+f x)) ≤ Fintype.card V := by
  classical
  let K := L.ker
  let I := (B.domRestrict K).ker
  let P : K →ₗ[F] K →ₗ[F] F :=
    { toFun := fun r => (B r).domRestrict K
      map_add' := fun r s => by ext t; simp
      map_smul' := fun c r => by ext t; simp }
  let J := P.ker
  let A (x : V) := ∑ k : K, sign (f (x+k))
  let H (x : V) := sign (out (L x)+f x)
  let C (x : V) := sign (out (L x))
  let D : ℤ := 2^(finrank F I + (m-w/2))
  have hIJ : finrank F I ≤ finrank F J := by
    apply Submodule.finrank_mono
    intro r hr
    change P r = 0
    have h : B r = 0 := hr
    ext t
    change B r t = 0
    simp [h]
  have hIK : finrank F I ≤ finrank F K := Submodule.finrank_le I
  have hsquare (x : V) : A x ^ 2 = (Fintype.card K : ℤ) *
      ∑ r : K, if P r = 0 then sign (f (x+r)+f x) else 0 := by
    change (∑ k : K, sign (f (x+k))) ^ 2 = _
    simpa only [Submodule.coe_add, Submodule.coe_zero, add_zero, ← add_assoc] using
      (square (fun k : K => f (x+k)) P LinearMap.toAddMonoidHom
        toAddMonoidHom_eq_zero
        (fun k r => by
          change f (x+(↑(k+r) : V))+f (x+k)+f (x+r)+f (x+(↑(0 : K) : V)) =
            B r k
          calc
            _ = f (x+r+k)+f (x+r)+f (x+k)+f x := by
              simp only [Submodule.coe_add, Submodule.coe_zero, add_zero]
              ac_rfl
            _ = _ := hq x r k))
  have hlocal (x : V) : A x = 0 ∨ A x ^ 2 = (2 : ℤ)^(finrank F K+finrank F J) := by
    let l : J →+ F :=
      { toFun := fun r => f (x+(r.val : V))+f x
        map_zero' := by
          change f (x+0)+f x = 0
          rw [add_zero, ← eq_iff_add_zero]
        map_add' := fun r s => by
          have hz : B (r.val : V) (s.val : V) = 0 := by
            have hh : P r.val = 0 := r.property
            exact DFunLike.congr_fun hh s.val
          have hh := hq x (r.val : V) (s.val : V)
          rw [hz] at hh
          change f (x+((r.val : V)+(s.val : V)))+f x =
            (f (x+(r.val : V))+f x)+(f (x+(s.val : V))+f x)
          rw [← add_assoc]
          exact (by decide : ∀ a b c d : F, a+b+c+d=0 → a+d=(b+d)+(c+d)) _ _ _ _ hh }
    have hx : (∑ r : K, if P r = 0 then sign (f (x+r)+f x) else 0) =
        ∑ r : J, sign (l r) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun r => by simp [J, LinearMap.mem_ker]) _
    have hy := hsquare x
    rw [hx, char_sum] at hy
    split at hy
    · right
      rw [card_pow K, card_pow J] at hy
      simpa [pow_add] using hy
    · left
      rw [mul_zero, pow_two, mul_eq_zero] at hy
      exact hy.elim id id
  have hpoint (x : V) : D * (C x * A x) ≤ A x ^ 2 := by
    rcases hlocal x with hz | hz
    · simp [hz]
    have hd : D ≤ |A x| := by
      apply square_pow_lower hz
      dsimp [I, K, J] at *
      omega
    have hC : C x * A x ≤ |A x| := by
      unfold C sign
      split
      · simpa using le_abs_self (A x)
      · simpa using neg_le_abs (A x)
    calc
      _ ≤ D * |A x| := mul_le_mul_of_nonneg_left hC (by dsimp [D]; positivity)
      _ ≤ |A x| * |A x| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = A x ^ 2 := by rw [← pow_two, sq_abs]
  have hglob (r : K) : (∑ x : V, sign (f (x+r)+f x)) =
      if B r = 0 then (Fintype.card V : ℤ)*sign (f r+f 0) else 0 := by
    simp only [derivative f B hq, sign_add, ← Finset.mul_sum]
    change sign (f r) * sign (f 0) * (∑ x : V, sign ((B r).toAddMonoidHom x)) = _
    rw [char_sum]
    simp only [toAddMonoidHom_eq_zero]
    split <;> ring

  have hsumsquare : (∑ x, A x ^ 2) ≤ (Fintype.card K : ℤ) *
      ((Fintype.card V : ℤ) * Fintype.card I) := by
    simp only [hsquare, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r : K, if B r = 0 then (Fintype.card V : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases h : P r = 0
        · simp only [h, ite_true, hglob]
          split
          · unfold sign
            split <;> simp
          · rfl
        · simp only [ite_eq_right h, Finset.sum_const_zero]
          split <;> positivity
      _ = _ := by
        rw [← Finset.sum_filter]
        rw [Finset.sum_subtype (p := fun r : K => r ∈ I) (F := (inferInstance : Fintype I)) _
          (fun r : K => by change _ ↔ B r = 0; simp) _]
        simp [mul_comm]
  have hAvg : (∑ x, C x * A x) = (Fintype.card K : ℤ) * ∑ x, H x := by
    have hshift (r : K) (x : V) : sign (out (L x)) * sign (f (x+r)) = H (x+r) := by
      have hh : L (r : V) = 0 := r.property
      simp [H, sign_add, hh]
    calc
      _ = ∑ x : V, ∑ r : K, sign (out (L x)) * sign (f (x+r)) := by
        simp only [C, A, Finset.mul_sum]
      _ = ∑ r : K, ∑ x : V, H (x+r) := by rw [Finset.sum_comm]; simp only [hshift]
      _ = _ := by simp only [sum_translate H, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hmain := (Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)).trans hsumsquare
  rw [← Finset.mul_sum, hAvg, mul_left_comm D] at hmain
  have hcardK : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hmain' := le_of_mul_le_mul_left hmain hcardK
  have hcardI : (0 : ℤ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hD : D = (Fintype.card I : ℤ) * (2 : ℤ)^(m-w/2) := by
    rw [card_pow I]
    simp [D, pow_add]
  rw [hD, mul_assoc, mul_comm (Fintype.card V : ℤ)] at hmain'
  exact le_of_mul_le_mul_left hmain' hcardI

open Classical in
private theorem oneBatch (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {m e : ℕ} (hr : finrank F V - finrank F B.ker = 2*m)
    (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F) :
    (∑ x : V, if out (L x) = f x then (1 : ℚ) else -1) / Fintype.card V ≤
      if ∃ r : B.ker, f r ≠ f 0 then
        if e = 0 then (0 : ℚ) else 1/2^(m-(e-1)/2)
      else 1/2^(m-e/2) := by
  classical
  have hscore : (∑ x : V, if out (L x) = f x then (1 : ℚ) else -1) =
      ((∑ x : V, sign (out (L x)+f x) : ℤ) : ℚ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    simp [eq_iff_add_zero (out (L x)) (f x), sign]
  rw [hscore]
  have hcard : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdim := dim_ker_inter B L
  rw [hr] at hdim
  have upper (w : ℕ)
      (hw : 2*m ≤ finrank F L.ker - finrank F (B.domRestrict L.ker).ker+w) :
      ((∑ x : V, sign (out (L x)+f x) : ℤ) : ℚ) / Fintype.card V ≤ 1/2^(m-w/2) := by
    apply (div_le_div_iff₀ hcard (by positivity)).2
    rw [one_mul, mul_comm]
    exact_mod_cast oneBatchInt f B hq L out hw
  split
  · rename_i hmask
    obtain ⟨r, hr⟩ := hmask
    by_cases hz : L r = 0
    · rw [shift_cancel f B hq L out r hr hz]
      push_cast
      split <;> simp
    · have hpos : 0 < finrank F (L.domRestrict B.ker).range := by
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        exact ⟨⟨L r, ⟨r, rfl⟩⟩, fun hh => hz (congrArg Subtype.val hh)⟩
      have hle := Submodule.finrank_le (L.domRestrict B.ker).range
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
      rw [ite_eq_right (by omega : e ≠ 0)]
      exact upper (e-1) (by omega)
  · exact upper e (by omega)

end BatchUpper
namespace Lower441
open Phase441 Phase441SymplecticCoordinates Phase441QuadraticCoordinates Query441 TwoStageSplit
private abbrev F := ZMod 2

private def character (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

private theorem character_add (x y : ZMod 2) :
    character (x + y) = character x * character y := by
  have all : ∀ a b : ZMod 2, character (a + b) = character a * character b := by decide
  exact all x y

private theorem character_sum {I : Type*} (s : Finset I) (f : I → F) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert a rest fresh ih =>
    rw [Finset.sum_insert fresh,Finset.prod_insert fresh,character_add,ih]

private theorem one_pair : (∑ q : F × F, character (q.1 * q.2)) = 2 := by decide

private theorem subset_bias {A : Type*} [Fintype A] (r k : ℕ) (S : Finset (Fin r)) (q : A → F)
    (coords : A ≃ (Fin r → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i ∈ S, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^S.card * (∑ x, character (q x)) = 2 ^ (2*r + k) := by
  classical
  let w (i : Fin r) (z : F × F) : ℤ := if i ∈ S then character (z.1 * z.2) else 1
  let a (i : Fin r) : ℤ := if i ∈ S then 2 else 1
  have count : (∏ i, a i) = (2 : ℤ)^S.card := by
    unfold a
    rw [Finset.prod_ite_mem_eq,Finset.prod_const]
  have term (z : Fin r → F × F) : character (∑ i ∈ S, (z i).1 * (z i).2) = ∏ i, w i (z i) := by
    rw [character_sum]
    unfold w
    rw [Finset.prod_ite_mem_eq]
  have product : (∏ i, a i * ∑ z, w i z) = (4 : ℤ)^r := by
    have pointwise (i : Fin r) : a i * (∑ z, w i z) = 4 := by
      by_cases h : i ∈ S
      · simp [a,w,h,one_pair]
      · simp [a,w,h,Fintype.card_prod,ZMod.card]
    simp only [pointwise,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have selected : (2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i)) = 4^r := by
    rw [← count, ← Fintype.prod_sum w, ← Finset.prod_mul_distrib]
    exact product
  have all : (∑ x, character (q x)) =
      ∑ p : (Fin r → F × F) × (Fin k → F), ∏ i, w i (p.1 i) := by
    apply Fintype.sum_equiv coords
    intro x
    rw [form,term]
  rw [all,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have free : (Fintype.card (Fin k → F) : ℤ) = 2^k := by
    simp [Fintype.card_fun,ZMod.card]
  rw [free]
  calc
    _ = (2 : ℤ)^k * ((2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i))) := by ring
    _ = (2 : ℤ)^(2*r+k) := by rw [selected,pow_add,pow_mul]; norm_num [mul_comm]

private noncomputable def split_fibers {A T : Type*} [AddCommGroup A] [Module F A] [AddCommGroup T] [Module F T] (G : A →ₗ[F] T)
    (surj : Function.Surjective G) : A ≃ T × LinearMap.ker G where
  toFun x := (G x,⟨x - (surj (G x)).choose, by
    rw [LinearMap.mem_ker,map_sub,(surj (G x)).choose_spec,sub_self]⟩)
  invFun y := y.2.val + (surj y.1).choose
  left_inv x := sub_add_cancel _ _
  right_inv := by
    rintro ⟨y,z⟩
    have h : G (z.val + (surj y).choose) = y := by
      rw [map_add,(surj y).choose_spec,LinearMap.mem_ker.mp z.property,zero_add]
    apply Prod.ext h
    apply Subtype.ext
    change z.val + (surj y).choose -
      (surj (G (z.val + (surj y).choose))).choose = z.val
    rw [h,add_sub_cancel_right]

variable {V : Type*} [AddCommGroup V] [Module F V]

private theorem bitEq (a b : F) : a = b ↔ a+b=0 :=
  (by decide : ∀ a b : F, a=b ↔ a+b=0) a b

private theorem repack {I : Type*} [Fintype I] {e : ℕ}
    (h : Fintype.card I ≤ e) (A : I → V →ₗ[F] F) :
    ∃ (L : V →ₗ[F] (Fin e → F)) (decode : (Fin e → F) → (I → F)),
      ∀ x i, decode (L x) i = A i x := by
  classical
  obtain ⟨E⟩ : Nonempty (I ↪ Fin e) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  let R (i : Fin e) : V →ₗ[F] F := if h : ∃ j, E j = i then A h.choose else 0
  refine ⟨LinearMap.pi R, fun v i => v (E i), ?_⟩
  intro x i
  have hi : ∃ j, E j = E i := ⟨i,rfl⟩
  have hh : hi.choose = i := E.injective hi.choose_spec
  change R (E i) x = _
  simp [R, hi, hh]

private def pairMap {B : LinearMap.BilinForm F V} {m : ℕ} (D : Coordinates B m) :
    V →ₗ[F] (Fin m → F × F) where
  toFun x i := (D.left i x, D.right i x)
  map_add' x y := by ext i <;> simp
  map_smul' c x := by ext i <;> simp

private theorem pairMap_surj {B : LinearMap.BilinForm F V} {m : ℕ} (D : Coordinates B m) :
    Function.Surjective (pairMap D) := by
  intro xs
  obtain ⟨x,h⟩ := D.independent (fun i => (xs i).1, fun i => (xs i).2)
  refine ⟨x,?_⟩
  funext i
  exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

private theorem remainder_score [Fintype V] {B : LinearMap.BilinForm F V} {m : ℕ}
    (D : Coordinates B m) (S : Finset (Fin m)) (q s : V → F)
    (h : ∀ x, s x + q x = ∑ i ∈ S, D.left i x * D.right i x) :
    score q s = 1/(2 : ℚ)^S.card := by
  classical
  let G := pairMap D
  let R := G.ker
  let k := Module.finrank F R
  let E := (split_fibers G (pairMap_surj D)).trans
    ((Equiv.refl _).prodCongr (Module.finBasis F R).equivFun.toEquiv)
  have hform (x : V) : s x + q x = ∑ i ∈ S, ((E x).1 i).1 * ((E x).1 i).2 := h x
  have hs := subset_bias m k S (fun x => s x+q x) E hform
  have hCard : Fintype.card V = 2^(2*m+k) := by
    have hg := Fintype.card_congr E
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hg
    rw [hg, pow_add, pow_mul]
    norm_num
    rfl
  have hs' : (2 : ℚ)^S.card * (∑ x : V, if s x = q x then (1 : ℚ) else -1) = Fintype.card V := by
    rw [hCard]
    have hg := congrArg (Int.cast : ℤ → ℚ) hs
    push_cast at hg ⊢
    simpa [character, ← bitEq] using hg
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold score
  apply (div_eq_div_iff (ne_of_gt hpos) (by positivity)).2
  linarith

private theorem select_pairs [Fintype V] {B : LinearMap.BilinForm F V} {m : ℕ}
    (D : Coordinates B m) (q : V → F) (c : F) {j b e : ℕ} (hj : j ≤ m) (he : 2*j+b ≤ e)
    (A : Fin b → V →ₗ[F] F)
    (h : ∀ x, q x = c + (∑ i, A i x) + quadraticPart D x) :
    ∃ (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F),
      score q (fun x => out (L x)) = 1/(2 : ℚ)^(m-j) := by
  classical
  let incl : Fin j ↪ Fin m := Fin.castLEEmb hj
  let I := (Fin j × Bool) ⊕ Fin b
  let ask : I → V →ₗ[F] F := Sum.elim
    (fun i => if i.2 then D.left (incl i.1) else D.right (incl i.1)) A
  have hcard : Fintype.card I ≤ e := by
    simpa only [I, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.mul_comm j 2] using he
  obtain ⟨L, dec, hdec⟩ := repack hcard ask
  let S : Finset (Fin m) := Finset.univ.map incl
  let out (v : Fin e → F) : F := c + (∑ i : Fin b, dec v (Sum.inr i)) +
    ∑ i : Fin j, dec v (Sum.inl (i,true)) * dec v (Sum.inl (i,false))
  have hC : Sᶜ.card = m-j := by simp [S, Finset.card_compl]
  refine ⟨L,out, (remainder_score D Sᶜ q (fun x => out (L x)) ?_).trans ?_⟩
  · intro x
    have hx : out (L x) = c + (∑ i, A i x) + ∑ i ∈ S, D.left i x * D.right i x := by
      simp [out, hdec, ask, S]
    have hsplit : quadraticPart D x =
        (∑ i ∈ S, D.left i x * D.right i x) + ∑ i ∈ Sᶜ, D.left i x * D.right i x := by
      have hd : Disjoint S Sᶜ := Finset.disjoint_left.mpr (by simp)
      rw [quadraticPart, ← Finset.sum_union hd, Finset.union_compl]
    rw [hx, h, hsplit]
    exact (by decide : ∀ a b c : F, (a+b)+(a+(b+c))=c) _ _ _
  · rw [hC]

private theorem score_translate [Fintype V] (q s : V → F) (v : V) :
    score q s = score (fun x => q (x+v)) (fun x => s (x+v)) := by
  unfold score
  congr 1
  exact (Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)).symm

open Classical in
private theorem batchAttain [Fintype V] (q : V → F) (B : LinearMap.BilinForm F V)
    (hq : IsPhase q B) (m e : ℕ) (hr : polarRank B = 2*m) :
    ∃ (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F),
      score q (fun x => out (L x)) = if mask B q hq = 0 then 1/(2 : ℚ)^(m-e/2)
        else if e = 0 then 0 else 1/(2 : ℚ)^(m-(e-1)/2) := by
  classical
  have alt := phase_alt hq
  have sym := phase_symm hq
  obtain ⟨D⟩ := normalForm m B alt sym hr
  have pol (u v : V) : q (u+v)+q u+q v+q 0=B u v := by simpa using hq 0 u v
  let ell := affineLinear D q pol
  have hshape := exact_decomposition D q pol
  by_cases hm : mask B q hq = 0
  · rw [if_pos hm]
    have van (r : B.ker) : ell r.val = 0 := by
      have hdiff : q r.val + q 0 = 0 := by rw [← mask_apply B q hq, hm, LinearMap.zero_apply]
      have hpair : quadraticPart D r.val = 0 := by
        have H := LinearMap.mem_ker.mp r.property
        apply Finset.sum_eq_zero
        intro i _
        have hL : D.left i r.val = 0 := by
          obtain ⟨x,hx⟩ := D.independent (0, Pi.single i 1)
          have hl : (fun j => D.left j x) = 0 := congrArg Prod.fst hx
          have hh : (fun j => D.right j x) = Pi.single i 1 := congrArg Prod.snd hx
          have hz : B r.val x = 0 := DFunLike.congr_fun H x
          rw [D.product] at hz
          change (∑ j, (D.left j r.val * (fun k => D.right k x) j +
            D.right j r.val * (fun k => D.left k x) j)) = 0 at hz
          rw [hh, hl] at hz
          simpa [Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using hz
        simp [hL]
      change q r.val + q 0 + quadraticPart D r.val = 0
      rw [hdiff, hpair, zero_add]
    obtain ⟨v, hv⟩ := TwoStageSplit.query_in_range B alt ell van
    let q' (x : V) := q (x+v)
    have hq' (x : V) : q' x = q v + (∑ i : Fin 0, (0 : V →ₗ[F] F) x) + quadraticPart D x := by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have hB : B x v = ell x := (sym x v).trans (DFunLike.congr_fun hv x)
      have h := pol x v
      rw [hB, hshape x] at h
      change q (x+v) = _
      exact (by decide : ∀ a b c d e : F, a+(b+c+d)+e+b=c → a=e+d) _ _ _ _ _ h
    let j := min m (e/2)
    obtain ⟨L,out,hout⟩ := select_pairs D q' (q v) (j := j) (b := 0) (e := e)
      (min_le_left _ _) (by dsimp [j]; omega) (fun _ => 0) hq'
    refine ⟨L, fun y => out (y - L v), ?_⟩
    rw [score_translate q _ v]
    simp only [L.map_add, add_sub_cancel_right]
    have hj : m-j = m-(e/2) := by dsimp [j]; omega
    simpa only [hj] using hout
  · rw [if_neg hm]
    by_cases he : e = 0
    · subst e
      simp only [ite_true]
      obtain ⟨r, hr⟩ := (Upper441.masked_iff q B hq).mpr hm
      refine ⟨0, fun _ => 0, ?_⟩
      have hz := BatchUpper.shift_cancel q B hq (0 : V →ₗ[F] (Fin 0 → F)) (fun _ => 0) r hr rfl
      have hz' := congrArg (Int.cast : ℤ → ℚ) hz
      push_cast at hz'
      unfold score
      rw [show (∑ x : V, if (0 : F) = q x then (1 : ℚ) else -1) = 0 by
        simpa [BatchUpper.sign, eq_comm] using hz', zero_div]
    · rw [if_neg he]
      let j := min m ((e-1)/2)
      obtain ⟨L,out,hout⟩ := select_pairs D q (q 0) (j := j) (b := 1) (e := e)
        (min_le_left _ _) (by dsimp [j]; omega) (fun _ => ell)
        (fun x => by simpa using hshape x)
      refine ⟨L,out,?_⟩
      have hj : m-j = m-((e-1)/2) := by dsimp [j]; omega
      simpa only [hj] using hout

end Lower441

namespace Atlas461
open Phase441 Phase441SymplecticCoordinates BatchUpper TwoStageSplit Upper441 Query441
open Classical in
theorem uniformScore (n : ℕ) (f : (Fin n → K) → K)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = f (u+v)+f u+f v+f 0) (j : ℕ) :
    let X := Fin n → K
    let g := Nat.card {u : X // ∀ v : X, f (u+v)+f u+f v+f 0=0}
    let m := (n-g.log2)/2
    let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
    let bound : ℚ := if bal then (if j=0 then 0 else 1/2^(m-(j-1)/2)) else 1/2^(m-j/2)
    let corr := fun (q : X →ₗ[K] (Fin j → K)) (out : (Fin j → K) → K) =>
      (∑ x : X, if out (q x)=f x then (1:ℚ) else -1) / Fintype.card X
    (∀ q out, corr q out ≤ bound) ∧ ∃ q out, corr q out = bound := by
  classical
  intro X g m bal b corr
  let B := polarMap f h
  have hq : IsPhase f B := h
  have hg : g = Nat.card B.ker := by
    change Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card B.ker
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (TwoStageSplit.rad_mem B u).symm)
  have hdim : Module.finrank K X = n := by simp [X]
  have hglog : g.log2 = Module.finrank K B.ker := by
    rw [hg, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ZMod.card, Nat.log2_two_pow]
  have hden := B.finrank_range_add_finrank_ker
  have hdiff : Module.finrank K X - Module.finrank K B.ker = polarRank B := by
    change polarRank B + Module.finrank K B.ker = Module.finrank K X at hden
    omega
  have hm : m = polarRank B/2 := by
    calc
      m = (n - g.log2)/2 := rfl
      _ = (Module.finrank K X - g.log2)/2 := congrArg (fun v => (v-g.log2)/2) hdim.symm
      _ = (Module.finrank K X - Module.finrank K B.ker)/2 :=
        congrArg (fun v => (Module.finrank K X-v)/2) hglog
      _ = polarRank B/2 := congrArg (· / 2) hdiff
  have hr : polarRank B = 2*m := by
    obtain ⟨j,hj⟩ := rank_even (polarRank B) B (phase_alt hq) (phase_symm hq) rfl
    omega
  have hb : bal ↔ mask B f hq ≠ 0 := balanced_iff_mask f B hq
  constructor
  · intro q out
    have hh := oneBatch f B hq (hdiff.trans hr) q out
    have hiff : (∃ r : B.ker, f r ≠ f 0) ↔ bal := (masked_iff f B hq).trans hb.symm
    by_cases z : bal
    · rw [ite_eq_left (hiff.mpr z)] at hh
      simpa only [b, ite_eq_left z] using hh
    · rw [ite_eq_right (fun hr => z (hiff.mp hr))] at hh
      simpa only [b, ite_eq_right z] using hh
  · obtain ⟨q,out,ho⟩ := Lower441.batchAttain f B hq m j hr
    refine ⟨q,out, ?_⟩
    have hc : corr q out = score f (fun x => out (q x)) := by
      unfold corr score
      congr 1
    rw [hc]
    by_cases hm : mask B f hq = 0
    · have hn : ¬bal := fun hh => hb.mp hh hm
      simpa only [b, ite_eq_right hn, ite_eq_left hm] using ho
    · have hb' := hb.mpr hm
      simpa only [b, ite_eq_left hb', ite_eq_right hm] using ho
end Atlas461
end Donor441

namespace Pcx461UniformUpper
open scoped BigOperators

theorem of_seeds {V I : Type*} [Fintype V] [Nonempty V] [Fintype I]
    (hit : I → V → Prop) [∀ i x, Decidable (hit i x)] (w : I → ℚ) (p b : ℚ)
    (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (hp : ∀ x, p ≤ ∑ i, if hit i x then w i else 0)
    (hs : ∀ i, (∑ x, if hit i x then (1:ℚ) else -1) / Fintype.card V ≤ b) :
    p ≤ (1+b)/2 := by
  let N : ℚ := Fintype.card V
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have per (i : I) : (∑ x, if hit i x then (1:ℚ) else 0) ≤ (1+b)/2 * N := by
    have h := (div_le_iff₀ hN).mp (hs i)
    have he : (∑ x, if hit i x then (1:ℚ) else -1) =
        2*(∑ x, if hit i x then (1:ℚ) else 0)-N := by
      calc
        _ = ∑ x, (2*(if hit i x then (1:ℚ) else 0)-1) := by
          apply Finset.sum_congr rfl; intro x _; split <;> norm_num
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, N]
    rw [he] at h
    linarith
  apply le_of_mul_le_mul_right (a := N) _ hN
  calc
    p*N = ∑ _x : V, p := by simp [N, mul_comm]
    _ ≤ ∑ x : V, ∑ i, if hit i x then w i else 0 := Finset.sum_le_sum (fun x _ => hp x)
    _ = ∑ i, w i * (∑ x, if hit i x then (1:ℚ) else 0) := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; split <;> simp_all
    _ ≤ ∑ i, w i * ((1+b)/2 * N) := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (per i) (hw i))
    _ = (1+b)/2 * N := by rw [← Finset.sum_mul, h1, one_mul]

end Pcx461UniformUpper

namespace Pcx461Balanced
open scoped BigOperators
open Pcx461Generic
open Donor441.Atlas461
variable {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]

def corr (f g : V → F) : ℚ := (∑ x, if g x=f x then (1:ℚ) else -1) / Fintype.card V

noncomputable def phaseRank {n : ℕ} (f : X n → F) : ℕ :=
  (n - (Nat.card {u : X n // ∀ v, f (u+v)+f u+f v+f 0=0}).log2)/2

def Bal {V : Type*} (f : V → F) := Nat.card {x // f x=0} = Nat.card {x // f x=1}

noncomputable def U {n : ℕ} (f : X n → F) (j : ℕ) : ℚ := open Classical in
  if Bal f then (if j=0 then 0 else 1/(2:ℚ)^(phaseRank f-(j-1)/2)) else 1/(2:ℚ)^(phaseRank f-j/2)

theorem bounds {n : ℕ} (f : X n → F) (h : Polar f) (j : ℕ) :
    (∀ (q : X n →ₗ[F] X j) (d : X j → F), corr f (fun x=>d (q x)) ≤ U f j) ∧
    ∃ (q : X n →ₗ[F] X j) (d : X j → F), corr f (fun x=>d (q x)) = U f j := by
  classical
  obtain ⟨hh,q,d,he⟩ := uniformScore n f h j
  refine ⟨fun q d => ?_, q, d, ?_⟩
  · convert hh q d using 1 <;> first | (unfold corr; congr 1) | (unfold U Bal phaseRank; congr 1)
  · convert he using 1 <;> first | (unfold corr; congr 1) | (unfold U Bal phaseRank; congr 1)

theorem uniform_upper {f : V → F} {j : ℕ} {p B : ℚ}
    (h : ∀ (q : V →ₗ[F] X j) (d : X j → F), corr f (fun x=>d (q x)) ≤ B)
    (hp : Succ f j p) : p ≤ (1+B)/2 := by
  obtain ⟨r,w,q,d,hw,hs,hx⟩ := hp
  exact Pcx461UniformUpper.of_seeds (fun i x => d i (q i x) = f x) w p B hw hs hx (fun i => h (q i) (d i))

private lemma sign_flip (a : F) : sign (a+1) = -sign a := by
  have hh : ∀ a : F, a=0 ∨ a=1 := by decide
  rcases hh a with rfl|rfl <;> decide

private lemma prodSign (a b : F) : sign a * sign b = if b=a then 1 else -1 := by
  have hh : ∀ a : F, a=0 ∨ a=1 := by decide
  rcases hh a with rfl|rfl <;> rcases hh b with rfl|rfl <;> norm_num [sign]

private lemma translate (r : V) (g : V → ℚ) : ∑ x, g (x+r) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight r) _ _ (fun _=>rfl)

theorem flip_attain {f : V → F} (h : Polar f) (r : V) (flip : ∀ x, f (x+r) = f x+1)
    {j : ℕ} (q : V →ₗ[F] X j) (d : X j → F) (A : ℚ) (ha : corr f (fun x=>d (q x)) = A) :
    Succ f j ((1+A)/2) := by
  classical
  let g (x : V) := sign (d (q x))
  let H (x : V) := (g x - g (x+r))/2
  let D (i : Fin 2) (z : X j) := if i=0 then d z else d (z+q r)+1
  refine lift_moments h (fun _ : Fin 2 => (1:ℚ)/2) (by intros; norm_num) (by norm_num [Fin.sum_univ_two])
    (fun _ => q) D A H ?_ ?_ ?_
  · intro x
    simp only [D,H,g,Fin.sum_univ_two,ite_true,show (1:Fin 2)≠0 by decide,ite_false,sign_flip,map_add]; ring
  · have hs := translate r (fun x => sign (f x) * g x)
    simp only [flip,sign_flip,neg_mul,Finset.sum_neg_distrib] at hs
    have h2 : ∑ x, sign (f x)*g x = A * Fintype.card V := by
      have hn : (Fintype.card V : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
      rw [corr, div_eq_iff hn] at ha
      simpa only [g,prodSign] using ha
    have hpoint (x : V) : sign (f x)*H x = (sign (f x)*g x - sign (f x)*g (x+r))*(1/2) := by dsimp only [H]; ring
    simp only [hpoint, ← Finset.sum_mul, Finset.sum_sub_distrib]
    linarith
  · have hs := translate r (fun x => sign (f x))
    simp only [flip,sign_flip,Finset.sum_neg_distrib] at hs
    have hf : ∑ x, sign (f x) = 0 := by linarith
    have hp (x : V) : H x = (g x - g (x+r))*(1/2) := by dsimp only [H]; ring
    simp only [hp, ← Finset.sum_mul, Finset.sum_sub_distrib,translate,hf,sub_self,zero_mul,mul_zero]

theorem succ_mono {f : V → F} {j : ℕ} {p p' : ℚ} (h : p ≤ p') : Succ f j p' → Succ f j p := by
  rintro ⟨r,w,q,d,hw,hs,hx⟩; exact ⟨r,w,q,d,hw,hs,fun x => h.trans (hx x)⟩

theorem balanced_iff {n : ℕ} (f : X n → F) (h : Polar f) (hb : Bal f) (j : ℕ) (p : ℚ) :
    Succ f j p ↔ p ≤ (1+(if j=0 then 0 else 1/(2:ℚ)^(phaseRank f-(j-1)/2)))/2 := by
  classical
  obtain ⟨hub,q,d,ha⟩ := bounds f h j
  obtain ⟨r,hr⟩ := (rankShape n f h).1 hb
  have hu : U f j = (if j=0 then 0 else 1/(2:ℚ)^(phaseRank f-(j-1)/2)) := by simp [U,hb]
  rw [← hu]; exact ⟨uniform_upper hub, fun hh => succ_mono hh (flip_attain h r hr q d _ ha)⟩

end Pcx461Balanced

namespace Pcx461Endpoints

open scoped BigOperators
abbrev F := ZMod 2
abbrev X (n : ℕ) := Fin n → F

def Success {n : ℕ} (f : X n → F) (j : ℕ) (p : ℚ) : Prop :=
  ∃ (r : ℕ) (w : Fin r → ℚ)
    (query : Fin r → X n →ₗ[F] (Fin j → F))
    (out : Fin r → (Fin j → F) → F),
    (∀ seed, 0 ≤ w seed) ∧ (∑ seed, w seed)=1 ∧
      ∀ x : X n, p ≤ ∑ seed : Fin r, if out seed (query seed x)=f x then w seed else 0

variable {n j : ℕ} {f : X n → F} {p : ℚ}

theorem le_one (hp : Success f j p) : p ≤ 1 := by
  rcases hp with ⟨r,w,q,d,hw,hs,hp⟩
  apply (hp 0).trans
  rw [← hs]
  apply Finset.sum_le_sum
  intro i hi
  split <;> simp [hw]

theorem factor (q : X n →ₗ[F] X j) (g : X j → F) (h : ∀ x, g (q x) = f x) :
    Success f j p ↔ p ≤ 1 := by
  refine ⟨le_one, fun hp => ⟨1, fun _ => 1, fun _ => q, fun _ => g, ?_, ?_, ?_⟩⟩
  · simp
  · simp
  · intro x
    simpa [h] using hp

theorem full (hj : n ≤ j) : Success f j p ↔ p ≤ 1 := by
  let q : X n →ₗ[F] X j :=
    { toFun := fun x i => if h : i.val < n then x ⟨i.val,h⟩ else 0
      map_add' := by intro x y; ext i; by_cases h : i.val < n <;> simp [h]
      map_smul' := by intro c x; ext i; by_cases h : i.val < n <;> simp [h] }
  apply factor q (fun y => f (fun i => y (i.castLE hj)))
  intro x
  congr 1
  funext i
  simp [q,i.isLt]

theorem constant (hc : ∀ x, f x = f 0) : Success f j p ↔ p ≤ 1 :=
  factor 0 (fun _ => f 0) (fun x => (hc x).symm)

theorem fair (hp : p ≤ 1/2) : Success f j p := by
  refine ⟨2, fun _ => 1/2, fun _ => 0, fun i _ => if i=0 then 0 else 1, ?_, ?_, ?_⟩
  · intro i; norm_num
  · norm_num [Fin.sum_univ_two]
  · intro x
    have hb : ∀ c : F, c = 0 ∨ c = 1 := by decide
    rcases hb (f x) with h|h <;> simpa [Fin.sum_univ_two,h] using hp

theorem zero_nonconstant (hn : ¬∀ x, f x = f 0) : Success f 0 p ↔ p ≤ 1/2 := by
  classical
  refine ⟨?_, fair⟩
  push Not at hn
  obtain ⟨y,hy⟩ := hn
  rintro ⟨r,w,q,d,hw,hs,hp⟩
  have he : ∀ i, q i y = q i 0 := fun i => Subsingleton.elim _ _
  have hh := add_le_add (hp y) (hp 0)
  have hb : (∑ i, ((if d i (q i y) = f y then w i else 0) +
      (if d i (q i 0) = f 0 then w i else 0))) ≤ ∑ i, w i := by
    apply Finset.sum_le_sum
    intro i hi
    rw [he i]
    by_cases h : d i (q i 0) = f y
    · have hn' : d i (q i 0) ≠ f 0 := fun h' => hy (h.symm.trans h')
      rw [if_pos h, if_neg hn', add_zero]
    · rw [if_neg h, zero_add]
      split <;> simp [hw]
  rw [Finset.sum_add_distrib,hs] at hb
  linarith

theorem zero : Success f 0 p ↔ p ≤ (if ∀ x, f x = f 0 then 1 else 1/2) := by
  classical
  split <;> rename_i h
  · exact constant h
  · exact zero_nonconstant h

abbrev Rad (f : X n → F) := {u : X n // ∀ v : X n, f (u+v)+f u+f v+f 0=0}
abbrev Fiber (f : X n → F) (v : F) := {x : X n // f x = v}
abbrev Bal (f : X n → F) := Nat.card (Fiber f 0) = Nat.card (Fiber f 1)
noncomputable abbrev halfRank (f : X n → F) := (n - (Nat.card (Rad f)).log2)/2

private theorem bit : ∀ a : F, a=0 ∨ a=1 := by decide
private theorem cancel : ∀ a b c d : F, a+b+c+d=0 → a=c+(b+d) := by decide
private theorem self_add (x : X n) : x+x=0 := by
  funext i
  exact (show ∀ a : F, a+a=0 by decide) (x i)

theorem balance_of_flip (u : X n) (h : ∀ v, f (u+v)=f v+1) : Bal f := by
  let E : Fiber f 0 ≃ Fiber f 1 :=
    { toFun := fun x => ⟨u+x, by rw [h, x.property, zero_add]⟩
      invFun := fun x => ⟨u+x, by rw [h,x.property]; decide⟩
      left_inv := fun x => Subtype.ext (by simp [← add_assoc,self_add])
      right_inv := fun x => Subtype.ext (by simp [← add_assoc,self_add]) }
  exact Nat.card_congr E

theorem unbalanced_period (hb : ¬Bal f) (u : Rad f) (v : X n) : f (u+v) = f v := by
  have h (x : X n) := cancel _ _ _ _ (u.property x)
  rcases bit (f u + f 0) with hh|hh
  · simpa [hh] using h v
  · exact (hb (balance_of_flip u (fun x => by rw [h,hh]))).elim

private theorem card_X : Nat.card (X n) = 2^n := by simp [Nat.card_eq_fintype_card,X,F,ZMod.card]

private theorem card_fibers : Nat.card (Fiber f 0) + Nat.card (Fiber f 1) = 2^n := by
  classical
  let e : (Fiber f 0 ⊕ Fiber f 1) ≃ X n :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun x => if h : f x = 0 then Sum.inl ⟨x,h⟩ else Sum.inr ⟨x,(bit (f x)).resolve_left h⟩
      left_inv := by
        rintro (⟨x,h⟩|⟨x,h⟩) <;> simp [h]
      right_inv := by intro x; by_cases h : f x = 0 <;> simp [h] }
  simpa [Nat.card_sum,card_X] using Nat.card_congr e

theorem bal_nonconst (hb : Bal f) : ¬ ∀ x, f x = f 0 := by
  intro hc
  rcases bit (f 0) with h|h
  · haveI : IsEmpty (Fiber f 1) := ⟨fun x => (zero_ne_one : (0:F) ≠ 1) ((hc x).symm.trans x.property ▸ h.symm)⟩
    haveI : Nonempty (Fiber f 0) := ⟨⟨0,h⟩⟩
    exact (Nat.card_pos (α := Fiber f 0)).ne' (hb.trans Nat.card_of_isEmpty)
  · haveI : IsEmpty (Fiber f 0) := ⟨fun x => (zero_ne_one : (0:F) ≠ 1) (x.property.symm.trans ((hc x).trans h))⟩
    haveI : Nonempty (Fiber f 1) := ⟨⟨0,h⟩⟩
    exact (Nat.card_pos (α := Fiber f 1)).ne' (hb.symm.trans Nat.card_of_isEmpty)

theorem halfRank_const (hc : ∀ x, f x = f 0) : halfRank f = 0 := by
  let e : Rad f ≃ X n :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, fun y => by rw [hc (x+y),hc x,hc y]; exact (show ∀ a : F, a+a+a+a=0 by decide) _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold halfRank
  rw [Nat.card_congr e,card_X,Nat.log2_two_pow,Nat.sub_self]

theorem unbal_nonconst_rank (hb : ¬Bal f) (hn : ¬∀ x, f x = f 0) : 0 < halfRank f := by
  classical
  push Not at hn
  obtain ⟨y,hy⟩ := hn
  have both : ∀ b : F, ∃ x, f x = b := by
    intro b
    rcases bit (f 0) with h|h <;> rcases bit (f y) with hy'|hy' <;> rcases bit b with rfl|rfl <;> grind
  have cle (b : F) : Nat.card (Rad f) ≤ Nat.card (Fiber f b) := by
    obtain ⟨x,hx⟩ := both b
    let inc : Rad f → Fiber f b := fun u => ⟨u+x, (unbalanced_period hb u x).trans hx⟩
    apply Nat.card_le_card_of_injective inc
    intro u v e
    exact Subtype.ext (add_right_cancel (congrArg Subtype.val e : u.val+x=v.val+x))
  have hs := card_fibers (f := f)
  have h0 := cle 0
  have h1 := cle 1
  have hr : 0 < Nat.card (Rad f) := by
    haveI : Nonempty (Rad f) := ⟨⟨0,fun v => by simp only [zero_add]; exact (show ∀ a b : F, a+b+a+b=0 by decide) _ _⟩⟩
    exact Nat.card_pos
  have hlg : 2 ^ (Nat.card (Rad f)).log2 ≤ Nat.card (Rad f) := Nat.log2_self_le hr.ne'
  by_contra! bad
  change (n - (Nat.card (Rad f)).log2)/2 ≤ 0 at bad
  have he : n ≤ (Nat.card (Rad f)).log2+1 := by omega
  have hh := Nat.pow_le_pow_right (by decide : 0<2) he
  rw [pow_succ] at hh
  apply hb
  unfold Bal
  omega

theorem zero_posted : Success f 0 p ↔ p ≤ (1+(if Bal f then (0 : ℚ) else if 2*halfRank f ≤ 0 then 1 else 0))/2 := by
  classical
  by_cases hb : Bal f
  · rw [if_pos hb]
    simpa only [add_zero] using (zero_nonconstant (p := p) (bal_nonconst hb))
  · by_cases hc : ∀ x, f x = f 0
    · rw [if_neg hb, if_pos (by rw [halfRank_const hc])]
      norm_num
      exact (constant (p := p) (j := 0) hc)
    · have h : ¬2*halfRank f ≤ 0 := by have := unbal_nonconst_rank hb hc; omega
      rw [if_neg hb, if_neg h,add_zero]
      exact (zero_nonconstant (p := p) hc)

end Pcx461Endpoints

namespace Pcx461Endpoints
open scoped BigOperators
variable {n m j : ℕ} {f : X n → F} {p : ℚ}

theorem pack {I : Type} [Fintype I] (hk : Fintype.card I ≤ j)
    (L : I → X n →ₗ[F] F) (g : (I → F) → F)
    (h : ∀ x, g (fun i => L i x) = f x) : Success f j p ↔ p ≤ 1 := by
  classical
  let emb : I ↪ Fin j := (Fintype.equivFin I).toEmbedding.trans (Fin.castLEEmb hk)
  let C := Function.extend emb L (fun _ => 0)
  apply factor (LinearMap.pi C) (fun y => g (fun i => y (emb i)))
  intro x
  convert h x using 2
  funext i
  change (C (emb i)) x = L i x
  rw [show C (emb i) = L i by exact emb.injective.extend_apply _ _ _]

theorem clear_pairs (hj : 2*m ≤ j) (t : X n) (A C : Fin m → X n →ₗ[F] F)
    (h : ∀ x, f (x+t) = f t + ∑ i, A i x * C i x) : Success f j p ↔ p ≤ 1 := by
  apply pack (I := Fin m ⊕ Fin m) (by simpa [two_mul] using hj) (Sum.elim A C)
    (fun y => f t + ∑ i, (y (.inl i) - A i t) * (y (.inr i) - C i t))
  intro x
  simpa only [Sum.elim_inl, Sum.elim_inr,map_sub,sub_add_cancel] using (h (x-t)).symm

theorem extra_pair_bit (hj : 2*m+1 ≤ j) (L : X n →ₗ[F] F) (A C : Fin m → X n →ₗ[F] F)
    (h : ∀ x, f x = f 0 + L x + ∑ i, A i x * C i x) : Success f j p ↔ p ≤ 1 := by
  apply pack (I := Option (Fin m ⊕ Fin m)) (by simpa [two_mul] using hj)
    (fun k => k.elim L (Sum.elim A C))
    (fun y => f 0 + y none + ∑ i, y (some (.inl i)) * y (some (.inr i)))
  exact fun x => (h x).symm

theorem flip_log_rad {r : X n} (h : ∀ x, f (x+r)=f x+1) :
    1 ≤ (Nat.card (Rad f)).log2 := by
  classical
  let z : Rad f := ⟨0,fun v => by simp only [zero_add]; exact (show ∀ a b : F, a+b+a+b=0 by decide) _ _⟩
  have h0 : f r = f 0 + 1 := by simpa only [zero_add] using h 0
  let w : Rad f := ⟨r,fun v => by
    rw [add_comm r v,h,h0]
    exact (show ∀ a b : F, a+1+(b+1)+a+b=0 by decide) _ _⟩
  have hn : r ≠ 0 := by
    intro e
    rw [e] at h0
    exact (show ∀ a : F, a ≠ a+1 by decide) _ h0
  have zw : w ≠ z := fun e => hn (congrArg Subtype.val e)
  letI : Nontrivial (Rad f) := ⟨⟨w,z,zw⟩⟩
  have hc : 1 < Nat.card (Rad f) := Finite.one_lt_card
  exact (Nat.le_log2 (by omega)).mpr (by norm_num only [pow_one]; exact hc)

end Pcx461Endpoints

namespace Pcx461Endpoints
open Donor441
open Donor441.TwoStageSplit (polarRank)
open Donor441.Phase441
open Donor441.Phase441QuadraticCoordinates
open Donor441.Phase441SymplecticCoordinates
open scoped BigOperators
variable {n j : ℕ} {f : X n → F} {p : ℚ}

abbrev Quad (f : X n → F) := ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = f (u+v)+f u+f v+f 0

theorem unbal_sat (h : Quad f) (hb : ¬Bal f) (hj : 2*halfRank f ≤ j) : Success f j p ↔ p ≤ 1 := by
  obtain ⟨_,t,A,C,_,hh⟩ := (Atlas461.rankShape n f h).2 hb
  exact clear_pairs hj t A C hh

theorem all_sat (h : Quad f) (hj : 2*halfRank f+1 ≤ j) : Success f j p ↔ p ≤ 1 := by
  classical
  let X := Fin n → F
  let g := Nat.card (Rad f)
  let m := halfRank f
  let B := polarMap f h
  have hq : IsPhase f B := h
  have hg : g = Nat.card B.ker := by
    change Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card B.ker
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (TwoStageSplit.rad_mem B u).symm)
  have hdim : Module.finrank F X = n := by simp [X]
  have hglog : g.log2 = Module.finrank F B.ker := by
    rw [hg, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F), ZMod.card, Nat.log2_two_pow]
  have hden := B.finrank_range_add_finrank_ker
  have hdiff : Module.finrank F X - Module.finrank F B.ker = polarRank B := by
    change polarRank B + Module.finrank F B.ker = Module.finrank F X at hden
    omega
  have hm : m = polarRank B/2 := by
    calc
      m = (n - g.log2)/2 := rfl
      _ = (Module.finrank F X - g.log2)/2 := congrArg (fun v => (v-g.log2)/2) hdim.symm
      _ = (Module.finrank F X - Module.finrank F B.ker)/2 :=
        congrArg (fun v => (Module.finrank F X-v)/2) hglog
      _ = polarRank B/2 := congrArg (· / 2) hdiff
  have hr : polarRank B = 2*m := by
    obtain ⟨j,hj⟩ := rank_even (polarRank B) B (phase_alt hq) (phase_symm hq) rfl
    omega
  have pol (u v : X) : f (u+v)+f u+f v+f 0=B u v := rfl
  obtain ⟨D⟩ := normalForm m B (phase_alt hq) (phase_symm hq) hr
  exact extra_pair_bit hj (affineLinear D f pol) D.left D.right (exact_decomposition D f pol)

noncomputable def advantage (f : X n → F) (j : ℕ) : ℚ :=
  let m := halfRank f
  let s := j/2
  let base := (1 : ℚ)/2^m
  let best := (1 : ℚ)/2^(m-s)
  let freq := (1 : ℚ)/2^s
  if Bal f then
    (if j=0 then 0 else 1/(2:ℚ)^(m-(j-1)/2))
  else if 2*m ≤ j then 1
  else if j=0 then 0
  else if j % 2 = 1 then best
  else 3*best/(3+2*freq-2*best*base)

theorem zero_exact : Success f 0 p ↔ p ≤ (1+advantage f 0)/2 := by
  simpa only [advantage,ite_true] using (zero_posted (f := f) (p := p))

theorem saturated_exact (h : Quad f) (hj : 2*halfRank f+(if Bal f then 1 else 0) ≤ j) :
    Success f j p ↔ p ≤ (1+advantage f j)/2 := by
  by_cases hb : Bal f
  · rw [if_pos hb] at hj
    rw [all_sat h hj]
    have hjp : j ≠ 0 := by omega
    have hjm : halfRank f - (j-1)/2 = 0 := by omega
    simp only [advantage,if_pos hb,if_neg hjp,hjm,pow_zero,div_one]
    norm_num
  · rw [if_neg hb,add_zero] at hj
    rw [unbal_sat h hb hj]
    simp only [advantage,if_neg hb,if_pos hj]
    norm_num

theorem full_exact (h : Quad f) (hj : n ≤ j) : Success f j p ↔ p ≤ (1+advantage f j)/2 := by
  apply saturated_exact h
  by_cases hb : Bal f
  · obtain ⟨r,hr⟩ := (Atlas461.rankShape n f h).1 hb
    have hlog := flip_log_rad hr
    have hn : 0 < n := by
      by_contra! he
      have en : n = 0 := by omega
      subst n
      exact bal_nonconst hb (fun x => congrArg f (Subsingleton.elim _ _))
    rw [if_pos hb]
    unfold halfRank
    omega
  · rw [if_neg hb,add_zero]
    unfold halfRank
    omega

end Pcx461Endpoints

namespace Atlas461Transfer
abbrev K := ZMod 2
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def Success (f : V → K) (j : ℕ) (p : ℚ) : Prop :=
  ∃ (r : ℕ) (w : Fin r → ℚ) (q : Fin r → V →ₗ[K] (Fin j → K))
    (out : Fin r → (Fin j → K) → K), (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    ∀ x, p ≤ ∑ i, if out i (q i x) = f x then w i else 0

theorem pull {f : V → K} {g : W → K} (P : V →ₗ[K] W) (t : W) (c : K)
    (agree : ∀ x, f x = g (P x + t) + c) {j : ℕ} {p : ℚ} : Success g j p → Success f j p := by
  rintro ⟨r,w,q,out,hp,hw,hx⟩
  refine ⟨r,w,fun i => (q i).comp P, fun i z => out i (z + q i t) + c,hp,hw,?_⟩
  intro x
  simpa only [agree, LinearMap.comp_apply, add_left_inj, map_add] using hx (P x+t)

theorem quotient_iff {f : V → K} {g : W → K} (P : V →ₗ[K] W) (onto : Function.Surjective P)
    (t : V) (c : K) (agree : ∀ x, f (x+t) = g (P x) + c) (j : ℕ) (p : ℚ) :
    Success f j p ↔ Success g j p := by
  obtain ⟨Q,hQ⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr onto)
  constructor
  · apply pull Q t (-c)
    intro y
    rw [agree, show P (Q y) = y from LinearMap.congr_fun hQ y, add_neg_cancel_right]
  · apply pull P (-(P t)) c
    intro x
    have h := agree (x-t)
    rw [sub_add_cancel, map_sub, sub_eq_add_neg] at h
    exact h

end Atlas461Transfer

namespace Atlas461Transfer
open Donor441.Atlas461
abbrev Vect (m : ℕ) := Fin m → K
def inner (m : ℕ) (x : Vect m × Vect m) : K := ∑ i, x.1 i * x.2 i

theorem clearSuccess (n : ℕ) (f : Vect n → K)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = f (u+v)+f u+f v+f 0)
    (hu : Nat.card {x : Vect n // f x=0} ≠ Nat.card {x : Vect n // f x=1})
    (j : ℕ) (p : ℚ) :
    let m := (n-(Nat.card {u : Vect n // ∀ v, f (u+v)+f u+f v+f 0=0}).log2)/2
    Success f j p ↔ Success (inner m) j p := by
  intro m
  obtain ⟨_,t,A,C,ho,ha⟩ := (rankShape n f h).2 hu
  let P := (LinearMap.pi A).prod (LinearMap.pi C)
  apply quotient_iff P ho t (f t) _ j p
  intro x
  change f (x+t) = (∑ i, A i x * C i x) + f t
  exact (ha x).trans (add_comm _ _)
end Atlas461Transfer

namespace Pcx461Moments
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (m : ℕ) := (Fin m → F) × (Fin m → F)
variable {m : ℕ}
def chi (c : F) : ℚ := if c=0 then 1 else -1
def phase (S : Finset (Fin m)) (x : V m) : F := ∑ i ∈ S, x.1 i * x.2 i
def gate (T : Finset (Fin m)) (x : V m) : Prop := ∀ i ∈ T, x.1 i = 0
instance (T : Finset (Fin m)) (x : V m) : Decidable (gate T x) := by unfold gate; infer_instance
def mask (T : Finset (Fin m)) (x : V m) : ℚ := if gate T x then 1 else 0
def predict (S T : Finset (Fin m)) (c : F) (x : V m) := if gate T x then phase S x else c

def mu {U : Type*} [Fintype U] (v : U → ℚ) := (∑ x, v x) / Fintype.card U

def dy (a : ℕ) : ℚ := (1/(2:ℚ))^a
private lemma chi_add (a b : F) : chi (a+b)=chi a * chi b := by
  have hh : ∀ t : F, t=0 ∨ t=1 := by decide
  rcases hh a with rfl|rfl <;> rcases hh b with rfl|rfl <;> norm_num [chi]
  decide

private lemma chi_sum (S : Finset (Fin m)) (v : Fin m → F) :
    chi (∑ i ∈ S, v i) = ∏ i ∈ S, chi (v i) := by
  induction S using Finset.induction_on with
  | empty => simp [chi]
  | insert i S h ih => simp [h,chi_add,ih]

private lemma mu_prod (a : Fin m → (F × F) → ℚ) :
    mu (fun x : V m => ∏ i, a i (x.1 i, x.2 i)) = ∏ i, (∑ z, a i z)/4 := by
  let e : V m ≃ (Fin m → F × F) := {
    toFun := fun x i => (x.1 i,x.2 i), invFun := fun z => (fun i=>(z i).1,fun i=>(z i).2)
    left_inv := by intro x; rfl, right_inv := by intro x; rfl }
  have hh := Fintype.sum_equiv e (fun x : V m => ∏ i, a i (x.1 i,x.2 i)) (fun x => ∏ i, a i (x i)) (fun _ => rfl)
  unfold mu; rw [hh, ← Fintype.prod_sum, Finset.prod_div_distrib]
  simp only [V,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card, Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat, Finset.prod_const, Finset.card_univ]
  congr 1; rw [← mul_pow]; norm_num

lemma masked_phase (S T : Finset (Fin m)) :
    mu (fun x => chi (phase S x) * mask T x) = dy (S ∪ T).card := by
  classical
  let P (i : Fin m) (z : F × F) : ℚ := if i ∈ S then chi (z.1*z.2) else 1
  let M (i : Fin m) (z : F × F) : ℚ := if i ∈ T ∧ z.1 ≠ 0 then 0 else 1
  have hp (x : V m) : chi (phase S x) = ∏ i, P i (x.1 i,x.2 i) := by
    simp only [phase,chi_sum,P,Finset.prod_ite_mem_eq,Finset.univ_inter]
  have hm (x : V m) : mask T x = ∏ i, M i (x.1 i,x.2 i) := by
    by_cases h : gate T x
    · have hh (i) : ¬(i ∈ T ∧ x.1 i ≠ 0) := fun hc => hc.2 (h i hc.1)
      simp [mask,h,M,hh]
    · obtain ⟨i,hi,hn⟩ : ∃ i ∈ T, x.1 i ≠ 0 := by simpa [gate] using h
      rw [mask,if_neg h,Finset.prod_eq_zero (Finset.mem_univ i) (by simp [M,hi,hn])]
  have hh (x : V m) : chi (phase S x)*mask T x = ∏ i, (P i (x.1 i,x.2 i) * M i (x.1 i,x.2 i)) := by rw [hp,hm,Finset.prod_mul_distrib]
  change mu _ = _; simp_rw [hh]
  rw [mu_prod (fun i z => P i z * M i z)]
  have pts : ∀ p t : Bool,
      (∑ z : F × F, (if p then chi (z.1*z.2) else 1)*(if t ∧ z.1 ≠ 0 then 0 else 1)) / 4 = if p ∨ t then 1/2 else 1 := by
    decide +kernel
  have hj (i) : (∑ z, P i z * M i z)/4 = if i∈ S∪T then 1/2 else 1 := by
    by_cases hS : i∈S <;> by_cases hT : i∈T <;>
      simpa [P,M,hS,hT] using pts (decide (i∈S)) (decide (i∈T))
  simp_rw [hj]; rw [Finset.prod_ite_mem_eq]; simp [dy]

private lemma chi_sq (a : F) : chi a * chi a = 1 := by
  by_cases h : a=0 <;> simp [chi,h]

private lemma total_times (S : Finset (Fin m)) (x : V m) :
    chi (phase Finset.univ x) * chi (phase S x) = chi (phase Sᶜ x) := by
  have hh : phase Finset.univ x = phase S x + phase Sᶜ x := by
    exact (Finset.sum_add_sum_compl S (fun i => x.1 i*x.2 i)).symm
  rw [hh,chi_add,mul_right_comm,chi_sq,one_mul]

private lemma pure (S : Finset (Fin m)) : mu (fun x => chi (phase S x)) = dy S.card := by
  simpa [mask,gate] using masked_phase S ∅

lemma bias : mu (fun x : V m => chi (phase Finset.univ x)) = dy m := by simpa using pure (Finset.univ : Finset (Fin m))

private lemma mask_mu (T : Finset (Fin m)) : mu (mask T) = dy T.card := by
  simpa [phase,chi] using masked_phase ∅ T

private lemma mean_lin {U : Type*} [Fintype U] (p a b : U → ℚ) (c : ℚ) :
    mu (fun x => p x + (a x - b x)*c) = mu p + (mu a - mu b)*c := by
  unfold mu
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
  ring

lemma moments (S T : Finset (Fin m)) (h : Disjoint S T) (c : F) :
    mu (fun x => chi (phase Finset.univ x)*chi (predict S T c x)) = dy (m-S.card) ∧
    mu (fun x => chi (predict S T c x)) = dy (S.card+T.card) + (1-dy T.card)*chi c := by
  classical
  have gp (x : V m) : chi (predict S T c x) = chi (phase S x)*mask T x + (1-mask T x)*chi c := by
    by_cases h : gate T x <;> simp [predict,mask,h]
  have gc (x : V m) : chi (phase Finset.univ x)*chi (predict S T c x) =
      chi (phase Sᶜ x)*mask T x + (chi (phase Finset.univ x)-chi (phase Finset.univ x)*mask T x)*chi c := by
    rw [gp,← total_times S x]; ring
  have hu : Sᶜ ∪ T = Sᶜ := Finset.union_eq_left.mpr (by
    intro i hi; exact Finset.mem_compl.mpr (fun hS=> Finset.disjoint_left.mp h hS hi))
  constructor
  · simp_rw [gc]; rw [mean_lin (fun x => chi (phase Sᶜ x)*mask T x) _ _ _, masked_phase,hu,pure,masked_phase]
    simp [Finset.card_compl]
  · simp_rw [gp]; rw [mean_lin (fun x => chi (phase S x)*mask T x) _ _ _, masked_phase,mask_mu,Finset.card_union_of_disjoint h]
    have hh : mu (fun _ : V m => (1:ℚ)) = 1 := by simp [mu,NeZero.ne (Fintype.card (V m))]
    rw [hh]

end Pcx461Moments

namespace Pcx461Queries
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (m : ℕ) := (Fin m → F) × (Fin m → F)

variable {W : Type*} [AddCommGroup W] [Module F W]

private theorem repack {I : Type*} [Fintype I] {e : ℕ}
    (h : Fintype.card I ≤ e) (A : I → W →ₗ[F] F) :
    ∃ (L : W →ₗ[F] (Fin e → F)) (decode : (Fin e → F) → (I → F)),
      ∀ x i, decode (L x) i = A i x := by
  classical
  obtain ⟨E⟩ : Nonempty (I ↪ Fin e) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  let R (i : Fin e) : W →ₗ[F] F := if h : ∃ j, E j = i then A h.choose else 0
  refine ⟨LinearMap.pi R, fun v i => v (E i), ?_⟩
  intro x i
  have hi : ∃ j, E j = E i := ⟨i,rfl⟩
  have hh : hi.choose = i := E.injective hi.choose_spec
  change R (E i) x = _
  simp only [R, dif_pos hi, hh]

private def left {m : ℕ} (i : Fin m) : V m →ₗ[F] F where
  toFun x := x.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def right {m : ℕ} (i : Fin m) : V m →ₗ[F] F where
  toFun x := x.2 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem compile {m j : ℕ} (S T : Finset (Fin m)) (hj : 2*S.card + T.card ≤ j) :
    ∃ L : V m →ₗ[F] (Fin j → F), ∀ c : F, ∃ out : (Fin j → F) → F,
      ∀ x, out (L x) = if ∀ i ∈ T, x.1 i = 0 then ∑ i ∈ S, x.1 i * x.2 i else c := by
  classical
  let I := (S × Bool) ⊕ T
  let ask : I → V m →ₗ[F] F := Sum.elim
    (fun i => if i.2 then left i.1.val else right i.1.val) (fun i => left i.val)
  have hc : Fintype.card I ≤ j := by simpa [I, Nat.mul_comm] using hj
  obtain ⟨L, read, hread⟩ := repack hc ask
  refine ⟨L, fun c => ⟨fun v => if ∀ i : T, read v (Sum.inr i) = 0 then
    ∑ i : S, read v (Sum.inl (i,true)) * read v (Sum.inl (i,false)) else c, ?_⟩⟩
  intro x
  simp [hread, ask, left, right, Finset.sum_attach S (fun i => x.1 i * x.2 i)]

theorem exists_disjoint {m s t : ℕ} (h : s+t ≤ m) :
    ∃ S T : Finset (Fin m), Disjoint S T ∧ S.card = s ∧ T.card = t := by
  classical
  have hs : s ≤ (Finset.univ : Finset (Fin m)).card := by simp; omega
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq hs
  have ht : t ≤ Sᶜ.card := by rw [Finset.card_compl, Fintype.card_fin, hS]; omega
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq ht
  exact ⟨S, T, Finset.disjoint_left.mpr (fun _ hi hj => Finset.mem_compl.mp (hT hj) hi), hS, hcard⟩

end Pcx461Queries

namespace Pcx461Attain
open Pcx461Moments
open scoped BigOperators
variable {m j : ℕ}

abbrev dot (m : ℕ) := phase (m := m) Finset.univ

private lemma polar : Pcx461Generic.Polar (dot m) := by
  intro p u v
  simp only [dot, phase, Prod.fst_add, Prod.snd_add, Pi.add_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf
  all_goals simp [show (4 : F) = 0 by decide, show (2 : F) = 0 by decide]

private abbrev Pair (m j : ℕ) (C D : ℚ) :=
  ∃ (Q : V m →ₗ[F] (Fin j → F)) (d : (Fin j → F) → F),
    mu (fun x => chi (dot m x)*chi (d (Q x))) = C ∧ mu (fun x => chi (d (Q x))) = D

private lemma mix {C₀ C₁ D₀ D₁ A t : ℚ}
    (p₀ : Pair m j C₀ D₀) (p₁ : Pair m j C₁ D₁)
    (hb : mu (fun x => chi (dot m x)) = dy m)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hc : t*C₀+(1-t)*C₁=A)
    (hd : t*D₀+(1-t)*D₁=dy m*A) : Pcx461Generic.Succ (dot m) j ((1+A)/2) := by
  classical
  obtain ⟨Q₀,d₀,hc₀,hd₀⟩ := p₀
  obtain ⟨Q₁,d₁,hc₁,hd₁⟩ := p₁
  let v₀ (x : V m) := chi (d₀ (Q₀ x))
  let v₁ (x : V m) := chi (d₁ (Q₁ x))
  let H (x : V m) := t*v₀ x+(1-t)*v₁ x
  let N : ℚ := Fintype.card (V m)
  have hn : N ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos : 0 < (Fintype.card (V m) : ℚ)).ne'
  have un (v : V m → ℚ) (b : ℚ) (e : mu v = b) : ∑ x, v x = b*N := (div_eq_iff hn).mp e
  apply Pcx461Generic.lift_moments polar (fun b : Bool => if b then t else 1-t)
      (by intro b; cases b <;> simp [ht, sub_nonneg.mpr ht']) (by simp [Fintype.sum_bool])
      (fun b => if b then Q₀ else Q₁) (fun b => if b then d₀ else d₁) A H
  · intro x; simp only [Fintype.sum_bool,if_true,if_false,Bool.false_eq_true]
    rfl
  · change ∑ x, chi (dot m x)*H x = A*N
    have eqn (x : V m) : chi (dot m x)*H x = t*(chi (dot m x)*v₀ x)+(1-t)*(chi (dot m x)*v₁ x) := by dsimp [H]; ring
    simp_rw [eqn]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, un _ _ hc₀, un _ _ hc₁, ←hc]; ring
  · change ∑ x, (t*v₀ x+(1-t)*v₁ x) = A*∑ x : V m, chi (dot m x)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, un _ _ hd₀, un _ _ hd₁, un _ _ hb]
    linear_combination N*hd

private lemma dy_add (a b : ℕ) : dy (a+b) = dy a*dy b := by simp only [dy,pow_add]
private lemma dy1 (a : ℕ) : dy a ≤ 1 := by unfold dy; exact pow_le_one₀ (by norm_num) (by norm_num)
private lemma dy0 (a : ℕ) : 0 ≤ dy a := by unfold dy; positivity

private lemma from_pairs (hj : 0 < j) (h : j < 2*m)
    (hb : mu (fun x => chi (dot m x)) = dy m)
    (point : ∀ s k : ℕ, s+k ≤ m → 2*s+k = j → ∀ c : F,
      Pair m j (dy (m-s)) (dy (s+k) + (1-dy k)*chi c)) :
    Pcx461Generic.Succ (dot m) j ((1 + if j%2=1 then dy (m-j/2) else
      3*dy (m-j/2)/(3+2*dy (j/2)-2*dy (m-j/2)*dy m))/2) := by
  let s := j/2
  have hs : s < m := by dsimp [s]; omega
  let A := dy (m-s)
  let u := dy s
  let b := dy m
  have hbu : b ≤ u := by
    change dy m ≤ dy s
    calc
      dy m = dy (s+(m-s)) := congrArg dy (by omega)
      _ = dy s*dy (m-s) := dy_add _ _
      _ ≤ dy s*1 := mul_le_mul_of_nonneg_left (dy1 _) (dy0 _)
      _ = dy s := mul_one _
  have hab : A*b ≤ u := calc
    A*b ≤ 1*b := mul_le_mul_of_nonneg_right (dy1 _) (dy0 _)
    _ = b := one_mul _
    _ ≤ u := hbu
  have hu : u ≤ 1 := dy1 _
  have h0 : 0 ≤ A*b := mul_nonneg (dy0 _) (dy0 _)
  by_cases hpar : j%2=1
  · rw [if_pos hpar]
    have point' (c : F) := point s 1 (by omega) (by dsimp [s]; omega) c
    have p₀ : Pair m j A (u/2+1/2) := by
      convert point' 0 using 2 <;> norm_num [u,dy_add,chi,dy] <;> ring
    have p₁ : Pair m j A (u/2-1/2) := by
      convert point' 1 using 2 <;> norm_num [u,dy_add,chi,dy] <;> ring
    let t := (1+2*(A*b)-u)/2
    apply mix p₀ p₁ hb (t := t)
    · dsimp only [t]; linarith
    · dsimp only [t]; linarith
    · change t*A+(1-t)*A=A; ring
    · change t*(u/2+1/2)+(1-t)*(u/2-1/2)=b*A; dsimp [t]; ring
  · rw [if_neg hpar]
    have hs0 : 0 < s := by dsimp [s]; omega
    have p₀ : Pair m j A u := by
      simpa [A,u,dy] using point s 0 (by omega) (by dsimp [s]; omega) 0
    have pp := point (s-1) 2 (by omega) (by dsimp [s]; omega) 1
    have hx : m-(s-1) = (m-s)+1 := by omega
    have hy : s-1+2 = s+1 := by omega
    rw [hx,hy,dy_add (m-s) 1,dy_add s 1] at pp
    have p₁ : Pair m j (A/2) (u/2-3/4) := by
      convert pp using 2 <;> norm_num [dy,chi,A,u] <;> ring
    obtain ⟨ht,ht',hc,hd⟩ := Pcx461Generic.even_mix A u b (by linarith) (by linarith)
    exact mix p₀ p₁ hb ht ht' hc hd

theorem attain (hj : 0 < j) (h : j < 2*m) :
    Pcx461Generic.Succ (dot m) j ((1 + if j%2=1 then dy (m-j/2) else
      3*dy (m-j/2)/(3+2*dy (j/2)-2*dy (m-j/2)*dy m))/2) := by
  apply from_pairs hj h bias
  intro s k hsk hjk c
  obtain ⟨S,T,hdis,hS,hT⟩ := Pcx461Queries.exists_disjoint hsk
  obtain ⟨Q,hQ⟩ := Pcx461Queries.compile S T (j:=j) (by omega)
  obtain ⟨d,hd⟩ := hQ c
  refine ⟨Q,d,?_⟩
  have hp (x : V m) : d (Q x) = predict S T c x := hd x
  simpa only [hp,←hS,←hT,dot] using moments S T hdis c

end Pcx461Attain

namespace Donor441.Atlas461
open Phase441 BatchUpper TwoStageSplit
open LinearMap Module

theorem evenData (n : ℕ) (f : (Fin n → K) → K)
    (h : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = f (u+v)+f u+f v+f 0)
    (hu : Nat.card {x // f x=0} ≠ Nat.card {x // f x=1}) :
    let X := Fin n → K
    let g := Nat.card {u : X // ∀ v : X, f (u+v)+f u+f v+f 0=0}
    let m := (n-g.log2)/2
    ∃ B : LinearMap.BilinForm K X,
      (∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) ∧
      Module.finrank K X - Module.finrank K B.ker = 2*m ∧
      |(∑ x : X, if f x=0 then (1:ℚ) else -1) / (Fintype.card X : ℚ)| = 1/2^m := by
  classical
  intro X g m
  let B := polarMap f h
  have hq : IsPhase f B := h
  have hg : g = Nat.card B.ker := by
    change Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card B.ker
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (TwoStageSplit.rad_mem B u).symm)
  have hdim : Module.finrank K X = n := by simp [X]
  have hglog : g.log2 = Module.finrank K B.ker := by
    rw [hg, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ZMod.card, Nat.log2_two_pow]
  have hden := B.finrank_range_add_finrank_ker
  have hdiff : Module.finrank K X - Module.finrank K B.ker = polarRank B := by
    change polarRank B + Module.finrank K B.ker = Module.finrank K X at hden
    omega
  have hm : m = polarRank B/2 := by
    calc
      m = (n - g.log2)/2 := rfl
      _ = (Module.finrank K X - g.log2)/2 := congrArg (fun v => (v-g.log2)/2) hdim.symm
      _ = (Module.finrank K X - Module.finrank K B.ker)/2 :=
        congrArg (fun v => (Module.finrank K X-v)/2) hglog
      _ = polarRank B/2 := congrArg (· / 2) hdiff
  have hr : polarRank B = 2*m := by
    obtain ⟨j,hj⟩ := rank_even (polarRank B) B (phase_alt hq) (phase_symm hq) rfl
    omega
  refine ⟨B,hq,hdiff.trans hr,?_⟩
  have hcard : (Fintype.card X : ℚ) = (2:ℚ)^n := by simp [X, Fintype.card_fun,ZMod.card]
  have him := ((rankShape n f h).2 hu).1
  have hs : |(∑ x : X, sign (f x))| = (2:ℤ)^(n-m) := (congrArg abs (signCount f)).trans him
  have hqabs : |(∑ x : X, if f x=0 then (1:ℚ) else -1)| = (2:ℚ)^(n-m) := by
    have hc := congrArg (Int.cast : ℤ → ℚ) hs
    push_cast at hc
    convert hc using 1
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases ht : f x=0 <;> simp [sign,ht]
  have hmle : m ≤ n := by dsimp [m]; omega
  rw [abs_div,hqabs,hcard,abs_of_nonneg (by positivity)]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  rw [← pow_add,Nat.sub_add_cancel hmle,one_mul]
end Donor441.Atlas461

namespace BatchParity461
open scoped BigOperators

theorem dyadicGap (h : ℕ) : (1 / (2 : ℚ)^h) = 1 ∨ (1 / (2 : ℚ)^h) ≤ 1/2 := by
  cases h with
  | zero => simp
  | succ k =>
    right
    have hk : (1 : ℚ) ≤ 2^k := one_le_pow₀ (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by norm_num), pow_succ]
    linarith

theorem decoderShift (g M l : ℚ) (hg : g = 1 ∨ g = -1) :
    g*M-l*g ≤ |M-l| := by
  rcases hg with rfl | rfl
  · simpa using le_abs_self (M-l)
  · simpa [abs_sub_comm, add_comm] using le_abs_self (l-M)

theorem evenDual {ι : Type*} [Fintype ι] (w M g : ι → ℚ)
    (A freq u z l : ℚ) (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (hg : ∀ i, g i = 1 ∨ g i = -1) (hM : ∀ i, M i = 0 ∨ M i = z ∨ M i = -z)
    (h1 : ∑ i, w i * M i = A * freq) (h2 : ∑ i, w i * M i^2 ≤ A^2)
    (hz : 0 < z) (hl : 0 ≤ l) (hlz : l ≤ z) (hzu : z*u = A)
    (hSl : l*(3/2 + freq) = A) (hgap : u = 1 ∨ u ≤ 1/2) :
    (∑ i, w i * (g i * M i - l * g i)) ≤ 3*l/2 := by
  have hp (i : ι) : z^2 * |M i-l| =
      l*z^2 + (z-l)*M i^2 - l*z*M i := by
    rcases hM i with H | H | H <;> rw [H]
    · rw [abs_of_nonpos (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith)]
      ring
    · rw [abs_of_nonpos (by linarith)]
      ring
  have hlt : (∑ i, w i * (g i * M i - l * g i)) ≤ ∑ i, w i * |M i-l| :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (decoderShift _ _ _ (hg i)) (hw i)
  have hv : z^2 * (∑ i, w i * |M i-l|) ≤ l*z^2 + (z-l)*A^2-l*z*(A*freq) := by
    calc
      _ = ∑ i, w i * (z^2 * |M i-l|) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ i, (l*z^2 * w i + (z-l)*(w i*M i^2) - l*z*(w i*M i)) := by
        apply Finset.sum_congr rfl; intro i _; rw [hp]; ring
      _ ≤ _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
                        ← Finset.mul_sum, ← Finset.mul_sum, hn, h1, mul_one]; gcongr
  have hpoly : 0 ≤ (u-1)*(u-1/2) := by
    rcases hgap with rfl | H
    · simp
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hv' : z^2 * (∑ i, w i * |M i-l|) ≤ z^2 * (l + (A-l*freq)*u - l*u^2) := by
    apply hv.trans; rw [← hzu]; exact le_of_eq (by ring)
  have hcalc : (∑ i, w i * |M i-l|) ≤ l + (A-l*freq)*u - l*u^2 :=
    le_of_mul_le_mul_left hv' (by positivity : 0 < z^2)
  apply (hlt.trans hcalc).trans
  rw [← hSl]
  nlinarith [mul_nonneg hl hpoly]

theorem mixDual {ι : Type*} [Fintype ι] (w C D : ι → ℚ) (l U : ℚ)
    (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1) (h : ∀ i, C i - l*D i ≤ U) :
    (∑ i, w i*C i) - l*(∑ i, w i*D i) ≤ U := by
  calc
    _ = ∑ i, w i*(C i-l*D i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ i, w i*U := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)
    _ = _ := by rw [← Finset.sum_mul, hn, one_mul]

theorem classDual (C D b c l : ℚ) (hl1 : l ≤ 1) (hl2 : -1 ≤ l)
    (hp : (1+b)*c ≤ C+D) (hm : (1-b)*c ≤ C-D) :
    (1-l*b)*c ≤ C-l*D := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hl1),
    mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ 1+l by linarith)]

theorem evenMix (A freq b : ℚ) (h : 0 ≤ freq-A*b) (hf : freq-A*b ≤ 1) :
    ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
      t*freq + (1-t)*(freq/2-3/4) = b*(t*A+(1-t)*(A/2)) ∧
      t*A + (1-t)*(A/2) = 3*A/(3+2*freq-2*A*b) := by
  let d := freq-A*b
  have hd : 0 ≤ d := h
  have hd' : d ≤ 1 := hf
  have hpos : 0 < 3+2*d := by linarith
  refine ⟨(3-2*d)/(3+2*d), div_nonneg (by linarith) hpos.le, ?_, ?_, ?_⟩
  · rw [div_le_one hpos]; linarith
  · field_simp [hpos.ne']; dsimp [d]; ring
  · have hrw : 3+2*freq-2*A*b = 3+2*d := by dsimp [d]; ring
    rw [hrw]; field_simp [hpos.ne']; ring

theorem evenDyadic {ι : Type*} [Fintype ι] (w M g : ι → ℚ)
    (s k t : ℕ) (hs : 0 < s) (l : ℚ) (hSl : l*(3/2+1/(2:ℚ)^s) = 1/2^k)
    (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i = 1)
    (hg : ∀ i, g i = 1 ∨ g i = -1)
    (hM : ∀ i, M i = 0 ∨ M i = 1/(2:ℚ)^t ∨ M i = -(1/(2:ℚ)^t))
    (h1 : ∑ i, w i * M i = 1/(2:ℚ)^k * (1/2^s))
    (h2 : ∑ i, w i * M i^2 ≤ (1/(2:ℚ)^k)^2) :
    (∑ i, w i * (g i * M i - l * g i)) ≤ 3*l/2 := by
  have hfreq : 1/(2:ℚ)^s ≤ 1/2 := (dyadicGap s).resolve_left (by
    have hp : (1:ℚ) < 2^s := one_lt_pow₀ (by norm_num) (by omega)
    intro h; rw [div_eq_iff (by positivity)] at h; linarith)
  have hg0 : 0 < 3/2+1/(2:ℚ)^s := by positivity
  have hl : 0 < l := pos_of_mul_pos_left (by rw [hSl]; positivity) hg0.le
  by_cases htk : t ≤ k
  · have hsu : (1/(2:ℚ)^t) * (1/2^(k-t)) = 1/2^k := by
      rw [div_mul_div_comm, one_mul, ← pow_add, Nat.add_sub_of_le htk]
    have hul : (1:ℚ)/2^(k-t) ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have hla : l ≤ 1/(2:ℚ)^k := by
      rw [← hSl]; nlinarith [mul_nonneg hl.le (show 0 ≤ (1:ℚ)/2^s by positivity)]
    apply evenDual w M g _ _ _ _ _ hw hn hg hM h1 h2 (by positivity) hl.le _ hsu hSl (dyadicGap _)
    apply hla.trans; rw [← hsu]; exact mul_le_of_le_one_right (by positivity) hul
  · have hpow : (2:ℚ)^k*2 ≤ 2^t := by rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hz2 : (1:ℚ)/2^t ≤ (1/2^k)/2 := by rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; simpa using hpow
    have hzl : (1:ℚ)/2^t ≤ l := by apply hz2.trans; rw [← hSl]; nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hfreq)]
    have hp (i : ι) : g i * M i - l * g i ≤ l - M i := by
      apply (decoderShift _ _ _ (hg i)).trans; rw [abs_of_nonpos]; · linarith
      have HH := hM i; rcases HH with H | H | H <;> rw [H] <;> linarith [show 0 ≤ (1:ℚ)/2^t by positivity]
    calc
      _ ≤ ∑ i, w i*(l-M i) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hp i) (hw i)
      _ = l - (1/(2:ℚ)^k * (1/2^s)) := by simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hn, h1, one_mul]
      _ ≤ _ := by linarith [show 0 ≤ (1/(2:ℚ)^k * (1/2^s)) by positivity]

end BatchParity461

namespace BatchParity461.Profile
open scoped BigOperators
open LinearMap Module
private abbrev F := ZMod 2

variable {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
variable [AddCommGroup W] [Module F W]

def sign (z : F) : ℤ := if z = 0 then 1 else -1

private theorem sign_add (x y : F) : sign (x + y) = sign x * sign y := by
  exact (by decide : ∀ x y : F, sign (x+y) = sign x * sign y) x y

private theorem sum_translate {A : Type*} [AddCommGroup A] [Fintype A]
    (g : A → ℤ) (r : A) : (∑ x, g (x+r)) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight r) _ _ fun _ => rfl

private theorem zero_or_one (x : F) : x = 0 ∨ x = 1 :=
  (by decide : ∀ y : F, y = 0 ∨ y = 1) x

private theorem char_sum {A : Type*} [AddCommGroup A] [Fintype A]
    (l : A →+ F) : (∑ x, sign (l x)) = if l = 0 then (Fintype.card A : ℤ) else 0 := by
  classical
  by_cases hz : l = 0
  · simp [hz, sign]
  · obtain ⟨r, hr⟩ : ∃ r, l r ≠ 0 := by
      by_contra! h
      exact hz (AddMonoidHom.ext h)
    have h := sum_translate (fun x => sign (l x)) r
    simp only [l.map_add, sign_add, (zero_or_one (l r)).resolve_left hr,
      show sign 1 = -1 by decide, ← Finset.sum_mul] at h
    rw [ite_eq_right hz]
    linarith

private theorem rearrange (a b c d z : F) (h : a+b+c+d=z) : a+b = c+d+z := by
  exact (by decide : ∀ a b c d z : F, a+b+c+d=z → a+b=c+d+z) a b c d z h

private theorem eq_iff_add_zero (a b : F) : a = b ↔ a+b = 0 :=
  (by decide : ∀ a b : F, a=b ↔ a+b=0) a b

open Classical in
private theorem square {A H : Type*} [AddCommGroup A] [Fintype A] [Zero H]
    (q : A → F) (p : A → H) (b : H → A →+ F) (hb : ∀ h, b h = 0 ↔ h = 0)
    (hq : ∀ x r, q (x+r)+q x+q r+q 0 = b (p r) x) :
    (∑ x, sign (q x)) ^ 2 =
      (Fintype.card A : ℤ) * ∑ r, if p r = 0 then sign (q r+q 0) else 0 := by
  classical
  rw [pow_two]
  calc
    _ = ∑ x : A, ∑ y : A, sign (q x) * sign (q y) := by
      simp only [Finset.mul_sum, mul_comm]
    _ = ∑ x : A, ∑ r : A, sign (q x) * sign (q (r+x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_translate (fun y => sign (q x) * sign (q y)) x).symm
    _ = ∑ r : A, ∑ x : A, sign (q r+q 0)*sign (b (p r) x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      rw [← sign_add, ← sign_add, add_comm r x, add_comm (q x)]
      rw [rearrange _ _ _ _ _ (hq x r)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.mul_sum, char_sum]
      simp only [hb]
      split <;> ring

private theorem card_pow (A : Type*) [AddCommGroup A] [Module F A] [Fintype A] :
    Fintype.card A = 2 ^ Module.finrank F A := by
  rw [Module.card_eq_pow_finrank (K := F), ZMod.card]

private theorem dim_ker_inter (B : V →ₗ[F] W) {e : ℕ} (L : V →ₗ[F] (Fin e → F)) :
    finrank F V - finrank F B.ker ≤
      finrank F L.ker - finrank F (B.domRestrict L.ker).ker +
        (e - finrank F (L.domRestrict B.ker).range) := by
  let I := (B.domRestrict L.ker).ker
  let J := (L.domRestrict B.ker).ker
  let E : I ≃ₗ[F] J :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hIJ := E.finrank_eq
  have hK := L.finrank_range_add_finrank_ker
  have hJ := (L.domRestrict B.ker).finrank_range_add_finrank_ker
  have hI := (B.domRestrict L.ker).finrank_range_add_finrank_ker
  have he := Submodule.finrank_le L.range
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  dsimp [I, J] at hIJ
  omega

omit [Fintype V] in
private theorem derivative (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (x r : V) :
    f (x+r)+f x = f r+f 0+B r x := by
  apply rearrange
  calc
    _ = f (0+r+x)+f (0+r)+f (0+x)+f 0 := by
      simp only [zero_add]
      ac_rfl
    _ = _ := hq 0 r x

private theorem toAddMonoidHom_eq_zero {A : Type*} [AddCommGroup A] [Module F A]
    (l : A →ₗ[F] F) : l.toAddMonoidHom = 0 ↔ l = 0 :=
  ⟨fun h => LinearMap.ext fun t => DFunLike.congr_fun h t, fun h => by subst l; rfl⟩

private theorem sumDiv {ι : Type*} [Fintype ι] (f : ι → ℚ) (c : ℚ) :
    (∑ i, f i)/c = ∑ i, f i/c := by simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem square_dyadic {a : ℤ} {j : ℕ} (h : a^2 = 2^j) :
    a = 2^(j/2) ∨ a = -2^(j/2) := by
  have hn : a.natAbs ^ 2 = 2^j := by
    simpa only [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 by decide] using congrArg Int.natAbs h
  have hj : 2 * (a.natAbs.factorization 2) = j := by
    have he := congrArg (fun n : ℕ => n.factorization 2) hn
    rw [Nat.factorization_pow_self Nat.prime_two, Nat.factorization_pow, Finsupp.smul_apply,
      smul_eq_mul] at he
    exact he
  have he : j/2*2=j := by omega
  have hf : a^2 = ((2:ℤ)^(j/2))^2 := by rwa [← pow_mul, he]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hf

theorem batchProfile (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {m s : ℕ} (hs : s ≤ m) (hr : finrank F V - finrank F B.ker = 2*m)
    (L : V →ₗ[F] (Fin (2*s) → F)) (out : (Fin (2*s) → F) → F) :
    ∃ (t : ℕ) (M : V → ℚ),
      (∀ x, M x = 0 ∨ M x = 1/(2:ℚ)^t ∨ M x = -(1/(2:ℚ)^t)) ∧
      (∑ x, M x) = ∑ x, (sign (f x) : ℚ) ∧
      (∑ x, M x^2) ≤ Fintype.card V * (1/(2:ℚ)^(m-s))^2 ∧
      (∑ x, (sign (out (L x)) : ℚ) * M x) = ∑ x, (sign (out (L x)+f x) : ℚ) := by
  classical
  let K := L.ker
  let I := (B.domRestrict K).ker
  let P : K →ₗ[F] K →ₗ[F] F :=
    { toFun := fun r => (B r).domRestrict K
      map_add' := fun r s => by ext t; simp
      map_smul' := fun c r => by ext t; simp }
  let J := P.ker
  let A (x : V) := ∑ k : K, sign (f (x+k))
  let H (x : V) := sign (out (L x)+f x)
  let C (x : V) := sign (out (L x))
  have hsquare (x : V) : A x ^ 2 = (Fintype.card K : ℤ) *
      ∑ r : K, if P r = 0 then sign (f (x+r)+f x) else 0 := by
    change (∑ k : K, sign (f (x+k))) ^ 2 = _
    simpa only [Submodule.coe_add, Submodule.coe_zero, add_zero, ← add_assoc] using
      (square (fun k : K => f (x+k)) P LinearMap.toAddMonoidHom
        toAddMonoidHom_eq_zero
        (fun k r => by
          change f (x+(↑(k+r) : V))+f (x+k)+f (x+r)+f (x+(↑(0 : K) : V)) =
            B r k
          calc
            _ = f (x+r+k)+f (x+r)+f (x+k)+f x := by
              simp only [Submodule.coe_add, Submodule.coe_zero, add_zero]
              ac_rfl
            _ = _ := hq x r k))
  have hlocal (x : V) : A x = 0 ∨ A x ^ 2 = (2 : ℤ)^(finrank F K+finrank F J) := by
    let l : J →+ F :=
      { toFun := fun r => f (x+(r.val : V))+f x
        map_zero' := by
          change f (x+0)+f x = 0
          rw [add_zero, ← eq_iff_add_zero]
        map_add' := fun r s => by
          have hz : B (r.val : V) (s.val : V) = 0 := by
            have hh : P r.val = 0 := r.property
            exact DFunLike.congr_fun hh s.val
          have hh := hq x (r.val : V) (s.val : V)
          rw [hz] at hh
          change f (x+((r.val : V)+(s.val : V)))+f x =
            (f (x+(r.val : V))+f x)+(f (x+(s.val : V))+f x)
          rw [← add_assoc]
          exact (by decide : ∀ a b c d : F, a+b+c+d=0 → a+d=(b+d)+(c+d)) _ _ _ _ hh }
    have hx : (∑ r : K, if P r = 0 then sign (f (x+r)+f x) else 0) =
        ∑ r : J, sign (l r) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun r => by simp [J, LinearMap.mem_ker]) _
    have hy := hsquare x
    rw [hx, char_sum] at hy
    split at hy
    · right
      rw [card_pow K, card_pow J] at hy
      simpa [pow_add] using hy
    · left
      rw [mul_zero, pow_two, mul_eq_zero] at hy
      exact hy.elim id id
  have hglob (r : K) : (∑ x : V, sign (f (x+r)+f x)) =
      if B r = 0 then (Fintype.card V : ℤ)*sign (f r+f 0) else 0 := by
    simp only [derivative f B hq, sign_add, ← Finset.mul_sum]
    change sign (f r) * sign (f 0) * (∑ x : V, sign ((B r).toAddMonoidHom x)) = _
    rw [char_sum]
    simp only [toAddMonoidHom_eq_zero]
    split <;> ring

  have hsumsquare : (∑ x, A x ^ 2) ≤ (Fintype.card K : ℤ) *
      ((Fintype.card V : ℤ) * Fintype.card I) := by
    simp only [hsquare, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r : K, if B r = 0 then (Fintype.card V : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases h : P r = 0
        · simp only [h, ite_true, hglob]
          split
          · unfold sign
            split <;> simp
          · rfl
        · simp only [ite_eq_right h, Finset.sum_const_zero]
          split <;> positivity
      _ = _ := by
        rw [← Finset.sum_filter]
        rw [Finset.sum_subtype (p := fun r : K => r ∈ I) (F := (inferInstance : Fintype I)) _
          (fun r : K => by change _ ↔ B r = 0; simp) _]
        simp [mul_comm]
  have hAvg : (∑ x, C x * A x) = (Fintype.card K : ℤ) * ∑ x, H x := by
    have hshift (r : K) (x : V) : sign (out (L x)) * sign (f (x+r)) = H (x+r) := by
      have hh : L (r : V) = 0 := r.property
      simp [H, sign_add, hh]
    calc
      _ = ∑ x : V, ∑ r : K, sign (out (L x)) * sign (f (x+r)) := by
        simp only [C, A, Finset.mul_sum]
      _ = ∑ r : K, ∑ x : V, H (x+r) := by rw [Finset.sum_comm]; simp only [hshift]
      _ = _ := by simp only [sum_translate H, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hKK : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hK := card_pow K
  have hI := card_pow I
  let k := finrank F K
  let d := finrank F J
  have hdk : d ≤ k := Submodule.finrank_le J
  have hk : (k+d)/2 ≤ k := by omega
  refine ⟨k-(k+d)/2, fun x => (A x : ℚ) / Fintype.card K, ?_, ?_, ?_, ?_⟩
  · intro x
    rcases hlocal x with h | h
    · left; simp [h]
    change (A x)^2=(2:ℤ)^(k+d) at h
    have hpow : ((2:ℚ)^((k+d)/2)) * 2^(k-(k+d)/2) = 2^k := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hK, Nat.cast_pow, Nat.cast_ofNat]
    change _ = 0 ∨ (A x : ℚ)/2^k = _ ∨ (A x : ℚ)/2^k = _
    rcases square_dyadic h with hh | hh <;> rw [hh] <;> push_cast
    · right; left; apply (div_eq_div_iff (by positivity) (by positivity)).2; simpa using hpow
    · right; right; rw [neg_div]; apply congrArg Neg.neg
      apply (div_eq_div_iff (by positivity) (by positivity)).2; simpa using hpow
  · have ham : (∑ x, A x) = (Fintype.card K : ℤ) * ∑ x, sign (f x) := by
      change (∑ x : V, ∑ r : K, sign (f (x+r))) = _
      rw [Finset.sum_comm]; simp only [sum_translate (fun x => sign (f x)), Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ]
    rw [← sumDiv, div_eq_iff hKK.ne']
    exact_mod_cast (ham.trans (mul_comm _ _))
  · have hd := dim_ker_inter B L
    rw [hr] at hd
    change 2*m ≤ k - finrank F I + _ at hd
    have hik : finrank F I ≤ k := Submodule.finrank_le I
    have he : finrank F I + (m-s)*2 ≤ k := by omega
    have hcard : (Fintype.card I : ℚ) * ((2:ℚ)^(m-s))^2 ≤ Fintype.card K := by
      rw [hI,hK]; push_cast; rw [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) he
    have hrat : (∑ x, (A x : ℚ)^2) ≤ (Fintype.card K : ℚ) * (Fintype.card V * Fintype.card I) := by
      exact_mod_cast hsumsquare
    simp only [div_pow, one_pow, ← sumDiv]
    rw [div_le_iff₀ (by positivity)]
    apply hrat.trans
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcard (show (0:ℚ) ≤ Fintype.card K * Fintype.card V by positivity)]
  · simp only [← mul_div_assoc, ← sumDiv]
    rw [div_eq_iff hKK.ne']
    exact_mod_cast (hAvg.trans (mul_comm _ _))

end BatchParity461.Profile

namespace BatchParity461
open scoped BigOperators
open LinearMap Module
abbrev Bit := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module Bit V] [Fintype V]

def sg (c : Bit) : ℚ := (Profile.sign c : ℚ)
private theorem sgpm (c : Bit) : sg c=1 ∨ sg c = -1 := by unfold sg Profile.sign; split <;> norm_num
private theorem sg_sq (c : Bit) : (sg c)^2 = 1 := by rcases sgpm c with H | H <;> rw [H] <;> norm_num
private theorem sg_add (c d : Bit) : sg (c+d)=sg c*sg d := by
  unfold sg; exact_mod_cast Profile.sign_add c d
private theorem sg_eq (c d : Bit) : sg (c+d) = if c=d then 1 else -1 := by
  fin_cases c <;> fin_cases d <;> decide

private def wt (V : Type*) [Fintype V] : ℚ := 1/Fintype.card V
private def avg {V : Type*} [Fintype V] (q : V → ℚ) := wt V * ∑ x, q x
private theorem aw_pos : 0 < wt V := by unfold wt; positivity
private theorem aw_total : ∑ _ : V, wt V = 1 := by simp [wt, Fintype.card_ne_zero]
private theorem avg_const (a : ℚ) : avg (fun _ : V => a) = a := by
  have h : (0:ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  simp [avg, wt]
private theorem avg_sub (f g : V → ℚ) : avg (fun x => f x-g x) = avg f-avg g := by
  simp only [avg,Finset.sum_sub_distrib,mul_sub]
private theorem avg_mul (a : ℚ) (f : V → ℚ) : avg (fun x => a*f x) = a*avg f := by
  simp only [avg,← Finset.mul_sum]; ring
private theorem avg_mono (f g : V → ℚ) (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) aw_pos.le

private theorem seedDual (f : V → Bit) (B : LinearMap.BilinForm Bit V)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (s m : ℕ) (hs : 0 < s) (hsm : s ≤ m) (hr : finrank Bit V - finrank Bit B.ker = 2*m)
    (L : V →ₗ[Bit] (Fin (2*s) → Bit)) (out : (Fin (2*s) → Bit) → Bit)
    (l : ℚ) (hSl : l*(3/2+1/(2:ℚ)^s) = 1/2^(m-s))
    (hm : avg (fun x => sg (f x)) = (1/(2:ℚ)^(m-s))*(1/2^s)) :
    avg (fun x => (1-l*sg (f x)) * sg (out (L x)+f x)) ≤ 3*l/2 := by
  obtain ⟨t,M,hz,h1,h2,hC⟩ := Profile.batchProfile f B hq hsm hr L out
  have hf : (∑ i, wt V * M i) = 1/(2:ℚ)^(m-s) * (1/2^s) := by
    rw [← Finset.mul_sum, h1]; exact hm
  have hv : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos
  have hS : (∑ i, wt V * M i^2) ≤ (1/(2:ℚ)^(m-s))^2 := by
    rw [← Finset.mul_sum]
    calc
      _ ≤ wt V * (Fintype.card V * (1/(2:ℚ)^(m-s))^2) := mul_le_mul_of_nonneg_left h2 aw_pos.le
      _ = _ := by unfold wt; field_simp
  have hDual := evenDyadic (fun _ : V => wt V) M (fun x => sg (out (L x))) s (m-s) t hs l hSl
    (fun _ => aw_pos.le) aw_total (fun x => sgpm _) hz hf hS
  rw [← Finset.mul_sum] at hDual
  change avg _ ≤ _ at hDual
  rw [avg_sub,avg_mul] at hDual
  have heq : avg (fun x => sg (out (L x))* M x) = avg (fun x => sg (out (L x)+f x)) := by
    unfold avg; rw [show (∑ x, sg (out (L x))*M x) = ∑ x, sg (out (L x)+f x) from hC]
  rw [heq] at hDual
  have hrep : (fun x => (1-l*sg (f x)) * sg (out (L x)+f x)) =
      fun x => sg (out (L x)+f x)-l*sg (out (L x)) := by
    funext x; rw [sg_add]; nlinarith [congrArg (fun z => l*sg (out (L x))*z) (sg_sq (f x))]
  rwa [hrep, avg_sub, avg_mul]

private theorem orientation {S q : ℚ} (h : |S|=q) : ∃ c : Bit, sg c * S=q := by
  by_cases hh : 0 ≤ S
  · refine ⟨0, ?_⟩; simpa [sg, Profile.sign, abs_of_nonneg hh] using h
  · refine ⟨1, ?_⟩; simpa [sg, Profile.sign, abs_of_neg (lt_of_not_ge hh)] using h

theorem evenUpper (f : V → Bit) (B : LinearMap.BilinForm Bit V)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (s m : ℕ) (hs : 0 < s) (hsm : s < m) (hr : finrank Bit V - finrank Bit B.ker = 2*m)
    (hb : |(∑ x, sg (f x))/(Fintype.card V)| = 1/(2:ℚ)^m)
    (p : ℚ) (r : ℕ) (w : Fin r → ℚ) (L : Fin r → V →ₗ[Bit] (Fin (2*s) → Bit))
    (out : Fin r → (Fin (2*s) → Bit) → Bit)
    (hw : ∀ i, 0 ≤ w i) (hn : ∑ i, w i=1)
    (hp : ∀ x, p ≤ ∑ i, if out i (L i x)=f x then w i else 0) :
    p ≤ (1+3*(1/(2:ℚ)^(m-s))/(3+2*(1/2^s)-2*(1/2^(m-s))*(1/2^m)))/2 := by
  classical
  let A := 1/(2:ℚ)^(m-s)
  let b := 1/(2:ℚ)^m
  let q := 1/(2:ℚ)^s
  let d := 3/2+q
  let l := A/d
  have hA : 0 < A := by dsimp [A]; positivity
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hA1 : A ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hb1 : b ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hd : 0 < d := by dsimp [d]; linarith
  have hl : 0 < l := div_pos hA hd
  have hl1 : l < 1 := (div_lt_one hd).2 (by dsimp [d]; linarith)
  have hSl : l*d=A := div_mul_cancel₀ _ hd.ne'
  have hbA : b=A*q := by dsimp [A,q,b]; rw [div_mul_div_comm, one_mul, ← pow_add, Nat.sub_add_cancel hsm.le]
  have hbavg : |avg (fun x => sg (f x))|=b := by simpa [avg,wt,b,div_eq_mul_inv,mul_comm] using hb
  obtain ⟨c,hc⟩ := orientation hbavg
  let f' (x : V) := c+f x
  let o' (i : Fin r) (y : Fin (2*s) → Bit) := c+out i y
  have hmean : avg (fun x => sg (f' x))=b := by simpa only [f', sg_add, avg_mul] using hc
  have hquad (p u v : V) : f' (p+u+v)+f' (p+u)+f' (p+v)+f' p = B u v := by
    rw [← hq p u v]; dsimp [f']; have hh : c+c=0 := ZModModule.add_self c
    linear_combination 2*hh
  let X (x : V) := 1-l*sg (f' x)
  let H (i : Fin r) (x : V) := sg (o' i (L i x)+f' x)
  have hX (x : V) : 0 ≤ X x := by dsimp [X]; rcases sgpm (f' x) with h | h <;> rw [h] <;> linarith
  have hH (i : Fin r) : avg (fun x => X x * H i x) ≤ 3*l/2 :=
    seedDual f' B hquad s m hs hsm.le hr (L i) (o' i) l hSl (hmean.trans hbA)
  have hpoint (x : V) : 2*p-1 ≤ ∑ i, w i * H i x := by
    have e : (∑ i, w i*H i x) = 2*(∑ i, if out i (L i x)=f x then w i else 0) - ∑ i,w i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl
      intro i _; simp only [H,sg_eq,o',f',add_right_inj]; split <;> ring
    rw [e,hn]; linarith [hp x]
  have hpoint' (x : V) : (2*p-1)*X x ≤ ∑ i, w i*(X x*H i x) := by
    have h := mul_le_mul_of_nonneg_left (hpoint x) (hX x)
    rw [Finset.mul_sum] at h
    simpa only [mul_left_comm, mul_comm, mul_assoc] using h
  have hav := avg_mono _ _ hpoint'
  have hmix : avg (fun x => ∑ i, w i*(X x*H i x)) = ∑ i, w i * avg (fun x => X x*H i x) := by
    unfold avg
    rw [Finset.sum_comm (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset (Fin r))), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    ring
  rw [avg_mul,hmix] at hav
  have hxavg : avg X = 1-l*b := by dsimp [X]; rw [avg_sub, avg_const, avg_mul, hmean]
  rw [hxavg] at hav
  have hu : (2*p-1)*(1-l*b) ≤ 3*l/2 := calc
    _ ≤ _ := hav
    _ ≤ ∑ i, w i*(3*l/2) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hH i) (hw i)
    _ = _ := by rw [← Finset.sum_mul,hn,one_mul]
  change p ≤ (1+3*A/(3+2*q-2*A*b))/2
  have hdB : 0 < 3+2*q-2*A*b := by nlinarith [mul_le_of_le_one_right hA.le hb1]
  have he : (2*p-1)*(3+2*q-2*A*b) ≤ 3*A := by
    have hh := mul_le_mul_of_nonneg_right hu hd.le
    change l*(3/2+q)=A at hSl
    change _*(3/2+q) ≤ _*(3/2+q) at hh
    rw [← hSl]; nlinarith only [hh]
  have hz := (le_div_iff₀ hdB).2 he
  linarith

end BatchParity461
namespace BatchParity461
lemma atlas461_sg (c : Bit) : sg c = if c = 0 then (1 : ℚ) else -1 := by
  by_cases h : c = 0 <;> simp [sg,Profile.sign,h]
end BatchParity461

namespace Pcx461Close
open scoped BigOperators
open Pcx461Endpoints

abbrev EvenUpper := ∀ {n : ℕ} (f : X n → F) (_ : Quad f) (_ : ¬ Bal f)
    (s : ℕ) (_ : 0 < s) (_ : s < halfRank f) (p : ℚ),
    Success f (2*s) p →
    let best := (1:ℚ)/2^(halfRank f-s)
    p ≤ (1+3*best/(3+2*(1/(2:ℚ)^s)-2*best*(1/(2:ℚ)^halfRank f)))/2

private theorem inner_dot (m : ℕ) : Atlas461Transfer.inner m = Pcx461Attain.dot m := by
  funext x
  simp [Atlas461Transfer.inner,Pcx461Attain.dot,Pcx461Moments.phase]

private theorem dy_eq (a : ℕ) : Pcx461Moments.dy a = 1/(2:ℚ)^a := by
  simp [Pcx461Moments.dy,div_pow]

theorem price (heven : EvenUpper) {n : ℕ} (f : X n → F) (hq : Quad f) (j : ℕ) (p : ℚ) :
    Success f j p ↔ p ≤ (1+advantage f j)/2 := by
  classical
  have hm : Pcx461Balanced.phaseRank f = halfRank f := rfl
  by_cases hzero : j=0
  · subst j; exact zero_exact
  by_cases hb : Bal f
  · have hb' : Pcx461Balanced.Bal f := hb
    have hsuccess : Pcx461Generic.Succ f j p = Success f j p := rfl
    simpa only [advantage,if_pos hb,hm,hsuccess] using Pcx461Balanced.balanced_iff f hq hb' j p
  by_cases hsat : 2*halfRank f ≤ j
  · exact saturated_exact hq (by simpa only [if_neg hb,add_zero] using hsat)
  have hj : j < 2*halfRank f := lt_of_not_ge hsat
  simp only [advantage,if_neg hb,if_neg hsat,if_neg hzero]
  constructor
  · intro hP
    by_cases ho : j%2=1
    · simp only [if_pos ho]
      have hUB := Pcx461Balanced.uniform_upper (Pcx461Balanced.bounds f hq j).1 hP
      have hu : ¬Pcx461Balanced.Bal f := hb
      simpa only [Pcx461Balanced.U,if_neg hu,hm] using hUB
    · simp only [if_neg ho]
      obtain ⟨s,rfl⟩ : ∃ s, j=2*s := ⟨j/2,by omega⟩
      simpa using heven f hq hb s (by omega) (by omega) p hP
  · intro hP
    apply (Atlas461Transfer.clearSuccess n f hq hb j p).2
    rw [inner_dot]
    apply Pcx461Balanced.succ_mono hP
    simpa only [dy_eq] using (Pcx461Attain.attain (m:=halfRank f) (j:=j) (by omega) hj)

open Classical in
theorem posted (heven : EvenUpper) : ∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ f : X → F,
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
    let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
    ∀ j : ℕ,
      let s := j/2
      let base := (1 : ℚ)/2^m
      let best := (1 : ℚ)/2^(m-s)
      let freq := (1 : ℚ)/2^s
      let advantage : ℚ := if bal then
          (if j=0 then 0 else 1/(2:ℚ)^(m-(j-1)/2))
        else if 2*m ≤ j then 1
        else if j=0 then 0
        else if j % 2 = 1 then best
        else 3*best/(3+2*freq-2*best*base)
      ∀ p : ℚ,
        (∃ (r : ℕ) (w : Fin r → ℚ)
          (query : Fin r → X →ₗ[F] (Fin j → F))
          (out : Fin r → (Fin j → F) → F),
          (∀ seed, 0 ≤ w seed) ∧ (∑ seed, w seed)=1 ∧
            ∀ x : X, p ≤ ∑ seed : Fin r, if out seed (query seed x)=f x then w seed else 0) ↔
        p ≤ (1+advantage)/2 := by
  intro n F X f B h m bal j s base best freq advantage p
  exact price heven f h j p

end Pcx461Close

namespace Pcx461Close
open Pcx461Endpoints

theorem even_upper : EvenUpper := by
  intro n f hq hu s hs hsm p hP
  obtain ⟨B,hB,hrank,hbias⟩ := Donor441.Atlas461.evenData n f hq hu
  obtain ⟨r,w,L,out,hw,hn,hp⟩ := hP
  exact BatchParity461.evenUpper f B hB s (halfRank f) hs hsm hrank
    (by simpa only [BatchParity461.atlas461_sg] using hbias) p r w L out hw hn hp

end Pcx461Close

end PEqualNP.Outside.L_pcx_461_aux

theorem PEqualNP.Outside.L_pcx_461 : (∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ f : X → F,
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
    let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
    ∀ j : ℕ,
      let s := j/2
      let base := (1 : ℚ)/2^m
      let best := (1 : ℚ)/2^(m-s)
      let freq := (1 : ℚ)/2^s
      let advantage : ℚ := if bal then
          (if j=0 then 0 else 1/(2:ℚ)^(m-(j-1)/2))
        else if 2*m ≤ j then 1
        else if j=0 then 0
        else if j % 2 = 1 then best
        else 3*best/(3+2*freq-2*best*base)
      ∀ p : ℚ,
        (∃ (r : ℕ) (w : Fin r → ℚ)
          (query : Fin r → X →ₗ[F] (Fin j → F))
          (out : Fin r → (Fin j → F) → F),
          (∀ seed, 0 ≤ w seed) ∧ (∑ seed, w seed)=1 ∧
            ∀ x : X, p ≤ ∑ seed : Fin r, if out seed (query seed x)=f x then w seed else 0) ↔
        p ≤ (1+advantage)/2) := PEqualNP.Outside.L_pcx_461_aux.Pcx461Close.posted PEqualNP.Outside.L_pcx_461_aux.Pcx461Close.even_upper

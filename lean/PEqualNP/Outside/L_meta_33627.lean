import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33627

abbrev F := ZMod 2

noncomputable def ct {X : Type} [Fintype X] (p : X → Prop) : ℕ := by
  classical
  exact ∑ x, if p x then 1 else 0

theorem ct_congr {X : Type} [Fintype X] {p q : X → Prop} (h : ∀ x, p x ↔ q x) :
    ct p = ct q := by
  classical
  unfold ct
  simp only [h]

theorem ct_card {X : Type} [Fintype X] (p : X → Prop) : ct p = Nat.card {x // p x} := by
  classical
  simp only [ct, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole, Nat.cast_id]

theorem ct_prod {X Y : Type} [Fintype X] [Fintype Y] (p : X → Y → Prop) :
    ct (fun z : X × Y => p z.1 z.2) = ∑ x, ct (p x) := by
  classical
  simp only [ct, Fintype.sum_prod_type]

theorem ct_swap {X Y : Type} [Fintype X] [Fintype Y] (p : X → Y → Prop) :
    (∑ x, ct (p x)) = ∑ y, ct (fun x => p x y) := by
  classical
  unfold ct
  rw [Finset.sum_comm]

theorem ct_partition {X S : Type} [Fintype X] [Fintype S] (k : X → S) (p : S → X → Prop) :
    ct (fun x => p (k x) x) = ∑ s, ct (fun x => k x = s ∧ p s x) := by
  classical
  unfold ct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (k x)]
  · simp
  · intro s _ h
    simp [Ne.symm h]
  · simp

variable {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module F X] [Module F Y] [Module F Z]

lemma ct_fiber [Fintype X] (L : X →ₗ[F] Z) (x₀ : X) :
    ct (fun x => L x = L x₀) = ct (fun x => L x = 0) := by
  rw [ct_card, ct_card]
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨x.1 - x₀, by simp [map_sub, x.property]⟩
    invFun := fun y => ⟨y.1 + x₀, by simp [map_add, y.property]⟩
    left_inv := fun x => Subtype.ext (sub_add_cancel _ _)
    right_inv := fun y => Subtype.ext (add_sub_cancel_right _ _) }

lemma ct_fiber_le [Fintype X] (L : X →ₗ[F] Z) (z : Z) :
    ct (fun x => L x = z) ≤ ct (fun x => L x = 0) := by
  classical
  by_cases h : ∃ x, L x = z
  · obtain ⟨x, rfl⟩ := h
    exact (ct_fiber L x).le
  · push Not at h
    simp [ct, h]

noncomputable def pureBound [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (r : Y →ₗ[F] F) : ℕ :=
  2 * ∑ y, ct (fun x => r y = 0 ∧ B x y = 0)

noncomputable def score [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) : ℕ :=
  ct (fun z : X × Y =>
    let s := l z.1 + r z.2
    B z.1 z.2 = A s z.1 + D s z.2 + b s)

theorem branch_le [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) (s : F) : ct (fun z : X × Y => l z.1 + r z.2 = s ∧
      B z.1 z.2 = A s z.1 + D s z.2 + b s) ≤ ∑ y, ct (fun x => r y = 0 ∧ B x y = 0) := by
    classical
    rw [ct_prod (fun x y => l x + r y = s ∧ B x y = A s x + D s y + b s)]
    calc
      _ ≤ ∑ x, ct (fun y => r y = 0 ∧ B x y = D s y) := by
        apply Finset.sum_le_sum
        intro x _
        let L := r.prod (B x - D s)
        calc
          _ = ct (fun y => L y = (s - l x, A s x + b s)) := by
            apply ct_congr
            intro y
            change _ ↔ (r y, B x y - D s y) = _
            rw [Prod.mk.injEq]
            rw [eq_sub_iff_add_eq, sub_eq_iff_eq_add]
            simp only [add_comm, add_assoc]
          _ ≤ ct (fun y => L y = 0) := ct_fiber_le L _
          _ = _ := by
            apply ct_congr
            intro y
            simp [L, Prod.ext_iff, sub_eq_zero]
      _ = ∑ y, ct (fun x => r y = 0 ∧ B x y = D s y) := ct_swap _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y _
        by_cases h : r y = 0
        · simp only [h, true_and]
          exact ct_fiber_le (B.flip y) (D s y)
        · simp [h, ct]

theorem score_le [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) : score B l r A D b ≤ pureBound B r := by
  classical
  unfold score
  rw [ct_partition (fun z : X × Y => l z.1 + r z.2)
    (fun s z => B z.1 z.2 = A s z.1 + D s z.2 + b s)]
  calc
    _ ≤ ∑ _s : F, ∑ y, ct (fun x => r y = 0 ∧ B x y = 0) :=
      Finset.sum_le_sum fun s _ => branch_le B l r A D b s
    _ = _ := by simp [pureBound, ZMod.card]

theorem score_pure [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (r : Y →ₗ[F] F) (v : Y) (hv : r v = 1) :
    score B 0 r (fun s => B.flip (s • v)) 0 0 = pureBound B r := by
  classical
  simp only [score, LinearMap.zero_apply, zero_add, LinearMap.flip_apply, Pi.zero_apply, add_zero]
  rw [ct_partition (fun z : X × Y => r z.2) (fun s z => B z.1 z.2 = B z.1 (s • v))]
  have hs (s : F) : ct (fun z : X × Y => r z.2 = s ∧ B z.1 z.2 = B z.1 (s • v)) =
      ∑ y, ct (fun x => r y = 0 ∧ B x y = 0) := by
    rw [ct_prod (fun x y => r y = s ∧ B x y = B x (s • v)), ← ct_swap (fun x y => r y = 0 ∧ B x y = 0)]
    apply Finset.sum_congr rfl
    intro x _
    convert ct_fiber (r.prod (B x)) (s • v) using 1 <;>
      apply ct_congr <;> intro y <;> simp [Prod.ext_iff, hv]
  simp only [hs]
  simp [pureBound, ZMod.card]

theorem dual_count {T : Type} [Fintype T] [Fintype (Z →ₗ[F] F)] (e : T → Z) :
    2 * ∑ u : Z →ₗ[F] F, ct (fun t => u (e t) = 0) =
      Fintype.card (Z →ₗ[F] F) * (Fintype.card T + ct (fun t => e t = 0)) := by
  classical
  let N := Fintype.card (Z →ₗ[F] F)
  have hc (z : Z) : 2 * ct (fun u : Z →ₗ[F] F => u z = 0) = N + (if z = 0 then N else 0) := by
    by_cases h : z = 0
    · simp [ct, h, N, two_mul]
    · simp only [ite_eq_right_iff.mpr (fun hz => (h hz).elim), add_zero]
      obtain ⟨u, hu⟩ := Module.Projective.exists_dual_eq_one F h
      let L := Module.Dual.eval F Z z
      have hL : Function.Surjective L := fun s => ⟨s • u, by change s * u z = s; rw [hu, mul_one]⟩
      have hk := AddSubgroup.card_ker_mul_card_of_surjective (f := L.toAddMonoidHom) hL
      rw [Nat.card_eq_fintype_card (α := F), ZMod.card] at hk
      rw [ct_card, mul_comm]
      exact hk.trans Nat.card_eq_fintype_card
  rw [ct_swap (fun (u : Z →ₗ[F] F) (t : T) => u (e t) = 0), Finset.mul_sum]
  simp_rw [hc, Finset.sum_add_distrib]
  simp [N, ct, mul_add, Finset.sum_ite, mul_comm]

theorem ct_lt_of_projection {T : Type} [Fintype T] [Fintype (Z →ₗ[F] F)] (e f : T → Z)
    (h : ∀ u : Z →ₗ[F] F, ct (fun t => u (e t) = 0) ≤ ct (fun t => u (f t) = 0))
    (u : Z →ₗ[F] F) (hu : ct (fun t => u (e t) = 0) < ct (fun t => u (f t) = 0)) :
    ct (fun t => e t = 0) < ct (fun t => f t = 0) := by
  classical
  have hs := Finset.sum_lt_sum (s := Finset.univ) (fun u _ => h u) ⟨u, Finset.mem_univ _, hu⟩
  have h2 := Nat.mul_lt_mul_of_pos_left hs (by decide : 0 < 2)
  rw [dual_count, dual_count] at h2
  exact Nat.lt_of_add_lt_add_left (Nat.lt_of_mul_lt_mul_left h2)

def err (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) (z : X × Y) : Z :=
  let s := l z.1 + r z.2
  B z.1 z.2 - (A s z.1 + D s z.2 + b s)

lemma projection_score [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) (u : Z →ₗ[F] F) :
    ct (fun z => u (err B l r A D b z) = 0) =
      score (B.compr₂ u) l r (fun s => u.comp (A s)) (fun s => u.comp (D s)) (u ∘ b) := by
  apply ct_congr
  intro z
  simp [err, sub_eq_zero]

theorem strict_of_scalar [Fintype X] [Fintype Y] [Fintype (Z →ₗ[F] F)] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) (v : Y) (hv : r v = 1) (u : Z →ₗ[F] F)
    (hu : score (B.compr₂ u) l r (fun s => u.comp (A s)) (fun s => u.comp (D s)) (u ∘ b) <
      pureBound (B.compr₂ u) r) : score B l r A D b < pureBound B r := by
  classical
  let C := fun s : F => B.flip (s • v)
  have hc (k : Z →ₗ[F] F) : ct (fun z => k (err B 0 r C 0 0 z) = 0) = pureBound (B.compr₂ k) r := by
    rw [projection_score, ← score_pure _ r v hv]
    apply ct_congr
    intro z
    simp [C]
  have h := ct_lt_of_projection (err B l r A D b) (err B 0 r C 0 0)
    (fun k => by rw [hc, projection_score]; apply score_le) u (by rwa [hc, projection_score])
  simpa only [← score_pure B r v hv, score, C, err, sub_eq_zero] using h

theorem strict_edge [Fintype X] [Fintype Y] [Fintype (Z →ₗ[F] F)] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) (v : Y) (hv : r v = 1) (x₀ x₁ : X) (h₀ : l x₀ = 1) (h₁ : l x₁ = 0)
    (u : Z →ₗ[F] F) (a : X →ₗ[F] F) (ha : a x₁ = 1) (he : ∀ x y, u (B x y) = a x * r y) :
    score B l r A D b < pureBound B r := by
  classical
  apply strict_of_scalar B l r A D b v hv u
  rw [← score_pure _ r v hv]
  simp only [score, LinearMap.zero_apply, zero_add, LinearMap.flip_apply, Pi.zero_apply, add_zero,
    LinearMap.compr₂_apply, he, map_smul, LinearMap.smul_apply, hv, smul_eq_mul, one_mul, mul_comm, LinearMap.comp_apply,
    Function.comp_apply, eq_self]
  let p := fun z : X × Y =>
    let s := l z.1 + r z.2
    a z.1 * r z.2 = u (A s z.1) + u (D s z.2) + u (b s)
  change ct p < ct (fun _ : X × Y => True)
  have hn : ¬∀ z, p z := by
    intro h
    have hz := h (0, 0)
    have hx := h (x₁, 0)
    have hy := h (x₀, v)
    have hxy := h (x₀ + x₁, v)
    simp [p, map_add, h₀, h₁, hv, ha, ZModModule.add_self] at hz hx hy hxy
    simp [← hz] at hx hy hxy
    simp [← hx, ← hy] at hxy
  obtain ⟨z, hz⟩ := not_forall.mp hn
  unfold ct
  apply Finset.sum_lt_sum
  · intro z _
    by_cases h : p z <;> simp [h]
  · refine ⟨z, Finset.mem_univ _, ?_⟩
    simp [hz]

theorem no_query [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z) (b : F → Z) :
    score B 0 0 A D b ≤ ∑ y, ct (fun x => B x y = 0) := by
  simpa [score] using branch_le B 0 0 A D b 0

theorem score_swap [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z)
    (l : X →ₗ[F] F) (r : Y →ₗ[F] F) (A : F → X →ₗ[F] Z) (D : F → Y →ₗ[F] Z)
    (b : F → Z) : score B l r A D b = score B.flip r l D A b := by
  classical
  unfold score
  rw [ct_prod (fun x y => B x y = A (l x + r y) x + D (l x + r y) y + b (l x + r y)),
    ct_swap, ct_prod (fun y x => B.flip y x = D (r y + l x) y + A (r y + l x) x + b (r y + l x))]
  simp only [LinearMap.flip_apply, add_comm]

lemma double_ker [Fintype Y] (L : Y →ₗ[F] Z) (r : Y →ₗ[F] F) :
    2 * ct (fun y => r y = 0 ∧ L y = 0) = ct (fun y => L y = 0) +
      ct (fun y => L y = 0 ∧ LinearMap.ker L ≤ LinearMap.ker r) := by
  classical
  by_cases h : LinearMap.ker L ≤ LinearMap.ker r
  · have hh (y : Y) : r y = 0 ∧ L y = 0 ↔ L y = 0 := ⟨And.right, fun hy => ⟨h hy, hy⟩⟩
    simp only [h, and_true, ct_congr hh, two_mul]
  · have hr : r.comp (LinearMap.ker L).subtype ≠ 0 := by
      intro he
      apply h
      intro y hy
      exact DFunLike.congr_fun he (⟨y, hy⟩ : LinearMap.ker L)
    let M := r.comp (LinearMap.ker L).subtype
    have hk := AddSubgroup.card_ker_mul_card_of_surjective (f := M.toAddMonoidHom)
      (LinearMap.surjective hr)
    rw [Nat.card_eq_fintype_card (α := F), ZMod.card] at hk
    have he : Nat.card {y // r y = 0 ∧ L y = 0} = Nat.card M.toAddMonoidHom.ker := by
      apply Nat.card_congr
      exact {
        toFun := fun y => ⟨⟨y.1, y.property.2⟩, y.property.1⟩
        invFun := fun y => ⟨y.1.1, y.property, y.1.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc : ct (fun _ : Y => False) = 0 := by simp [ct]
    simp only [h, and_false, hc, add_zero, ct_card, he, mul_comm 2]
    exact hk

theorem pure_gain [Fintype X] [Fintype Y] (B : X →ₗ[F] Y →ₗ[F] Z) (r : Y →ₗ[F] F) :
    pureBound B r = ct (fun z : X × Y => B z.1 z.2 = 0) +
      ct (fun z : X × Y => B z.1 z.2 = 0 ∧ LinearMap.ker (B z.1) ≤ LinearMap.ker r) := by
  rw [pureBound, ← ct_swap (fun x y => r y = 0 ∧ B x y = 0), Finset.mul_sum]
  simp_rw [double_ker, Finset.sum_add_distrib]
  rw [ct_prod (fun x y => B x y = 0), ct_prod (fun x y => B x y = 0 ∧ LinearMap.ker (B x) ≤ LinearMap.ker r)]

abbrev Lane (m : ℕ) := ZMod m → F

def tri {m : ℕ} : Lane m →ₗ[F] Lane m :=
  let e := fun i : ZMod m => (LinearMap.proj i : Lane m →ₗ[F] F)
  LinearMap.pi fun i => e i + e (i + 1) + e (i - 1)

lemma tri_apply {m : ℕ} (x : Lane m) (i : ZMod m) :
    tri x i = x i + x (i + 1) + x (i - 1) := rfl

def mask {m : ℕ} [NeZero m] (a : Lane m) : Lane m →ₗ[F] F :=
  (dotProductEquiv F (ZMod m) a).comp tri

lemma mask_selfAdjoint {m : ℕ} [NeZero m] (a : Lane m) :
    mask a = dotProductEquiv F (ZMod m) (tri a) := by
  apply LinearMap.ext
  intro x
  change (∑ i, a i * (x i + x (i + 1) + x (i - 1))) =
    ∑ i, (a i + a (i + 1) + a (i - 1)) * x i
  have hp : (∑ i, a i * x (i + 1)) = ∑ j, a (j - 1) * x j := by
    apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod m))
    intro i
    simp
  have hm : (∑ i, a i * x (i - 1)) = ∑ j, a (j + 1) * x j := by
    apply Fintype.sum_equiv (Equiv.subRight (1 : ZMod m))
    intro i
    simp
  simp only [mul_add, add_mul, Finset.sum_add_distrib, hp, hm]
  abel

lemma mask_eq_iff {m : ℕ} [NeZero m] (a b : Lane m) :
    mask a = mask b ↔ tri (a - b) = 0 := by
  rw [mask_selfAdjoint, mask_selfAdjoint, (dotProductEquiv F (ZMod m)).injective.eq_iff,
    map_sub, sub_eq_zero]

lemma kernel_period {m : ℕ} (a : Lane m) (h : tri a = 0) (i : ZMod m) : a (i + 3) = a i := by
  have hx := congrFun h (i + 1)
  have hy := congrFun h (i + 2)
  simp only [tri_apply, Pi.zero_apply, add_sub_cancel_right] at hx hy
  rw [show i + 1 + 1 = i + 2 by ring] at hx
  rw [show i + 2 + 1 = i + 3 by ring, show i + 2 - 1 = i + 1 by ring] at hy
  linear_combination hy - hx

lemma kernel_nat {m : ℕ} (a : Lane m) (h : tri a = 0) (j : ℕ) :
    a (j : ZMod m) = a ((j % 3 : ℕ) : ZMod m) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < 3
    · rw [Nat.mod_eq_of_lt hj]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
      rw [Nat.cast_add, Nat.cast_ofNat, kernel_period a h, ih k (by omega)]
      simp

lemma kernel_factor {t : ℕ} [NeZero (3*t)] (a : Lane (3*t)) (h : tri a = 0) :
    ∃ f : ZMod 3 → F,
      (∀ i, a i = f (ZMod.castHom (dvd_mul_right 3 t) (ZMod 3) i)) ∧ f 0 + f 1 + f 2 = 0 := by
  let f := fun z : ZMod 3 => a (z.val : ZMod (3*t))
  refine ⟨f, ?_, ?_⟩
  · intro i
    conv_lhs => rw [← ZMod.natCast_zmod_val i, kernel_nat a h]
    conv_rhs => rw [← ZMod.natCast_zmod_val i, map_natCast]
    exact congrArg (fun n : ℕ => a (n : ZMod (3*t))) (ZMod.val_natCast 3 i.val).symm
  · have hh := congrFun h 1
    change a 1 + a (1+1) + a (1-1) = 0 at hh
    simp only [f, show (0 : ZMod 3).val = 0 by decide, show (1 : ZMod 3).val = 1 by decide,
      show (2 : ZMod 3).val = 2 by decide, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [one_add_one_eq_two, sub_self] at hh
    linear_combination hh

lemma ct_pull {U V : Type} [AddGroup U] [AddGroup V] [Fintype U] [Fintype V] (L : U →+ V)
    (hs : Function.Surjective L) (p : V → Prop) :
    ct (fun x => p (L x)) = Nat.card L.ker * ct p := by
  classical
  rw [ct_partition L (fun y _ => p y)]
  conv_rhs => rw [ct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p y
  · simp only [h, and_true, ite_true, mul_one, ct_card]
    exact Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hs y)
  · simp [h, ct]

def res {t : ℕ} : ZMod (3*t) →+* ZMod 3 := ZMod.castHom (dvd_mul_right 3 t) _

lemma residue_count {t : ℕ} [NeZero (3*t)] (p : ZMod 3 → Prop) :
    ct (fun i : ZMod (3*t) => p (res i)) = t * ct p := by
  have hs := ZMod.castHom_surjective (dvd_mul_right 3 t)
  change ct (fun x => p ((res (t := t)).toAddMonoidHom x)) = _
  rw [ct_pull (res (t := t)).toAddMonoidHom hs p]
  have h := AddSubgroup.card_ker_mul_card_of_surjective (f := (res (t := t)).toAddMonoidHom) hs
  simp only [Nat.card_eq_fintype_card (α := ZMod 3), Nat.card_eq_fintype_card (α := ZMod (3*t)),
    ZMod.card] at h
  congr 1
  omega

lemma kernel_weight {t : ℕ} [NeZero (3*t)] (a : Lane (3*t)) (ha : tri a = 0) (hn : a ≠ 0) :
    ct (fun i => a i ≠ 0) = 2*t := by
  obtain ⟨f, hf, hsum⟩ := kernel_factor a ha
  have hfn : f ≠ 0 := by
    intro he
    apply hn
    funext i
    rw [hf, he]
    rfl
  have small : ∀ g : ZMod 3 → F, g ≠ 0 → g 0 + g 1 + g 2 = 0 →
      (Finset.univ.filter (fun i => g i ≠ 0)).card = 2 := by decide
  have hw : ct (fun i => f i ≠ 0) = 2 := by
    classical
    rw [ct_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact small f hfn hsum
  calc
    _ = ct (fun i : ZMod (3*t) => f (res i) ≠ 0) := ct_congr fun i => by rw [hf]; rfl
    _ = _ := by rw [residue_count (fun i => f i ≠ 0), hw, mul_comm]

lemma mask_distance {t : ℕ} [NeZero (3*t)] (a b : Lane (3*t)) (h : mask a = mask b)
    (hne : a ≠ b) : ct (fun i => a i ≠ b i) = 2*t := by
  simpa only [Pi.sub_apply, ne_eq, sub_eq_zero] using
    kernel_weight (a-b) ((mask_eq_iff a b).mp h) (sub_ne_zero.mpr hne)

lemma ct_mono {T : Type} [Fintype T] {p q : T → Prop} (h : ∀ t, p t → q t) : ct p ≤ ct q := by
  classical
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : p t
  · simp [ht, h t ht]
  · simp [ht]

lemma mask_large {t : ℕ} [NeZero (3*t)] (a b : Lane (3*t)) (h : mask a = mask b)
    (hne : a ≠ b) (hmin : ct (fun i => a i ≠ 0) ≤ ct (fun i => b i ≠ 0)) :
    t ≤ ct (fun i => b i ≠ 0) := by
  have hd := mask_distance a b h hne
  have hu : ct (fun i => a i ≠ b i) ≤ ct (fun i => a i ≠ 0) + ct (fun i => b i ≠ 0) := by
    classical
    unfold ct
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp_all
  omega

lemma kernel_two {t : ℕ} [NeZero (3*t)] {a : Lane (3*t)} (ha : tri a = 0)
    {i j : ZMod (3*t)} (hij : res i ≠ res j) (hi : a i = 0) (hj : a j = 0) : a = 0 := by
  obtain ⟨f, hf, hs⟩ := kernel_factor a ha
  have small : ∀ g : ZMod 3 → F, ∀ k l, k ≠ l → g k = 0 → g l = 0 →
      g 0 + g 1 + g 2 = 0 → g = 0 := by decide
  have he := small f _ _ hij ((hf i).symm.trans hi) ((hf j).symm.trans hj) hs
  funext k
  rw [hf, he]
  rfl

lemma mask_count {t : ℕ} [NeZero (3*t)] (r : Lane (3*t) →ₗ[F] F) :
    ct (fun a => mask a = r) ≤ 4 := by
  rw [ct_card]
  let f := fun a : {a : Lane (3*t) // mask a = r} => (a.1 0, a.1 1)
  have h : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply kernel_two ((mask_eq_iff _ _).mp (a.property.trans b.property.symm)) (i := 0) (j := 1)
    · simp [res]
    · exact sub_eq_zero.mpr (congrArg Prod.fst he)
    · exact sub_eq_zero.mpr (congrArg Prod.snd he)
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card] using Nat.card_le_card_of_injective f h

noncomputable def clip {I : Type} (S : I → Prop) : (I → F) →ₗ[F] (I → F) := by
  classical
  exact LinearMap.pi fun i => if S i then LinearMap.proj i else 0

lemma clip_apply {I : Type} (S : I → Prop) [DecidablePred S] (w : I → F) (i : I) :
    clip S w i = if S i then w i else 0 := by
  classical
  by_cases h : S i <;> simp [clip, h]

lemma clip_adj {I : Type} [Fintype I] [DecidableEq I] (S : I → Prop) (a w : I → F) :
    dotProductEquiv F I a (clip S w) = dotProductEquiv F I (clip S a) w := by
  classical
  change (∑ i, a i * clip S w i) = ∑ i, clip S a i * w i
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : S i <;> simp [clip_apply, h]

lemma mask_clip {m : ℕ} [NeZero m] (S : ZMod m → Prop) (a : Lane m) :
    (dotProductEquiv F _ a).comp ((clip S).comp tri) = mask (clip S a) := by
  apply LinearMap.ext
  intro y
  exact clip_adj S a (tri y)

lemma forced_iff_mask {m : ℕ} [NeZero m] (S : ZMod m → Prop) (r : Lane m →ₗ[F] F) :
    LinearMap.ker ((clip S).comp tri) ≤ LinearMap.ker r ↔
      ∃ a : Lane m, mask a = r ∧ ∀ i, a i ≠ 0 → S i := by
  classical
  let L := (clip S).comp (tri (m := m))
  change LinearMap.ker L ≤ _ ↔ _
  have hh : LinearMap.ker L ≤ LinearMap.ker r ↔ r ∈ LinearMap.range L.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    rfl
  rw [hh]
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨a, rfl⟩ := (dotProductEquiv F (ZMod m)).surjective f
    refine ⟨clip S a, (mask_clip S a).symm, fun i h => ?_⟩
    by_contra hn
    simp [clip_apply, hn] at h
  · rintro ⟨a, rfl, ha⟩
    refine ⟨dotProductEquiv F (ZMod m) a, ?_⟩
    change (dotProductEquiv F _ a).comp ((clip S).comp tri) = _
    rw [mask_clip]
    congr 1
    funext i
    by_cases h : S i
    · simp [clip_apply, h]
    · simp [clip_apply, h, not_imp_comm.mp (ha i) h]

lemma repair_two {t : ℕ} [NeZero (3*t)] (i j : ZMod (3*t)) (hij : res i ≠ res j) (w : Lane (3*t)) :
    ∃ y : Lane (3*t), ∀ k, k ≠ i → k ≠ j → tri y k = w k := by
  classical
  let S := fun k => k ≠ i ∧ k ≠ j
  let L := (clip S).comp (tri (m := 3*t))
  have hm : clip S w ∈ LinearMap.range L := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) _).mp
    intro φ hφ
    obtain ⟨a, rfl⟩ := (dotProductEquiv F _).surjective φ
    have he : mask (clip S a) = 0 := by
      rw [← mask_clip]
      exact LinearMap.mem_ker.mp (show dotProductEquiv F _ a ∈ LinearMap.ker L.dualMap by
        rwa [LinearMap.ker_dualMap_eq_dualAnnihilator_range])
    have hz : tri (clip S a) = 0 := by
      rw [mask_selfAdjoint] at he
      exact (dotProductEquiv F _).map_eq_zero_iff.mp he
    have h0 := kernel_two hz hij (by simp [clip_apply, S]) (by simp [clip_apply, S])
    rw [clip_adj, h0, map_zero, LinearMap.zero_apply]
  obtain ⟨y, hy⟩ := hm
  refine ⟨y, fun k hi hj => ?_⟩
  simpa [L, clip_apply, S, hi, hj] using congrFun hy k

lemma ct_split {T : Type} [Fintype T] (p q : T → Prop) :
    ct (fun z => p z ∧ q z) + ct (fun z => p z ∧ ¬q z) = ct p := by
  classical
  unfold ct
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : p z <;> by_cases hq : q z <;> simp [hp,hq]

def blocked {m : ℕ} (x : Lane m) (i : ZMod m) : Prop := x i ≠ 0 ∨ x (i+1) ≠ 0

def indep {m : ℕ} (z : Lane m × Lane m) : Prop :=
  ∀ i, blocked z.1 i → z.2 i = 0

def event {m : ℕ} (s : Finset (ZMod m)) (z : Lane m × Lane m) : Prop :=
  indep z ∧ ∀ i ∈ s, blocked z.1 i

lemma delete_pair {m : ℕ} [NeZero m] (s : Finset (ZMod m)) (i : ZMod m)
    (hs : ∀ j ∈ s, j ≠ i ∧ j ≠ i+1 ∧ j ≠ i-1) :
    4 * ct (fun z => event s z ∧ blocked z.1 i) ≤ 3 * ct (event s) := by
  classical
  let bad := fun z : Lane m × Lane m => event s z ∧ blocked z.1 i
  let good := fun z : Lane m × Lane m => event s z ∧ ¬blocked z.1 i
  let T := {ab : F × F // ab.1 ≠ 0 ∨ ab.2 ≠ 0}
  let clear := fun x : Lane m => fun k : ZMod m => if k = i ∨ k = i+1 then (0 : F) else x k
  have hb (x : Lane m) (k) : blocked (clear x) k → blocked x k := by
    simp only [blocked, clear]
    split_ifs <;> tauto
  have hg (z : {z // bad z}) : good (clear z.1.1, z.1.2) := by
    refine ⟨⟨fun k hk => z.property.1.1 k (hb _ _ hk), fun j hj => ?_⟩, ?_⟩
    · obtain ⟨h₁,h₂,h₃⟩ := hs j hj
      have h₄ : j+1 ≠ i := fun h => h₃ (eq_sub_of_add_eq h)
      simpa [blocked, clear, h₁,h₂,h₄] using z.property.1.2 j hj
    · simp [blocked, clear]
  let enc := fun z : {z // bad z} =>
    ((⟨(z.1.1 i, z.1.1 (i+1)), z.property.2⟩ : T),
     (⟨(clear z.1.1, z.1.2), hg z⟩ : {z // good z}))
  have hinj : Function.Injective enc := by
    rintro ⟨⟨x,y⟩,hx⟩ ⟨⟨x',y'⟩,hy⟩ he
    apply Subtype.ext
    have hbits := congrArg (fun v : T × {z // good z} => v.1.val) he
    have hz := congrArg (fun v : T × {z // good z} => v.2.val) he
    change (x i, x (i+1)) = (x' i, x' (i+1)) at hbits
    change (clear x,y) = (clear x',y') at hz
    refine Prod.ext ?_ ?_
    swap
    · exact (Prod.mk.inj hz).2
    funext k
    by_cases h : k = i
    · subst k; exact (Prod.mk.inj hbits).1
    by_cases h' : k = i+1
    · subst k; exact (Prod.mk.inj hbits).2
    simpa [clear, h, h'] using congrFun (congrArg Prod.fst hz) k
  have hk := Nat.card_le_card_of_injective enc hinj
  rw [Nat.card_prod, ← ct_card bad, ← ct_card good] at hk
  have hc : Nat.card T = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc] at hk
  have hp := ct_split (event s) (fun z => blocked z.1 i)
  change ct bad + ct good = _ at hp
  change 4 * ct bad ≤ _
  omega

lemma large_event {m : ℕ} [NeZero m] (k : ℕ) (s : Finset (ZMod m)) (hs : 3*k ≤ s.card) :
    4^k * ct (event s) ≤ 3^k * ct (indep (m := m)) := by
  classical
  induction k generalizing s with
  | zero =>
    simpa only [pow_zero, one_mul] using ct_mono (p := event s) (q := indep) (fun _ h => h.1)
  | succ k ih =>
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
    let d : Finset (ZMod m) := {i, i+1, i-1}
    let u := s \ d
    have hcard := Finset.le_card_sdiff d s
    have hd : d.card ≤ 3 := Finset.card_le_three
    have hu : 3*k ≤ u.card := by dsimp [u]; omega
    have hsub : u ⊆ s := Finset.sdiff_subset
    have hu' : ∀ j ∈ u, j ≠ i ∧ j ≠ i+1 ∧ j ≠ i-1 := by
      intro j hj
      simpa [d, not_or] using (Finset.mem_sdiff.mp hj).2
    have h₁ := ct_mono (p := event s) (q := fun z => event u z ∧ blocked z.1 i)
      (fun z hz => ⟨⟨hz.1, fun j hj => hz.2 j (hsub hj)⟩, hz.2 i hi⟩)
    have h₂ := (Nat.mul_le_mul_left 4 h₁).trans (delete_pair u i hu')
    have h₃ := ih u hu
    calc
      4^(k+1) * ct (event s) = 4^k * (4 * ct (event s)) := by ring
      _ ≤ 4^k * (3 * ct (event u)) := Nat.mul_le_mul_left _ h₂
      _ = 3 * (4^k * ct (event u)) := by ring
      _ ≤ 3 * (3^k * ct (indep (m := m))) := Nat.mul_le_mul_left _ h₃
      _ = _ := by ring

lemma surgery_count {I : Type} [Fintype I] [DecidableEq I] (s d : Finset I)
    (p q : (I → F) × (I → F) → Prop)
    (h : ∀ z, p z → ∃ w, q w ∧ (∀ i ∉ s, z.1 i = w.1 i) ∧ (∀ i ∉ d, z.2 i = w.2 i)) :
    ct p ≤ 2^(s.card + d.card) * ct q := by
  classical
  let f (z : {z // p z}) := (h z.1 z.2).choose
  have hf (z : {z // p z}) := (h z.1 z.2).choose_spec
  let enc := fun z : {z // p z} =>
    (((fun i : s => z.1.1 i), (fun i : d => z.1.2 i)),
     (⟨f z, (hf z).1⟩ : {w // q w}))
  have hi : Function.Injective enc := by
    intro x y he
    have hs := congrArg (fun w : ((s → F) × (d → F)) × {w // q w} => w.1.1) he
    have hd := congrArg (fun w : ((s → F) × (d → F)) × {w // q w} => w.1.2) he
    have hw := congrArg (fun w : ((s → F) × (d → F)) × {w // q w} => w.2.1) he
    change f x = f y at hw
    apply Subtype.ext
    apply Prod.ext <;> funext i
    · by_cases h : i ∈ s
      · exact congrFun hs ⟨i,h⟩
      · exact ((hf x).2.1 i h).trans ((congrArg (fun z => z.1 i) hw).trans ((hf y).2.1 i h).symm)
    · by_cases h : i ∈ d
      · exact congrFun hd ⟨i,h⟩
      · exact ((hf x).2.2 i h).trans ((congrArg (fun z => z.2 i) hw).trans ((hf y).2.2 i h).symm)
  have hc := Nat.card_le_card_of_injective enc hi
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := F), ZMod.card,
    Nat.card_eq_fintype_card (α := s), Nat.card_eq_fintype_card (α := d),
    Fintype.card_coe, pow_add, ct_card] using hc

def coded {m : ℕ} (z : Lane m × Lane m) : Prop :=
  z.1 ∈ LinearMap.range tri ∧ z.2 ∈ LinearMap.range tri

def witness {m : ℕ} (a b : ZMod m) (z : Lane m × Lane m) : Prop :=
  indep z ∧ coded z ∧ blocked z.1 a ∧ ¬blocked z.1 b

lemma fresh {m : ℕ} [NeZero m] (s : Finset (ZMod m)) (h : s.card < m) : ∃ k, k ∉ s := by
  classical
  by_contra! hn
  have hs : s = Finset.univ := Finset.eq_univ_of_forall hn
  simp [hs, ZMod.card] at h

lemma residue_next {t : ℕ} (i : ZMod (3*t)) : res i ≠ res (i+1) := by simp

lemma witness_lower {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t)
    (a b : ZMod (3*t)) (hab : a ≠ b) :
    ct (indep (m := 3*t)) ≤ 2^16 * ct (witness a b) := by
  classical
  have hp : ∃ p, (p=a ∨ p=a+1) ∧ p ≠ b ∧ p ≠ b+1 := by
    by_cases h : a = b+1
    · refine ⟨a+1, Or.inr rfl, ?_, by simpa using hab⟩
      intro he
      have h₂ : (2 : ZMod (3*t)) = 0 := by linear_combination he - h
      apply (by decide : (1:ZMod 3)+1 ≠ 0)
      simpa only [← one_add_one_eq_two, map_add, map_one, map_zero] using congrArg res h₂
    · exact ⟨a, Or.inl rfl, hab, h⟩
  obtain ⟨p,hpa,hpb,hpb'⟩ := hp
  let base : Finset (ZMod (3*t)) := {p,b,b+1}
  have hbase : base.card ≤ 3 := Finset.card_le_three
  obtain ⟨u, hu⟩ := fresh (base ∪ base.image (·-1)) (by
    have := Finset.card_union_le base (base.image (·-1))
    have := Finset.card_image_le (s := base) (f := (·-1))
    omega)
  have hu' : u ∉ base ∧ u+1 ∉ base := by
    refine ⟨fun h => hu (Finset.mem_union_left _ h), fun h => hu (Finset.mem_union_right _ ?_)⟩
    exact Finset.mem_image.mpr ⟨u+1,h,by simp⟩
  let up : Finset (ZMod (3*t)) := {p,u,u+1}
  have hup : up.card ≤ 3 := Finset.card_le_three
  obtain ⟨v, hv⟩ := fresh ((up ∪ up.image (·-1)) ∪ up.image (·-2)) (by
    have := Finset.card_union_le (up ∪ up.image (·-1)) (up.image (·-2))
    have := Finset.card_union_le up (up.image (·-1))
    have := Finset.card_image_le (s := up) (f := (·-1))
    have := Finset.card_image_le (s := up) (f := (·-2))
    omega)
  have hv' : v ∉ up ∧ v+1 ∉ up ∧ v+2 ∉ up := by
    simp only [Finset.mem_union, not_or] at hv
    exact ⟨hv.1.1, fun h => hv.1.2 (Finset.mem_image.mpr ⟨v+1,h,by simp⟩),
      fun h => hv.2 (Finset.mem_image.mpr ⟨v+2,h,by simp⟩)⟩
  let vx : Finset (ZMod (3*t)) := {v,v+1,v+2}
  let xx : Finset (ZMod (3*t)) := base ∪ ({u,u+1} ∪ vx)
  let yy : Finset (ZMod (3*t)) := (up ∪ up.image (·-1)) ∪ {v,v+1}
  have hsize : xx.card + yy.card ≤ 16 := by
    have := Finset.card_union_le base (({u,u+1} : Finset _) ∪ vx)
    have := Finset.card_union_le ({u,u+1} : Finset _) vx
    have := Finset.card_union_le (up ∪ up.image (·-1)) ({v,v+1} : Finset _)
    have := Finset.card_union_le up (up.image (·-1))
    have := Finset.card_image_le (s := up) (f := (·-1))
    have h₁ : vx.card ≤ 3 := Finset.card_le_three
    have h₂ : ({u,u+1} : Finset _).card ≤ 2 := Finset.card_le_two
    have h₃ : ({v,v+1} : Finset _).card ≤ 2 := Finset.card_le_two
    dsimp only [xx,yy]
    omega
  apply le_trans (surgery_count xx yy indep (witness a b) ?_)
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hsize))
  rintro ⟨x,y⟩ hold
  let wx := fun k => if k = p then (1 : F) else if k = b ∨ k = b+1 ∨ k ∈ vx then 0 else x k
  let wy := fun k => if k ∈ up ∨ k+1 ∈ up then (0 : F) else y k
  obtain ⟨x', hx⟩ := repair_two u (u+1) (residue_next _) wx
  obtain ⟨y', hy⟩ := repair_two v (v+1) (residue_next _) wy
  have hup₀ : ∀ k ∈ base, k ≠ u ∧ k ≠ u+1 := by
    intro k hk
    exact ⟨fun h => hu'.1 (h ▸ hk), fun h => hu'.2 (h ▸ hk)⟩
  have hvx : ∀ k ∈ vx, k ∉ up := by
    intro k hk
    simp only [vx, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl
    · exact hv'.1
    · exact hv'.2.1
    · exact hv'.2.2
  have hz (k) (hk : k ∉ up) : tri x' k = wx k := by
    apply hx <;> intro he <;> simp [he,up] at hk
  have hvz (k) (hk : k ∈ vx) : tri x' k = 0 := by
    have h := hvx k hk
    have hp : k ≠ p := fun he => h (by simp [he,up])
    simp [hz k h, wx, hp, hk]
  have hyz (k) (hk : k ∈ up ∨ k+1 ∈ up) : tri y' k = 0 := by
    have hn : k ≠ v ∧ k ≠ v+1 := by
      constructor
      · rintro rfl
        exact hk.elim hv'.1 hv'.2.1
      · rintro rfl
        exact hk.elim hv'.2.1 (fun h => hv'.2.2 (by simpa [← add_assoc, ← one_add_one_eq_two] using h))
    simp [hy k hn.1 hn.2, wy,hk]
  have hidep : indep (tri x',tri y') := by
    intro k hb
    by_cases hk : k ∈ up ∨ k+1 ∈ up
    · exact hyz k hk
    have hnot : k ≠ v ∧ k ≠ v+1 := by
      constructor <;> rintro rfl <;> rcases hb with hh|hh <;> apply hh <;> apply hvz <;>
        simp [vx, ← add_assoc, ← one_add_one_eq_two]
    have hk₁ : k ∉ up := fun h => hk (Or.inl h)
    have hk₂ : k+1 ∉ up := fun h => hk (Or.inr h)
    have keep (j) (hj : j ∉ up) : tri x' j ≠ 0 → x j ≠ 0 := by
      have hjp : j ≠ p := fun he => hj (by simp [he,up])
      rw [hz j hj]
      simp only [wx, hjp, ite_false]
      split_ifs <;> simp
    have hbo : blocked x k := hb.imp (keep _ hk₁) (keep _ hk₂)
    change tri y' k = 0
    rw [hy k hnot.1 hnot.2]
    simpa [wy, hk] using (show y k = 0 from hold k hbo)
  have hp₁ := hup₀ p (by simp [base])
  have hp' : tri x' p = 1 := by simp [hx p hp₁.1 hp₁.2,wx]
  have hb₀ := hup₀ b (by simp [base])
  have hb₁ := hup₀ (b+1) (by simp [base])
  refine ⟨(tri x',tri y'), ⟨hidep, ⟨⟨x',rfl⟩, ⟨y',rfl⟩⟩, ?_, ?_⟩, ?_, ?_⟩
  · rcases hpa with rfl|rfl
    · exact Or.inl (hp'.trans_ne one_ne_zero)
    · exact Or.inr (hp'.trans_ne one_ne_zero)
  · simp [blocked,hx b hb₀.1 hb₀.2,hx (b+1) hb₁.1 hb₁.2,wx,hpb.symm,hpb'.symm]
  · intro k hk
    change x k = tri x' k
    simp only [xx,base,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    simp [hx k hk.2.1.1 hk.2.1.2,wx,hk.1.1,hk.1.2.1,hk.1.2.2,hk.2.2]
  · intro k hk
    change y k = tri y' k
    simp only [yy,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    have hk₁ : k+1 ∉ up := fun h => hk.1.2 (Finset.mem_image.mpr ⟨k+1,h,by simp⟩)
    simp [hy k hk.2.1 hk.2.2,wy,hk.1.1,hk₁]

def site {m : ℕ} (i : ZMod m) : Lane m →ₗ[F] F := (LinearMap.proj i).comp tri

lemma mask_single {m : ℕ} [NeZero m] (i : ZMod m) : mask (Pi.single i 1) = site i := by
  apply LinearMap.ext
  intro y
  exact single_one_dotProduct i (tri y)

def forces {m : ℕ} [NeZero m] (r : Lane m →ₗ[F] F) (x : Lane m) : Prop :=
  ∃ c : Lane m, mask c = r ∧ ∀ i, c i ≠ 0 → blocked x i

def prize {m : ℕ} [NeZero m] (r : Lane m →ₗ[F] F) (z : Lane m × Lane m) : Prop :=
  indep z ∧ coded z ∧ forces r z.1

lemma forces_site {m : ℕ} [NeZero m] (i : ZMod m) (x : Lane m) (h : blocked x i) :
    forces (site i) x := by
  refine ⟨Pi.single i 1, mask_single i, fun k hk => ?_⟩
  by_cases he : k = i
  · exact he ▸ h
  · simp [Pi.single_eq_of_ne he] at hk

lemma witness_prize {m : ℕ} [NeZero m] (a b : ZMod m) (z : Lane m × Lane m) (h : witness a b z) :
    prize (site a) z := ⟨h.1,h.2.1,forces_site a _ h.2.2.1⟩

lemma ct_pos {T : Type} [Fintype T] {p : T → Prop} (z : T) (h : p z) : 0 < ct p := by
  classical
  rw [ct_card, Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨z,h⟩⟩

lemma indep_pos {m : ℕ} [NeZero m] : 0 < ct (indep (m := m)) :=
  ct_pos (0,0) (fun _ _ => rfl)

lemma witness_pos {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t) {a b : ZMod (3*t)} (hab : a ≠ b) :
    0 < ct (witness a b) := by
  have := witness_lower ht a b hab
  have := indep_pos (m := 3*t)
  omega

lemma site_prize_pos {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t) (a : ZMod (3*t)) :
    0 < ct (prize (site a)) := by
  have h : a ≠ a+1 := fun he => residue_next a (congrArg res he)
  exact (witness_pos ht h).trans_le (ct_mono (witness_prize a (a+1)))

lemma non_simple {m : ℕ} [NeZero m] (c : Lane m) (h : mask c ≠ 0)
    (hs : ∀ i, mask c ≠ site i) : ∃ i j, c i ≠ 0 ∧ c j ≠ 0 ∧ i ≠ j := by
  classical
  by_cases hc : c = 0
  · simp [hc,mask] at h
  have hex : ∃ i, c i ≠ 0 := by
    by_contra! he
    exact hc (funext he)
  obtain ⟨i,hi⟩ := hex
  by_contra! hn
  apply hs i
  rw [← mask_single i]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp
    exact (by decide : ∀ f : F, f ≠ 0 → f = 1) _ hi
  · have h₀ : c j = 0 := by_contra fun he => hj (hn j i he hi)
    simp [Pi.single_eq_of_ne hj,h₀]

lemma ct_exists_le {T U : Type} [Fintype T] [Fintype U] (p : U → T → Prop) :
    ct (fun t => ∃ u, p u t) ≤ ∑ u, ct (p u) := by
  classical
  unfold ct
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  by_cases h : ∃ u, p u t
  · obtain ⟨u,hu⟩ := h
    simp only [show ∃ u, p u t from ⟨u,hu⟩, ite_true]
    exact le_trans (by simp [hu] : 1 ≤ if p u t then 1 else 0)
      (Finset.single_le_sum (f := fun j => if p j t then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
  · simp [h]

lemma ct_disj {T : Type} [Fintype T] (p q : T → Prop) :
    ct (fun z => p z ∨ q z) ≤ ct p + ct q := by
  classical
  unfold ct
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  by_cases hp : p z <;> by_cases hq : q z <;> simp [hp,hq]

theorem prize_gap {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t)
    (r : Lane (3*t) →ₗ[F] F) (hr : r ≠ 0) (hn : ∀ i, r ≠ site i) :
    ∃ i : ZMod (3*t), ct (prize r) < ct (prize (site i)) := by
  classical
  by_cases hex : ∃ c, mask c = r
  · let R := {c : Lane (3*t) // mask c = r}
    have : Nonempty R := ⟨⟨hex.choose,hex.choose_spec⟩⟩
    obtain ⟨c,hmin⟩ := Finite.exists_min (fun a : R => ct (fun i => a.1 i ≠ 0))
    obtain ⟨a,b,ha,hb,hab⟩ := non_simple c.1 (by rwa [c.property]) (by rwa [c.property])
    refine ⟨a, ?_⟩
    let U := {d : R // d ≠ c}
    let supp := fun d : U => Finset.univ.filter (fun i => d.1.1 i ≠ 0)
    have hw (d : U) : 240 ≤ (supp d).card := by
      have h := mask_large c.1 d.1.1 (c.2.trans d.1.2.symm) (fun he => d.2 (Subtype.ext he.symm)) (hmin d.1)
      rw [ct_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      exact ht.trans h
    have hcard : Fintype.card U ≤ 4 := by
      have h₁ := Fintype.card_le_of_injective (Subtype.val : U → R) Subtype.val_injective
      have h₂ := mask_count r
      rw [ct_card, Nat.card_eq_fintype_card] at h₂
      exact h₁.trans h₂
    let extra := fun z => ∃ d : U, event (supp d) z
    have hupper : 4^80 * ct extra ≤ 4 * (3^80 * ct (indep (m := 3*t))) := by
      calc
        _ ≤ 4^80 * ∑ d : U, ct (event (supp d)) := Nat.mul_le_mul_left _ (ct_exists_le _)
        _ = _ := Finset.mul_sum ..
        _ ≤ ∑ _ : U, (3^80 * ct (indep (m := 3*t))) :=
          Finset.sum_le_sum fun d _ => large_event 80 (supp d) (hw d)
        _ ≤ _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact Nat.mul_le_mul_right _ hcard
    have hcover : ct (prize r) ≤ ct (fun z => prize (site a) z ∧ ¬witness a b z) + ct extra := by
      apply le_trans (ct_mono (q := fun z => (prize (site a) z ∧ ¬witness a b z) ∨ extra z) ?_) (ct_disj _ _)
      intro z hz
      obtain ⟨hc,hd,d,hd',hblock⟩ := hz
      by_cases he : (⟨d,hd'⟩ : R) = c
      · have hh : d = c.1 := congrArg Subtype.val he
        subst d
        exact Or.inl ⟨⟨hc,hd,forces_site a _ (hblock a ha)⟩, fun h => h.2.2.2 (hblock b hb)⟩
      · exact Or.inr ⟨⟨⟨d,hd'⟩,he⟩, hc, fun i hi => hblock i (Finset.mem_filter.mp hi).2⟩
    have hpart := ct_split (prize (site a)) (witness a b)
    rw [ct_congr (fun z => and_iff_right_of_imp (witness_prize a b z))] at hpart
    have hlow := witness_lower ht a b hab
    have hpos := witness_pos ht hab
    norm_num1 at hupper hlow
    omega
  · refine ⟨0, ?_⟩
    have he : ct (prize r) = 0 := by
      have hh (z) : ¬prize r z := fun h => hex ⟨h.2.2.choose,h.2.2.choose_spec.1⟩
      simp [ct, hh]
    rw [he]
    exact site_prize_pos ht 0

abbrev Pair (m : ℕ) := Lane m × Lane m

def edge {m : ℕ} : Lane m →ₗ[F] Lane m →ₗ[F] Pair m := by
  apply LinearMap.mk₂ F (fun x y : Lane m =>
    ((fun i => tri x i * tri y i), (fun i => tri x (i+1) * tri y i)) : Lane m → Lane m → Pair m)
  all_goals intros; apply Prod.ext <;> funext i <;>
    simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,mul_add,mul_left_comm,mul_assoc]

lemma edge_zero {m : ℕ} (x y : Lane m) : edge x y = 0 ↔ indep (tri x,tri y) := by
  change ((fun i => tri x i * tri y i), (fun i => tri x (i+1) * tri y i)) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h,j⟩ k (hk|hk)
    · exact (mul_eq_zero.mp (congrFun h k)).resolve_left hk
    · exact (mul_eq_zero.mp (congrFun j k)).resolve_left hk
  · intro h
    constructor <;> funext i <;> apply mul_eq_zero.mpr <;> by_cases hi : tri y i = 0
    all_goals first | exact Or.inr hi | exact Or.inl (by_contra fun hh => hi (h i (Or.inl hh))) | exact Or.inl (by_contra fun hh => hi (h i (Or.inr hh)))

lemma edge_ker {m : ℕ} (x : Lane m) :
    LinearMap.ker (edge x) = LinearMap.ker ((clip (blocked (tri x))).comp tri) := by
  classical
  ext y
  simp only [LinearMap.mem_ker, edge_zero, LinearMap.comp_apply, funext_iff,clip_apply,Pi.zero_apply]
  constructor
  · intro h i; by_cases hi : blocked (tri x) i <;> simp [hi]; exact h i hi
  · intro h i hi; simpa [hi] using h i

def both {m : ℕ} : Pair m →ₗ[F] Pair m := tri.prodMap tri

lemma both_range {m : ℕ} (z : Pair m) : z ∈ LinearMap.range both ↔ coded z := by
  constructor
  · rintro ⟨⟨x,y⟩,rfl⟩; exact ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩; exact ⟨(x,y),Prod.ext hx hy⟩

noncomputable def mult (m : ℕ) := Nat.card (both (m := m)).rangeRestrict.toAddMonoidHom.ker

lemma mult_pos {m : ℕ} [NeZero m] : 0 < mult m := Nat.card_pos

lemma count_both {m : ℕ} [NeZero m] (p : Pair m → Prop) :
    ct (fun z => p (both z)) = mult m * ct (fun z => p z ∧ coded z) := by
  classical
  refine (ct_pull (both (m := m)).rangeRestrict.toAddMonoidHom
    (LinearMap.surjective_rangeRestrict _) (fun z => p z.val)).trans ?_
  congr 1
  rw [ct_card,ct_card]
  apply Nat.card_congr
  exact (Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquivRight fun z => by rw [both_range,and_comm])

lemma edge_bound {m : ℕ} [NeZero m] (r : Lane m →ₗ[F] F) :
    pureBound edge r = ct (fun z : Pair m => edge z.1 z.2 = 0) + mult m * ct (prize r) := by
  rw [pure_gain]
  congr 1
  calc
    _ = ct (fun z : Pair m => indep (both z) ∧ forces r (both z).1) :=
      ct_congr fun z => by rw [edge_zero,edge_ker,forced_iff_mask]; rfl
    _ = _ := by
      rw [count_both (fun z => indep z ∧ forces r z.1)]
      congr 1
      exact ct_congr fun _ => by unfold prize; tauto

lemma bound_gap {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t)
    (r : Lane (3*t) →ₗ[F] F) (hr : r ≠ 0) (hn : ∀ i, r ≠ site i) :
    ∃ i : ZMod (3*t), pureBound edge r < pureBound edge (site i) := by
  obtain ⟨i,hi⟩ := prize_gap ht r hr hn
  refine ⟨i, ?_⟩
  rw [edge_bound,edge_bound]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hi mult_pos) _

def sh {m : ℕ} (d : ZMod m) : Lane m ≃ₗ[F] Lane m where
  toFun x i := x (i+d)
  invFun x i := x (i-d)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma tri_sh {m : ℕ} (d : ZMod m) (x : Lane m) (i : ZMod m) : tri (sh d x) i = tri x (i+d) := by
  change x (i+d) + x (i+1+d) + x (i-1+d) = x (i+d) + x (i+d+1) + x (i+d-1)
  rw [add_right_comm i 1 d,show i-1+d = i+d-1 by abel]

lemma ct_equiv {T U : Type} [Fintype T] [Fintype U] (e : T ≃ U) (p : U → Prop) :
    ct (fun z => p (e z)) = ct p := by
  rw [ct_card,ct_card]
  exact Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)

lemma edge_flip_zero {m : ℕ} (x y : Lane m) : edge y x = 0 ↔ edge (sh (-1) x) y = 0 := by
  rw [edge_zero,edge_zero]
  change (∀ i, (tri y i ≠ 0 ∨ tri y (i+1) ≠ 0) → tri x i = 0) ↔
    ∀ i, (tri (sh (-1) x) i ≠ 0 ∨ tri (sh (-1) x) (i+1) ≠ 0) → tri y i = 0
  simp only [tri_sh,← sub_eq_add_neg,add_sub_cancel_right]
  constructor
  · intro h i hk; by_contra hh
    rcases hk with h₁|h₁
    · apply h₁ (h _ (Or.inr (by simpa using hh)))
    · exact h₁ (h i (Or.inl hh))
  · intro h i hk; by_contra hh
    rcases hk with h₁|h₁
    · exact h₁ (h i (Or.inr hh))
    · exact h₁ (h _ (Or.inl (by simpa using hh)))

lemma flip_bound {m : ℕ} [NeZero m] (r : Lane m →ₗ[F] F) : pureBound edge.flip r = pureBound edge r := by
  unfold pureBound
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ct (fun x => r y = 0 ∧ edge (sh (-1) x) y = 0) :=
      ct_congr fun x => and_congr_right fun _ => edge_flip_zero x y
    _ = _ := ct_equiv (sh (-1)).toEquiv (fun x => r y = 0 ∧ edge x y = 0)

lemma edge_shift {m : ℕ} (d : ZMod m) (x y : Lane m) :
    edge (sh d x) (sh d y) = 0 ↔ edge x y = 0 := by
  rw [edge_zero,edge_zero]
  change (∀ i, (tri (sh d x) i ≠ 0 ∨ tri (sh d x) (i+1) ≠ 0) → tri (sh d y) i = 0) ↔ ∀ i, (tri x i ≠ 0 ∨ tri x (i+1) ≠ 0) → tri y i = 0
  simp only [tri_sh, add_right_comm _ 1 d]
  constructor
  · intro h i; simpa only [sub_add_cancel] using h (i-d)
  · intro h i; exact h (i+d)

lemma bound_site_eq {m : ℕ} [NeZero m] (i j : ZMod m) : pureBound edge (site i) = pureBound edge (site j) := by
  unfold pureBound
  congr 1
  rw [← ct_prod (fun y x => site i y = 0 ∧ edge x y = 0), ← ct_prod (fun y x => site j y = 0 ∧ edge x y = 0)]
  let d := i-j
  let e := (sh d).toEquiv.prodCongr (sh d).toEquiv
  rw [← ct_equiv e (fun z : Pair m => site j z.1 = 0 ∧ edge z.2 z.1 = 0)]
  apply ct_congr
  intro z
  change (_ ∧ _) ↔ tri (sh d z.1) j = 0 ∧ edge (sh d z.2) (sh d z.1) = 0
  rw [tri_sh,edge_shift,show j+d = i by dsimp [d]; abel]
  rfl

lemma site_one {m : ℕ} (i : ZMod m) : site i (fun _ => 1) = 1 := by
  change (1:F)+1+1=1
  decide

lemma set_two {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t) (i j : ZMod (3*t)) (hij : i ≠ j) :
    ∃ x, site i x = 0 ∧ site j x = 1 := by
  classical
  let s : Finset (ZMod (3*t)) := {i,j,i-1,j-1}
  have hs : s.card ≤ 4 := by
    dsimp [s]
    have h₁ := Finset.card_insert_le i {j,i-1,j-1}
    have h₂ := Finset.card_insert_le j {i-1,j-1}
    have h₃ := Finset.card_insert_le (i-1) {j-1}
    simp only [Finset.card_singleton] at *
    omega
  obtain ⟨u,hu⟩ := fresh s (by omega)
  have hi : i ≠ u ∧ i ≠ u+1 := by
    constructor
    · rintro rfl; exact hu (by simp [s])
    · intro he; apply hu; have : u = i-1 := by rw [he]; simp
      simp [s,this]
  have hj : j ≠ u ∧ j ≠ u+1 := by
    constructor
    · rintro rfl; exact hu (by simp [s])
    · intro he; apply hu; have : u = j-1 := by rw [he]; simp
      simp [s,this]
  obtain ⟨x,hx⟩ := repair_two u (u+1) (residue_next _) (fun k => if k = j then 1 else 0)
  refine ⟨x, ?_, ?_⟩
  · change tri x i = 0; simpa [hij] using hx i hi.1 hi.2
  · change tri x j = 1; simpa using hx j hj.1 hj.2

lemma sites_strict {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t) (i j : ZMod (3*t))
    (A D : F → Lane (3*t) →ₗ[F] Pair (3*t)) (b : F → Pair (3*t)) :
    score edge (site i) (site j) A D b < pureBound edge (site j) := by
  classical
  let : Fintype (Pair (3*t) →ₗ[F] F) := Fintype.ofInjective
    (fun (f : Pair (3*t) →ₗ[F] F) => (f : Pair (3*t) → F)) DFunLike.coe_injective
  by_cases hij : i = j
  · subst j
    have hi : i ≠ i+1 := fun h => residue_next i (congrArg res h)
    obtain ⟨x,hx,hx'⟩ := set_two ht i (i+1) hi
    exact strict_edge edge (site i) (site i) A D b _ (site_one i) _ x (site_one i) hx
      ((LinearMap.proj i).comp (LinearMap.snd F _ _)) (site (i+1)) hx' (fun _ _ => rfl)
  · obtain ⟨x,hx,hx'⟩ := set_two ht i j hij
    exact strict_edge edge (site i) (site j) A D b _ (site_one j) _ x (site_one i) hx
      ((LinearMap.proj j).comp (LinearMap.fst F _ _)) (site j) hx' (fun _ _ => rfl)

def isCoord {m : ℕ} (l r : Lane m →ₗ[F] F) : Prop :=
  (∃ i, l = 0 ∧ r = site i) ∨ (∃ i, l = site i ∧ r = 0)

lemma zero_strict {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t)
    (A D : F → Lane (3*t) →ₗ[F] Pair (3*t)) (b : F → Pair (3*t)) :
    score edge 0 0 A D b < pureBound edge (site (0 : ZMod (3*t))) := by
  have h := no_query edge A D b
  rw [← ct_swap (fun x y : Lane (3*t) => edge x y = 0),← ct_prod] at h
  rw [edge_bound]
  exact h.trans_lt (Nat.lt_add_of_pos_right (Nat.mul_pos mult_pos (site_prize_pos ht 0)))

lemma scores {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t) (l r : Lane (3*t) →ₗ[F] F)
    (A D : F → Lane (3*t) →ₗ[F] Pair (3*t)) (b : F → Pair (3*t)) :
    score edge l r A D b ≤ pureBound edge (site (0 : ZMod (3*t))) ∧
      (pureBound edge (site (0 : ZMod (3*t))) ≤ score edge l r A D b → isCoord l r) := by
  let val := score edge l r A D b
  let goal := pureBound edge (site (0 : ZMod (3*t)))
  change val ≤ goal ∧ (goal ≤ val → _)
  have hrB : val ≤ pureBound edge r := score_le ..
  have hlB : val ≤ pureBound edge l := (score_swap edge l r A D b).le.trans
    ((score_le edge.flip r l D A b).trans_eq (flip_bound l))
  have exc (h : val < goal) : val ≤ goal ∧ (goal ≤ val → isCoord l r) :=
    ⟨h.le, fun hh => (h.not_ge hh).elim⟩
  by_cases hr : r = 0
  · by_cases hl : l = 0
    · apply exc; simpa only [val,goal,hl,hr] using (zero_strict ht A D b)
    · by_cases h : ∃ i, l = site i
      · obtain ⟨i,hi⟩ := h
        exact ⟨hlB.trans_eq (hi ▸ bound_site_eq i 0), fun _ => Or.inr ⟨i,hi,hr⟩⟩
      · obtain ⟨i,hi⟩ := bound_gap ht l hl (not_exists.mp h)
        exact exc ((hlB.trans_lt hi).trans_eq (bound_site_eq i 0))
  · by_cases h : ∃ j, r = site j
    · obtain ⟨j,hj⟩ := h
      by_cases hl : l = 0
      · exact ⟨hrB.trans_eq (hj ▸ bound_site_eq j 0), fun _ => Or.inl ⟨j,hl,hj⟩⟩
      · by_cases h : ∃ i, l = site i
        · obtain ⟨i,hi⟩ := h
          apply exc
          exact (show val < pureBound edge (site j) by simpa only [val,hi,hj] using (sites_strict ht i j A D b)).trans_eq (bound_site_eq j 0)
        · obtain ⟨i,hi⟩ := bound_gap ht l hl (not_exists.mp h)
          exact exc ((hlB.trans_lt hi).trans_eq (bound_site_eq i 0))
    · obtain ⟨j,hj⟩ := bound_gap ht r hr (not_exists.mp h)
      exact exc ((hrB.trans_lt hj).trans_eq (bound_site_eq j 0))

lemma coord_attains {m : ℕ} [NeZero m] {l r : Lane m →ₗ[F] F} (h : isCoord l r) :
    ∃ A D b, score edge l r A D b = pureBound edge (site (0 : ZMod m)) := by
  rcases h with ⟨i,rfl,rfl⟩|⟨i,rfl,rfl⟩
  · exact ⟨_,_,_,(score_pure edge _ _ (site_one i)).trans (bound_site_eq i 0)⟩
  · refine ⟨0,(fun s => edge.flip.flip (s • (fun _ => 1))),0,(score_swap edge _ _ _ _ _).trans ?_⟩
    rw [score_pure edge.flip _ _ (site_one i),flip_bound,bound_site_eq i 0]

noncomputable def hits' [Fintype X] (f : X → Z) (q : X →ₗ[F] F)
    (A : F → X →ₗ[F] Z) (b : F → Z) : ℕ := ct (fun w => f w = A (q w) w + b (q w))

def query {m : ℕ} (e : X ≃ₗ[F] Pair m) (l r : Lane m →ₗ[F] F) : X →ₗ[F] F :=
  (l.coprod r).comp e.toLinearMap

lemma query_exists {m : ℕ} (e : X ≃ₗ[F] Pair m) (q : X →ₗ[F] F) :
    ∃ l r, q = query e l r := by
  let q' := q.comp e.symm.toLinearMap
  refine ⟨q'.comp (LinearMap.inl F _ _),q'.comp (LinearMap.inr F _ _),?_⟩
  apply LinearMap.ext
  intro x
  change q x = q' ((e x).1,0) + q' (0,(e x).2)
  rw [← map_add]
  simp [q']

lemma query_left {m : ℕ} (e : X ≃ₗ[F] Pair m) (l r : Lane m →ₗ[F] F) (i : ZMod m) :
    (∀ w, query e l r w = site i (e w).1) ↔ l = site i ∧ r = 0 := by
  constructor
  · intro h
    constructor <;> apply LinearMap.ext <;> intro x
    · simpa [query] using h (e.symm (x,0))
    · simpa [query] using h (e.symm (0,x))
  · rintro ⟨rfl,rfl⟩ w; simp [query]

lemma query_right {m : ℕ} (e : X ≃ₗ[F] Pair m) (l r : Lane m →ₗ[F] F) (i : ZMod m) :
    (∀ w, query e l r w = site i (e w).2) ↔ l = 0 ∧ r = site i := by
  constructor
  · intro h
    constructor <;> apply LinearMap.ext <;> intro x
    · simpa [query] using h (e.symm (x,0))
    · simpa [query] using h (e.symm (0,x))
  · rintro ⟨rfl,rfl⟩ w; simp [query]

lemma transport_hits [Fintype X] {m : ℕ} [NeZero m] (e : X ≃ₗ[F] Pair m) (o : Z ≃ₗ[F] Pair m)
    (K : X →ₗ[F] Pair m) (d : Pair m) (f : X → Z)
    (hf : ∀ w, o (f w) = edge (e w).1 (e w).2 + K w + d)
    (l r : Lane m →ₗ[F] F) (A : F → X →ₗ[F] Z) (b : F → Z)
    (C D : F → Lane m →ₗ[F] Pair m) (c : F → Pair m)
    (hA : ∀ s w, o (A s w) = C s (e w).1 + D s (e w).2 + K w)
    (hb : ∀ s, o (b s) = c s + d) :
    hits' f (query e l r) A b = score edge l r C D c := by
  unfold score hits'
  rw [← ct_equiv e.toEquiv (fun z : Pair m => edge z.1 z.2 = C (l z.1+r z.2) z.1 + D (l z.1+r z.2) z.2 + c (l z.1+r z.2))]
  apply ct_congr
  intro w
  rw [← o.injective.eq_iff, map_add,hf,hA,hb]
  change _ ↔ edge (e w).1 (e w).2 = C (query e l r w) (e w).1 + D (query e l r w) (e w).2 + c (query e l r w)
  rw [← add_assoc _ _ d, add_left_inj, add_right_comm _ (K w) (c _),add_left_inj]

lemma normalize_hits [Fintype X] {m : ℕ} [NeZero m] (e : X ≃ₗ[F] Pair m) (o : Z ≃ₗ[F] Pair m)
    (K : X →ₗ[F] Pair m) (d : Pair m) (f : X → Z)
    (hf : ∀ w, o (f w) = edge (e w).1 (e w).2 + K w + d)
    (l r : Lane m →ₗ[F] F) (A : F → X →ₗ[F] Z) (b : F → Z) :
    ∃ C D c, hits' f (query e l r) A b = score edge l r C D c := by
  let L := fun s => ((o.toLinearMap.comp (A s))-K).comp e.symm.toLinearMap
  refine ⟨fun s => (L s).comp (LinearMap.inl F _ _),fun s => (L s).comp (LinearMap.inr F _ _),
    fun s => o (b s)-d,transport_hits e o K d f hf l r A b _ _ _ ?_ (by simp)⟩
  intro s w
  change o (A s w) = L s ((e w).1,0) + L s (0,(e w).2) + K w
  rw [← map_add]
  have he : ((e w).1,0) + (0,(e w).2) = e w := by simp
  simp [he,L]

lemma realize_hits [Fintype X] {m : ℕ} [NeZero m] (e : X ≃ₗ[F] Pair m) (o : Z ≃ₗ[F] Pair m)
    (K : X →ₗ[F] Pair m) (d : Pair m) (f : X → Z)
    (hf : ∀ w, o (f w) = edge (e w).1 (e w).2 + K w + d)
    (l r : Lane m →ₗ[F] F) (C D : F → Lane m →ₗ[F] Pair m) (c : F → Pair m) :
    ∃ A b, hits' f (query e l r) A b = score edge l r C D c := by
  refine ⟨fun s => o.symm.toLinearMap.comp ((((C s).coprod (D s)).comp e.toLinearMap)+K),
    fun s => o.symm (c s+d),transport_hits e o K d f hf l r _ _ C D c ?_ (by simp)⟩
  simp

lemma affine_opt [Fintype X] {t : ℕ} [NeZero (3*t)] (ht : 240 ≤ t)
    (e : X ≃ₗ[F] Pair (3*t)) (o : Z ≃ₗ[F] Pair (3*t)) (K : X →ₗ[F] Pair (3*t)) (d : Pair (3*t))
    (f : X → Z) (hf : ∀ w, o (f w) = edge (e w).1 (e w).2 + K w + d)
    (l r : Lane (3*t) →ₗ[F] F) :
    (∃ A b, ∀ q' A' b', hits' f q' A' b' ≤ hits' f (query e l r) A b) ↔ isCoord l r := by
  let G := pureBound edge (site (0 : ZMod (3*t)))
  have attain {l' r' : Lane (3*t) →ₗ[F] F} (hc : isCoord l' r') :
      ∃ A b, hits' f (query e l' r') A b = G := by
    obtain ⟨C,D,c,h⟩ := coord_attains hc
    obtain ⟨A,b,h'⟩ := realize_hits e o K d f hf l' r' C D c
    exact ⟨A,b,h'.trans h⟩
  constructor
  · rintro ⟨A,b,h⟩
    obtain ⟨A',b',hh⟩ := attain (show isCoord 0 (site (0 : ZMod (3*t))) from Or.inl ⟨0,rfl,rfl⟩)
    obtain ⟨C,D,c,h'⟩ := normalize_hits e o K d f hf l r A b
    exact (scores ht l r C D c).2 (hh.ge.trans ((h _ A' b').trans_eq h'))
  · intro hc
    obtain ⟨A,b,hh⟩ := attain hc
    refine ⟨A,b,?_⟩
    intro q' A' b'
    obtain ⟨l',r',rfl⟩ := query_exists e q'
    obtain ⟨C,D,c,h'⟩ := normalize_hits e o K d f hf l' r' A' b'
    exact h'.le.trans ((scores ht l' r' C D c).1.trans_eq hh.symm)

abbrev Word (t : ℕ) := Fin (6*t) → F

open Fin.NatCast

def evenIx {t : ℕ} [NeZero (6*t)] (i : ZMod (3*t)) : Fin (6*t) := ((2*i.val : ℕ) : Fin (6*t))

def oddIx {t : ℕ} [NeZero (6*t)] (i : ZMod (3*t)) : Fin (6*t) := ((2*i.val+1 : ℕ) : Fin (6*t))

lemma even_val {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (i : ZMod (3*t)) : (evenIx i).val = 2*i.val := by
  have hi := ZMod.val_lt i
  exact Nat.mod_eq_of_lt (by omega)

lemma odd_val {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (i : ZMod (3*t)) : (oddIx i).val = 2*i.val+1 := by
  have hi := ZMod.val_lt i
  exact Nat.mod_eq_of_lt (by omega)

lemma even_cast {t : ℕ} [NeZero (6*t)] (k : ℕ) : evenIx (k : ZMod (3*t)) = ((2*k : ℕ) : Fin (6*t)) := by
  apply Fin.ext
  simp only [evenIx, Fin.val_natCast, ZMod.val_natCast]
  rw [show 6*t = 2*(3*t) by omega, Nat.mul_mod_mul_left,Nat.mul_mod_mul_left,Nat.mod_mod]

lemma even_next {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (i : ZMod (3*t)) : evenIx (i+1) = evenIx i + 2 := by
  calc
    _ = evenIx ((i.val+1 : ℕ) : ZMod (3*t)) := by simp
    _ = _ := by rw [even_cast,Nat.mul_add,Nat.mul_one,Nat.cast_add]; rfl

lemma even_prev {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (i : ZMod (3*t)) : evenIx (i-1) = evenIx i - 2 := by
  apply eq_sub_of_add_eq
  exact (even_next (t := t) (i-1)).symm.trans (congrArg evenIx (sub_add_cancel i 1))

lemma odd_eq {t : ℕ} [NeZero (6*t)] (i : ZMod (3*t)) : oddIx i = evenIx i + 1 := by simp [evenIx,oddIx]

lemma odd_next {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (i : ZMod (3*t)) : oddIx (i+1) = oddIx i + 2 := by
  rw [odd_eq,even_next,odd_eq]; abel

lemma odd_prev {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (i : ZMod (3*t)) : oddIx (i-1) = oddIx i - 2 := by
  rw [odd_eq,even_prev,odd_eq]; abel

lemma even_half {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (j : Fin (6*t)) (h : j.val % 2 = 0) :
    evenIx (j.val / 2 : ℕ) = j := by
  apply Fin.ext
  rw [even_val,ZMod.val_natCast_of_lt (by have := j.isLt; omega)]
  omega

lemma odd_half {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (j : Fin (6*t)) (h : j.val % 2 ≠ 0) :
    oddIx (j.val / 2 : ℕ) = j := by
  apply Fin.ext
  rw [odd_val,ZMod.val_natCast_of_lt (by have := j.isLt; omega)]
  omega

def interleave {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] : Word t ≃ₗ[F] Pair (3*t) where
  toFun w := (fun i => w (evenIx i), fun i => w (oddIx i))
  invFun z j := if j.val % 2 = 0 then z.1 (j.val / 2 : ℕ) else z.2 (j.val / 2 : ℕ)
  left_inv w := by
    funext j
    by_cases h : j.val % 2 = 0 <;> simp [h, even_half,odd_half]
  right_inv z := by
    apply Prod.ext <;> funext i
    · change (if (evenIx i).val % 2 = 0 then z.1 ((evenIx i).val/2 : ℕ) else z.2 ((evenIx i).val/2 : ℕ)) = _
      rw [even_val]; simp
    · change (if (oddIx i).val % 2 = 0 then z.1 ((oddIx i).val/2 : ℕ) else z.2 ((oddIx i).val/2 : ℕ)) = _
      rw [odd_val]; simp [Nat.mul_add_div]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def offset {n : ℕ} [NeZero n] (s : Fin n) : (Fin n → F) ≃ₗ[F] (Fin n → F) where
  toFun w i := w (i+s)
  invFun w i := w (i-s)
  left_inv _ := by funext; simp
  right_inv _ := by funext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rawIso {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] : Word t ≃ₗ[F] Pair (3*t) :=
  (offset (-3)).trans interleave

def outIso {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] : Word t ≃ₗ[F] Pair (3*t) :=
  (offset (-1)).trans interleave

def triform {n : ℕ} [NeZero n] (i : Fin n) : (Fin n → F) →ₗ[F] F :=
  let e := fun k : Fin n => (LinearMap.proj k : (Fin n → F) →ₗ[F] F)
  e i + e (i+2) + e (i-2)

def mx {n : ℕ} [NeZero n] (i : Fin n) : (Fin n → F) →ₗ[F] F :=
  (triform i).comp (offset (-3)).toLinearMap

lemma mx_even {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (w : Word t) (i : ZMod (3*t)) :
    mx (evenIx i) w = site i (rawIso w).1 := by
  change _ = (offset (-3) w) (evenIx i) + (offset (-3) w) (evenIx (i+1)) + (offset (-3) w) (evenIx (i-1))
  rw [even_next,even_prev]
  rfl

lemma mx_odd {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (w : Word t) (i : ZMod (3*t)) :
    mx (oddIx i) w = site i (rawIso w).2 := by
  change _ = (offset (-3) w) (oddIx i) + (offset (-3) w) (oddIx (i+1)) + (offset (-3) w) (oddIx (i-1))
  rw [odd_next,odd_prev]
  rfl

def linPart {n : ℕ} [NeZero n] (name : Fin n → F) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  LinearMap.pi fun i => mx i + (1 + triform (i+1) name) • mx (i+2) +
    triform (i+2) name • mx (i+1) + LinearMap.proj (i-4)

def constPart {n : ℕ} [NeZero n] (name c : Fin n → F) (i : Fin n) : F :=
  triform i name + (1 + triform (i+1) name)*triform (i+2) name + c i

def output {n : ℕ} [NeZero n] (name c w : Fin n → F) (i : Fin n) : F :=
  let y := fun k => mx k w + triform k name
  y i + (1+y (i+1))*y (i+2) + w (i-4) + c i

lemma output_decomp {n : ℕ} [NeZero n] (name c w : Fin n → F) (i : Fin n) :
    output name c w i = mx (i+1) w * mx (i+2) w + linPart name w i + constPart name c i := by
  simp [output, linPart, constPart, smul_eq_mul]
  ring

lemma output_normal {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (name c w : Word t) :
    outIso (output name c w) = edge (rawIso w).1 (rawIso w).2 + outIso (linPart name w) + outIso (constPart name c) := by
  apply Prod.ext <;> funext i
  · change output name c w (evenIx i + -1) = (site i (rawIso w).1 * site i (rawIso w).2) + _ + _
    rw [output_decomp,← mx_even,← mx_odd,odd_eq]
    rw [show evenIx i + -1 + 1 = evenIx i by abel,
      show evenIx i + -1 + 2 = evenIx i + 1 by rw [← one_add_one_eq_two]; abel]
    rfl
  · change output name c w (oddIx i + -1) = site (i+1) (rawIso w).1 * site i (rawIso w).2 + linPart name w (oddIx i + -1) + constPart name c (oddIx i + -1)
    rw [output_decomp,← mx_even,← mx_odd,even_next,odd_eq]
    rw [show evenIx i + 1 + -1 = evenIx i by abel,mul_comm (mx (evenIx i+1) w)]

theorem model_opt {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (ht : 240 ≤ t)
    (name c : Word t) (q : Word t →ₗ[F] F) :
    (∃ A b, ∀ q' A' b', hits' (output name c) q' A' b' ≤ hits' (output name c) q A b) ↔
      ∃ i, ∀ w, q w = mx i w := by
  obtain ⟨l,r,rfl⟩ := query_exists rawIso q
  rw [affine_opt ht rawIso outIso (outIso.toLinearMap.comp (linPart name)) (outIso (constPart name c))
    (output name c) (output_normal name c)]
  constructor
  · rintro (⟨i,hl,hr⟩|⟨i,hl,hr⟩)
    · exact ⟨oddIx i, fun w => ((query_right rawIso l r i).mpr ⟨hl,hr⟩ w).trans (mx_odd w i).symm⟩
    · exact ⟨evenIx i, fun w => ((query_left rawIso l r i).mpr ⟨hl,hr⟩ w).trans (mx_even w i).symm⟩
  · rintro ⟨i,hi⟩
    by_cases hp : i.val % 2 = 0
    · refine Or.inr ⟨(i.val/2 : ℕ), (query_left rawIso l r _).mp (fun w => (hi w).trans ?_)⟩
      exact (congrArg (fun j => mx j w) (even_half i hp).symm).trans (mx_even w _)
    · refine Or.inl ⟨(i.val/2 : ℕ), (query_right rawIso l r _).mp (fun w => (hi w).trans ?_)⟩
      exact (congrArg (fun j => mx j w) (odd_half i hp).symm).trans (mx_odd w _)

lemma ix_plus {n : ℕ} [NeZero n] (i : Fin n) (s : ℕ) :
    Fin.ofNat n (i.val+s) = i + Fin.ofNat n s := by simp

lemma ix_minus {n : ℕ} [NeZero n] (i : Fin n) (s : ℕ) (hs : s ≤ n) :
    Fin.ofNat n (i.val+n-s) = i - Fin.ofNat n s := by
  apply eq_sub_of_add_eq
  simp only [Fin.ofNat_eq_cast]
  rw [← Nat.cast_add,Nat.sub_add_cancel (by omega),Nat.cast_add,Fin.cast_val_eq_self,Fin.natCast_self,add_zero]

def rotNat {n : ℕ} [NeZero n] (s : ℕ) (w : Fin n → F) (i : Fin n) : F :=
  w (Fin.ofNat n (i.val+n-s%n))

def triNat {n : ℕ} [NeZero n] (w : Fin n → F) (i : Fin n) : F :=
  w i + w (Fin.ofNat n (i.val+2)) + w (Fin.ofNat n (i.val+n-2))

def outNat {n : ℕ} [NeZero n] (name c w : Fin n → F) (i : Fin n) : F :=
  let y := triNat (rotNat 3 w + name)
  y i + (1+y (Fin.ofNat n (i.val+1)))*y (Fin.ofNat n (i.val+2)) + rotNat 4 w i + c i

lemma triNat_eq {n : ℕ} [NeZero n] (h : 2 ≤ n) (w : Fin n → F) (i : Fin n) :
    triNat w i = triform i w := by
  unfold triNat
  rw [ix_plus,ix_minus _ _ h]
  rfl

lemma rotNat_eq {n : ℕ} [NeZero n] (s : ℕ) (hs : s < n) (w : Fin n → F) :
    rotNat s w = offset (-Fin.ofNat n s) w := by
  funext i
  unfold rotNat
  rw [Nat.mod_eq_of_lt hs,ix_minus _ _ hs.le]
  rw [sub_eq_add_neg]; rfl

lemma outNat_eq {n : ℕ} [NeZero n] (h : 4 < n) (name c w : Fin n → F) :
    outNat name c w = output name c w := by
  have h₃ : 3 < n := by omega
  have h₂ : 2 ≤ n := by omega
  funext i
  simp only [outNat,triNat_eq h₂,map_add,rotNat_eq 3 h₃,rotNat_eq 4 h,Fin.ofNat_eq_cast,Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_ofNat,Nat.cast_one]
  unfold output
  rw [sub_eq_add_neg i 4]
  rfl

theorem nat_opt {t : ℕ} [NeZero (3*t)] [NeZero (6*t)] (ht : 240 ≤ t)
    (name c : Word t) (q : Word t →ₗ[F] F) :
    (∃ (A : F → Word t →ₗ[F] Word t) (b : F → Word t), ∀ (q' : Word t →ₗ[F] F)
        (A' : F → Word t →ₗ[F] Word t) (b' : F → Word t),
      Nat.card {w : Word t // outNat name c w = A' (q' w) w + b' (q' w)} ≤
        Nat.card {w : Word t // outNat name c w = A (q w) w + b (q w)}) ↔
      ∃ i, ∀ w, q w = triNat (rotNat 3 w) i := by
  have h : 4 < 6*t := by omega
  simpa only [hits',ct_card, outNat_eq h,triNat_eq (show 2 ≤ 6*t by omega),
    rotNat_eq 3 (show 3 < 6*t by omega),Fin.ofNat_eq_cast,Nat.cast_ofNat,mx,LinearMap.comp_apply,LinearEquiv.coe_coe] using model_opt ht name c q

end PEqualNP.Outside.L_meta_33627

theorem PEqualNP.Outside.L_meta_33627 : ∀ (t : ℕ) (ht : 0 < t), 240 ≤ t →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  ∀ name c : W,
    let hits := fun (q : W →ₗ[F] F) (A : F → W →ₗ[F] W) (b : F → W) =>
      Nat.card {w : W // out name c w = A (q w) w + b (q w)}
    ∀ q : W →ₗ[F] F,
      (∃ A b, ∀ (q' : W →ₗ[F] F) A' b', hits q' A' b' ≤ hits q A b) ↔
        ∃ i : Fin n, ∀ w : W, q w = mix w i := by
  intro t ht h
  have : NeZero (3*t) := ⟨by omega⟩
  have : NeZero (6*t) := ⟨by omega⟩
  exact PEqualNP.Outside.L_meta_33627.nat_opt h

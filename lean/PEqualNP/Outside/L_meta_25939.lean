import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_25939_aux

abbrev F := ZMod 2
abbrev Coefficients (m : ℕ) := Fin m → F

variable {m : ℕ}

def unit (i : Fin m) : Coefficients m := fun j => if i = j then 1 else 0

def defect (f : Coefficients m → F) (z x y : Coefficients m) : F :=
  f z + f (z + x) + f (z + y) + f (z + x + y)

def Affine (f : Coefficients m → F) : Prop :=
  ∃ A : Coefficients m →ₗ[F] F, ∃ c : F, ∀ x, f x = c + A x

theorem affine_of_zero_defect (f : Coefficients m → F)
    (h : ∀ x y, defect f 0 x y = 0) : Affine f := by
  let A : Coefficients m →ₗ[F] F :=
    { toFun := fun x => f x + f 0
      map_add' := fun x y => by
        have pair : (f (x + y) + f 0) + (f x + f y) = 0 := by
          simpa [defect, add_comm, add_left_comm, add_assoc] using h x y
        have sum := (add_eq_zero_iff_eq_neg.mp pair).trans (ZModModule.neg_eq_self _)
        exact sum.trans (by rw [add_add_add_comm, ZModModule.add_self, add_zero])
      map_smul' := fun r x => by
        fin_cases r
        · change f ((0 : F) • x) + f 0 = (0 : F) • (f x + f 0)
          simp [ZModModule.add_self]
        · change f ((1 : F) • x) + f 0 = (1 : F) • (f x + f 0)
          simp }
  refine ⟨A, f 0, ?_⟩
  intro x
  change f x = f 0 + (f x + f 0)
  rw [add_left_comm, ZModModule.add_self, add_zero]

theorem affine_defect_zero {f : Coefficients m → F} (hf : Affine f)
    (z x y : Coefficients m) : defect f z x y = 0 := by
  obtain ⟨A, c, h⟩ := hf
  simp only [defect, h, map_add]
  calc
    _ = (c + c) + (c + c) + (A z + A z) + (A z + A z) + (A x + A x) + (A y + A y) := by ring
    _ = 0 := by simp [ZModModule.add_self]

theorem defect_add (f g : Coefficients m → F) (z x y : Coefficients m) :
    defect (fun a => f a + g a) z x y = defect f z x y + defect g z x y := by
  unfold defect
  ring

theorem affine_add {f g : Coefficients m → F} (hf : Affine f) (hg : Affine g) :
    Affine (fun x => f x + g x) := by
  obtain ⟨A, a, hf⟩ := hf
  obtain ⟨B, b, hg⟩ := hg
  refine ⟨A + B, a + b, ?_⟩
  intro x
  simp only [hf, hg, LinearMap.add_apply]
  ring

theorem affine_const (c : F) : Affine (fun _ : Coefficients m => c) :=
  ⟨0, c, fun _ => by simp⟩

def polar (A B : Coefficients m →ₗ[F] F) (x y : Coefficients m) : F :=
  A x * B y + B x * A y

theorem product_defect (A B : Coefficients m →ₗ[F] F) (c d : F)
    (z x y : Coefficients m) :
    defect (fun a => (c + A a) * (d + B a)) z x y = polar A B x y := by
  simp only [defect, map_add]
  let p := c + A z
  let q := d + B z
  have collapse : (p * q + p * q) + (p * q + p * q)
      + (p * (B x + B y) + p * (B x + B y))
      + ((A x + A y) * q + (A x + A y) * q)
      + ((A x * B x + A y * B y) + (A x * B x + A y * B y))
      + polar A B x y = polar A B x y := by simp [ZModModule.add_self]
  rw [← collapse]
  dsimp [p, q, polar]
  ring

theorem affine_plus_product_defect {p f g : Coefficients m → F}
    (hp : Affine p) (hf : Affine f) (hg : Affine g) :
    ∃ A B : Coefficients m →ₗ[F] F, ∀ z x y,
      defect (fun a => p a + f a * g a) z x y = polar A B x y := by
  obtain ⟨A, a, hf⟩ := hf
  obtain ⟨B, b, hg⟩ := hg
  refine ⟨A, B, fun z x y => ?_⟩
  rw [defect_add, affine_defect_zero hp, zero_add]
  simp only [hf, hg]
  exact product_defect A B a b z x y

private def polarAt (A B : Coefficients m →ₗ[F] F) (x : Coefficients m) : Coefficients m →ₗ[F] F :=
  A x • B + B x • A

private theorem basis_eq_unit (i : Fin m) : Pi.basisFun F (Fin m) i = unit i := by
  ext j
  simp [unit, Pi.single_apply, eq_comm]

theorem polar_zero_of_unit_pairs (A B : Coefficients m →ₗ[F] F)
    (h : ∀ i j, polar A B (unit i) (unit j) = 0) (x y : Coefficients m) : polar A B x y = 0 := by
  have onBasis (i : Fin m) : polarAt A B (unit i) = 0 := by
    apply (Pi.basisFun F (Fin m)).ext
    intro j
    rw [basis_eq_unit]
    simpa [polarAt, polar] using h i j
  have atX : polarAt A B x = 0 := by
    apply (Pi.basisFun F (Fin m)).ext
    intro i
    rw [basis_eq_unit]
    have atI := congrArg (fun M : Coefficients m →ₗ[F] F => M x) (onBasis i)
    simpa [polarAt, mul_comm, add_comm] using atI
  simpa [polarAt, polar] using congrArg (fun M : Coefficients m →ₗ[F] F => M y) atX

theorem polar_self (A B : Coefficients m →ₗ[F] F) (x : Coefficients m) : polar A B x x = 0 := by
  rw [polar, mul_comm (B x), ZModModule.add_self]

private def determinant (p : (F × F) × (F × F)) : F :=
  p.1.1 * p.2.2 + p.1.2 * p.2.1

private theorem determinant_count : Fintype.card {p // determinant p ≠ 0} = 6 := by
  decide +kernel

theorem count_nonzero_polar {m : ℕ} (A B : Coefficients m →ₗ[F] F)
    {u v : Coefficients m} (witness : polar A B u v ≠ 0) :
    8 * ((Finset.univ : Finset (Coefficients m × Coefficients m)).filter
      (fun p => polar A B p.1 p.2 ≠ 0)).card = 3 * 2 ^ (2 * m) := by
  have det_one : polar A B u v = 1 := Fin.eq_one_of_ne_zero _ witness
  let lift (p : F × F) : Coefficients m :=
    (p.1 * B v + p.2 * A v) • u + (p.1 * B u + p.2 * A u) • v
  have liftA (p : F × F) : A (lift p) = p.1 := by
    simp only [lift, map_add, map_smul, smul_eq_mul]
    calc
      _ = p.1 * polar A B u v + p.2 * (A v * A u + A v * A u) := by
        unfold polar
        ring
      _ = p.1 := by simp [det_one, ZModModule.add_self]
  have liftB (p : F × F) : B (lift p) = p.2 := by
    simp only [lift, map_add, map_smul, smul_eq_mul]
    calc
      _ = p.1 * (B v * B u + B v * B u) + p.2 * polar A B u v := by
        unfold polar
        ring
      _ = p.2 := by simp [det_one, ZModModule.add_self]
  let K := {x : Coefficients m // A x = 0 ∧ B x = 0}
  let split : Coefficients m ≃ (F × F) × K :=
    { toFun := fun x => ((A x, B x), ⟨x - lift (A x, B x), by
        simp only [map_sub, liftA, liftB, sub_self, and_self]⟩)
      invFun := fun p => p.2.val + lift p.1
      left_inv := fun x => sub_add_cancel x _
      right_inv := by
        rintro ⟨⟨a,b⟩, x⟩
        have ha : A (x.val + lift (a,b)) = a := by simp [x.property.1, liftA]
        have hb : B (x.val + lift (a,b)) = b := by simp [x.property.2, liftB]
        refine Prod.ext (Prod.ext ha hb) (Subtype.ext ?_)
        change x.val + lift (a,b) - lift (A _, B _) = x.val
        rw [ha, hb, add_sub_cancel_right] }
  let splitPairs : Coefficients m × Coefficients m ≃ ((F × F) × (F × F)) × (K × K) :=
    (split.prodCongr split).trans (Equiv.prodProdProdComm _ _ _ _)
  let splitNonzero : {p : Coefficients m × Coefficients m // polar A B p.1 p.2 ≠ 0} ≃
      {p // determinant p ≠ 0} × (K × K) :=
    (splitPairs.subtypeEquiv (p := fun p => polar A B p.1 p.2 ≠ 0)
      (q := fun p => determinant p.1 ≠ 0) (fun _ => Iff.rfl)).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (β := K × K) (p := fun p => determinant p ≠ 0))
  have card_nonzero := Fintype.card_congr splitNonzero
  simp only [Fintype.card_subtype (fun p : Coefficients m × Coefficients m => polar A B p.1 p.2 ≠ 0),
    Fintype.card_prod, determinant_count, ← pow_two] at card_nonzero
  have card_f : Fintype.card F = 2 := by decide +kernel
  have card_full := Fintype.card_congr split
  simp only [Coefficients, Fintype.card_pi_const, Fintype.card_prod, card_f] at card_full
  rw [card_nonzero, Nat.mul_comm 2 m, pow_mul, card_full]
  ring

end PEqualNP.Outside.L_meta_25939_aux

open PEqualNP.Outside.L_meta_25939_aux

theorem PEqualNP.Outside.L_meta_25939 : (∀ (k m r : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let E := Fin m → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-s % k))
  let gap := fun (b : Bool) => if b then 2 else 1
  let start := fun (b : Bool) => if b then 3 else 1
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let unit := fun (i j : Fin m) => (if i = j then 1 else 0 : F)
  let closed := fun (N : Nat) (watch : Bool → Nat → Fin k → Bool) =>
    ∀ (b : Bool) (t : Nat), t < N → ∀ j : Fin k, watch b (t+1) j = true →
      ∀ e : Fin 3, let i := ix (j.val+e.val)
        watch b t i = true ∧ watch b t (ix (i.val+gap b)) = true ∧
        watch b t (ix (i.val+k-gap b % k)) = true
  ∀ (watch : Bool → Nat → Fin k → Bool), closed r watch →
  ∀ (base : W) (gen : Fin m → W) (name : Bool → W) (c : Bool → Fin r → W),
    let state := fun (b : Bool) (key : W) (n : Nat) =>
      ((List.finRange r).take n).foldl (fun z tick =>
        let y := fun i : Fin k =>
          z i + z (ix (i.val+gap b)) + z (ix (i.val+k-gap b % k))
        fun j : Fin k => y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
          rot (feed b tick.val) key j + c b tick j) (rot (start b) key + name b)
    let shift := fun a : E => ∑ i : Fin m, a i • gen i
    let atKey := fun (b : Bool) (t : Nat) (j : Fin k) (a : E) => state b (base+shift a) t j
    let defect := fun (b : Bool) (t : Nat) (j : Fin k) (z x y : E) =>
      atKey b t j z + atKey b t j (z+x) + atKey b t j (z+y) + atKey b t j (z+x+y)
    let affineThrough := fun h : Nat => ∀ (b : Bool) (t : Nat), t ≤ h → ∀ j : Fin k,
      watch b t j = true → ∀ x y : E, defect b t j 0 x y = 0
    (∀ h : Nat, h ≤ r → (affineThrough h ↔ ∀ (b : Bool) (t : Nat), t ≤ h → ∀ j : Fin k,
      watch b t j = true → ∀ i l : Fin m, defect b t j 0 (unit i) (unit l) = 0)) ∧
    (∀ t : Nat, t < r → affineThrough t → ¬affineThrough (t+1) →
      ∃ (b : Bool) (j : Fin k) (i l : Fin m), watch b (t+1) j = true ∧ i ≠ l ∧
        ∀ z : E, defect b (t+1) j z (unit i) (unit l) ≠ 0 ∧
          8 * ((Finset.univ : Finset (E × E)).filter
            (fun xy => defect b (t+1) j z xy.1 xy.2 ≠ 0)).card = 3 * 2^(2*m))) := by
  intro k m r hk F W E ix rot gap start feed unit closed watch hw base gen name c state shift atKey defect affineThrough
  have keyAffine (s : Nat) (j : Fin k) : Affine (fun a : E => rot s (base + shift a) j) := by
    let coord := ix (j.val + k - s % k)
    let evaluate : W →ₗ[F] F := LinearMap.proj coord
    let projection : E →ₗ[F] F :=
      ∑ i : Fin m, (gen i coord) • (LinearMap.proj (R := F) i : E →ₗ[F] F)
    refine ⟨projection, base coord, fun a => ?_⟩
    change base coord + evaluate (∑ i : Fin m, a i • gen i) = base coord + projection a
    congr 1
    rw [map_sum]
    simp only [projection, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change a i * gen i coord = gen i coord * a i
    exact mul_comm _ _
  have initial (b : Bool) (j : Fin k) : Affine (atKey b 0 j) := by
    change Affine (fun a : E => rot (start b) (base + shift a) j + name b j)
    exact affine_add (keyAffine (start b) j) (affine_const (name b j))
  have state_succ (b : Bool) (key : W) (t : Nat) (ht : t < r) (j : Fin k) :
      state b key (t + 1) j =
        let y := fun i : Fin k =>
          state b key t i + state b key t (ix (i.val + gap b)) + state b key t (ix (i.val + k - gap b % k))
        y j + (1 + y (ix (j.val + 1))) * y (ix (j.val + 2)) + rot (feed b t) key j + c b ⟨t, ht⟩ j := by
    have hlen : t < (List.finRange r).length := by simpa using ht
    have tickAt : (List.finRange r)[t]'hlen = (⟨t, ht⟩ : Fin r) := by
      apply Fin.ext
      simp [List.getElem_finRange]
    simp only [state, List.take_succ_eq_append_getElem hlen, List.foldl_append, List.foldl_cons,
      List.foldl_nil, tickAt]
  have stepPolar (t : Nat) (ht : t < r) (prev : affineThrough t) (b : Bool) (j : Fin k)
      (hj : watch b (t + 1) j = true) :
      ∃ A B : E →ₗ[F] F, ∀ z x y, defect b (t + 1) j z x y = polar A B x y := by
    let y (i : Fin k) (a : E) : F :=
      atKey b t i a + atKey b t (ix (i.val + gap b)) a + atKey b t (ix (i.val + k - gap b % k)) a
    have watched (e : Fin 3) : Affine (y (ix (j.val + e.val))) := by
      obtain ⟨h0, h1, h2⟩ := hw b t ht j hj e
      exact affine_add (affine_add (affine_of_zero_defect _ (prev b t le_rfl _ h0))
        (affine_of_zero_defect _ (prev b t le_rfl _ h1))) (affine_of_zero_defect _ (prev b t le_rfl _ h2))
    have ix_zero : ix (j.val + 0) = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have ha : Affine (y j) := by
      have h0 : Affine (y (ix (j.val + 0))) := watched 0
      rwa [ix_zero] at h0
    let p (a : E) : F := y j a + rot (feed b t) (base + shift a) j + c b ⟨t, ht⟩ j
    have hp : Affine p := affine_add (affine_add ha (keyAffine (feed b t) j)) (affine_const (c b ⟨t, ht⟩ j))
    have hb : Affine (fun a : E => 1 + y (ix (j.val + 1)) a) := affine_add (affine_const 1) (watched 1)
    have hc : Affine (y (ix (j.val + 2))) := watched 2
    have hs : atKey b (t + 1) j = fun a : E => p a + (1 + y (ix (j.val + 1)) a) * y (ix (j.val + 2)) a := by
      funext a
      calc
        _ = y j a + (1 + y (ix (j.val + 1)) a) * y (ix (j.val + 2)) a +
            rot (feed b t) (base + shift a) j + c b ⟨t, ht⟩ j := state_succ b (base + shift a) t ht j
        _ = _ := by dsimp only [p]; ac_rfl
    obtain ⟨A, B, hd⟩ := affine_plus_product_defect hp hb hc
    refine ⟨A, B, fun z x y => ?_⟩
    change PEqualNP.Outside.L_meta_25939_aux.defect (atKey b (t + 1) j) z x y = polar A B x y
    rw [hs]
    exact hd z x y
  let unitTests (h : Nat) := ∀ (b : Bool) (t : Nat), t ≤ h → ∀ j : Fin k,
    watch b t j = true → ∀ i l : Fin m, defect b t j 0 (unit i) (unit l) = 0
  have tests_suffice : ∀ h : Nat, h ≤ r → unitTests h → affineThrough h := by
    intro h
    induction h with
    | zero =>
      intro _ _ b t ht j _ x y
      have ht0 : t = 0 := by omega
      subst t
      exact affine_defect_zero (initial b j) 0 x y
    | succ n ih =>
      intro hn tests b t ht j hj x y
      have prev : affineThrough n := ih (by omega) (fun b s hs j hj i l => tests b s (by omega) j hj i l)
      by_cases htn : t ≤ n
      · exact prev b t htn j hj x y
      have eq : t = n + 1 := by omega
      subst t
      obtain ⟨A, B, hd⟩ := stepPolar n (by omega) prev b j hj
      have on_units (i l : Fin m) : polar A B (unit i) (unit l) = 0 :=
        (hd 0 (unit i) (unit l)).symm.trans (tests b (n + 1) le_rfl j hj i l)
      exact (hd 0 x y).trans (polar_zero_of_unit_pairs A B on_units x y)
  refine ⟨fun h hr => ⟨?_, tests_suffice h hr⟩, ?_⟩
  · intro full b t ht j hj i l
    exact full b t ht j hj (unit i) (unit l)
  · intro t ht prev failAtNext
    have failTest : ¬ unitTests (t + 1) := fun all => failAtNext (tests_suffice _ (by omega) all)
    simp only [unitTests, not_forall] at failTest
    obtain ⟨b, s, hs, j, hj, i, l, fails⟩ := failTest
    have hsNext : s = t + 1 := by
      by_contra hne
      exact fails (prev b s (by omega) j hj (unit i) (unit l))
    subst s
    obtain ⟨A, B, hd⟩ := stepPolar t ht prev b j hj
    have nonzero : polar A B (unit i) (unit l) ≠ 0 := by
      simpa only [hd] using fails
    refine ⟨b, j, i, l, hj, ?_, fun z => ?_⟩
    · intro equal
      apply nonzero
      subst l
      exact polar_self A B (unit i)
    · simp only [hd]
      exact ⟨nonzero, count_nonzero_polar A B nonzero⟩

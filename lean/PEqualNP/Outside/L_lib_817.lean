import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_817_aux

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F
abbrev Form (n : ℕ) := Vec n →ₗ[F] F

def bit (b : Bool) : F := if b then 1 else 0

def IsAffine {Z : Type*} {m : ℕ} (f : Z → Vec m → Bool) : Prop :=
  ∃ (l : Form m) (a : Z → F), ∀ z x, bit (f z x) = l x + a z

def goodGate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

noncomputable def charged (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def gateValue (g : Gate) (W : Z → Vec m → List Bool) (z : Z) (x : Vec m) : Bool :=
  g.op.eval (g.inputs.map fun i => (W z x).getD i false)

theorem charged_eq_true (g : Gate) :
    charged g = true ↔ (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  unfold charged
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

private theorem gateAffine_const {Z : Type*} {m : ℕ} (f : Z → Bool) :
    IsAffine (fun z (_ : Vec m) => f z) := by
  exact ⟨0, fun z => bit (f z), by simp⟩

private theorem gateBit_not (a : Bool) :
    bit (GateOp.not.eval [a]) = 1 + bit a := by
  cases a <;> decide

private theorem gateBit_mod1 (a : Bool) :
    bit ((GateOp.mod 2).eval [a]) = 1 + bit a := by
  cases a <;> decide

private theorem gateBit_mod2 (a b : Bool) :
    bit ((GateOp.mod 2).eval [a, b]) = 1 + bit a + bit b := by
  cases a <;> cases b <;> decide

private theorem gateBit_and1 (a : Bool) : GateOp.and.eval [a] = a := by
  cases a <;> rfl

private theorem gateBit_or1 (a : Bool) : GateOp.or.eval [a] = a := by
  cases a <;> rfl

theorem gate_affine {Z : Type*} {m : ℕ} {g : Gate} {W : Z → Vec m → List Bool}
    (hg : goodGate g) (hc : charged g = false)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    IsAffine (gateValue g W) := by
  rcases g with ⟨op, inputs⟩
  rcases hg with ⟨hlen, hop⟩
  change inputs.length ≤ 2 at hlen
  have hnot : ¬ ((op = .and ∨ op = .or) ∧ inputs.length = 2) := by
    intro h
    have ht := (charged_eq_true ⟨op, inputs⟩).2 h
    rw [hc] at ht
    contradiction
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ inputs.length = 1) at hop
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · exact gateAffine_const (fun _ => op.eval [])
  · rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩
    · change IsAffine (fun z x => GateOp.and.eval [(W z x).getD i false])
      simpa only [gateBit_and1] using hW i
    · change IsAffine (fun z x => GateOp.or.eval [(W z x).getD i false])
      simpa only [gateBit_or1] using hW i
    · obtain ⟨l, a, ha⟩ := hW i
      refine ⟨l, fun z => 1 + a z, fun z x => ?_⟩
      change bit ((GateOp.mod 2).eval [(W z x).getD i false]) = _
      rw [gateBit_mod1, ha]
      ring
    · obtain ⟨l, a, ha⟩ := hW i
      refine ⟨l, fun z => 1 + a z, fun z x => ?_⟩
      change bit (GateOp.not.eval [(W z x).getD i false]) = _
      rw [gateBit_not, ha]
      ring
  · have hi : (op = .and ∨ op = .or) → False := fun h => hnot ⟨h, rfl⟩
    rcases hop with h | h | rfl | ⟨_, hn⟩
    · exact (hi (Or.inl h)).elim
    · exact (hi (Or.inr h)).elim
    · obtain ⟨l, a, ha⟩ := hW i
      obtain ⟨r, c, hc⟩ := hW j
      refine ⟨l + r, fun z => 1 + a z + c z, fun z x => ?_⟩
      change bit ((GateOp.mod 2).eval [(W z x).getD i false, (W z x).getD j false]) = _
      rw [gateBit_mod2, ha, hc, LinearMap.add_apply]
      ring
    · simp at hn
  · simp only [List.length_cons] at hlen
    omega

private theorem gateBit_and2 (a b : Bool) :
    bit (GateOp.and.eval [a, b]) = bit a * bit b + 0 * (bit a + bit b) := by
  cases a <;> cases b <;> decide

private theorem gateBit_or2 (a b : Bool) :
    bit (GateOp.or.eval [a, b]) = bit a * bit b + 1 * (bit a + bit b) := by
  cases a <;> cases b <;> decide

private theorem gateBinary_cut {Z : Type*} {n : ℕ} {f g : Z → Vec (n + 1) → Bool}
    {v : Z → Vec (n + 1) → Bool} {ε : F}
    (hv : ∀ z x, bit (v z x) = bit (f z x) * bit (g z x) + ε * (bit (f z x) + bit (g z x)))
    (hf : IsAffine f) (hg : IsAffine g) :
    ∃ ℓ : Form (n + 1), ∃ c : Z → F, ℓ ≠ 0 ∧
      ∀ b : F, ∃ l : Form (n + 1), ∃ a : Z → F,
        ∀ z x, ℓ x + c z = b → bit (v z x) = l x + a z := by
  obtain ⟨l, a, ha⟩ := hf
  obtain ⟨r, c, hc⟩ := hg
  by_cases hl : l = 0
  · by_cases hr : r = 0
    · let p : Form (n + 1) := LinearMap.proj (0 : Fin (n + 1))
      have hp : p ≠ 0 := by
        intro h
        have he := DFunLike.congr_fun h (fun _ => (1 : F))
        have hf : (1 : F) = 0 := he
        exact one_ne_zero hf
      refine ⟨p, fun _ => 0, hp, fun _ => ⟨0, fun z => a z * c z + ε * (a z + c z), ?_⟩⟩
      intro z x _
      simp [hv, ha, hc, hl, hr]
    · refine ⟨r, c, hr, fun b => ⟨(b + ε) • l, fun z => a z * b + ε * (a z + b), ?_⟩⟩
      intro z x h
      rw [hv, ha, hc, h, LinearMap.smul_apply, smul_eq_mul]
      ring
  · refine ⟨l, a, hl, fun b => ⟨(b + ε) • r, fun z => b * c z + ε * (b + c z), ?_⟩⟩
    intro z x h
    rw [hv, ha, hc, h, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem gate_affine_on_cut {Z : Type*} {m : ℕ} {g : Gate} {W : Z → Vec (m + 1) → List Bool}
    (hc : charged g = true)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false)) :
    ∃ ℓ : Form (m + 1), ∃ c : Z → F, ℓ ≠ 0 ∧
      ∀ b : F, ∃ l : Form (m + 1), ∃ a : Z → F,
        ∀ z x, ℓ x + c z = b → bit (gateValue g W z x) = l x + a z := by
  obtain ⟨hop, hlen⟩ := (charged_eq_true g).1 hc
  rcases g with ⟨op, inputs⟩
  change op = .and ∨ op = .or at hop
  change inputs.length = 2 at hlen
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · rcases hop with rfl | rfl
    · exact gateBinary_cut (fun z x => gateBit_and2 _ _) (hW i) (hW j)
    · exact gateBinary_cut (fun z x => gateBit_or2 _ _) (hW i) (hW j)
  · simp only [List.length_cons] at hlen
    omega

theorem wires_extend {Z : Type*} {m n : ℕ} {W : Z → Vec m → List Bool}
    {v : Z → Vec m → Bool} (hlen : ∀ z x, (W z x).length = n)
    (hW : ∀ i : ℕ, IsAffine (fun z x => (W z x).getD i false))
    (hv : IsAffine v) (i : ℕ) :
    IsAffine (fun z x => (W z x ++ [v z x]).getD i false) := by
  by_cases hi : i < n
  · have h : (fun z x => (W z x ++ [v z x]).getD i false) =
        (fun z x => (W z x).getD i false) := by
      funext z x
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa [hlen] using hi)]
    simpa only [h] using hW i
  · by_cases he : i = n
    · subst i
      have h : (fun z x => (W z x ++ [v z x]).getD n false) = v := by
        funext z x
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen])]
        simp [hlen]
      simpa only [h] using hv
    · have h : (fun z x => (W z x ++ [v z x]).getD i false) = (fun _ _ => false) := by
        funext z x
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hlen]; omega)]
        rfl
      rw [h]
      exact gateAffine_const (fun _ => false)

private theorem cut_pivot {m : ℕ} (ℓ : Form (m + 1)) (hℓ : ℓ ≠ 0) :
    ∃ j : Fin (m + 1), ℓ (Pi.single j 1) = 1 := by
  by_contra! h
  apply hℓ
  apply LinearMap.pi_ext
  intro j a
  have hj : ℓ (Pi.single j 1) = 0 := by
    exact (show ∀ t : F, t ≠ 1 → t = 0 by decide) _ (h j)
  have ha : (Pi.single j a : Vec (m + 1)) = a • Pi.single j 1 := by
    ext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Pi.single_eq_of_ne hi]
  rw [ha, map_smul, hj, smul_zero, LinearMap.zero_apply]

theorem cut_exists_split {m : ℕ} (ℓ : Form (m + 1)) (hℓ : ℓ ≠ 0) :
    ∃ E : (F × Vec m) ≃ₗ[F] Vec (m + 1), ∀ e x, ℓ (E (e, x)) = e := by
  classical
  obtain ⟨j, hj⟩ := cut_pivot ℓ hℓ
  let w : Vec (m + 1) := Pi.single j 1
  change ℓ w = 1 at hj
  let u := finSuccAboveEquiv j
  let drop : Vec (m + 1) →ₗ[F] Vec m :=
    { toFun := fun v i => v (u i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p := ℓ.prod drop
  have hdw : drop w = 0 := by
    ext i
    exact Pi.single_eq_of_ne (u i).2 _
  have hinj : Function.Injective p := by
    intro x y hxy
    have hl : ℓ x = ℓ y := congrArg Prod.fst hxy
    have hd : drop x = drop y := congrArg Prod.snd hxy
    have hxy' : x - y = (x j - y j) • w := by
      ext i
      by_cases hi : i = j
      · subst i
        simp [w]
      · have he : x i = y i := by
          have h := congrFun hd (u.symm ⟨i, hi⟩)
          change x (u (u.symm ⟨i, hi⟩)).1 = y (u (u.symm ⟨i, hi⟩)).1 at h
          simpa only [Equiv.apply_symm_apply] using h
        simp [w, Pi.single_eq_of_ne hi, he]
    have hs := congrArg ℓ hxy'
    simp [map_sub, hl, hj] at hs
    apply sub_eq_zero.mp
    rw [hxy', ← hs, zero_smul]
  have hsurj : Function.Surjective p := by
    rintro ⟨e, x⟩
    let base : Vec (m + 1) := fun i => if hi : i = j then 0 else x (u.symm ⟨i, hi⟩)
    have hbase : drop base = x := by
      ext i
      change base (u i).1 = x i
      simp [base, dite_eq_right (u i).2]
    refine ⟨base + (e - ℓ base) • w, Prod.ext ?_ ?_⟩
    · change ℓ (base + (e - ℓ base) • w) = e
      simp [hj]
    · change drop (base + (e - ℓ base) • w) = x
      simp [hdw, hbase]
  let E := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩
  refine ⟨E.symm, fun e x => ?_⟩
  exact congrArg Prod.fst (E.apply_symm_apply (e, x))

private def walshSign (x : F) : ℤ := if x = 0 then 1 else -1

private theorem walshSign_add_one (x : F) : walshSign (x + 1) = -walshSign x := by
  fin_cases x <;> decide

private theorem walshSign_agreement (q : Bool) (x : F) :
    walshSign (bit q - x) = (if q = decide (x = 1) then 2 else 0) - 1 := by
  cases q <;> fin_cases x <;> decide

private theorem walshSign_natAbs (x : F) : (walshSign x).natAbs = 1 := by
  fin_cases x <;> decide

private theorem walsh_eq_agreement {k : ℕ} (f : Vec k → Bool) (v : Vec k) :
    (∑ x : Vec k, walshSign (bit (f x) - dotProduct v x)) =
    2 * ((((Finset.univ : Finset (Vec k)).filter
      (fun x => f x = decide (dotProduct v x = 1))).card : ℕ) : ℤ) - (2:ℤ)^k := by
  simp_rw [walshSign_agreement]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp [ZMod.card, mul_comm]

open Classical in
private theorem walshSign_sum {m : ℕ} (g : Form m) (c : F) :
    (∑ y : Vec m, walshSign (c + g y)).natAbs = if g = 0 then 2^m else 0 := by
  classical
  by_cases hg : g = 0
  · simp [hg, ZMod.card, Int.natAbs_mul, walshSign_natAbs]
  · rw [ite_eq_right hg]
    have hex : ∃ w : Vec m, g w ≠ 0 := by
      by_contra! h
      exact hg (LinearMap.ext fun x => h x)
    obtain ⟨w, hw⟩ := hex
    have hw' : g w = 1 := by
      have h01 (x : F) : x = 0 ∨ x = 1 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h01 (g w) with h | h
      · exact (hw h).elim
      · exact h
    have h := Equiv.sum_comp (Equiv.addRight w) fun y : Vec m => walshSign (c + g y)
    change (∑ y : Vec m, walshSign (c + g (y + w))) =
      ∑ y : Vec m, walshSign (c + g y) at h
    simp_rw [map_add, hw', ← add_assoc, walshSign_add_one, Finset.sum_neg_distrib] at h
    have hz : (∑ y : Vec m, walshSign (c + g y)) = 0 := by omega
    simp [hz]

private def walshRestriction {k m : ℕ} (L : Vec m →ₗ[F] Vec k) : Vec k →ₗ[F] Form m :=
  (Module.Dual.transpose L).comp (dotProductEquiv F (Fin k)).toLinearMap

private theorem walshRestriction_apply {k m : ℕ} (L : Vec m →ₗ[F] Vec k)
    (v : Vec k) (y : Vec m) : walshRestriction L v y = dotProduct v (L y) := rfl

private theorem walshRestriction_surjective {k m : ℕ} (L : Vec m →ₗ[F] Vec k)
    (R : Vec k →ₗ[F] Vec m) (hRL : Function.LeftInverse R L) :
    Function.Surjective (walshRestriction L) := by
  intro ℓ
  refine ⟨(dotProductEquiv F (Fin k)).symm (ℓ.comp R), ?_⟩
  apply LinearMap.ext
  intro y
  rw [walshRestriction_apply]
  change dotProductEquiv F (Fin k) ((dotProductEquiv F (Fin k)).symm (ℓ.comp R)) (L y) = ℓ y
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, hRL y]

private theorem walshRestriction_ker_finrank {k b : ℕ} (hb : b ≤ k)
    (L : Vec (k-b) →ₗ[F] Vec k) (R : Vec k →ₗ[F] Vec (k-b))
    (hRL : Function.LeftInverse R L) : Module.finrank F (LinearMap.ker (walshRestriction L)) = b := by
  have hdim (n : ℕ) : Module.finrank F (Vec n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h := (walshRestriction L).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (walshRestriction_surjective L R hRL), finrank_top,
    ← (dotProductEquiv F (Fin (k-b))).finrank_eq, hdim, hdim] at h
  omega

theorem walshCover {k b : ℕ} {Z : Type*} (hb : b ≤ k) (f : Z → Vec k → Bool)
    (L : Fin (2^b) → Vec (k-b) →ₗ[F] Vec k)
    (R : Fin (2^b) → Vec k →ₗ[F] Vec (k-b))
    (hRL : ∀ i, Function.LeftInverse (R i) (L i))
    (p : Fin (2^b) → Z → Vec k) (ℓ : Fin (2^b) → Form (k-b))
    (a : Fin (2^b) → Z → F)
    (hf : ∀ i z y, bit (f z (p i z + L i y)) = ℓ i y + a i z)
    (hsum : ∀ z (h : Vec k → ℤ), ∑ x, h x = ∑ i, ∑ y, h (p i z + L i y)) :
    ∃ (D : Fin (2^b) → Submodule F (Vec k)) (aa : Fin (2^b) → Vec k),
      (∀ i, Module.finrank F (D i) = b) ∧
      ∀ z v,
        let H := ((Finset.univ : Finset (Vec k)).filter
          (fun x => f z x = decide (dotProduct v x = 1))).card
        2^b * (2 * (H : ℤ) - (2:ℤ)^k).natAbs ≤
          2^k * ((Finset.univ : Finset (Fin (2^b))).filter
            (fun i => @decide (v-aa i ∈ D i) (Classical.propDecidable _))).card := by
  classical
  choose aa haa using fun i => walshRestriction_surjective (L i) (R i) (hRL i) (ℓ i)
  refine ⟨fun i => LinearMap.ker (walshRestriction (L i)), aa,
    fun i => walshRestriction_ker_finrank hb (L i) (R i) (hRL i), ?_⟩
  intro z v
  dsimp only
  rw [← walsh_eq_agreement (f z) v, hsum z]
  let W (i : Fin (2^b)) : ℤ :=
    ∑ y, walshSign (bit (f z (p i z + L i y)) - dotProduct v (p i z + L i y))
  change 2^b * (∑ i, W i).natAbs ≤ _
  have hW (i : Fin (2^b)) : (W i).natAbs =
      if v - aa i ∈ LinearMap.ker (walshRestriction (L i)) then 2^(k-b) else 0 := by
    have hterm (y : Vec (k-b)) :
        bit (f z (p i z + L i y)) - dotProduct v (p i z + L i y) =
          (a i z - dotProduct v (p i z)) + (ℓ i - walshRestriction (L i) v) y := by
      rw [hf, dotProduct_add, LinearMap.sub_apply, walshRestriction_apply]
      abel
    simp_rw [W, hterm, walshSign_sum]
    have hc : ℓ i - walshRestriction (L i) v = 0 ↔
        v - aa i ∈ LinearMap.ker (walshRestriction (L i)) := by
      rw [LinearMap.mem_ker, map_sub, haa, sub_eq_zero, sub_eq_zero]
      exact eq_comm
    simp only [hc]
  have hbound : (∑ i, W i).natAbs ≤ ∑ i, (W i).natAbs := by
    exact Int.natAbs_sum_le _ _
  refine (Nat.mul_le_mul_left _ hbound).trans_eq ?_
  simp_rw [hW, decide_eq_true_eq]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm _ (2^(k-b)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le hb]
  rfl

private structure Frame (k : ℕ) (Z : Type) (m : ℕ) where
  linear : Vec m →ₗ[F] Vec k
  retract : Vec k →ₗ[F] Vec m
  left_inv : Function.LeftInverse retract linear
  offset : Z → Vec k

private def Frame.point (T : Frame k Z m) (z : Z) (x : Vec m) : Vec k :=
  T.offset z + T.linear x

private def cutLinear (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) : Vec m →ₗ[F] Vec (m+1) :=
  E.toLinearMap.comp (LinearMap.inr F F (Vec m))

private theorem split_add (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (a : F) (x : Vec m) :
    E (a,x) = E (a,0) + E (0,x) := by
  rw [← map_add]
  simp

private def Frame.cut (T : Frame k Z (m+1)) (E : (F × Vec m) ≃ₗ[F] Vec (m+1))
    (c : Z → F) (e : F) : Frame k Z m where
  linear := T.linear.comp (cutLinear E)
  retract := (LinearMap.snd F F (Vec m)).comp (E.symm.toLinearMap.comp T.retract)
  left_inv := by
    intro x
    change (E.symm (T.retract (T.linear (E (0,x))))).2 = x
    rw [T.left_inv,E.symm_apply_apply]
  offset z := T.offset z + T.linear (E (e+c z,0))

private theorem Frame.cut_point (T : Frame k Z (m+1)) (E : (F × Vec m) ≃ₗ[F] Vec (m+1))
    (c : Z → F) (e : F) (z : Z) (x : Vec m) :
    (T.cut E c e).point z x = T.point z (E (e+c z,x)) := by
  change T.offset z + T.linear (E (e+c z,0)) + T.linear (E (0,x)) = _
  simp only [Frame.point, split_add E (e+c z) x, map_add, add_assoc]

private theorem sum_cut (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (a : F)
    (f : Vec (m+1) → ℤ) :
    (∑ q, f q) = ∑ e : F, ∑ x : Vec m, f (E (e+a,x)) := by
  let Q := (Equiv.prodCongr (Equiv.addRight a) (Equiv.refl (Vec m))).trans E.toEquiv
  rw [← Equiv.sum_comp Q f]
  rw [Fintype.sum_prod_type]
  rfl

private def consEquiv (m : ℕ) : F × Vec m ≃ Vec (m+1) where
  toFun p := Fin.cons p.1 p.2
  invFun q := (q 0, Fin.tail q)
  left_inv p := by simp
  right_inv q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem sum_cons (f : Vec (m+1) → ℤ) :
    (∑ q, f q) = ∑ e : F, ∑ x : Vec m, f (Fin.cons e x) := by
  rw [← Equiv.sum_comp (consEquiv m) f, Fintype.sum_prod_type]
  rfl

private theorem affine_reparam (E : (F × Vec m) ≃ₗ[F] Vec (m+1)) (c : Z → F)
    (e : F) (l : Form (m+1)) (a : Z → F)
    (f : Z → Vec (m+1) → Bool)
    (h : ∀ z y, bit (f z (E (e+c z,y))) = l (E (e+c z,y)) + a z) :
    IsAffine (fun z y => f z (E (e+c z,y))) := by
  refine ⟨l.comp (cutLinear E),fun z => l (E (e+c z,0)) + a z, ?_⟩
  intro z y
  rw [h,split_add E (e+c z) y,map_add]
  change l (E (e+c z,0)) + l (E (0,y)) + a z = l (E (0,y)) + (l (E (e+c z,0)) + a z)
  ac_rfl

private def step (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def finalValue (gs : List Gate) (W : Z → Vec k → List Bool)
    (out : ℕ) (z : Z) (x : Vec k) : Bool :=
  (gs.foldl (fun w g => step g w) (W z x)).getD out false

private structure Cell (k : ℕ) (Z : Type) (m : ℕ) extends Frame k Z m where
  slope : Form m
  phase : Z → F

private theorem partition (gs : List Gate) (hg : ∀ g ∈ gs, goodGate g)
    (s : ℕ) (hs : gs.countP charged = s) (T : Frame k Z (m+s))
    (W : Z → Vec k → List Bool) (out n : ℕ) (hwlength : ∀ z x, (W z x).length = n)
    (hwaffine : ∀ i : ℕ, IsAffine (fun z x => (W z (T.point z x)).getD i false)) :
    ∃ cells : Vec s → Cell k Z m,
      (∀ i z x, bit (finalValue gs W out z ((cells i).toFrame.point z x)) =
        (cells i).slope x + (cells i).phase z) ∧
      ∀ z (f : Vec k → ℤ),
        (∑ x, f (T.point z x)) = ∑ i, ∑ x, f ((cells i).toFrame.point z x) := by
  induction gs generalizing s n W out with
  | nil =>
      have hzero : s = 0 := by simpa using hs.symm
      clear hs
      subst s
      obtain ⟨l,a,ha⟩ := hwaffine out
      refine ⟨fun _ => ⟨T,l,a⟩, ?_, ?_⟩
      · intro i z x
        exact ha z x
      · intro z f
        have hcard : Fintype.card (Vec 0) = 1 := by simp [Vec,F]
        change (∑ x, f (T.point z x)) = ∑ _ : Vec 0, ∑ x, f (T.point z x)
        simp only [Finset.sum_const,Finset.card_univ,hcard,one_nsmul]
  | cons g gs ih =>
      have hgate := hg g (by simp)
      have hgs (a : Gate) (ha : a ∈ gs) := hg a (by simp [ha])
      let W' z x := step g (W z x)
      have hW' (z : Z) (x : Vec k) : (W' z x).length = n+1 := by
        simp [W',step,hwlength]
      cases hch : charged g
      · have hs' : gs.countP charged = s := by simpa [List.countP_cons,hch] using hs
        let localW := fun z x => W z (T.point z x)
        have ha := gate_affine (g := g) (W := localW) hgate hch hwaffine
        have hall : ∀ i, IsAffine (fun z x => (W' z (T.point z x)).getD i false) :=
          fun i => wires_extend (W := localW) (fun z x => hwlength z _) hwaffine ha i
        obtain ⟨cells,hcells,hsum⟩ := ih hgs s hs' T W' out (n+1) hW' hall
        exact ⟨cells,hcells,hsum⟩
      · have hs' : gs.countP charged + 1 = s := by simpa [List.countP_cons,hch] using hs
        cases s with
        | zero => omega
        | succ s =>
          have htail : gs.countP charged = s := by omega
          let localW := fun z x => W z (T.point z x)
          obtain ⟨l,c,hl,hcut⟩ := gate_affine_on_cut (g := g) (W := localW) hch hwaffine
          obtain ⟨E,hE⟩ := cut_exists_split l hl
          let C (e : F) := T.cut E c e
          have hchild (e : F) :
              ∀ i, IsAffine (fun z x => (W' z ((C e).point z x)).getD i false) := by
            let childW := fun z x => W z ((C e).point z x)
            have ha (i : ℕ) : IsAffine (fun z x => (childW z x).getD i false) := by
              obtain ⟨l,a,ha⟩ := hwaffine i
              have hv := affine_reparam E c e l a
                (fun z x => (W z (T.point z x)).getD i false) (fun z y => ha z _)
              simpa only [childW,C,Frame.cut_point] using hv
            obtain ⟨l',a',hcut'⟩ := hcut e
            have hv := affine_reparam E c e l' a' (gateValue g localW) (by
              intro z y
              apply hcut'
              rw [hE]
              exact (by decide : ∀ x y : F, x+y+y=x) _ _)
            have hb : IsAffine (gateValue g childW) := by
              change IsAffine (fun z y => gateValue g childW z y)
              simpa only [gateValue,childW,C,Frame.cut_point,localW] using hv
            exact wires_extend (W := childW) (fun z x => hwlength z _) ha hb
          have hbranch (e : F) := ih hgs s htail (C e) W' out (n+1) hW' (hchild e)
          choose cells he hsum using hbranch
          refine ⟨(fun i : Vec (s+1) => cells (i 0) (Fin.tail i)),?_,?_⟩
          · intro i z x
            exact he _ _ z x
          · intro z f
            calc
              (∑ x, f (T.point z x)) =
                  ∑ e : F, ∑ x, f ((C e).point z x) := by
                erw [sum_cut E (c z) (fun x => f (T.point z x))]
                apply Finset.sum_congr rfl
                intro e _
                apply Finset.sum_congr rfl
                intro x _
                rw [show (C e).point z x = T.point z (E (e+c z,x)) from T.cut_point E c e z x]
              _ = ∑ e : F, ∑ i : Vec s, ∑ x, f ((cells e i).toFrame.point z x) := by
                exact Finset.sum_congr rfl fun e _ => hsum e z f
              _ = ∑ i : Vec (s+1), ∑ x, f ((cells (i 0) (Fin.tail i)).toFrame.point z x) := by
                rw [sum_cons]
                simp

private def inputs (z : Fin t → Bool) (x : Vec k) : List Bool :=
  List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z

private theorem bit_decide (x : F) : bit (decide (x = 1)) = x :=
  (by decide : ∀ y : F, bit (decide (y = 1)) = y) x

private theorem inputs_affine {k t : ℕ} (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) (x : Vec k) => (inputs z x).getD i false) := by
  by_cases hi : i < k
  · refine ⟨LinearMap.proj ⟨i,hi⟩,fun _ => 0,?_⟩
    intro z x
    change bit ((inputs z x).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_ofFn, dif_pos hi, Option.getD_some, bit_decide,
      LinearMap.proj_apply, add_zero]
  · refine ⟨0,fun z => bit ((List.ofFn z).getD (i-k) false),?_⟩
    intro z x
    change bit ((inputs z x).getD i false) = _
    rw [inputs,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]

private def standard (h : m = k) : Frame k Z m := by
  subst m
  exact ⟨LinearMap.id,LinearMap.id,fun _ => rfl,fun _ => 0⟩

private theorem standard_affine {m k t : ℕ} (h : m = k) (i : ℕ) :
    IsAffine (fun (z : Fin t → Bool) x => (inputs z ((standard h).point z x)).getD i false) := by
  subst m
  simpa [standard,Frame.point] using inputs_affine (k := k) (t := t) i

private theorem standard_sum {m k : ℕ} {Z : Type} (h : m = k) (z : Z) (f : Vec k → ℤ) :
    (∑ x, f ((standard h).point z x)) = ∑ x, f x := by
  subst m
  simp [standard,Frame.point]

private def boundAt (b : ℕ) (f : Z → Vec k → Bool) : Prop :=
  ∃ (D : Fin (2^b) → Submodule F (Vec k)) (a : Fin (2^b) → Vec k),
    (∀ i, Module.finrank F (D i) = b) ∧
    ∀ z v,
      let H := ((Finset.univ : Finset (Vec k)).filter (fun x =>
        f z x = decide (dotProduct v x = 1))).card
      2^b * (2*(H : ℤ)-(2:ℤ)^k).natAbs ≤
        2^k * ((Finset.univ : Finset (Fin (2^b))).filter (fun l =>
          @decide (v-a l ∈ D l) (Classical.propDecidable _))).card

private theorem fullCover (f : Z → Vec k → Bool) : boundAt k f := by
  classical
  refine ⟨fun _ => ⊤,fun _ => 0,fun i => ?_,?_⟩
  · rw [finrank_top, Module.finrank_fin_fun]
  · intro z v
    dsimp only
    rw [← walsh_eq_agreement (f z) v]
    have h : (∑ x : Vec k, walshSign (bit (f z x) - dotProduct v x)).natAbs ≤ 2^k := by
      calc
        _ ≤ ∑ x : Vec k, (walshSign (bit (f z x) - dotProduct v x)).natAbs :=
          Int.natAbs_sum_le _ _
        _ = _ := by simp [walshSign_natAbs,ZMod.card]
    simpa [Submodule.mem_top, Fintype.card_fin] using Nat.mul_le_mul_left (2^k) h

private theorem circuit_cover {k t s : ℕ} (C : Circuit) (hs : C.gates.countP charged = s)
    (hle : s ≤ k) (hgood : ∀ g ∈ C.gates, goodGate g) :
    boundAt s (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x)) := by
  classical
  let m := k-s
  have hm : m+s=k := Nat.sub_add_cancel hle
  let T : Frame k (Fin t → Bool) (m+s) := standard hm
  obtain ⟨C₀,hC,hsum⟩ := partition C.gates hgood s hs T inputs C.output (k+t)
    (by intro z x; simp [inputs]) (fun i => standard_affine hm i)
  let ind : Vec s ≃ Fin (2^s) := Fintype.equivFinOfCardEq (by simp [Vec,F,ZMod.card])
  let C₁ (j : Fin (2^s)) := C₀ (ind.symm j)
  apply walshCover hle (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x))
    (fun i => (C₁ i).linear) (fun i => (C₁ i).retract) (fun i => (C₁ i).left_inv)
    (fun i => (C₁ i).offset) (fun i => (C₁ i).slope) (fun i => (C₁ i).phase)
  · intro i z y
    exact hC (ind.symm i) z y
  · intro z f
    calc
      (∑ x, f x) = ∑ x, f (T.point z x) := (standard_sum hm z f).symm
      _ = ∑ i, ∑ x, f ((C₀ i).toFrame.point z x) := hsum z f
      _ = ∑ i : Fin (2^s), ∑ x, f ((C₁ i).toFrame.point z x) :=
        (Equiv.sum_comp ind.symm _).symm

end PEqualNP.Outside.L_lib_817_aux

open PEqualNP.Outside.L_lib_817_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_lib_817 : (∀ (k t : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  let Z := Fin t → Bool
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) →
    let s := C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let b := min s k
    let I := Fin (2^b)
    ∃ (D : I → Submodule F V) (a : I → V), (∀ i, Module.finrank F (D i) = b) ∧
      ∀ (z : Z) (v : V),
        let H := ((Finset.univ : Finset V).filter (fun x =>
          C.eval (List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z) =
            decide (dotProduct v x = 1))).card
        2^b * (2*(H : ℤ)-(2:ℤ)^k).natAbs ≤
          2^k * ((Finset.univ : Finset I).filter (fun l =>
            @decide (v-a l ∈ D l) (Classical.propDecidable _))).card) := by

  classical
  intro k t
  dsimp only
  intro C _hread hgood
  change boundAt (min (C.gates.countP charged) k)
    (fun (z : Fin t → Bool) (x : Vec k) => C.eval (inputs z x))
  by_cases h : C.gates.countP charged ≤ k
  · rw [Nat.min_eq_left h]
    exact circuit_cover C rfl h hgood
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact fullCover _

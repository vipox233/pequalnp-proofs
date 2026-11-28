import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1082

open Finset
open scoped BigOperators

abbrev F2 := ZMod 2

lemma z2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> rfl

lemma z2_one_add_one : (1 : F2) + 1 = 0 := by decide

lemma z2_one_ne_zero : (1 : F2) ≠ 0 := by decide

lemma z2_two_eq_zero : (2 : F2) = 0 := by decide

lemma z2_four_eq_zero : (4 : F2) = 0 := by decide

lemma card_z2_zero_prod : Fintype.card {p : F2 × F2 // p.1 * p.2 = 0} = 3 := by decide

lemma fin3_one_ne_zero : (1 : Fin 3) ≠ 0 := by decide

lemma fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide

lemma fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide

def ix {t : ℕ} (ht : 0 < t) (j : ℕ) : Fin (3 * t) :=
  ⟨j % (3 * t), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩

def nxt {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : Fin (3 * t) :=
  ix ht (i.val + 1)

def prv {t : ℕ} (i : Fin (3 * t)) : Fin (3 * t) :=
  ⟨if i.val = 0 then 3 * t - 1 else i.val - 1, by have := i.isLt; split_ifs <;> omega⟩

def revIdx {t : ℕ} (i : Fin (3 * t)) : Fin (3 * t) :=
  ⟨3 * t - 1 - i.val, by have := i.isLt; omega⟩

abbrev codeP (t : ℕ) (x : Fin (3 * t) → F2) : Prop :=
  ∀ e : Fin 2, (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0

def suppF {t : ℕ} (x : Fin (3 * t) → F2) : Finset (Fin (3 * t)) :=
  Finset.univ.filter (fun i => x i ≠ 0)

def nbrF {t : ℕ} (x : Fin (3 * t) → F2) : Finset (Fin (3 * t)) :=
  suppF x ∪ (suppF x).image prv

def dualDrop {t : ℕ} (S : Finset (Fin (3 * t))) : ℕ :=
  if S = Finset.univ then 2
  else if ∃ r : Fin 3, ∀ i : Fin (3 * t), i.val % 3 ≠ r.val → i ∈ S then 1
  else 0

def rkC {t : ℕ} (S : Finset (Fin (3 * t))) : ℕ := S.card - dualDrop S

def tripVec {t : ℕ} (ht : 0 < t) (s : Fin (3 * t)) : Fin (3 * t) → F2 :=
  fun i => if i = s ∨ i = nxt ht s ∨ i = nxt ht (nxt ht s) then 1 else 0

def wt8 (r : ℕ) : ℕ := if r ≤ 8 then 2 ^ (8 - r) else 1

lemma dec_t2_top_sum :
    (∑ f : Fin 3 → F2,
      256 / 2 ^ rkC (nbrF (fun i : Fin (3 * 2) => f ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩))) = 416 := by
  decide

def top3Vec (s : Fin 9) (f : Fin 3 → F2) (i : Fin 9) : F2 :=
  if i = s then f 0 else if i = ix (by decide : 0 < 3) (s.val + 3) then f 1
  else if i = ix (by decide : 0 < 3) (s.val + 6) then f 0 + f 1 + f 2
  else if i = ix (by decide : 0 < 3) (s.val + 1) then f 2
  else if i = ix (by decide : 0 < 3) (s.val + 2) then f 2 else 0

def top3Read (s : Fin 9) (x : Fin 9 → F2) : Fin 3 → F2 :=
  ![x s, x (ix (by decide : 0 < 3) (s.val + 3)), x (ix (by decide : 0 < 3) (s.val + 1))]

abbrev top3Word (s : Fin 9) (x : Fin 9 → F2) : Prop :=
  codeP 3 x ∧ ∀ i, x i ≠ 0 → i.val % 3 = s.val % 3 ∨
    i = ix (by decide : 0 < 3) (s.val + 1) ∨ i = ix (by decide : 0 < 3) (s.val + 2)

lemma top3_encode : ∀ s f, top3Word s (top3Vec s f) ∧ top3Read s (top3Vec s f) = f := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
lemma top3_decode : ∀ s x, top3Word s x → top3Vec s (top3Read s x) = x := by
  decide

def threeTrip (a b c : Fin 9) (f : Fin 3 → F2) : Fin 9 → F2 :=
  f 0 • tripVec (by decide : 0 < 3) a + f 1 • tripVec (by decide : 0 < 3) b +
    f 2 • tripVec (by decide : 0 < 3) c

def maskWord (m : BitVec 9) (i : Fin 9) : F2 := if m.getLsbD i.val then 1 else 0

def maskTerm (s : Fin 9) (z : F2) : BitVec 9 :=
  if z = 0 then 0 else (7 : BitVec 9).rotateLeft s.val

lemma maskTerm_word : ∀ s z, maskWord (maskTerm s z) = z • tripVec (by decide : 0 < 3) s := by
  decide

lemma maskWord_xor (a b : BitVec 9) : maskWord (a ^^^ b) = maskWord a + maskWord b := by
  funext i
  simp only [maskWord, BitVec.getLsbD_xor, Pi.add_apply]
  cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> rfl

def maskWeight (x : BitVec 9) : ℕ :=
  let n := x ||| x.rotateRight 1
  let drop := if n = 511 then 2 else if n &&& 438 = 438 ∨ n &&& 365 = 365 ∨ n &&& 219 = 219 then 1 else 0
  wt8 (n.cpop.toNat - drop)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
lemma maskWeight_spec : ∀ x, maskWeight x = wt8 (rkC (nbrF (t := 3) (maskWord x))) := by
  decide

def tripleMask (a b c : Fin 9) (f : Fin 3 → F2) :=
  maskTerm a (f 0) ^^^ maskTerm b (f 1) ^^^ maskTerm c (f 2)

lemma tripleMask_spec (a b c : Fin 9) (f : Fin 3 → F2) :
    maskWord (tripleMask a b c f) = threeTrip a b c f := by
  simp only [tripleMask, maskWord_xor, maskTerm_word, threeTrip]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
lemma tripleMask_bound : ∀ a b c : Fin 9, a ≠ b ∧ a ≠ c ∧ b ≠ c →
    (∑ f ∈ (Finset.univ : Finset (Fin 3 → F2)).erase 0, maskWeight (tripleMask a b c f)) ≤ 88 := by
  decide

lemma threeTrip_bound (a b c : Fin 9) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (∑ f ∈ (Finset.univ : Finset (Fin 3 → F2)).erase 0, wt8 (rkC (nbrF (t := 3) (threeTrip a b c f)))) ≤ 88 := by
  simpa only [maskWeight_spec, tripleMask_spec] using tripleMask_bound a b c h

def fiveMask (a b c d e : Fin 9) (f : Fin 5 → F2) :=
  maskTerm a (f 0) ^^^ (maskTerm b (f 1) ^^^ (maskTerm c (f 2) ^^^ (maskTerm d (f 3) ^^^ maskTerm e (f 4))))

lemma fiveMask_spec (a b c d e : Fin 9) (f : Fin 5 → F2) :
    maskWord (fiveMask a b c d e f) = ∑ j : Fin 5, f j • tripVec (by decide : 0 < 3) (![a,b,c,d,e] j) := by
  simp [fiveMask, maskWord_xor, maskTerm_word, Fin.sum_univ_succ]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
lemma fiveMask_bound : ∀ a b c d e : Fin 9, a < b ∧ b < c ∧ c < d ∧ d < e →
    (∑ f ∈ (Finset.univ : Finset (Fin 5 → F2)).erase 0, maskWeight (fiveMask a b c d e f)) ≤ 280 := by
  decide

lemma fiveTrip_bound (a b c d e : Fin 9) (h : a < b ∧ b < c ∧ c < d ∧ d < e) :
    (∑ f ∈ (Finset.univ : Finset (Fin 5 → F2)).erase 0,
      wt8 (rkC (nbrF (t := 3) (∑ j : Fin 5, f j • tripVec (by decide : 0 < 3) (![a,b,c,d,e] j))))) ≤ 280 := by
  simpa only [maskWeight_spec, fiveMask_spec] using fiveMask_bound a b c d e h

lemma top3_remainder : ∀ (s : Fin 9) (f : Fin 3 → F2),
    let x := top3Vec s f + f 2 • tripVec (by decide : 0 < 3) s
    (∀ i, i.val % 3 ≠ s.val % 3 → x i = 0) ∧ (∑ i, x i) = 0 := by
  decide

lemma dec_t3_top_sum (ht : 0 < 3) (s0 : Fin (3 * 3)) :
    (∑ f : Fin 3 → F2, 256 / 2 ^ rkC (nbrF (fun i : Fin (3 * 3) =>
      if i = s0 then f 0
      else if i = ix ht (s0.val + 3) then f 1
      else if i = ix ht (s0.val + 6) then f 0 + f 1 + f 2
      else if i = ix ht (s0.val + 1) then f 2
      else if i = ix ht (s0.val + 2) then f 2
      else 0))) = 348 := by
  revert ht s0; decide

lemma dec_t2_rk_all : ∀ x : Fin (3 * 2) → F2, codeP 2 x →
    (x = 0 ∧ rkC (nbrF x) = 0) ∨
    ((suppF x).card = 2 ∧ rkC (nbrF x) = 3) ∨
    (x ≠ 0 ∧ (suppF x).card ≠ 2 ∧ rkC (nbrF x) = 4) := by
  decide

lemma dec_t2_allPairs_card :
    (Finset.univ.filter (fun x : Fin (3 * 2) → F2 => codeP 2 x ∧ (suppF x).card = 2)).card = 3 := by
  decide

lemma dec_t2_pair0 : codeP 2 (fun i : Fin (3 * 2) => if i = 0 ∨ i = 3 then (1 : F2) else 0) ∧
    (suppF (fun i : Fin (3 * 2) => if i = 0 ∨ i = 3 then (1 : F2) else 0)).card = 2 := by
  decide

lemma dec_t2_pair1 : codeP 2 (fun i : Fin (3 * 2) => if i = 1 ∨ i = 4 then (1 : F2) else 0) ∧
    (suppF (fun i : Fin (3 * 2) => if i = 1 ∨ i = 4 then (1 : F2) else 0)).card = 2 := by
  decide

lemma dec_t2_pair2 : codeP 2 (fun i : Fin (3 * 2) => if i = 2 ∨ i = 5 then (1 : F2) else 0) ∧
    (suppF (fun i : Fin (3 * 2) => if i = 2 ∨ i = 5 then (1 : F2) else 0)).card = 2 := by
  decide

open Classical

lemma z2_eq_one_of_ne_zero {a : F2} (h : a ≠ 0) : a = 1 := by
  rcases z2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

lemma z2_sum_const_mod2 {ι : Type*} (s : Finset ι) :
    (∑ _i ∈ s, (1 : F2)) = (s.card : F2) := by
  simp

lemma z2_natCast_eq_zero_iff (k : ℕ) : (k : F2) = 0 ↔ k % 2 = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_iff_mod_eq_zero

lemma card_eq_two_pow_finrank {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] :
    Nat.card V = 2 ^ Module.finrank F2 V := by
  let b := Module.finBasis F2 V
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

lemma card_rows {X Y : Type*} [Fintype X] [Finite Y] (P : X → Y → Prop) :
    Nat.card {w : X × Y // P w.1 w.2} = ∑ x : X, Nat.card {y : Y // P x y} := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype P), Nat.card_sigma]

lemma card_fiber_of_surjective {X Y : Type*} [AddCommGroup X] [Module F2 X] [Finite X]
    [AddCommGroup Y] [Module F2 Y] [Finite Y]
    (φ : X →ₗ[F2] Y) (hsurj : Function.Surjective φ) (S : Y → Prop) :
    Nat.card {x : X // S (φ x)} * Nat.card Y = Nat.card {y : Y // S y} * Nat.card X := by
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype Y := Fintype.ofFinite Y
  have hfib : ∀ y : Y, Nat.card {x : X // φ x = y} = Nat.card (LinearMap.ker φ) := by
    intro y
    obtain ⟨x0, hx0⟩ := hsurj y
    refine Nat.card_congr ⟨
      fun x => ⟨x.1 - x0, by simp [LinearMap.mem_ker, x.2, hx0]⟩,
      fun k => ⟨k.1 + x0, by simp [LinearMap.mem_ker.mp k.2, hx0]⟩,
      fun x => by ext; simp,
      fun k => by ext; simp⟩
  have hS : Nat.card {x : X // S (φ x)} = Nat.card {y : Y // S y} * Nat.card (LinearMap.ker φ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfw := Finset.card_eq_sum_card_fiberwise (f := φ)
      (s := (Finset.univ : Finset X).filter (fun x => S (φ x)))
      (t := (Finset.univ : Finset Y).filter S)
      (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
    rw [hfw]
    have heach : ∀ y ∈ (Finset.univ : Finset Y).filter S,
        (((Finset.univ : Finset X).filter (fun x => S (φ x))).filter (fun x => φ x = y)).card =
          Nat.card (LinearMap.ker φ) := by
      intro y hy
      have hSy : S y := (Finset.mem_filter.mp hy).2
      have hfeq : ((Finset.univ : Finset X).filter (fun x => S (φ x))).filter (fun x => φ x = y) =
          (Finset.univ : Finset X).filter (fun x => φ x = y) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hSy, h⟩⟩
      rw [hfeq, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hfib y
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
  have hAll : Nat.card X = Nat.card Y * Nat.card (LinearMap.ker φ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hfw := Finset.card_eq_sum_card_fiberwise (f := φ)
      (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset Y))
      (fun _ _ => Finset.mem_univ _)
    rw [← Finset.card_univ, ← Finset.card_univ, hfw]
    have heach : ∀ y ∈ (Finset.univ : Finset Y),
        ((Finset.univ : Finset X).filter (fun x => φ x = y)).card = Nat.card (LinearMap.ker φ) := by
      intro y _
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hfib y
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
  rw [hS, hAll]
  ring

lemma exists_nonzero_dual_of_lt_top {E : Type*} [AddCommGroup E] [Module F2 E]
    [FiniteDimensional F2 E] {U : Submodule F2 E} (hU : U < ⊤) :
    ∃ ψ : E →ₗ[F2] F2, ψ ≠ 0 ∧ ∀ x ∈ U, ψ x = 0 := by
  obtain ⟨V, hUV⟩ := Submodule.exists_isCompl U
  have hVne : V ≠ ⊥ := by
    intro hV
    have : U = ⊤ := by simpa [hV] using hUV.sup_eq_top
    exact hU.ne this
  obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  let bV := Module.finBasis F2 V
  have hcomp : bV.repr ⟨v, hvV⟩ ≠ 0 := by
    intro h
    apply hv0
    have : (⟨v, hvV⟩ : V) = 0 := bV.repr.injective (by simp [h])
    exact congrArg Subtype.val this
  obtain ⟨i0, hi0⟩ : ∃ i0, bV.repr ⟨v, hvV⟩ i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hcomp (Finsupp.ext h)
  let pV : E →ₗ[F2] V := Submodule.linearProjOfIsCompl V U hUV.symm
  let ψ : E →ₗ[F2] F2 := (Finsupp.lapply i0).comp (bV.repr.toLinearMap.comp pV)
  refine ⟨ψ, ?_, ?_⟩
  · intro hψ
    have h1 : ψ v = 0 := by rw [hψ]; rfl
    have h2 : pV v = ⟨v, hvV⟩ := Submodule.linearProjOfIsCompl_apply_left hUV.symm ⟨v, hvV⟩
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2, Finsupp.lapply_apply] at h1
    exact hi0 h1
  · intro x hx
    have h2 : pV x = 0 := Submodule.linearProjOfIsCompl_apply_right hUV.symm ⟨x, hx⟩
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2, map_zero]

lemma pi_surjective_of_linearIndependent {X : Type*} [AddCommGroup X] [Module F2 X]
    [FiniteDimensional F2 X] {ι : Type*} [Fintype ι]
    (L : ι → (X →ₗ[F2] F2)) (hL : LinearIndependent F2 L) :
    Function.Surjective (LinearMap.pi L) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hlt : LinearMap.range (LinearMap.pi L) < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨ψ, hψ0, hψker⟩ := exists_nonzero_dual_of_lt_top hlt
  let c : ι → F2 := fun i => ψ (Pi.single i 1)
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hψ0
    refine LinearMap.ext fun u => ?_
    have hu : u = ∑ i : ι, u i • Pi.single i (1 : F2) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hu, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, show ψ (Pi.single i 1) = 0 from h i, smul_zero]
  have hsum : ∑ i : ι, c i • L i = 0 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    have hx := hψker (LinearMap.pi L x) ⟨x, rfl⟩
    have hpi : LinearMap.pi L x = ∑ i : ι, L i x • Pi.single i (1 : F2) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hpi, map_sum] at hx
    simpa [c, mul_comm] using hx
  have hzero := Fintype.linearIndependent_iff.mp hL c hsum
  obtain ⟨i, hi⟩ := hc0
  exact hi (hzero i)

lemma card_linear_constraint_bound {X Y : Type*} [AddCommGroup X] [Module F2 X]
    [FiniteDimensional F2 X] [Finite X] [AddCommGroup Y] [Module F2 Y] [FiniteDimensional F2 Y] [Finite Y]
    {k l : ℕ} (L : Fin k → (X →ₗ[F2] F2)) (M : Fin l → (Y →ₗ[F2] F2))
    (hL : LinearIndependent F2 L) (hM : LinearIndependent F2 M)
    (P : X → Y → Prop) (S : (Fin k → F2) → (Fin l → F2) → Prop)
    (hPS : ∀ x y, P x y → S (LinearMap.pi L x) (LinearMap.pi M y)) :
    Nat.card {w : X × Y // P w.1 w.2} * 2 ^ (k + l) ≤
      Nat.card {uv : (Fin k → F2) × (Fin l → F2) // S uv.1 uv.2} * (Nat.card X * Nat.card Y) := by
  let φ : X × Y →ₗ[F2] (Fin k → F2) × (Fin l → F2) :=
    LinearMap.prodMap (LinearMap.pi L) (LinearMap.pi M)
  have hsurj : Function.Surjective φ :=
    Function.Surjective.prodMap (pi_surjective_of_linearIndependent L hL)
      (pi_surjective_of_linearIndependent M hM)
  have hle : Nat.card {w : X × Y // P w.1 w.2} ≤ Nat.card {w : X × Y // S (φ w).1 (φ w).2} :=
    Nat.card_le_card_of_injective (fun w => ⟨w.1, hPS w.1.1 w.1.2 w.2⟩)
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  have heq := card_fiber_of_surjective φ hsurj (fun uv => S uv.1 uv.2)
  have hcardY : Nat.card ((Fin k → F2) × (Fin l → F2)) = 2 ^ (k + l) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin,
      pow_add]
  rw [hcardY, Nat.card_prod] at heq
  calc Nat.card {w : X × Y // P w.1 w.2} * 2 ^ (k + l)
      ≤ Nat.card {w : X × Y // S (φ w).1 (φ w).2} * 2 ^ (k + l) := Nat.mul_le_mul_right _ hle
    _ = Nat.card {uv : (Fin k → F2) × (Fin l → F2) // S uv.1 uv.2} * (Nat.card X * Nat.card Y) := heq

section lane_code

lemma nxt_val {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) :
    (nxt ht i).val = if i.val + 1 = 3 * t then 0 else i.val + 1 := by
  change (i.val + 1) % (3 * t) = _
  have hi := i.isLt
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma nxt_prv {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : nxt ht (prv i) = i := by
  apply Fin.ext
  rw [nxt_val]
  change (if (if i.val = 0 then 3 * t - 1 else i.val - 1) + 1 = 3 * t then 0
    else (if i.val = 0 then 3 * t - 1 else i.val - 1) + 1) = i.val
  have hi := i.isLt
  split_ifs <;> omega

lemma prv_nxt {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : prv (nxt ht i) = i := by
  apply Fin.ext
  change (if (nxt ht i).val = 0 then 3 * t - 1 else (nxt ht i).val - 1) = i.val
  rw [nxt_val]
  have hi := i.isLt
  by_cases h : i.val + 1 = 3 * t
  · simp [h]; omega
  · simp [h]

lemma prv_inj {t : ℕ} (ht : 0 < t) : Function.Injective (@prv t) :=
  fun a b h => by simpa [nxt_prv ht] using congrArg (nxt ht) h

lemma nxt_inj {t : ℕ} (ht : 0 < t) : Function.Injective (@nxt t ht) :=
  fun a b h => by simpa [prv_nxt ht] using congrArg prv h

lemma nxt_mod3 {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) :
    (nxt ht i).val % 3 = (i.val + 1) % 3 := by
  rw [nxt_val]
  have hi := i.isLt
  split_ifs with h
  · omega
  · rfl

lemma prv_mod3 {t : ℕ} (i : Fin (3 * t)) :
    (prv i).val % 3 = (i.val + 2) % 3 := by
  change (if i.val = 0 then 3 * t - 1 else i.val - 1) % 3 = (i.val + 2) % 3
  have hi := i.isLt
  split_ifs <;> omega

lemma prv_reach {t : ℕ} (i j : Fin (3 * t)) : ∃ k : ℕ, prv^[k] i = j := by
  have hi := i.isLt
  have hjlt := j.isLt
  have hdec : ∀ (d : ℕ) (a : Fin (3 * t)), d ≤ a.val → (prv^[d] a).val = a.val - d := by
    intro d
    induction d with
    | zero => intro a _; simp
    | succ d ih =>
      intro a hda
      rw [Function.iterate_succ_apply']
      have hprev := ih a (by omega)
      change (if (prv^[d] a).val = 0 then 3 * t - 1 else (prv^[d] a).val - 1) = _
      rw [hprev]
      split_ifs <;> omega
  let z0 : Fin (3 * t) := ⟨0, by omega⟩
  let ztop : Fin (3 * t) := ⟨3 * t - 1, by omega⟩
  have h0 : prv^[i.val] i = z0 := by
    apply Fin.ext; rw [hdec i.val i le_rfl]; dsimp [z0]; omega
  have htop : prv z0 = ztop := by
    apply Fin.ext; rfl
  have hj : prv^[3 * t - 1 - j.val] ztop = j := by
    apply Fin.ext
    rw [hdec (3 * t - 1 - j.val) ztop (by dsimp [ztop]; omega)]
    dsimp [ztop]; omega
  refine ⟨(3 * t - 1 - j.val) + (1 + i.val), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, h0]
  simp only [Function.iterate_one, htop, hj]

lemma revIdx_revIdx {t : ℕ} (i : Fin (3 * t)) : revIdx (revIdx i) = i := by
  apply Fin.ext
  change 3 * t - 1 - (3 * t - 1 - i.val) = i.val
  have hi := i.isLt
  omega

lemma revIdx_mod3 {t : ℕ} (i : Fin (3 * t)) :
    (revIdx i).val % 3 = 2 - i.val % 3 := by
  change (3 * t - 1 - i.val) % 3 = 2 - i.val % 3
  have hi := i.isLt
  omega

lemma revIdx_nxt {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) :
    revIdx (nxt ht i) = prv (revIdx i) := by
  apply Fin.ext
  change 3 * t - 1 - (nxt ht i).val =
    if 3 * t - 1 - i.val = 0 then 3 * t - 1 else (3 * t - 1 - i.val) - 1
  rw [nxt_val]
  have hi := i.isLt
  split_ifs <;> omega

def hitP {t : ℕ} (ht : 0 < t) (x y : Fin (3 * t) → F2) : Prop :=
  ∀ i : Fin (3 * t), x i * y i = 0 ∧ x (nxt ht i) * y i = 0

def checkMap (t : ℕ) : (Fin (3 * t) → F2) →ₗ[F2] (Fin 2 → F2) where
  toFun x e := ∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0
  map_add' x y := by
    ext e
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  map_smul' c x := by
    ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

def codeSub (t : ℕ) : Submodule F2 (Fin (3 * t) → F2) := LinearMap.ker (checkMap t)

lemma mem_codeSub {t : ℕ} {x : Fin (3 * t) → F2} : x ∈ codeSub t ↔ codeP t x := by
  simp only [codeSub, LinearMap.mem_ker, checkMap, LinearMap.coe_mk, AddHom.coe_mk, codeP]
  exact ⟨fun h e => congrFun h e, fun h => funext h⟩

def resSum (t : ℕ) (r : ℕ) (x : Fin (3 * t) → F2) : F2 :=
  ∑ i : Fin (3 * t), if i.val % 3 = r then x i else 0

lemma sum_eq_resSum (t : ℕ) (x : Fin (3 * t) → F2) :
    (∑ i : Fin (3 * t), x i) = resSum t 0 x + resSum t 1 x + resSum t 2 x := by
  simp only [resSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [h]

lemma codeP_iff_resSum {t : ℕ} {x : Fin (3 * t) → F2} :
    codeP t x ↔ resSum t 0 x = resSum t 2 x ∧ resSum t 1 x = resSum t 2 x := by
  have h0 : (∑ i : Fin (3 * t), if i.val % 3 = 0 ∨ i.val % 3 = 2 then x i else 0) =
      resSum t 0 x + resSum t 2 x := by
    simp only [resSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases h with h | h | h <;> simp [h]
  have h1 : (∑ i : Fin (3 * t), if i.val % 3 = 1 ∨ i.val % 3 = 2 then x i else 0) =
      resSum t 1 x + resSum t 2 x := by
    simp only [resSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases h with h | h | h <;> simp [h]
  constructor
  · intro hc
    have c0 := hc 0
    have c1 := hc 1
    change (∑ i : Fin (3 * t), if i.val % 3 = 0 ∨ i.val % 3 = 2 then x i else 0) = 0 at c0
    change (∑ i : Fin (3 * t), if i.val % 3 = 1 ∨ i.val % 3 = 2 then x i else 0) = 0 at c1
    rw [h0] at c0
    rw [h1] at c1
    constructor
    · have := congrArg (· + resSum t 2 x) c0
      simpa [add_assoc, z2_add_self] using this
    · have := congrArg (· + resSum t 2 x) c1
      simpa [add_assoc, z2_add_self] using this
  · rintro ⟨e0, e1⟩ e
    fin_cases e
    · change (∑ i : Fin (3 * t), if i.val % 3 = 0 ∨ i.val % 3 = 2 then x i else 0) = 0
      rw [h0, e0, z2_add_self]
    · change (∑ i : Fin (3 * t), if i.val % 3 = 1 ∨ i.val % 3 = 2 then x i else 0) = 0
      rw [h1, e1, z2_add_self]

lemma codeP_resSum_eq_total {t : ℕ} {x : Fin (3 * t) → F2} (hx : codeP t x) (r : Fin 3) :
    resSum t r.val x = ∑ i : Fin (3 * t), x i := by
  obtain ⟨h0, h1⟩ := codeP_iff_resSum.mp hx
  rw [sum_eq_resSum, h0, h1, z2_add_self, zero_add]
  fin_cases r
  · exact h0
  · exact h1
  · rfl

def revEquiv (t : ℕ) : (Fin (3 * t) → F2) ≃ₗ[F2] (Fin (3 * t) → F2) where
  toFun x i := x (revIdx i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x i := x (revIdx i)
  left_inv x := funext fun i => by simp [revIdx_revIdx]
  right_inv x := funext fun i => by simp [revIdx_revIdx]

lemma rev_codeP {t : ℕ} {x : Fin (3 * t) → F2} : codeP t (revEquiv t x) ↔ codeP t x := by
  have hr : ∀ r : Fin 3, resSum t r.val (revEquiv t x) = resSum t (2 - r.val) x := by
    intro r
    unfold resSum revEquiv
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_bij (fun i _ => revIdx i) (fun _ _ => Finset.mem_univ _)
      (fun a b _ _ h => by simpa [revIdx_revIdx] using congrArg revIdx h)
      (fun j _ => ⟨revIdx j, Finset.mem_univ _, revIdx_revIdx j⟩) (fun i _ => ?_)
    have hmod := revIdx_mod3 i
    have hr3 := r.isLt
    have : (i.val % 3 = r.val) ↔ ((revIdx i).val % 3 = 2 - r.val) := by omega
    simp [this]
  rw [codeP_iff_resSum, codeP_iff_resSum]
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  change resSum t 0 (revEquiv t x) = resSum t 2 x at h0
  change resSum t 1 (revEquiv t x) = resSum t 1 x at h1
  change resSum t 2 (revEquiv t x) = resSum t 0 x at h2
  rw [h0, h1, h2]
  constructor
  · rintro ⟨a, b⟩; exact ⟨a.symm, b.trans a.symm⟩
  · rintro ⟨a, b⟩; exact ⟨a.symm, b.trans a.symm⟩

lemma rev_hitP {t : ℕ} (ht : 0 < t) (x y : Fin (3 * t) → F2) :
    hitP ht (revEquiv t y) (revEquiv t x) ↔ hitP ht x y := by
  unfold hitP revEquiv
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · intro h i
    have h1 := (h (revIdx i)).1
    have h2 := (h (prv (revIdx i))).2
    rw [revIdx_revIdx, mul_comm] at h1
    rw [nxt_prv ht, revIdx_revIdx, ← revIdx_nxt ht, revIdx_revIdx, mul_comm] at h2
    exact ⟨h1, h2⟩
  · intro h j
    have h1 := (h (revIdx j)).1
    have h2 := (h (revIdx (nxt ht j))).2
    rw [mul_comm] at h1
    rw [revIdx_nxt ht, nxt_prv ht, ← revIdx_nxt ht, mul_comm] at h2
    exact ⟨h1, h2⟩

lemma mem_suppF {t : ℕ} {x : Fin (3 * t) → F2} {i : Fin (3 * t)} :
    i ∈ suppF x ↔ x i ≠ 0 := by
  simp [suppF]

lemma mem_nbrF {t : ℕ} (ht : 0 < t) {x : Fin (3 * t) → F2} {i : Fin (3 * t)} :
    i ∈ nbrF x ↔ x i ≠ 0 ∨ x (nxt ht i) ≠ 0 := by
  simp only [nbrF, Finset.mem_union, Finset.mem_image, mem_suppF]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rwa [nxt_prv ht])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨nxt ht i, h, prv_nxt ht i⟩

lemma hitP_iff_nbrF {t : ℕ} (ht : 0 < t) (x y : Fin (3 * t) → F2) :
    hitP ht x y ↔ ∀ i ∈ nbrF x, y i = 0 := by
  constructor
  · intro h i hi
    rw [mem_nbrF ht] at hi
    rcases hi with h1 | h1
    · have := (h i).1
      rw [z2_eq_one_of_ne_zero h1, one_mul] at this
      exact this
    · have := (h i).2
      rw [z2_eq_one_of_ne_zero h1, one_mul] at this
      exact this
  · intro h i
    constructor
    · by_cases hx : x i = 0
      · simp [hx]
      · have hy := h i ((mem_nbrF ht).mpr (Or.inl hx))
        simp [hy]
    · by_cases hx : x (nxt ht i) = 0
      · simp [hx]
      · have hy := h i ((mem_nbrF ht).mpr (Or.inr hx))
        simp [hy]

def suppSub {t : ℕ} (S : Finset (Fin (3 * t))) : Submodule F2 (Fin (3 * t) → F2) :=
  { add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
    carrier := {x | ∀ i, i ∉ S → x i = 0}
    zero_mem' := fun _ _ => rfl
    smul_mem' := fun c _ ha i hi => by simp [ha i hi] }

lemma finrank_suppSub {t : ℕ} (S : Finset (Fin (3 * t))) :
    Module.finrank F2 (suppSub S) = S.card := by
  let e : suppSub S ≃ₗ[F2] (S → F2) :=
    { toFun := fun x i => x.1 i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => ⟨fun i => if h : i ∈ S then f ⟨i, h⟩ else 0,
        fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        ext i
        by_cases h : i ∈ S
        · simp [h]
        · simp [h, x.2 i h]
      right_inv := fun f => by ext ⟨i, hi⟩; simp [hi] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

lemma checkMap_single {t : ℕ} (i : Fin (3 * t)) :
    checkMap t (Pi.single i 1) =
      fun e : Fin 2 => if i.val % 3 = e.val ∨ i.val % 3 = 2 then 1 else 0 := by
  ext e
  simp only [checkMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

lemma finrank_code_inf_suppSub_one_res {t : ℕ} (S : Finset (Fin (3 * t)))
    (hS : S.Nonempty) (r : Fin 3) (hres : ∀ i ∈ S, i.val % 3 = r.val) :
    Module.finrank F2 (codeSub t ⊓ suppSub S : Submodule F2 (Fin (3 * t) → F2)) = S.card - 1 := by
  let φ : suppSub S →ₗ[F2] (Fin 2 → F2) := (checkMap t).comp (suppSub S).subtype
  have hker : LinearMap.ker φ = Submodule.comap (suppSub S).subtype (codeSub t) := rfl
  have hker_dim : Module.finrank F2 (LinearMap.ker φ) =
      Module.finrank F2 (codeSub t ⊓ suppSub S : Submodule F2 (Fin (3 * t) → F2)) := by
    let e : LinearMap.ker φ ≃ₗ[F2] (codeSub t ⊓ suppSub S : Submodule F2 (Fin (3 * t) → F2)) :=
      { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  obtain ⟨i0, hi0⟩ := hS
  let v0 : Fin 2 → F2 := fun e => if r.val = e.val ∨ r.val = 2 then 1 else 0
  have hv0_ne : v0 ≠ 0 := by
    intro h
    fin_cases r
    · have := congrFun h 0; simp [v0] at this
    · have := congrFun h 1; simp [v0] at this
    · have := congrFun h 0; simp [v0] at this
  have hrange : LinearMap.range φ = Submodule.span F2 {v0} := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hxS⟩, rfl⟩
      have hval : φ ⟨x, hxS⟩ = (∑ i ∈ S, x i) • v0 := by
        ext e
        simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, checkMap,
          LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, v0]
        have hsum : (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) =
            ∑ i ∈ S, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0 := by
          symm
          refine Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => ?_
          simp [hxS i hiS]
        rw [hsum]
        split_ifs with hcond
        · rw [mul_one]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [if_pos (by rwa [hres i hi])]
        · rw [mul_zero]
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [if_neg (by rwa [hres i hi])]
      rw [hval]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨⟨Pi.single i0 1, fun j hj => by
        exact Pi.single_eq_of_ne (show j ≠ i0 from fun h => hj (h ▸ hi0)) 1⟩, ?_⟩
      change checkMap t (Pi.single i0 1) = v0
      rw [checkMap_single]
      ext e
      simp [v0, hres i0 hi0]
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [finrank_suppSub, hker_dim, hrange, finrank_span_singleton hv0_ne] at hrk
  omega

lemma finrank_code_inf_suppSub_two_res {t : ℕ} (S : Finset (Fin (3 * t)))
    (i1 i2 : Fin (3 * t)) (hi1 : i1 ∈ S) (hi2 : i2 ∈ S) (hmod : i1.val % 3 ≠ i2.val % 3) :
    Module.finrank F2 (codeSub t ⊓ suppSub S : Submodule F2 (Fin (3 * t) → F2)) = S.card - 2 := by
  let φ : suppSub S →ₗ[F2] (Fin 2 → F2) := (checkMap t).comp (suppSub S).subtype
  have hker_dim : Module.finrank F2 (LinearMap.ker φ) =
      Module.finrank F2 (codeSub t ⊓ suppSub S : Submodule F2 (Fin (3 * t) → F2)) := by
    let e : LinearMap.ker φ ≃ₗ[F2] (codeSub t ⊓ suppSub S : Submodule F2 (Fin (3 * t) → F2)) :=
      { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  let v1 := checkMap t (Pi.single i1 1)
  let v2 := checkMap t (Pi.single i2 1)
  have hv1 : v1 ∈ LinearMap.range φ :=
    ⟨⟨Pi.single i1 1, fun j hj => by exact Pi.single_eq_of_ne (show j ≠ i1 from fun h => hj (h ▸ hi1)) 1⟩, rfl⟩
  have hv2 : v2 ∈ LinearMap.range φ :=
    ⟨⟨Pi.single i2 1, fun j hj => by exact Pi.single_eq_of_ne (show j ≠ i2 from fun h => hj (h ▸ hi2)) 1⟩, rfl⟩
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have h1 : v1 0 = (if i1.val % 3 = 0 ∨ i1.val % 3 = 2 then 1 else 0) ∧
        v1 1 = (if i1.val % 3 = 1 ∨ i1.val % 3 = 2 then 1 else 0) := by
      simp [v1, checkMap_single]
    have h2 : v2 0 = (if i2.val % 3 = 0 ∨ i2.val % 3 = 2 then 1 else 0) ∧
        v2 1 = (if i2.val % 3 = 1 ∨ i2.val % 3 = 2 then 1 else 0) := by
      simp [v2, checkMap_single]
    have hcases : ∀ a b : ℕ, a < 3 → b < 3 → a ≠ b →
        ∃ c1 c2 : F2, c1 • v1 + c2 • v2 = u := by
      intro a b ha hb hab
      have hu0 := z2_cases (u 0)
      have hu1 := z2_cases (u 1)
      have h10 : v1 0 = (if i1.val % 3 = 0 ∨ i1.val % 3 = 2 then 1 else 0) := h1.1
      have h11 : v1 1 = (if i1.val % 3 = 1 ∨ i1.val % 3 = 2 then 1 else 0) := h1.2
      have h20 : v2 0 = (if i2.val % 3 = 0 ∨ i2.val % 3 = 2 then 1 else 0) := h2.1
      have h21 : v2 1 = (if i2.val % 3 = 1 ∨ i2.val % 3 = 2 then 1 else 0) := h2.2
      have hi1r : i1.val % 3 = 0 ∨ i1.val % 3 = 1 ∨ i1.val % 3 = 2 := by omega
      have hi2r : i2.val % 3 = 0 ∨ i2.val % 3 = 1 ∨ i2.val % 3 = 2 := by omega
      rcases z2_cases (u 0) with hu0 | hu0 <;> rcases z2_cases (u 1) with hu1 | hu1 <;>
      rcases hi1r with r1 | r1 | r1 <;> rcases hi2r with r2 | r2 | r2
      all_goals try exact absurd (r1.trans r2.symm) hmod
      all_goals first
        | (solve | refine ⟨0, 0, ?_⟩; ext e; fin_cases e <;> simp [h10, h11, h20, h21, r1, r2, hu0, hu1, z2_one_add_one])
        | (solve | refine ⟨1, 0, ?_⟩; ext e; fin_cases e <;> simp [h10, h11, h20, h21, r1, r2, hu0, hu1, z2_one_add_one])
        | (solve | refine ⟨0, 1, ?_⟩; ext e; fin_cases e <;> simp [h10, h11, h20, h21, r1, r2, hu0, hu1, z2_one_add_one])
        | (solve | refine ⟨1, 1, ?_⟩; ext e; fin_cases e <;> simp [h10, h11, h20, h21, r1, r2, hu0, hu1, z2_one_add_one])
    obtain ⟨c1, c2, hcomb⟩ := hcases (i1.val % 3) (i2.val % 3) (Nat.mod_lt _ (by omega))
      (Nat.mod_lt _ (by omega)) hmod
    rw [← hcomb]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv1) (Submodule.smul_mem _ _ hv2)
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [finrank_suppSub, hker_dim, hsurj, finrank_top, Module.finrank_fin_fun] at hrk
  omega

lemma finrank_codeSub {t : ℕ} (ht : 0 < t) : Module.finrank F2 (codeSub t) = 3 * t - 2 := by
  have htop : suppSub (Finset.univ : Finset (Fin (3 * t))) = ⊤ := by
    ext x; simp [suppSub]
  have h0 : (⟨0, by omega⟩ : Fin (3 * t)) ∈ (Finset.univ : Finset (Fin (3 * t))) := Finset.mem_univ _
  have h1 : (⟨1, by omega⟩ : Fin (3 * t)) ∈ (Finset.univ : Finset (Fin (3 * t))) := Finset.mem_univ _
  have h := finrank_code_inf_suppSub_two_res Finset.univ ⟨0, by omega⟩ ⟨1, by omega⟩ h0 h1 (by simp)
  rw [htop, inf_top_eq, Finset.card_univ, Fintype.card_fin] at h
  exact h

lemma card_resClass {t : ℕ} (r : Fin 3) :
    (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = r.val)).card = t := by
  let f : Fin t ↪ Fin (3 * t) :=
    ⟨fun k => ⟨3 * k.val + r.val, by have := k.isLt; have := r.isLt; omega⟩,
     fun a b h => by
       have := congrArg Fin.val h
       dsimp at this
       exact Fin.ext (by omega)⟩
  have heq : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = r.val) =
      Finset.univ.map f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hi
      refine ⟨⟨i.val / 3, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext
      change 3 * (i.val / 3) + r.val = i.val
      omega
    · rintro ⟨k, rfl⟩
      change (3 * k.val + r.val) % 3 = r.val
      have := r.isLt
      omega
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma card_compl_resClass {t : ℕ} (r : Fin 3) :
    (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val)).card = 2 * t := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (3 * t))))
    (p := fun i => i.val % 3 = r.val)
  simp only [ne_eq] at h ⊢
  rw [card_resClass r, Finset.card_univ, Fintype.card_fin] at h
  omega

lemma finrank_code_inf_suppSub_compl_add_rkC {t : ℕ} (ht : 0 < t) (S : Finset (Fin (3 * t))) :
    Module.finrank F2 (codeSub t ⊓ suppSub Sᶜ : Submodule F2 (Fin (3 * t) → F2)) + rkC S =
      3 * t - 2 := by
  have hcard : Sᶜ.card + S.card = 3 * t := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  unfold rkC dualDrop
  by_cases huniv : S = Finset.univ
  · subst huniv
    have hbot : (codeSub t ⊓ suppSub (Finset.univᶜ : Finset (Fin (3 * t))) :
        Submodule F2 (Fin (3 * t) → F2)) = ⊥ := by
      ext x
      simp only [Submodule.mem_inf, Submodule.mem_bot]
      constructor
      · intro hx; ext i; exact hx.2 i (by simp)
      · rintro rfl; exact ⟨zero_mem _, zero_mem _⟩
    rw [if_pos rfl, hbot, finrank_bot, zero_add, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg huniv]
    have hne : Sᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      apply huniv
      ext i
      have : i ∉ Sᶜ := by simp [hem]
      simpa using this
    by_cases h1 : ∃ r : Fin 3, ∀ i : Fin (3 * t), i.val % 3 ≠ r.val → i ∈ S
    · rw [if_pos h1]
      obtain ⟨r, hr⟩ := h1
      have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) ⊆ S := by
        intro i hi
        exact hr i (Finset.mem_filter.mp hi).2
      have hScard : 2 * t ≤ S.card := by
        rw [← card_compl_resClass r]
        exact Finset.card_le_card hsub
      have hres : ∀ i ∈ Sᶜ, i.val % 3 = r.val := by
        intro i hi
        by_contra hne'
        exact (Finset.mem_compl.mp hi) (hr i hne')
      rw [finrank_code_inf_suppSub_one_res Sᶜ hne r hres]
      have hpos : 1 ≤ Sᶜ.card := Finset.Nonempty.card_pos hne
      omega
    · rw [if_neg h1]
      obtain ⟨i1, hi1⟩ := hne
      have hex2 : ∃ i2 ∈ Sᶜ, i1.val % 3 ≠ i2.val % 3 := by
        by_contra hall
        push Not at hall
        apply h1
        refine ⟨⟨i1.val % 3, Nat.mod_lt _ (by omega)⟩, fun i hi => ?_⟩
        by_contra hiS
        exact hi (hall i (Finset.mem_compl.mpr hiS)).symm
      obtain ⟨i2, hi2, hmod⟩ := hex2
      rw [finrank_code_inf_suppSub_two_res Sᶜ i1 i2 hi1 hi2 hmod]
      have hge2 : 2 ≤ Sᶜ.card := by
        have hne12 : i1 ≠ i2 := fun h => hmod (by rw [h])
        have hsub : ({i1, i2} : Finset (Fin (3 * t))) ⊆ Sᶜ := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hi1
          · exact (Finset.mem_singleton.mp hx) ▸ hi2
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hne12] at this
      omega

lemma card_hit_code_eq {t : ℕ} (ht : 0 < t) (x : Fin (3 * t) → F2) :
    Nat.card {y : codeSub t // hitP ht x y.val} * 2 ^ rkC (nbrF x) = Nat.card (codeSub t) := by
  let e : {y : codeSub t // hitP ht x y.val} ≃
      (codeSub t ⊓ suppSub (nbrF x)ᶜ : Submodule F2 (Fin (3 * t) → F2)) :=
    { toFun := fun y => ⟨y.1.1, y.1.2, fun i hi => by
        have hi' : i ∈ nbrF x := by simpa using hi
        exact (hitP_iff_nbrF ht x y.1.1).mp y.2 i hi'⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hitP_iff_nbrF ht x y.1).mpr fun i hi =>
        y.2.2 i (by simpa using hi)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_eq_two_pow_finrank, card_eq_two_pow_finrank,
    ← pow_add, finrank_code_inf_suppSub_compl_add_rkC ht (nbrF x), finrank_codeSub ht]

lemma card_hit_sub_le_code {t : ℕ} (ht : 0 < t) {Q : Submodule F2 (Fin (3 * t) → F2)}
    (hQ : Q ≤ codeSub t) (x : Fin (3 * t) → F2) :
    Nat.card {y : Q // hitP ht x y.val} * 2 ^ rkC (nbrF x) ≤
      2 ^ (3 * t - 2 - Module.finrank F2 Q) * Nat.card Q := by
  have hinj : Function.Injective (fun y : {y : Q // hitP ht x y.val} =>
      (⟨⟨y.1.1, hQ y.1.2⟩, y.2⟩ : {y : codeSub t // hitP ht x y.val})) := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1.1) h))
  have hle := Nat.card_le_card_of_injective _ hinj
  have hcode := card_hit_code_eq ht x
  have hdimQ : Module.finrank F2 Q ≤ 3 * t - 2 := by
    rw [← finrank_codeSub ht]
    exact Submodule.finrank_mono hQ
  have hcardC : Nat.card (codeSub t) = 2 ^ (3 * t - 2 - Module.finrank F2 Q) * Nat.card Q := by
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, finrank_codeSub ht, ← pow_add]
    congr 1
    omega
  calc Nat.card {y : Q // hitP ht x y.val} * 2 ^ rkC (nbrF x)
      ≤ Nat.card {y : codeSub t // hitP ht x y.val} * 2 ^ rkC (nbrF x) :=
        Nat.mul_le_mul_right _ hle
    _ = Nat.card (codeSub t) := hcode
    _ = 2 ^ (3 * t - 2 - Module.finrank F2 Q) * Nat.card Q := hcardC

lemma card_nbrF_gt_card_suppF {t : ℕ} (ht : 0 < t) {x : Fin (3 * t) → F2}
    (hx0 : x ≠ 0) (hxall : suppF x ≠ Finset.univ) :
    (suppF x).card + 1 ≤ (nbrF x).card := by
  have hne : (suppF x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    apply hx0
    ext i
    by_contra hi
    have : i ∈ suppF x := mem_suppF.mpr hi
    simp [hem] at this
  have hnotall : ∃ i ∈ suppF x, prv i ∉ suppF x := by
    by_contra hall
    push Not at hall
    obtain ⟨i0, hi0⟩ := hne
    have hstep : ∀ k : ℕ, (prv^[k] i0) ∈ suppF x := by
      intro k
      induction k with
      | zero => exact hi0
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hall _ ih
    apply hxall
    ext j
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨k, hkj⟩ := prv_reach i0 j
    exact hkj ▸ hstep k
  obtain ⟨i, hi, hpi⟩ := hnotall
  have hss : insert (prv i) (suppF x) ⊆ nbrF x := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem prv hi)
    · exact Finset.mem_union_left _ hj
  have := Finset.card_le_card hss
  rwa [Finset.card_insert_of_notMem hpi] at this

lemma card_nbrF_one_res {t : ℕ} (ht : 0 < t) {x : Fin (3 * t) → F2}
    (r : Fin 3) (hres : ∀ i ∈ suppF x, i.val % 3 = r.val) :
    (nbrF x).card = 2 * (suppF x).card := by
  have hdisj : Disjoint (suppF x) ((suppF x).image prv) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj2
    have h1 := hres (prv i) hj1
    have h2 := hres i hi
    have h3 := prv_mod3 i
    have hr := r.isLt
    omega
  rw [nbrF, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (prv_inj ht)]
  ring

lemma suppF_card_res_parity {t : ℕ} {x : Fin (3 * t) → F2} (hx : codeP t x) (r : Fin 3) :
    ((suppF x).filter (fun i => i.val % 3 = r.val)).card % 2 = (suppF x).card % 2 := by
  have h1 : resSum t r.val x = (((suppF x).filter (fun i => i.val % 3 = r.val)).card : F2) := by
    unfold resSum
    rw [← z2_sum_const_mod2]
    have hsf : (∑ _i ∈ (suppF x).filter (fun i => i.val % 3 = r.val), (1 : F2)) =
        ∑ i : Fin (3 * t), if i ∈ suppF x ∧ i.val % 3 = r.val then 1 else 0 := by
      rw [← Finset.sum_filter]
      congr 1; ext i; simp [Finset.mem_filter]
    rw [hsf]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i.val % 3 = r.val
    · simp only [h, ↓reduceIte, mem_suppF]
      by_cases hx0 : x i = 0
      · simp [hx0]
      · simp [hx0, z2_eq_one_of_ne_zero hx0]
    · simp [h]
  have h2 : (∑ i : Fin (3 * t), x i) = ((suppF x).card : F2) := by
    rw [← z2_sum_const_mod2, suppF]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx0 : x i = 0
    · simp [hx0]
    · simp [hx0, z2_eq_one_of_ne_zero hx0]
  have heq := codeP_resSum_eq_total hx r
  rw [h1, h2] at heq
  have hdvd : ((((suppF x).filter (fun i => i.val % 3 = r.val)).card + (suppF x).card : ℕ) : F2) = 0 := by
    push_cast
    rw [heq, z2_add_self]
  rw [z2_natCast_eq_zero_iff] at hdvd
  omega

lemma suppF_card_ge_two {t : ℕ} {x : Fin (3 * t) → F2} (hx : codeP t x) (hx0 : x ≠ 0) :
    2 ≤ (suppF x).card := by
  have hne : (suppF x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    apply hx0
    ext i
    by_contra hi
    have : i ∈ suppF x := mem_suppF.mpr hi
    simp [hem] at this
  have hpos : 1 ≤ (suppF x).card := Finset.Nonempty.card_pos hne
  by_contra hlt
  have h1 : (suppF x).card = 1 := by omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
  have hr0 := suppF_card_res_parity hx 0
  have hr1 := suppF_card_res_parity hx 1
  have hr2 := suppF_card_res_parity hx 2
  rw [hi] at hr0 hr1 hr2
  simp only [Finset.card_singleton] at hr0 hr1 hr2
  have hmod : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  have hfil0 : ∀ (r : Fin 3), i.val % 3 ≠ r.val →
      (({i} : Finset (Fin (3 * t))).filter (fun j => j.val % 3 = r.val)) = ∅ := by
    intro r hne; ext j; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, hm⟩; exact hne hm
  rcases hmod with hm | hm | hm
  · rw [hfil0 1 (by change i.val % 3 ≠ 1; omega)] at hr1; simp at hr1
  · rw [hfil0 0 (by change i.val % 3 ≠ 0; omega)] at hr0; simp at hr0
  · rw [hfil0 0 (by change i.val % 3 ≠ 0; omega)] at hr0; simp at hr0

lemma codeP_weight2_same_res {t : ℕ} {x : Fin (3 * t) → F2} (hx : codeP t x)
    (hw : (suppF x).card = 2) :
    ∃ a b : Fin (3 * t), a ≠ b ∧ a.val % 3 = b.val % 3 ∧ suppF x = {a, b} := by
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hw
  refine ⟨a, b, hab, ?_, hset⟩
  have hr : ∀ r : Fin 3, ((({a, b} : Finset (Fin (3 * t))).filter
      (fun i => i.val % 3 = r.val)).card) % 2 = 0 := by
    intro r
    have h := suppF_card_res_parity hx r
    rw [hset, Finset.card_pair hab] at h
    exact h
  have ha : a.val % 3 = 0 ∨ a.val % 3 = 1 ∨ a.val % 3 = 2 := by omega
  have hb : b.val % 3 = 0 ∨ b.val % 3 = 1 ∨ b.val % 3 = 2 := by omega
  have hfil1 : ∀ (r : Fin 3), a.val % 3 = r.val → b.val % 3 ≠ r.val →
      (({a, b} : Finset (Fin (3 * t))).filter (fun j => j.val % 3 = r.val)) = {a} := by
    intro r h1 h2; ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun ⟨h, hm⟩ => h.elim id (fun hb' => absurd (hb' ▸ hm) h2), fun h => ⟨Or.inl h, h ▸ h1⟩⟩
  have hfil2 : ∀ (r : Fin 3), a.val % 3 ≠ r.val → b.val % 3 = r.val →
      (({a, b} : Finset (Fin (3 * t))).filter (fun j => j.val % 3 = r.val)) = {b} := by
    intro r h1 h2; ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun ⟨h, hm⟩ => h.elim (fun ha' => absurd (ha' ▸ hm) h1) id, fun h => ⟨Or.inr h, h ▸ h2⟩⟩
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · omega
  · have h := hr 0; rw [hfil1 0 ha (by change b.val % 3 ≠ 0; omega)] at h; simp at h
  · have h := hr 0; rw [hfil1 0 ha (by change b.val % 3 ≠ 0; omega)] at h; simp at h
  · have h := hr 0; rw [hfil2 0 (by change a.val % 3 ≠ 0; omega) hb] at h; simp at h
  · omega
  · have h := hr 1; rw [hfil1 1 ha (by change b.val % 3 ≠ 1; omega)] at h; simp at h
  · have h := hr 0; rw [hfil2 0 (by change a.val % 3 ≠ 0; omega) hb] at h; simp at h
  · have h := hr 1; rw [hfil2 1 (by change a.val % 3 ≠ 1; omega) hb] at h; simp at h
  · omega

lemma codeP_odd_hits_all_res {t : ℕ} {x : Fin (3 * t) → F2} (hx : codeP t x)
    (hodd : (suppF x).card % 2 = 1) (r : Fin 3) :
    ∃ i ∈ suppF x, i.val % 3 = r.val := by
  have hr := suppF_card_res_parity hx r
  rw [hodd] at hr
  have hpos : 0 < ((suppF x).filter (fun i => i.val % 3 = r.val)).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

lemma nbrF_subset_compl_res_imp {t : ℕ} {x : Fin (3 * t) → F2} {r : Fin 3}
    (hsub : ∀ i ∈ nbrF x, i.val % 3 ≠ r.val) :
    ∀ i ∈ suppF x, i.val % 3 = (r.val + 2) % 3 := by
  intro i hi
  have h1 : i.val % 3 ≠ r.val := hsub i (Finset.mem_union_left _ hi)
  have h2 : (prv i).val % 3 ≠ r.val := hsub (prv i) (Finset.mem_union_right _ (Finset.mem_image_of_mem prv hi))
  rw [prv_mod3] at h2
  have hr := r.isLt
  omega

lemma dualDrop_eq_zero_of_lt_2t {t : ℕ} (ht : 0 < t) {S : Finset (Fin (3 * t))}
    (hlt : S.card < 2 * t) : dualDrop S = 0 := by
  unfold dualDrop
  have hne : S ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hlt
    omega
  rw [if_neg hne]
  have hno : ¬ ∃ r : Fin 3, ∀ i : Fin (3 * t), i.val % 3 ≠ r.val → i ∈ S := by
    rintro ⟨r, hr⟩
    have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) ⊆ S := by
      intro i hi; exact hr i (Finset.mem_filter.mp hi).2
    have := Finset.card_le_card hsub
    rw [card_compl_resClass r] at this
    omega
  rw [if_neg hno]

lemma rkC_even_wt2 {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {x : Fin (3 * t) → F2}
    (hx : codeP t x) (hw : (suppF x).card = 2) :
    rkC (nbrF x) = 4 := by
  obtain ⟨a, b, hab, hmod, hset⟩ := codeP_weight2_same_res hx hw
  have hres : ∀ i ∈ suppF x, i.val % 3 = a.val % 3 := by
    intro i hi
    rw [hset] at hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rfl
    · rw [Finset.mem_singleton.mp hi]; exact hmod.symm
  have hcard : (nbrF x).card = 4 := by
    rw [card_nbrF_one_res ht ⟨a.val % 3, Nat.mod_lt _ (by omega)⟩ hres, hw]
  unfold rkC
  rw [hcard, dualDrop_eq_zero_of_lt_2t ht (by omega)]

lemma rkC_even_ge6 {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {x : Fin (3 * t) → F2}
    (hx : codeP t x) (heven : (suppF x).card % 2 = 0) (hw : 4 ≤ (suppF x).card) :
    6 ≤ rkC (nbrF x) := by
  by_cases h1res : ∃ r : Fin 3, ∀ i ∈ suppF x, i.val % 3 = r.val
  · obtain ⟨r, hr⟩ := h1res
    have hcard : (nbrF x).card = 2 * (suppF x).card := card_nbrF_one_res ht r hr
    have hdrop : dualDrop (nbrF x) ≤ 1 := by
      unfold dualDrop
      have hne : nbrF x ≠ Finset.univ := by
        intro huniv
        have hmiss : ∀ i ∈ nbrF x, i.val % 3 ≠ (r.val + 1) % 3 := by
          intro i hi
          rw [mem_nbrF ht] at hi
          rcases hi with h | h
          · have := hr i (mem_suppF.mpr h); have := r.isLt; omega
          · have := hr (nxt ht i) (mem_suppF.mpr h)
            rw [nxt_mod3 ht] at this
            have := r.isLt; omega
        have h0 := hmiss ⟨(r.val + 1) % 3, by omega⟩ (by rw [huniv]; exact Finset.mem_univ _)
        exact h0 (by simp)
      rw [if_neg hne]
      split_ifs <;> omega
    unfold rkC
    omega
  · push Not at h1res
    by_cases huniv : nbrF x = Finset.univ
    · unfold rkC dualDrop
      rw [if_pos huniv, huniv, Finset.card_univ, Fintype.card_fin]
      omega
    · have hdrop1 : dualDrop (nbrF x) ≤ 1 := by
        unfold dualDrop; rw [if_neg huniv]; split_ifs <;> omega
      by_cases hge7 : 7 ≤ (nbrF x).card
      · unfold rkC; omega
      · have hle6 : (nbrF x).card ≤ 6 := by omega
        have hSnotuniv : suppF x ≠ Finset.univ := by
          intro hu
          apply huniv
          ext i
          simp only [Finset.mem_univ, iff_true]
          exact Finset.mem_union_left _ (by rw [hu]; exact Finset.mem_univ i)
        let B := (suppF x).filter (fun i => prv i ∉ suppF x)
        have hBdisj : Disjoint (suppF x) (B.image prv) := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj2
          exact (Finset.mem_filter.mp hi).2 hj1
        have hBsub : suppF x ∪ B.image prv ⊆ nbrF x := by
          intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · exact Finset.mem_union_left _ hj
          · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
            exact Finset.mem_union_right _ (Finset.mem_image_of_mem prv (Finset.mem_filter.mp hi).1)
        have hnbr_ge : (suppF x).card + B.card ≤ (nbrF x).card := by
          have := Finset.card_le_card hBsub
          rwa [Finset.card_union_of_disjoint hBdisj, Finset.card_image_of_injective _ (prv_inj ht)] at this
        have hBpos : 1 ≤ B.card := by
          by_contra hB0
          have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
          have hstep : ∀ i ∈ suppF x, prv i ∈ suppF x := by
            intro i hi
            by_contra hpi
            have : i ∈ B := Finset.mem_filter.mpr ⟨hi, hpi⟩
            simp [hBe] at this
          have hgt := card_nbrF_gt_card_suppF ht (x := x) (by
            intro h0; have : suppF x = ∅ := by ext i; simp [suppF, h0]
            rw [this] at hw; simp at hw) hSnotuniv
          have hsub2 : nbrF x ⊆ suppF x := by
            intro j hj
            rcases Finset.mem_union.mp hj with hj | hj
            · exact hj
            · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
              exact hstep i hi
          have := Finset.card_le_card hsub2
          omega
        have hcard6 : (nbrF x).card = 6 := by
          by_cases hB2 : 2 ≤ B.card
          · omega
          · have hB1 : B.card = 1 := by omega
            obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hB1
            have hi0B : i0 ∈ B := by rw [hi0]; exact Finset.mem_singleton_self i0
            have hi0S : i0 ∈ suppF x := (Finset.mem_filter.mp hi0B).1
            have hpi0 : prv i0 ∉ suppF x := (Finset.mem_filter.mp hi0B).2
            have hstep_fwd : ∀ k < (suppF x).card, (nxt ht)^[k] i0 ∈ suppF x := by
              intro k hk
              by_contra hnot
              let m := Nat.find (⟨k, hnot⟩ : ∃ m, (nxt ht)^[m] i0 ∉ suppF x)
              have hmin : (nxt ht)^[m] i0 ∉ suppF x :=
                Nat.find_spec (⟨k, hnot⟩ : ∃ m, (nxt ht)^[m] i0 ∉ suppF x)
              have hm_pos : 0 < m := by
                by_contra hm0
                have : m = 0 := by omega
                rw [this] at hmin
                exact hmin hi0S
              have hm_lt : m < (suppF x).card := lt_of_le_of_lt (Nat.find_min' _ hnot) hk
              have hclosed : ∀ j ∈ suppF x, j ≠ i0 → prv j ∈ suppF x := by
                intro j hj hne
                by_contra hnj
                have : j ∈ B := Finset.mem_filter.mpr ⟨hj, hnj⟩
                rw [hi0, Finset.mem_singleton] at this
                exact hne this
              let T : Finset (Fin (3 * t)) := (Finset.range m).image (fun a => (nxt ht)^[a] i0)
              have hTsub : T ⊆ suppF x := by
                intro j hj
                obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
                have hal : a < m := Finset.mem_range.mp ha
                by_contra hna
                exact Nat.find_min (⟨k, hnot⟩ : ∃ m, (nxt ht)^[m] i0 ∉ suppF x) hal hna
              have hTlt : T.card < (suppF x).card := lt_of_le_of_lt Finset.card_image_le (by simpa using hm_lt)
              obtain ⟨j0, hj0S, hj0T⟩ := Finset.exists_mem_notMem_of_card_lt_card hTlt
              have hstay : ∀ r : ℕ, prv^[r] j0 ∈ suppF x ∧ prv^[r] j0 ∉ T := by
                intro r
                induction r with
                | zero => exact ⟨hj0S, hj0T⟩
                | succ r ih =>
                  rw [Function.iterate_succ_apply']
                  have hne_i0 : prv^[r] j0 ≠ i0 := by
                    intro heq
                    apply ih.2
                    rw [heq]
                    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hm_pos, rfl⟩
                  refine ⟨hclosed _ ih.1 hne_i0, ?_⟩
                  intro hmemT
                  obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hmemT
                  have hal : a < m := Finset.mem_range.mp ha
                  have hnxt : prv^[r] j0 = (nxt ht)^[a + 1] i0 := by
                    rw [Function.iterate_succ_apply', haeq, nxt_prv ht]
                  by_cases ham : a + 1 < m
                  · apply ih.2
                    rw [hnxt]
                    exact Finset.mem_image.mpr ⟨a + 1, Finset.mem_range.mpr ham, rfl⟩
                  · have heqm : a + 1 = m := by omega
                    rw [heqm] at hnxt
                    exact hmin (hnxt ▸ ih.1)
              have hnot_all_in : ∀ r : ℕ, prv^[r] j0 ∈ suppF x := fun r => (hstay r).1
              have hpi0_in : prv i0 ∈ suppF x := by
                obtain ⟨r, hr⟩ := prv_reach j0 (prv i0)
                exact hr ▸ hnot_all_in r
              exact hpi0 hpi0_in
            have hSlen : (suppF x).card ≤ 5 := by omega
            have hS4 : (suppF x).card = 4 := by omega
            have hnxt_mod : ∀ k : ℕ, ((nxt ht)^[k] i0).val % 3 = (i0.val + k) % 3 := by
              intro k
              induction k with
              | zero => simp
              | succ k ih =>
                rw [Function.iterate_succ_apply', nxt_mod3 ht]
                omega
            have hnxt_val : ∀ k : ℕ, ((nxt ht)^[k] i0).val = (i0.val + k) % (3 * t) := by
              intro k
              induction k with
              | zero => simp [Nat.mod_eq_of_lt i0.isLt]
              | succ k ih =>
                rw [Function.iterate_succ_apply']
                change (((nxt ht)^[k] i0).val + 1) % (3 * t) = (i0.val + (k + 1)) % (3 * t)
                rw [ih, ← Nat.add_assoc, Nat.mod_add_mod]
            have hS4_eq : suppF x = {(nxt ht)^[0] i0, (nxt ht)^[1] i0, (nxt ht)^[2] i0, (nxt ht)^[3] i0} := by
              let T4 : Finset (Fin (3 * t)) :=
                {(nxt ht)^[0] i0, (nxt ht)^[1] i0, (nxt ht)^[2] i0, (nxt ht)^[3] i0}
              have hsub4 : T4 ⊆ suppF x := by
                intro j hj
                simp only [T4, Finset.mem_insert, Finset.mem_singleton] at hj
                rcases hj with rfl | rfl | rfl | rfl
                · exact hstep_fwd 0 (by omega)
                · exact hstep_fwd 1 (by omega)
                · exact hstep_fwd 2 (by omega)
                · exact hstep_fwd 3 (by omega)
              have hinj4 : ∀ a b : ℕ, a < 4 → b < 4 → (nxt ht)^[a] i0 = (nxt ht)^[b] i0 → a = b := by
                intro a b ha hb heq
                have hv := congrArg Fin.val heq
                rw [hnxt_val a, hnxt_val b] at hv
                have hi0lt := i0.isLt
                have hmod_step : ∀ c : ℕ, c < 4 → (i0.val + c) % (3 * t) =
                    if i0.val + c < 3 * t then i0.val + c else i0.val + c - 3 * t := by
                  intro c hc
                  split_ifs with hlt
                  · exact Nat.mod_eq_of_lt hlt
                  · have hsub : i0.val + c = (i0.val + c - 3 * t) + 3 * t := by omega
                    conv_lhs => rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                rw [hmod_step a ha, hmod_step b hb] at hv
                split_ifs at hv <;> omega
              have hcardT4 : T4.card = 4 := by
                simp only [T4]
                rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                    Finset.card_insert_of_notMem, Finset.card_singleton]
                · intro h; simp only [Finset.mem_singleton] at h
                  have := hinj4 2 3 (by omega) (by omega) h; omega
                · intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
                  rcases h with h | h
                  · have := hinj4 1 2 (by omega) (by omega) h; omega
                  · have := hinj4 1 3 (by omega) (by omega) h; omega
                · intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
                  rcases h with h | h | h
                  · have := hinj4 0 1 (by omega) (by omega) h; omega
                  · have := hinj4 0 2 (by omega) (by omega) h; omega
                  · have := hinj4 0 3 (by omega) (by omega) h; omega
              exact (Finset.eq_of_subset_of_card_le hsub4 (by omega)).symm
            have hr_next := suppF_card_res_parity hx ⟨(i0.val + 1) % 3, Nat.mod_lt _ (by omega)⟩
            rw [hS4] at hr_next
            rw [hS4_eq] at hr_next
            have hm0 := hnxt_mod 0
            have hm1 := hnxt_mod 1
            have hm2 := hnxt_mod 2
            have hm3 := hnxt_mod 3
            have hne0 : ((nxt ht)^[0] i0).val % 3 ≠ (i0.val + 1) % 3 := by omega
            have heq1 : ((nxt ht)^[1] i0).val % 3 = (i0.val + 1) % 3 := by omega
            have hne2 : ((nxt ht)^[2] i0).val % 3 ≠ (i0.val + 1) % 3 := by omega
            have hne3 : ((nxt ht)^[3] i0).val % 3 ≠ (i0.val + 1) % 3 := by omega
            simp only [Finset.filter_insert, Finset.filter_singleton, hne0, heq1, hne2, hne3, if_true, if_false, Finset.insert_empty, Finset.card_singleton, Nat.reduceMod] at hr_next
            contradiction
        have hdrop0 : dualDrop (nbrF x) = 0 := by
          unfold dualDrop
          rw [if_neg huniv]
          have hno : ¬ ∃ r : Fin 3, ∀ i : Fin (3 * t), i.val % 3 ≠ r.val → i ∈ nbrF x := by
            rintro ⟨r, hr⟩
            have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) ⊆ nbrF x := by
              intro i hi; exact hr i (Finset.mem_filter.mp hi).2
            have hle := Finset.card_le_card hsub
            rw [card_compl_resClass r, hcard6] at hle
            have ht_eq3 : t = 3 := by omega
            have heq_set : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) = nbrF x :=
              Finset.eq_of_subset_of_card_le hsub (by rw [card_compl_resClass r, hcard6, ht_eq3])
            have hall_in : ∀ i ∈ nbrF x, i.val % 3 ≠ r.val := by
              intro i hi
              rw [← heq_set] at hi
              exact (Finset.mem_filter.mp hi).2
            have h1r := nbrF_subset_compl_res_imp hall_in
            obtain ⟨j, hj, hjne⟩ := h1res ⟨(r.val + 2) % 3, Nat.mod_lt _ (by omega)⟩
            exact hjne (h1r j hj)
          rw [if_neg hno]
        unfold rkC
        rw [hcard6, hdrop0]

lemma rkC_even_one_res_ge7 {t : ℕ} (ht : 0 < t) {x : Fin (3 * t) → F2}
    (r : Fin 3) (hres : ∀ i ∈ suppF x, i.val % 3 = r.val) (hw : 4 ≤ (suppF x).card) :
    7 ≤ rkC (nbrF x) := by
  have hcard : (nbrF x).card = 2 * (suppF x).card := card_nbrF_one_res ht r hres
  have hdrop : dualDrop (nbrF x) ≤ 1 := by
    unfold dualDrop
    have hne : nbrF x ≠ Finset.univ := by
      intro huniv
      have hmiss : ∀ i ∈ nbrF x, i.val % 3 ≠ (r.val + 1) % 3 := by
        intro i hi
        rw [mem_nbrF ht] at hi
        rcases hi with h | h
        · have := hres i (mem_suppF.mpr h); have := r.isLt; omega
        · have := hres (nxt ht i) (mem_suppF.mpr h)
          rw [nxt_mod3 ht] at this; have := r.isLt; omega
      exact hmiss ⟨(r.val + 1) % 3, by omega⟩ (by rw [huniv]; exact Finset.mem_univ _) (by simp)
    rw [if_neg hne]
    split_ifs <;> omega
  unfold rkC
  omega

def isTriple {t : ℕ} (ht : 0 < t) (x : Fin (3 * t) → F2) : Prop :=
  ∃ s : Fin (3 * t), suppF x = {s, nxt ht s, nxt ht (nxt ht s)}

lemma rkC_odd_ge6_of_wt_ge5 {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {x : Fin (3 * t) → F2}
    (hx : codeP t x) (hodd : (suppF x).card % 2 = 1) (hw : 5 ≤ (suppF x).card) :
    6 ≤ rkC (nbrF x) := by
  by_cases huniv : nbrF x = Finset.univ
  · unfold rkC dualDrop
    rw [if_pos huniv, huniv, Finset.card_univ, Fintype.card_fin]
    omega
  · have hSnotuniv : suppF x ≠ Finset.univ := by
      intro hu
      apply huniv
      ext i
      simp only [Finset.mem_univ, iff_true]
      exact Finset.mem_union_left _ (by rw [hu]; exact Finset.mem_univ i)
    have hx0 : x ≠ 0 := by
      intro h0
      have : suppF x = ∅ := by ext i; simp [suppF, h0]
      rw [this] at hw; simp at hw
    have hcard6 : 6 ≤ (nbrF x).card := by
      have := card_nbrF_gt_card_suppF ht hx0 hSnotuniv
      omega
    unfold rkC dualDrop
    rw [if_neg huniv]
    split_ifs with h1
    · obtain ⟨r, hr⟩ := h1
      obtain ⟨j, hjS, hjr⟩ := codeP_odd_hits_all_res hx hodd r
      have hj_nbr : j ∈ nbrF x := Finset.mem_union_left _ hjS
      have hsub : insert j (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val)) ⊆ nbrF x := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hj_nbr
        · exact hr i (Finset.mem_filter.mp hi).2
      have hnotmem : j ∉ Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) := by
        simp [hjr]
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnotmem, card_compl_resClass r] at hle
      omega
    · omega

lemma rkC_odd_wt3_eq_card {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {x : Fin (3 * t) → F2}
    (hx : codeP t x) (hw : (suppF x).card = 3) :
    rkC (nbrF x) = (nbrF x).card := by
  have hodd : (suppF x).card % 2 = 1 := by omega
  have hle6 : (nbrF x).card ≤ 6 := by
    unfold nbrF
    have h1 := Finset.card_union_le (suppF x) ((suppF x).image prv)
    have h2 := Finset.card_image_le (s := suppF x) (f := prv)
    omega
  unfold rkC dualDrop
  have huniv : nbrF x ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hle6
    omega
  rw [if_neg huniv]
  have hno : ¬ ∃ r : Fin 3, ∀ i : Fin (3 * t), i.val % 3 ≠ r.val → i ∈ nbrF x := by
    rintro ⟨r, hr⟩
    obtain ⟨j, hjS, hjr⟩ := codeP_odd_hits_all_res hx hodd r
    have hj_nbr : j ∈ nbrF x := Finset.mem_union_left _ hjS
    have hsub : insert j (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val)) ⊆ nbrF x := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hj_nbr
      · exact hr i (Finset.mem_filter.mp hi).2
    have hnotmem : j ∉ Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) := by
      simp [hjr]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotmem, card_compl_resClass r] at hle
    omega
  rw [if_neg hno, Nat.sub_zero]

lemma rkC_odd_ge4 {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {x : Fin (3 * t) → F2}
    (hx : codeP t x) (hodd : (suppF x).card % 2 = 1) :
    4 ≤ rkC (nbrF x) := by
  have hge3 : 3 ≤ (suppF x).card := by
    have h2 := suppF_card_ge_two hx (by
      intro h0; have : suppF x = ∅ := by ext i; simp [suppF, h0]
      rw [this] at hodd; simp at hodd)
    omega
  by_cases h3 : (suppF x).card = 3
  · rw [rkC_odd_wt3_eq_card ht ht3 hx h3]
    have hgt := card_nbrF_gt_card_suppF ht (x := x) (by
      intro h0; have : suppF x = ∅ := by ext i; simp [suppF, h0]
      rw [this] at h3; simp at h3) (by
      intro hu; rw [hu, Finset.card_univ, Fintype.card_fin] at h3; omega)
    omega
  · have h5 : 5 ≤ (suppF x).card := by omega
    have := rkC_odd_ge6_of_wt_ge5 ht ht3 hx hodd h5
    omega

lemma rkC_odd_eq4_iff_isTriple {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {x : Fin (3 * t) → F2}
    (hx : codeP t x) (hodd : (suppF x).card % 2 = 1) :
    rkC (nbrF x) = 4 ↔ isTriple ht x := by
  constructor
  · intro hrk4
    have h3 : (suppF x).card = 3 := by
      by_contra hne3
      have hge3 : 3 ≤ (suppF x).card := by
        have h2 := suppF_card_ge_two hx (by
          intro h0; have : suppF x = ∅ := by ext i; simp [suppF, h0]
          rw [this] at hodd; simp at hodd)
        omega
      have h5 : 5 ≤ (suppF x).card := by omega
      have := rkC_odd_ge6_of_wt_ge5 ht ht3 hx hodd h5
      omega
    rw [rkC_odd_wt3_eq_card ht ht3 hx h3] at hrk4
    let B := (suppF x).filter (fun i => prv i ∉ suppF x)
    have hBdisj : Disjoint (suppF x) (B.image prv) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj2
      exact (Finset.mem_filter.mp hi).2 hj1
    have hBsub : suppF x ∪ B.image prv ⊆ nbrF x := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_union_left _ hj
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem prv (Finset.mem_filter.mp hi).1)
    have hB_le : (suppF x).card + B.card ≤ (nbrF x).card := by
      have := Finset.card_le_card hBsub
      rwa [Finset.card_union_of_disjoint hBdisj, Finset.card_image_of_injective _ (prv_inj ht)] at this
    have hB_pos : 1 ≤ B.card := by
      by_contra hB0
      have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
      have hsub2 : nbrF x ⊆ suppF x := by
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · exact hj
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          by_contra hpi
          have : i ∈ B := Finset.mem_filter.mpr ⟨hi, hpi⟩
          simp [hBe] at this
      have := Finset.card_le_card hsub2
      omega
    have hB1 : B.card = 1 := by omega
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hB1
    have hsS : s ∈ suppF x := (Finset.mem_filter.mp (hs ▸ Finset.mem_singleton_self s)).1
    have hnotB : ∀ j ∈ suppF x, j ≠ s → prv j ∈ suppF x := by
      intro j hj hne
      by_contra hnj
      have : j ∈ B := Finset.mem_filter.mpr ⟨hj, hnj⟩
      rw [hs, Finset.mem_singleton] at this
      exact hne this
    have hpair_rem : ((suppF x).erase s).card = 2 := by
      rw [Finset.card_erase_of_mem hsS, h3]
    obtain ⟨a, b, hab, hrem⟩ := Finset.card_eq_two.mp hpair_rem
    have haS : a ∈ suppF x ∧ a ≠ s := by
      have : a ∈ (suppF x).erase s := hrem ▸ Finset.mem_insert_self a {b}
      exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
    have hbS : b ∈ suppF x ∧ b ≠ s := by
      have : b ∈ (suppF x).erase s := hrem ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
    have hpa : prv a ∈ suppF x := hnotB a haS.1 haS.2
    have hpb : prv b ∈ suppF x := hnotB b hbS.1 hbS.2
    have hS_eq : suppF x = {s, a, b} := by
      rw [← Finset.insert_erase hsS, hrem]
    have hpa_ne_a : prv a ≠ a := by
      intro h; have h1 := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      rw [prv_mod3] at h1; omega
    have hpb_ne_b : prv b ≠ b := by
      intro h; have h1 := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      rw [prv_mod3] at h1; omega
    have hpa_cases : prv a = s ∨ prv a = b := by
      rw [hS_eq] at hpa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpa
      rcases hpa with h | h | h
      · exact Or.inl h
      · exact absurd h hpa_ne_a
      · exact Or.inr h
    have hpb_cases : prv b = s ∨ prv b = a := by
      rw [hS_eq] at hpb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpb
      rcases hpb with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hpb_ne_b
    rcases hpa_cases with h1 | h1 <;> rcases hpb_cases with h2 | h2
    · exact absurd (prv_inj ht (h1.trans h2.symm)) hab
    · refine ⟨s, ?_⟩
      have ha' : a = nxt ht s := by rw [← h1, nxt_prv ht]
      have hb' : b = nxt ht (nxt ht s) := by rw [← ha', ← h2, nxt_prv ht]
      rw [hS_eq, ha', hb']
    · refine ⟨s, ?_⟩
      have hb' : b = nxt ht s := by rw [← h2, nxt_prv ht]
      have ha' : a = nxt ht (nxt ht s) := by rw [← hb', ← h1, nxt_prv ht]
      rw [hS_eq, ha', hb']
      ext i; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · have h2step : prv (prv a) = a := by rw [h1, h2]
      have hmod := congrArg (fun z : Fin (3 * t) => z.val % 3) h2step
      have hm1 := prv_mod3 (prv a)
      have hm2 := prv_mod3 a
      omega
  · rintro ⟨s, hs⟩
    have hinj01 : s ≠ nxt ht s := by
      intro h; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      rw [nxt_mod3 ht] at this; omega
    have hinj02 : s ≠ nxt ht (nxt ht s) := by
      intro h; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      have hm1 := nxt_mod3 ht (nxt ht s); have hm2 := nxt_mod3 ht s; omega
    have hinj12 : nxt ht s ≠ nxt ht (nxt ht s) := fun h => hinj01 (nxt_inj ht h)
    have hw : (suppF x).card = 3 := by
      rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hinj12]
      · simp [hinj01, hinj02]
    rw [rkC_odd_wt3_eq_card ht ht3 hx hw]
    have hnbr : nbrF x = {prv s, s, nxt ht s, nxt ht (nxt ht s)} := by
      ext i
      simp only [nbrF, hs, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ((rfl | rfl | rfl) | ⟨j, (rfl | rfl | rfl), rfl⟩)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inl rfl
        · rw [prv_nxt ht]; exact Or.inr (Or.inl rfl)
        · rw [prv_nxt ht]; exact Or.inr (Or.inr (Or.inl rfl))
      · rintro (rfl | rfl | rfl | rfl)
        · exact Or.inr ⟨s, Or.inl rfl, rfl⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr rfl))
    have hps0 : prv s ≠ s := by
      intro h; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      rw [prv_mod3] at this; omega
    have hps1 : prv s ≠ nxt ht s := by
      intro h; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      rw [prv_mod3, nxt_mod3 ht] at this; omega
    have hps2 : prv s ≠ nxt ht (nxt ht s) := by
      intro h
      have h1 := congrArg Fin.val (congrArg (nxt ht) h)
      rw [nxt_prv ht] at h1
      have hv1 := nxt_val ht s
      have hv2 := nxt_val ht (nxt ht s)
      have hv3 := nxt_val ht (nxt ht (nxt ht s))
      have hs' := s.isLt
      have hs1' := (nxt ht s).isLt
      have hs2' := (nxt ht (nxt ht s)).isLt
      split_ifs at hv1 hv2 hv3 <;> omega
    rw [hnbr, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hinj12]
    · simp [hinj01, hinj02]
    · simp [hps0, hps1, hps2]

end lane_code

section top_and_t2

def formP {t : ℕ} (ht : 0 < t) (U V : Submodule F2 (Fin (3 * t) → F2)) : Prop :=
  (∀ y, y ∈ V ↔ codeP t y) ∧
    ((t = 2 ∧ ∀ x : Fin (3 * t) → F2, x ∈ U ↔ ∀ i, x i = x (ix ht (i.val + 3))) ∨
     (t = 3 ∧ ∃ s : Fin (3 * t), ∀ x : Fin (3 * t) → F2, x ∈ U ↔ codeP t x ∧ ∀ i, x i ≠ 0 →
        i.val % 3 = s.val % 3 ∨ i = ix ht (s.val + 1) ∨ i = ix ht (s.val + 2)) ∨
     (4 ≤ t ∧ ∃ (T : Finset (Fin (3 * t))) (e : Fin 3),
        T.card = 4 ∧ (∀ i ∈ T, i.val % 3 = e.val) ∧ ∀ x : Fin (3 * t) → F2,
          x ∈ U ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0))

lemma formP_rev {t : ℕ} (ht : 0 < t) (U V : Submodule F2 (Fin (3 * t) → F2)) :
    formP ht (Submodule.map (revEquiv t).toLinearMap U) (Submodule.map (revEquiv t).toLinearMap V) ↔
      formP ht U V := by
  have hrev2 : ∀ x : Fin (3 * t) → F2, revEquiv t (revEquiv t x) = x := (revEquiv t).left_inv
  have hmem : ∀ (M : Submodule F2 (Fin (3 * t) → F2)) (x : Fin (3 * t) → F2),
      x ∈ Submodule.map (revEquiv t).toLinearMap M ↔ revEquiv t x ∈ M := by
    intro M x
    constructor
    · rintro ⟨w, hw, rfl⟩
      change revEquiv t (revEquiv t w) ∈ M
      rwa [hrev2]
    · intro h
      exact ⟨revEquiv t x, h, hrev2 x⟩
  have hV : (∀ y, y ∈ Submodule.map (revEquiv t).toLinearMap V ↔ codeP t y) ↔
      (∀ y, y ∈ V ↔ codeP t y) := by
    constructor
    · intro h y
      have := h (revEquiv t y)
      rw [hmem, show revEquiv t (revEquiv t y) = y from (revEquiv t).left_inv y] at this
      exact this.trans rev_codeP
    · intro h y
      rw [hmem, h, rev_codeP]
  unfold formP
  rw [hV]
  apply and_congr_right
  intro _
  apply or_congr
  · apply and_congr_right
    intro ht2
    subst t
    have hidx2 : ∀ i : Fin (3 * 2), revIdx (ix ht (i.val + 3)) = ix ht ((revIdx i).val + 3) := by
      intro i
      apply Fin.ext
      change 3 * 2 - 1 - ((i.val + 3) % (3 * 2)) = (3 * 2 - 1 - i.val + 3) % (3 * 2)
      have hi := i.isLt
      omega
    have hrev_iff2 : ∀ x : Fin (3 * 2) → F2,
        (∀ i, revEquiv 2 x i = revEquiv 2 x (ix ht (i.val + 3))) ↔
        (∀ i, x i = x (ix ht (i.val + 3))) := by
      intro x
      constructor
      · intro hp i
        have := hp (revIdx i)
        change x (revIdx (revIdx i)) = x (revIdx (ix ht ((revIdx i).val + 3))) at this
        rw [revIdx_revIdx, ← hidx2 i, revIdx_revIdx] at this
        exact this
      · intro hp i
        change x (revIdx i) = x (revIdx (ix ht (i.val + 3)))
        rw [hidx2 i]
        exact hp (revIdx i)
    constructor
    · intro h x
      have hx := h (revEquiv 2 x)
      rw [hmem, hrev2] at hx
      exact hx.trans (hrev_iff2 x)
    · intro h x
      rw [hmem, h, hrev_iff2]
  apply or_congr
  · apply and_congr_right
    intro ht3
    have hshift : ∀ s : Fin (3 * t), ∃ s' : Fin (3 * t),
        ∀ i : Fin (3 * t),
          ((revIdx i).val % 3 = s.val % 3 ∨ revIdx i = ix ht (s.val + 1) ∨ revIdx i = ix ht (s.val + 2)) ↔
          (i.val % 3 = s'.val % 3 ∨ i = ix ht (s'.val + 1) ∨ i = ix ht (s'.val + 2)) := by
      intro s
      let s' : Fin (3 * t) := ⟨(14 - s.val) % (3 * t), Nat.mod_lt _ (by omega)⟩
      refine ⟨s', fun i => ?_⟩
      have hi := i.isLt
      have hs := s.isLt
      have h1 : (revIdx i).val % 3 = s.val % 3 ↔ i.val % 3 = s'.val % 3 := by
        rw [revIdx_mod3]
        change 2 - i.val % 3 = s.val % 3 ↔ i.val % 3 = ((14 - s.val) % (3 * t)) % 3
        subst t
        omega
      have h2 : revIdx i = ix ht (s.val + 1) ↔ i = ix ht (s'.val + 2) := by
        constructor <;> intro heq <;> apply Fin.ext <;>
          have hv := congrArg Fin.val heq <;>
          dsimp only [revIdx, ix, s'] at hv ⊢ <;> subst t <;> omega
      have h3 : revIdx i = ix ht (s.val + 2) ↔ i = ix ht (s'.val + 1) := by
        constructor <;> intro heq <;> apply Fin.ext <;>
          have hv := congrArg Fin.val heq <;>
          dsimp only [revIdx, ix, s'] at hv ⊢ <;> subst t <;> omega
      tauto
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨s', hs'⟩ := hshift s
      refine ⟨s', fun x => ?_⟩
      have hx := hs (revEquiv t x)
      rw [hmem, hrev2, rev_codeP] at hx
      rw [hx]
      apply and_congr_right
      intro _
      constructor
      · intro h i hi
        have h' : revEquiv t x (revIdx i) ≠ 0 := by
          change x (revIdx (revIdx i)) ≠ 0; rwa [revIdx_revIdx]
        exact (hs' i).mp (h (revIdx i) h')
      · intro h i hi
        have h' : x (revIdx i) ≠ 0 := hi
        have := (hs' (revIdx i)).mpr (h (revIdx i) h')
        simpa [revIdx_revIdx] using this
    · rintro ⟨s, hs⟩
      obtain ⟨s', hs'⟩ := hshift s
      refine ⟨s', fun x => ?_⟩
      rw [hmem, hs, rev_codeP]
      apply and_congr_right
      intro _
      constructor
      · intro h i hi
        have h' : revEquiv t x (revIdx i) ≠ 0 := by
          change x (revIdx (revIdx i)) ≠ 0; rwa [revIdx_revIdx]
        exact (hs' i).mp (h (revIdx i) h')
      · intro h i hi
        have h' : x (revIdx i) ≠ 0 := hi
        have := (hs' (revIdx i)).mpr (h (revIdx i) h')
        simpa [revIdx_revIdx] using this
  · apply and_congr_right
    intro _
    have hmapT : ∀ (T : Finset (Fin (3 * t))) (e : Fin 3),
        T.card = 4 → (∀ i ∈ T, i.val % 3 = e.val) →
        ∃ (T' : Finset (Fin (3 * t))) (e' : Fin 3),
          T'.card = 4 ∧ (∀ i ∈ T', i.val % 3 = e'.val) ∧
          (∀ i, i ∈ T' ↔ revIdx i ∈ T) := by
      intro T e hcard hres
      let T' := T.image revIdx
      let e' : Fin 3 := ⟨2 - e.val, by have := e.isLt; omega⟩
      have hinj : Function.Injective (@revIdx t) :=
        fun a b h => by simpa [revIdx_revIdx] using congrArg revIdx h
      refine ⟨T', e', by rw [Finset.card_image_of_injective _ hinj, hcard], ?_, ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        rw [revIdx_mod3, hres j hj]
      · intro i
        simp only [T', Finset.mem_image]
        exact ⟨fun ⟨j, hj, hji⟩ => by rw [← hji, revIdx_revIdx]; exact hj,
               fun h => ⟨revIdx i, h, revIdx_revIdx i⟩⟩
    have hsum_rev : ∀ x : Fin (3 * t) → F2, (∑ i, revEquiv t x i) = ∑ i, x i := fun x =>
      Finset.sum_bij (fun i _ => revIdx i) (fun _ _ => Finset.mem_univ _)
        (fun a b _ _ h => by simpa [revIdx_revIdx] using congrArg revIdx h)
        (fun j _ => ⟨revIdx j, Finset.mem_univ _, revIdx_revIdx j⟩) (fun _ _ => rfl)
    constructor
    · rintro ⟨T, e, hcard, hres, hU⟩
      obtain ⟨T', e', hcard', hres', hiff⟩ := hmapT T e hcard hres
      refine ⟨T', e', hcard', hres', fun x => ?_⟩
      have hx := hU (revEquiv t x)
      rw [hmem, show revEquiv t (revEquiv t x) = x from (revEquiv t).left_inv x, hsum_rev] at hx
      rw [hx]
      apply and_congr_left
      intro _
      constructor
      · intro h i hi
        have := h (revIdx i) (fun hmemT => hi ((hiff i).mpr hmemT))
        simpa [revEquiv, revIdx_revIdx] using this
      · intro h i hi
        have := h (revIdx i) (fun hmemT' => hi (by simpa [revIdx_revIdx] using (hiff (revIdx i)).mp hmemT'))
        exact this
    · rintro ⟨T, e, hcard, hres, hU⟩
      obtain ⟨T', e', hcard', hres', hiff⟩ := hmapT T e hcard hres
      refine ⟨T', e', hcard', hres', fun x => ?_⟩
      rw [hmem, hU, hsum_rev]
      apply and_congr_left
      intro _
      constructor
      · intro h i hi
        have := h (revIdx i) (fun hmemT => hi ((hiff i).mpr hmemT))
        simpa [revEquiv, revIdx_revIdx] using this
      · intro h i hi
        have := h (revIdx i) (fun hmemT' => hi (by simpa [revIdx_revIdx] using (hiff (revIdx i)).mp hmemT'))
        exact this

lemma top_exact_t2 {t : ℕ} (ht : 0 < t) (ht2 : t = 2)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hQ : ∀ y, y ∈ Q ↔ codeP t y)
    (hP : ∀ x : Fin (3 * t) → F2, x ∈ P ↔ ∀ i, x i = x (ix ht (i.val + 3))) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} =
      416 * (Nat.card P * Nat.card Q) := by
  subst ht2
  letI : Fintype P := Fintype.ofFinite P
  have hQeq : Q = codeSub 2 := by ext y; rw [hQ, mem_codeSub]
  let eP : P ≃ (Fin 3 → F2) :=
    { toFun := fun x j => x.1 ⟨j.val, by omega⟩
      invFun := fun f => ⟨fun i => f ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩, (hP _).mpr fun i => by
        have hi := i.isLt
        congr 1; apply Fin.ext; dsimp [ix]; omega⟩
      left_inv := fun x => by
        ext i
        have hp := (hP x.1).mp x.2 i
        have hi := i.isLt
        dsimp only
        by_cases h3 : i.val < 3
        · have hmod : (⟨i.val % 3, by omega⟩ : Fin (3 * 2)) = i := Fin.ext (Nat.mod_eq_of_lt h3)
          rw [hmod]
        · have hidx : ix ht (i.val + 3) = ⟨i.val % 3, by omega⟩ := by
            apply Fin.ext; dsimp [ix]; omega
          rw [hp, hidx]
      right_inv := fun f => by
        ext j; dsimp only; have hj := j.isLt
        have hmod : (⟨j.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = j := Fin.ext (Nat.mod_eq_of_lt hj)
        rw [hmod] }
  have hcardP : Nat.card P = 8 := by
    rw [Nat.card_congr eP, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hQcard : ∀ x : P, Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val) = Nat.card Q := by
    intro x; subst hQeq; exact card_hit_code_eq ht x.val
  have hrows : 256 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} = 416 * Nat.card Q := by
    rw [card_rows (P := fun (x : P) (y : Q) => hitP ht x.val y.val), Finset.mul_sum]
    have hrk_le : ∀ x : P, rkC (nbrF x.val) ≤ 8 := fun x => by
      unfold rkC
      have := Finset.card_le_univ (nbrF x.val)
      rw [Fintype.card_fin] at this
      omega
    have hstep : ∀ x : P, 256 * Nat.card {y : Q // hitP ht x.val y.val} =
        (256 / 2 ^ rkC (nbrF x.val)) * Nat.card Q := by
      intro x
      have hdvd : 2 ^ rkC (nbrF x.val) ∣ 256 := by
        rw [show (256 : ℕ) = 2 ^ 8 by norm_num]
        exact pow_dvd_pow 2 (hrk_le x)
      calc 256 * Nat.card {y : Q // hitP ht x.val y.val}
          = (256 / 2 ^ rkC (nbrF x.val)) * (Nat.card {y : Q // hitP ht x.val y.val} *
              2 ^ rkC (nbrF x.val)) := by rw [mul_left_comm, Nat.div_mul_cancel hdvd, mul_comm]
        _ = (256 / 2 ^ rkC (nbrF x.val)) * Nat.card Q := by rw [hQcard x]
    simp_rw [hstep, ← Finset.sum_mul]
    congr 1
    rw [Fintype.sum_equiv eP (fun x : P => 256 / 2 ^ rkC (nbrF x.val))
      (fun f => 256 / 2 ^ rkC (nbrF (eP.symm f).val)) (fun x => by rw [eP.symm_apply_apply])]
    exact dec_t2_top_sum
  rw [hcardP]
  linarith

set_option maxHeartbeats 2000000 in
lemma top_exact_t3 {t : ℕ} (ht : 0 < t) (ht3 : t = 3)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hQ : ∀ y, y ∈ Q ↔ codeP t y)
    (s : Fin (3 * t))
    (hP : ∀ x : Fin (3 * t) → F2, x ∈ P ↔ codeP t x ∧ ∀ i, x i ≠ 0 →
      i.val % 3 = s.val % 3 ∨ i = ix ht (s.val + 1) ∨ i = ix ht (s.val + 2)) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} =
      348 * (Nat.card P * Nat.card Q) := by
  subst ht3
  letI : Fintype P := Fintype.ofFinite P
  have hQeq : Q = codeSub 3 := by ext y; rw [hQ, mem_codeSub]
  let eP : (Fin 3 → F2) ≃ P :=
    { toFun := fun f => ⟨top3Vec s f, (hP _).mpr (top3_encode s f).1⟩
      invFun := fun x => top3Read s x.val
      left_inv := fun f => (top3_encode s f).2
      right_inv := fun x => Subtype.ext (top3_decode s x.val ((hP _).mp x.property)) }
  have hcardP : Nat.card P = 8 := by
    rw [← Nat.card_congr eP, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hQcard : ∀ x : P, Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val) = Nat.card Q := by
    intro x; subst hQeq; exact card_hit_code_eq ht x.val
  have hrows : 256 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} = 348 * Nat.card Q := by
    rw [card_rows (P := fun (x : P) (y : Q) => hitP ht x.val y.val), Finset.mul_sum]
    have hrk_le : ∀ x : P, rkC (nbrF x.val) ≤ 8 := fun x => by
      unfold rkC
      have := Finset.card_le_univ (nbrF x.val)
      rw [Fintype.card_fin] at this
      by_cases hu : nbrF x.val = Finset.univ
      · unfold dualDrop; rw [if_pos hu, hu, Finset.card_univ, Fintype.card_fin]; omega
      · have hlt : (nbrF x.val).card < 9 := by
          have hne := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hu⟩
          simpa using Finset.card_lt_card hne
        omega
    have hstep : ∀ x : P, 256 * Nat.card {y : Q // hitP ht x.val y.val} =
        (256 / 2 ^ rkC (nbrF x.val)) * Nat.card Q := by
      intro x
      have hdvd : 2 ^ rkC (nbrF x.val) ∣ 256 := by
        rw [show (256 : ℕ) = 2 ^ 8 by norm_num]
        exact pow_dvd_pow 2 (hrk_le x)
      calc 256 * Nat.card {y : Q // hitP ht x.val y.val}
          = (256 / 2 ^ rkC (nbrF x.val)) * (Nat.card {y : Q // hitP ht x.val y.val} *
              2 ^ rkC (nbrF x.val)) := by rw [mul_left_comm, Nat.div_mul_cancel hdvd, mul_comm]
        _ = (256 / 2 ^ rkC (nbrF x.val)) * Nat.card Q := by rw [hQcard x]
    simp_rw [hstep, ← Finset.sum_mul]
    congr 1
    exact (Fintype.sum_equiv eP (fun f => 256 / 2 ^ rkC (nbrF ((eP f).val)))
      (fun x : P => 256 / 2 ^ rkC (nbrF x.val)) (fun _ => rfl)).symm.trans (dec_t3_top_sum ht s)
  rw [hcardP]
  linarith

lemma top_exact_ge4 {t : ℕ} (ht : 0 < t) (ht4 : 4 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hQ : ∀ y, y ∈ Q ↔ codeP t y)
    (T : Finset (Fin (3 * t))) (e : Fin 3)
    (hTcard : T.card = 4) (hTres : ∀ i ∈ T, i.val % 3 = e.val)
    (hP : ∀ x : Fin (3 * t) → F2, x ∈ P ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} =
      (if t = 4 then 354 else 353) * (Nat.card P * Nat.card Q) := by
  letI : Fintype P := Fintype.ofFinite P
  have hQeq : Q = codeSub t := by ext y; rw [hQ, mem_codeSub]
  have hPsub : P ≤ codeSub t := by
    intro x hx
    rw [mem_codeSub, codeP_iff_resSum]
    obtain ⟨hsupp, hsum0⟩ := (hP x).mp hx
    have hzero : ∀ r : Fin 3, resSum t r.val x = 0 := by
      intro r
      unfold resSum
      by_cases hre : r = e
      · subst hre
        have : (∑ i : Fin (3 * t), if i.val % 3 = r.val then x i else 0) = ∑ i : Fin (3 * t), x i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hiT : i ∈ T
          · rw [if_pos (hTres i hiT)]
          · simp [hsupp i hiT]
        rw [this, hsum0]
      · refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hiT : i ∈ T
        · have : i.val % 3 ≠ r.val := by
            rw [hTres i hiT]
            intro h; exact hre (Fin.ext h.symm)
          simp [this]
        · simp [hsupp i hiT]
    exact ⟨(hzero 0).trans (hzero 2).symm, (hzero 1).trans (hzero 2).symm⟩
  have hPeq : P = codeSub t ⊓ suppSub T := by
    ext x
    simp only [Submodule.mem_inf, mem_codeSub, suppSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro hx
      exact ⟨mem_codeSub.mp (hPsub hx), ((hP x).mp hx).1⟩
    · rintro ⟨hxc, hxT⟩
      rw [hP]
      refine ⟨hxT, ?_⟩
      have hother : ∃ r : Fin 3, r ≠ e := by
        fin_cases e
        · exact ⟨1, fin3_one_ne_zero⟩
        · exact ⟨0, fin3_zero_ne_one⟩
        · exact ⟨0, fin3_zero_ne_two⟩
      obtain ⟨r, hre⟩ := hother
      rw [← codeP_resSum_eq_total hxc r]
      unfold resSum
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hiT : i ∈ T
      · have : i.val % 3 ≠ r.val := by
          rw [hTres i hiT]; intro h; exact hre (Fin.ext h.symm)
        simp [this]
      · simp [hxT i hiT]
  have hdimP : Module.finrank F2 P = 3 := by
    rw [hPeq, finrank_code_inf_suppSub_one_res T (Finset.card_pos.mp (by omega)) e hTres, hTcard]
  have hcardP : Nat.card P = 8 := by
    rw [card_eq_two_pow_finrank, hdimP]; norm_num
  have hQcard : ∀ x : P, Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val) = Nat.card Q := by
    intro x; subst hQeq; exact card_hit_code_eq ht x.val
  let indT : Fin (3 * t) → F2 := fun i => if i ∈ T then 1 else 0
  have hindT_mem : indT ∈ P := by
    rw [hP]
    refine ⟨fun i hi => by simp [indT, hi], ?_⟩
    have : (∑ i : Fin (3 * t), indT i) = (T.card : F2) := by
      simp [indT]
    rw [this, hTcard]
    exact z2_four_eq_zero
  have hsupp_indT : suppF indT = T := by
    ext i; simp [suppF, indT]
  have hrk_indT : rkC (nbrF indT) = if t = 4 then 7 else 8 := by
    have hcard8 : (nbrF indT).card = 8 := by
      rw [card_nbrF_one_res ht e (by rw [hsupp_indT]; exact hTres), hsupp_indT, hTcard]
    unfold rkC
    rw [hcard8]
    by_cases ht4eq : t = 4
    · rw [if_pos ht4eq]
      have hdrop1 : dualDrop (nbrF indT) = 1 := by
        unfold dualDrop
        have huniv : nbrF indT ≠ Finset.univ := by
          intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hcard8; omega
        rw [if_neg huniv]
        have hex : ∃ r : Fin 3, ∀ i : Fin (3 * t), i.val % 3 ≠ r.val → i ∈ nbrF indT := by
          refine ⟨⟨(e.val + 1) % 3, Nat.mod_lt _ (by omega)⟩, fun i hi => ?_⟩
          have hsub_compl : nbrF indT ⊆ Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ (e.val + 1) % 3) := by
            intro j hj
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [mem_nbrF ht] at hj
            rcases hj with h | h
            · have hjT : j ∈ T := by rw [← hsupp_indT]; exact mem_suppF.mpr h
              have := hTres j hjT; have := e.isLt; omega
            · have hjT : nxt ht j ∈ T := by rw [← hsupp_indT]; exact mem_suppF.mpr h
              have := hTres (nxt ht j) hjT
              rw [nxt_mod3 ht] at this; have := e.isLt; omega
          have heq := Finset.eq_of_subset_of_card_le hsub_compl (by
            rw [card_compl_resClass ⟨(e.val + 1) % 3, Nat.mod_lt _ (by omega)⟩, hcard8, ht4eq])
          rw [heq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        rw [if_pos hex]
      rw [hdrop1]
    · rw [if_neg ht4eq]
      rw [dualDrop_eq_zero_of_lt_2t ht (by omega)]
  have hclass : ∀ x : P, x.val = 0 ∨ x.val = indT ∨ (suppF x.val).card = 2 := by
    intro x
    obtain ⟨hsupp, hsum0⟩ := (hP x.val).mp x.2
    have hsubT : suppF x.val ⊆ T := by
      intro i hi
      by_contra hiT
      exact mem_suppF.mp hi (hsupp i hiT)
    have hle4 : (suppF x.val).card ≤ 4 := by
      rw [← hTcard]; exact Finset.card_le_card hsubT
    have heven : (suppF x.val).card % 2 = 0 := by
      have h2 : (∑ i : Fin (3 * t), x.val i) = ((suppF x.val).card : F2) := by
        rw [← z2_sum_const_mod2, suppF, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hx0 : x.val i = 0
        · simp [hx0]
        · simp [hx0, z2_eq_one_of_ne_zero hx0]
      rw [hsum0] at h2
      exact (z2_natCast_eq_zero_iff _).mp h2.symm
    have h024 : (suppF x.val).card = 0 ∨ (suppF x.val).card = 2 ∨ (suppF x.val).card = 4 := by omega
    rcases h024 with h0 | h2 | h4
    · left
      ext i
      by_contra hi
      have : i ∈ suppF x.val := mem_suppF.mpr hi
      rw [Finset.card_eq_zero.mp h0] at this
      exact Finset.notMem_empty _ this
    · right; right; exact h2
    · right; left
      have heqT : suppF x.val = T := Finset.eq_of_subset_of_card_le hsubT (by omega)
      ext i
      dsimp only [indT]
      by_cases hiT : i ∈ T
      · rw [if_pos hiT]
        exact z2_eq_one_of_ne_zero (mem_suppF.mp (heqT.symm ▸ hiT))
      · rw [if_neg hiT]
        exact hsupp i hiT
  have hrows : 256 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} =
      (if t = 4 then 354 else 353) * Nat.card Q := by
    rw [card_rows (P := fun (x : P) (y : Q) => hitP ht x.val y.val), Finset.mul_sum]
    have hval : ∀ x : P, 256 * Nat.card {y : Q // hitP ht x.val y.val} =
        (if x.val = 0 then 256 else if x.val = indT then (if t = 4 then 2 else 1) else 16) *
          Nat.card Q := by
      intro x
      rcases hclass x with hx0 | hxT | hxw2
      · rw [if_pos hx0]
        have heq : Nat.card {y : Q // hitP ht x.val y.val} = Nat.card Q := by
          refine Nat.card_congr (Equiv.subtypeUnivEquiv fun y i => by simp [hx0])
        rw [heq]
      · have hne0 : x.val ≠ 0 := by
          intro h0
          rw [h0] at hxT
          have : (suppF indT).card = 0 := by rw [← hxT]; simp [suppF]
          rw [hsupp_indT, hTcard] at this
          omega
        rw [if_neg hne0, if_pos hxT]
        have hq := hQcard x
        rw [hxT, hrk_indT] at hq
        rw [hxT]; split_ifs at hq ⊢ <;> linarith
      · have hne0 : x.val ≠ 0 := by
          intro h0; rw [h0] at hxw2; simp [suppF] at hxw2
        have hneT : x.val ≠ indT := by
          intro hT; rw [hT, hsupp_indT, hTcard] at hxw2; omega
        rw [if_neg hne0, if_neg hneT]
        have hq := hQcard x
        have hrk4 := rkC_even_wt2 ht (by omega) (mem_codeSub.mp (hPsub x.2)) hxw2
        rw [hrk4] at hq
        linarith
    simp_rw [hval, ← Finset.sum_mul]
    congr 1
    let p0 : P := ⟨0, zero_mem P⟩
    let pT : P := ⟨indT, hindT_mem⟩
    have hp0T : p0 ≠ pT := by
      intro h
      have h1 : (0 : Fin (3 * t) → F2) = indT := congrArg Subtype.val h
      have : (suppF indT).card = 0 := by rw [← h1]; simp [suppF]
      rw [hsupp_indT, hTcard] at this; omega
    have hsplit : (∑ x : P, (if x.val = 0 then 256 else if x.val = indT then (if t = 4 then 2 else 1) else 16)) =
        256 + (if t = 4 then 2 else 1) + ∑ x ∈ (Finset.univ.erase p0).erase pT, 16 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0)]
      have hpT_mem : pT ∈ (Finset.univ : Finset P).erase p0 :=
        Finset.mem_erase.mpr ⟨hp0T.symm, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hpT_mem]
      have h0v : (if p0.val = 0 then 256 else if p0.val = indT then (if t = 4 then 2 else 1) else 16) = 256 := by
        simp [p0]
      have hTv : (if pT.val = 0 then 256 else if pT.val = indT then (if t = 4 then 2 else 1) else 16) =
          (if t = 4 then 2 else 1) := by
        have hne : pT.val ≠ 0 := fun h => hp0T (Subtype.ext h.symm)
        simp [pT, hne]
      rw [h0v, hTv, add_assoc]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxT : x ≠ pT := Finset.ne_of_mem_erase hx
      have hx0 : x ≠ p0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hx0v : x.val ≠ 0 := fun h => hx0 (Subtype.ext h)
      have hxTv : x.val ≠ indT := fun h => hxT (Subtype.ext h)
      simp [hx0v, hxTv]
    rw [hsplit, Finset.sum_const, smul_eq_mul]
    have hrem : ((Finset.univ.erase p0).erase pT).card = 6 := by
      have hpT_mem : pT ∈ (Finset.univ : Finset P).erase p0 :=
        Finset.mem_erase.mpr ⟨hp0T.symm, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem hpT_mem, Finset.card_erase_of_mem (Finset.mem_univ p0),
          Finset.card_univ, ← Nat.card_eq_fintype_card, hcardP]
    rw [hrem]
    split_ifs <;> norm_num
  rw [hcardP]
  linarith

lemma t2_not_top {t : ℕ} (ht : 0 < t) (ht2 : t = 2)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hle : Module.finrank F2 P ≤ Module.finrank F2 Q)
    (hnt : ¬ formP ht P Q) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      400 * (Nat.card P * Nat.card Q) := by
  subst ht2
  letI : Fintype P := Fintype.ofFinite P
  have hPsub : P ≤ codeSub 2 := fun x hx => mem_codeSub.mpr (hP x hx)
  have hQsub : Q ≤ codeSub 2 := fun y hy => mem_codeSub.mpr (hQ y hy)
  have hdimQle : Module.finrank F2 Q ≤ 4 := by
    have := Submodule.finrank_mono hQsub
    rwa [finrank_codeSub ht] at this
  have hdimQ : Module.finrank F2 Q = 4 := by omega
  have hQeq : Q = codeSub 2 :=
    Submodule.eq_of_le_of_finrank_eq hQsub (by rw [hdimQ, finrank_codeSub ht])
  have hQcard : ∀ x : P, Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val) = Nat.card Q := by
    intro x; subst hQeq; exact card_hit_code_eq ht x.val
  have hrk_all := dec_t2_rk_all
  have hdimP34 : Module.finrank F2 P = 3 ∨ Module.finrank F2 P = 4 := by omega
  rcases hdimP34 with hdimP3 | hdimP4
  · have hcardP : Nat.card P = 8 := by rw [card_eq_two_pow_finrank, hdimP3]; norm_num
    let pairsP := (Finset.univ : Finset P).filter (fun x => (suppF x.val).card = 2)
    have hpairs_le2 : pairsP.card ≤ 2 := by
      by_contra hge3
      have hge3' : 3 ≤ pairsP.card := by omega
      let allPairs : Finset (Fin (3 * 2) → F2) :=
        Finset.univ.filter (fun x => codeP 2 x ∧ (suppF x).card = 2)
      have hall3 : allPairs.card = 3 := dec_t2_allPairs_card
      have hsub : pairsP.image Subtype.val ⊆ allPairs := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP p.1 p.2, (Finset.mem_filter.mp hp).2⟩
      have heq_pairs : pairsP.image Subtype.val = allPairs :=
        Finset.eq_of_subset_of_card_le hsub (by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, hall3]; omega)
      let U0 : Submodule F2 (Fin (3 * 2) → F2) :=
        { add_mem' := fun ha hb i => by simp [ha i, hb i]
          carrier := {x | ∀ i, x i = x (ix ht (i.val + 3))}
          zero_mem' := fun _ => rfl
          smul_mem' := fun c _ ha i => by simp [ha i] }
      have hU0_le : U0 ≤ P := by
        intro x hx
        have hdecomp : ∀ u : Fin (3 * 2) → F2, (∀ i, u i = u (ix ht (i.val + 3))) →
            u = u 0 • (fun i : Fin (3 * 2) => if i = 0 ∨ i = 3 then 1 else 0) +
                u 1 • (fun i : Fin (3 * 2) => if i = 1 ∨ i = 4 then 1 else 0) +
                u 2 • (fun i : Fin (3 * 2) => if i = 2 ∨ i = 5 then 1 else 0) := by
          intro u hu
          ext i
          fin_cases i
          · simp
          · simp
          · simp
          · have := hu 0; simpa [ix] using this.symm
          · have := hu 1; simpa [ix] using this.symm
          · have := hu 2; simpa [ix] using this.symm
        have hm0 : (fun i : Fin (3 * 2) => if i = 0 ∨ i = 3 then (1 : F2) else 0) ∈ P := by
          have : (fun i : Fin (3 * 2) => if i = 0 ∨ i = 3 then (1 : F2) else 0) ∈ allPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, dec_t2_pair0⟩
          rw [← heq_pairs] at this
          obtain ⟨p, _, hp⟩ := Finset.mem_image.mp this
          exact hp ▸ p.2
        have hm1 : (fun i : Fin (3 * 2) => if i = 1 ∨ i = 4 then (1 : F2) else 0) ∈ P := by
          have : (fun i : Fin (3 * 2) => if i = 1 ∨ i = 4 then (1 : F2) else 0) ∈ allPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, dec_t2_pair1⟩
          rw [← heq_pairs] at this
          obtain ⟨p, _, hp⟩ := Finset.mem_image.mp this
          exact hp ▸ p.2
        have hm2 : (fun i : Fin (3 * 2) => if i = 2 ∨ i = 5 then (1 : F2) else 0) ∈ P := by
          have : (fun i : Fin (3 * 2) => if i = 2 ∨ i = 5 then (1 : F2) else 0) ∈ allPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, dec_t2_pair2⟩
          rw [← heq_pairs] at this
          obtain ⟨p, _, hp⟩ := Finset.mem_image.mp this
          exact hp ▸ p.2
        rw [hdecomp x hx]
        exact P.add_mem (P.add_mem (P.smul_mem _ hm0) (P.smul_mem _ hm1)) (P.smul_mem _ hm2)
      have hU0_card : Nat.card U0 = 8 := by
        let eU : U0 ≃ (Fin 3 → F2) :=
          { toFun := fun x j => x.1 ⟨j.val, by omega⟩
            invFun := fun f => ⟨fun i => f ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩, fun i => by
              change f ⟨i.val % 3, _⟩ = f ⟨((i.val + 3) % 6) % 3, _⟩
              exact congrArg f (Fin.ext (by dsimp; omega))⟩
            left_inv := fun x => by
              ext i; dsimp only
              have hi := i.isLt
              by_cases h3 : i.val < 3
              · have hmod : (⟨i.val % 3, by omega⟩ : Fin (3 * 2)) = i := Fin.ext (Nat.mod_eq_of_lt h3)
                rw [hmod]
              · have hp := x.2 i
                have hidx : ix ht (i.val + 3) = ⟨i.val % 3, by omega⟩ := by
                  apply Fin.ext; dsimp [ix]; omega
                rw [hp, hidx]
            right_inv := fun f => by
              ext j; dsimp only; have hj := j.isLt
              have hmod : (⟨j.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = j := Fin.ext (Nat.mod_eq_of_lt hj)
              rw [hmod] }
        rw [Nat.card_congr eU, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num
      have hdimU0 : Module.finrank F2 U0 = 3 := by
        have h := card_eq_two_pow_finrank (V := U0)
        rw [hU0_card] at h
        have : 2 ^ 3 = 2 ^ Module.finrank F2 U0 := by linarith
        exact (Nat.pow_right_injective (by norm_num : 1 < 2) this).symm
      have hPU0 : U0 = P := Submodule.eq_of_le_of_finrank_eq hU0_le (by omega)
      apply hnt
      refine ⟨fun y => by rw [hQeq, mem_codeSub], Or.inl ⟨rfl, fun x => by rw [← hPU0]; rfl⟩⟩
    have hrows : 256 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤ 400 * Nat.card Q := by
      rw [card_rows (P := fun (x : P) (y : Q) => hitP ht x.val y.val), Finset.mul_sum]
      have hterm : ∀ x : P, 256 * Nat.card {y : Q // hitP ht x.val y.val} =
          (if x.val = 0 then 256 else if (suppF x.val).card = 2 then 32 else 16) * Nat.card Q := by
        intro x
        have hq := hQcard x
        rcases hrk_all x.val (hP x.val x.2) with ⟨h0, hr⟩ | ⟨hw2, hr⟩ | ⟨hne0, hnew2, hr⟩
        · rw [if_pos h0]; rw [hr] at hq; linarith
        · have hne0 : x.val ≠ 0 := by intro h; rw [h] at hw2; simp [suppF] at hw2
          rw [if_neg hne0, if_pos hw2]; rw [hr] at hq; linarith
        · rw [if_neg hne0, if_neg hnew2]; rw [hr] at hq; linarith
      simp_rw [hterm, ← Finset.sum_mul]
      refine Nat.mul_le_mul_right _ ?_
      let p0 : P := ⟨0, zero_mem P⟩
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0)]
      have h0v : (if p0.val = 0 then 256 else if (suppF p0.val).card = 2 then 32 else 16) = 256 := by
        simp [p0]
      rw [h0v]
      have hrem : (∑ x ∈ (Finset.univ : Finset P).erase p0,
          (if x.val = 0 then 256 else if (suppF x.val).card = 2 then 32 else 16)) =
          16 * 7 + 16 * pairsP.card := by
        have hrew : ∀ x ∈ (Finset.univ : Finset P).erase p0,
            (if x.val = 0 then 256 else if (suppF x.val).card = 2 then 32 else 16) =
            16 + (if (suppF x.val).card = 2 then 16 else 0) := by
          intro x hx
          have hne : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase hx (Subtype.ext h)
          simp only [hne, ↓reduceIte]
          split_ifs <;> norm_num
        rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ,
            ← Nat.card_eq_fintype_card, hcardP]
        have hp0_not : p0 ∉ pairsP := by simp [pairsP, p0, suppF]
        have hpairs_eq : ((Finset.univ : Finset P).erase p0).filter (fun x => (suppF x.val).card = 2) =
            pairsP := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, pairsP, true_and]
          exact ⟨fun h => h.2, fun h => ⟨fun h0 => hp0_not (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), h⟩⟩
        rw [← Finset.sum_filter, hpairs_eq, Finset.sum_const, smul_eq_mul]
        ring
      rw [hrem]
      omega
    rw [hcardP]
    linarith
  · have hPeq : P = codeSub 2 :=
      Submodule.eq_of_le_of_finrank_eq hPsub (by rw [hdimP4, finrank_codeSub ht])
    have hcardP : Nat.card P = 16 := by rw [card_eq_two_pow_finrank, hdimP4]; norm_num
    have hrows : 128 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤ 400 * Nat.card Q := by
      rw [card_rows (P := fun (x : P) (y : Q) => hitP ht x.val y.val), Finset.mul_sum]
      have hterm : ∀ x : P, 128 * Nat.card {y : Q // hitP ht x.val y.val} ≤
          (if x.val = 0 then 128 else 16) * Nat.card Q := by
        intro x
        have hq := hQcard x
        rcases hrk_all x.val (hP x.val x.2) with ⟨h0, hr⟩ | ⟨hw2, hr⟩ | ⟨hne0, _, hr⟩
        · rw [if_pos h0]; rw [hr] at hq; linarith
        · have hne0 : x.val ≠ 0 := by intro h; rw [h] at hw2; simp [suppF] at hw2
          rw [if_neg hne0]; rw [hr] at hq; linarith
        · rw [if_neg hne0]; rw [hr] at hq; linarith
      calc ∑ x : P, 128 * Nat.card {y : Q // hitP ht x.val y.val}
          ≤ ∑ x : P, (if x.val = 0 then 128 else 16) * Nat.card Q :=
            Finset.sum_le_sum fun x _ => hterm x
        _ = (∑ x : P, if x.val = 0 then 128 else 16) * Nat.card Q := (Finset.sum_mul _ _ _).symm
        _ ≤ 400 * Nat.card Q := by
            refine Nat.mul_le_mul_right _ ?_
            let p0 : P := ⟨0, zero_mem P⟩
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0)]
            have h0v : (if p0.val = 0 then 128 else 16) = 128 := by simp [p0]
            rw [h0v]
            have hrem : ∑ x ∈ (Finset.univ : Finset P).erase p0,
                (if x.val = 0 then 128 else 16) = 15 * 16 := by
              rw [Finset.sum_congr (g := fun _ => (16 : ℕ)) rfl (fun x hx => by
                have hne : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase hx (Subtype.ext h)
                simp [hne]), Finset.sum_const, smul_eq_mul,
                Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ,
                ← Nat.card_eq_fintype_card, hcardP]
            rw [hrem]
            norm_num
    rw [hcardP]
    linarith

end top_and_t2

section matroid_inter

variable {U V : Type*} [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]

def CommonIndep {m : ℕ} (a : Fin m → U) (b : Fin m → V) (I : Finset (Fin m)) : Prop :=
  LinearIndependent F2 (fun i : I => a i.val) ∧ LinearIndependent F2 (fun i : I => b i.val)

section Abs

open Module

variable {ι : Type*} [DecidableEq ι]

def IsRk (r : Finset ι → ℕ) : Prop :=
  r ∅ = 0 ∧ (∀ A B : Finset ι, A ⊆ B → r A ≤ r B) ∧
  (∀ A B : Finset ι, r (A ∪ B) + r (A ∩ B) ≤ r A + r B) ∧ (∀ a : ι, r {a} ≤ 1)

theorem rk_insert_le {r : Finset ι → ℕ} (h : IsRk r) (a : ι) (A : Finset ι) :
    r (insert a A) ≤ r {a} + r A := by
  have := h.2.2.1 {a} A
  rw [← Finset.insert_eq] at this
  omega

theorem rk_union_le {r : Finset ι → ℕ} (h : IsRk r) (A D : Finset ι) :
    r (A ∪ D) ≤ r A + D.card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert x D hx ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hx]
    have h1 := rk_insert_le h x (A ∪ D)
    have h2 := h.2.2.2 x
    omega

theorem rk_le_sum {r : Finset ι → ℕ} (h : IsRk r) (A : Finset ι) :
    r A ≤ ∑ e ∈ A, r {e} := by
  induction A using Finset.induction_on with
  | empty => simp [h.1]
  | insert x A hx ih =>
    rw [Finset.sum_insert hx]
    have h1 := rk_insert_le h x A
    omega

theorem weak {r1 r2 : Finset ι → ℕ} (h1 : IsRk r1) (h2 : IsRk r2) (S A E : Finset ι)
    (hS : S ⊆ E) (i1 : r1 S = S.card) (i2 : r2 S = S.card) :
    S.card ≤ r1 A + r2 (E \ A) := by
  have e1 : S ∩ A ∪ S \ A = S := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have e2 : S \ A ∪ S ∩ A = S := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have a1 := rk_union_le h1 (S ∩ A) (S \ A)
  have b1 := rk_union_le h2 (S \ A) (S ∩ A)
  rw [e1] at a1
  rw [e2] at b1
  have a2 := h1.2.1 (S ∩ A) A Finset.inter_subset_right
  have b2 := h2.2.1 (S \ A) (E \ A) (Finset.sdiff_subset_sdiff hS le_rfl)
  have c := Finset.card_inter_add_card_sdiff S A
  omega

theorem contr {r : Finset ι → ℕ} (h : IsRk r) (e : ι) (he : r {e} = 1) :
    IsRk (fun A => r (insert e A) - 1) := by
  have lb : ∀ A : Finset ι, 1 ≤ r (insert e A) := fun A => by
    have := h.2.1 {e} (insert e A) (by simp)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [he]
  · intro A B hAB
    have := h.2.1 _ _ (Finset.insert_subset_insert e hAB)
    simp only
    omega
  · intro A B
    have := h.2.2.1 (insert e A) (insert e B)
    rw [← Finset.insert_union_distrib, ← Finset.insert_inter_distrib] at this
    have := lb A
    have := lb B
    have := lb (A ∪ B)
    have := lb (A ∩ B)
    simp only
    omega
  · intro a
    have h1 := rk_insert_le h e {a}
    have h2 := h.2.2.2 a
    simp only
    omega

theorem inter (n : ℕ) : ∀ (r1 r2 : Finset ι → ℕ), IsRk r1 → IsRk r2 → ∀ E : Finset ι,
    E.card = n → ∃ S ⊆ E, ∃ C ⊆ E, r1 S = S.card ∧ r2 S = S.card ∧
      r1 C + r2 (E \ C) = S.card := by
  induction n with
  | zero =>
    intro r1 r2 h1 h2 E hE
    rw [Finset.card_eq_zero] at hE
    subst hE
    exact ⟨∅, subset_refl _, ∅, subset_refl _, by simp [h1.1, h2.1]⟩
  | succ n ih =>
    intro r1 r2 h1 h2 E hE
    by_cases hx : ∃ e ∈ E, r1 {e} = 1 ∧ r2 {e} = 1
    · obtain ⟨e, heE, he1, he2⟩ := hx
      have hcard : (E.erase e).card = n := by rw [Finset.card_erase_of_mem heE]; omega
      obtain ⟨S1, hS1, A, hA, i1, j1, c1⟩ := ih r1 r2 h1 h2 _ hcard
      obtain ⟨S2, hS2, B, hB, i2, j2, c2⟩ :=
        ih _ _ (contr h1 e he1) (contr h2 e he2) _ hcard
      obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image E.powerset
        (fun C => r1 C + r2 (E \ C)) ⟨∅, Finset.empty_mem_powerset E⟩
      rw [Finset.mem_powerset] at hC
      have heS2 : e ∉ S2 := fun h => by have := hS2 h; simp at this
      have heA : e ∉ A := fun h => by have := hA h; simp at this
      have heB : e ∉ B := fun h => by have := hB h; simp at this
      have lb1 := h1.2.1 {e} (insert e S2) (by simp)
      have lb2 := h2.2.1 {e} (insert e S2) (by simp)
      have hS1E : S1 ⊆ E := hS1.trans (Finset.erase_subset e E)
      have hS2E : insert e S2 ⊆ E :=
        Finset.insert_subset heE (hS2.trans (Finset.erase_subset e E))
      have k1 : r1 (insert e S2) = (insert e S2).card := by
        rw [Finset.card_insert_of_notMem heS2]; omega
      have k2 : r2 (insert e S2) = (insert e S2).card := by
        rw [Finset.card_insert_of_notMem heS2]; omega
      by_cases hp : r1 C + r2 (E \ C) ≤ S1.card
      · refine ⟨S1, hS1E, C, hC, i1, j1, ?_⟩
        have := weak h1 h2 S1 C E hS1E i1 j1
        omega
      by_cases hq : r1 C + r2 (E \ C) ≤ S2.card + 1
      · refine ⟨insert e S2, hS2E, C, hC, k1, k2, ?_⟩
        have := weak h1 h2 _ C E hS2E k1 k2
        rw [Finset.card_insert_of_notMem heS2] at this ⊢
        omega
      exfalso
      have hAE : A ⊆ E := hA.trans (Finset.erase_subset e E)
      have hBE : insert e B ⊆ E := Finset.insert_subset heE (hB.trans (Finset.erase_subset e E))
      have s1 := h1.2.2.1 A (insert e B)
      have s2 := h2.2.2.1 ((E.erase e) \ A) (E \ B)
      have m1 := hmin (A ∩ insert e B)
        (Finset.mem_powerset.2 (Finset.inter_subset_left.trans hAE))
      have m2 := hmin (A ∪ insert e B) (Finset.mem_powerset.2 (Finset.union_subset hAE hBE))
      have q1 : (E.erase e \ A) ∪ (E \ B) = E \ (A ∩ insert e B) := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heA, heB, heE]
        · simp [hxe]; tauto
      have q2 : (E.erase e \ A) ∩ (E \ B) = E \ (A ∪ insert e B) := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heA, heB, heE]
        · simp [hxe]; tauto
      have q3 : insert e (E.erase e \ B) = E \ B := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heB, heE]
        · simp [hxe]
      rw [q1, q2] at s2
      rw [q3] at c2
      have lb3 := h1.2.1 {e} (insert e B) (by simp)
      have lb4 := h2.2.1 {e} (E \ B) (by simp [heE, heB])
      omega
    · simp only [not_exists, not_and] at hx
      refine ⟨∅, Finset.empty_subset _, E.filter (fun e => r1 {e} = 0),
        Finset.filter_subset _ _, by simp [h1.1], by simp [h2.1], ?_⟩
      have a := rk_le_sum h1 (E.filter (fun e => r1 {e} = 0))
      have b := rk_le_sum h2 (E \ E.filter (fun e => r1 {e} = 0))
      rw [Finset.sum_eq_zero (fun i hi => (Finset.mem_filter.1 hi).2)] at a
      rw [Finset.sum_eq_zero] at b
      · simp only [Finset.card_empty]; omega
      · intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hi
        have h3 := h1.2.2.2 i
        have h4 := h2.2.2.2 i
        have h5 := hx i hi.1
        have h6 := hi.2 hi.1
        omega

end Abs

section Lin

open Module

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  {ι : Type*} [DecidableEq ι]

noncomputable def lrk (u : ι → V) (A : Finset ι) : ℕ :=
  finrank F (Submodule.span F (u '' (A : Set ι)))

theorem lrk_isRk [FiniteDimensional F V] (u : ι → V) : IsRk (lrk (F := F) u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [lrk]
  · intro A B hAB
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 hAB)))
  · intro A B
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (u '' (A : Set ι)))
      (Submodule.span F (u '' (B : Set ι)))
    have e : Submodule.span F (u '' ((A ∪ B : Finset ι) : Set ι)) =
        Submodule.span F (u '' (A : Set ι)) ⊔ Submodule.span F (u '' (B : Set ι)) := by
      rw [Finset.coe_union, Set.image_union, Submodule.span_union]
    have hle : Submodule.span F (u '' ((A ∩ B : Finset ι) : Set ι)) ≤
        Submodule.span F (u '' (A : Set ι)) ⊓ Submodule.span F (u '' (B : Set ι)) :=
      le_inf (Submodule.span_mono (Set.image_mono (by simp)))
        (Submodule.span_mono (Set.image_mono (by simp)))
    have := Submodule.finrank_mono hle
    unfold lrk
    rw [e]
    omega
  · intro a
    unfold lrk
    rw [Finset.coe_singleton, Set.image_singleton]
    by_cases hv : u a = 0
    · rw [hv, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]; omega
    · rw [finrank_span_singleton hv]

theorem li_iff (u : ι → V) (S : Finset ι) :
    LinearIndependent F (fun i : S => u i.val) ↔ lrk (F := F) u S = S.card := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_coe]
  have : Set.range (fun i : S => u i.val) = u '' (S : Set ι) := by
    ext x; simp
  unfold Set.finrank lrk
  rw [this]
  constructor <;> intro h <;> omega

end Lin

lemma linear_matroid_intersection {m : ℕ} (a : Fin m → U) (b : Fin m → V) (k : ℕ)
    (hcut : ∀ S : Finset (Fin m),
      k ≤ Module.finrank F2 (Submodule.span F2 (a '' (S : Set (Fin m)))) +
          Module.finrank F2 (Submodule.span F2 (b '' ((Sᶜ : Finset (Fin m)) : Set (Fin m))))) :
    ∃ I : Finset (Fin m), I.card = k ∧ CommonIndep a b I := by
  obtain ⟨S, _, C, _, hA, hB, hSC⟩ :=
    inter _ _ _ (lrk_isRk (F := F2) a) (lrk_isRk (F := F2) b) Finset.univ rfl
  have hle := hcut C
  have hr : k ≤ S.card := by
    rw [← hSC]
    simpa only [lrk, Finset.compl_eq_univ_sdiff] using hle
  obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq hr
  let inc : I → S := fun i => ⟨i.val, hI i.property⟩
  have hinj : Function.Injective inc := fun i j h => Subtype.ext (congrArg (fun z : S => z.val) h)
  exact ⟨I, hcard, ((li_iff a S).mpr hA).comp inc hinj, ((li_iff b S).mpr hB).comp inc hinj⟩

end matroid_inter

section two_large_lanes

lemma card_six_indep_extra_in_span (a b : Fin 6 → F2) (ha : a ≠ 0) (hb : b ≠ 0)
    (hnc : ∀ j : Fin 6, ¬ (a = Pi.single j 1 ∧ b = Pi.single j 1)) :
    Nat.card {uv : (Fin 6 → F2) × (Fin 6 → F2) //
      (∀ j : Fin 6, uv.1 j * uv.2 j = 0) ∧
      (∑ j : Fin 6, a j * uv.1 j) * (∑ j : Fin 6, b j * uv.2 j) = 0} ≤ 648 := by
  have hex : ∃ j k : Fin 6, j ≠ k ∧ a j = 1 ∧ b k = 1 := by
    have ha1 : ∃ j : Fin 6, a j = 1 := by
      by_contra h; push Not at h; apply ha; ext j
      rcases z2_cases (a j) with h0 | h1; exact h0; exact absurd h1 (h j)
    obtain ⟨j, haj⟩ := ha1
    by_cases hbk : ∃ k : Fin 6, k ≠ j ∧ b k = 1
    · obtain ⟨k, hkj, hbk⟩ := hbk; exact ⟨j, k, hkj.symm, haj, hbk⟩
    · push Not at hbk
      have hb_eq : b = Pi.single j 1 := by
        ext m
        by_cases hmj : m = j
        · subst hmj
          simp only [Pi.single_eq_same]
          by_contra hbj
          have hbj0 : b m = 0 := by rcases z2_cases (b m) with h0 | h1; exact h0; exact absurd h1 hbj
          apply hb; ext r
          by_cases hrm : r = m
          · simp [hrm, hbj0]
          · rcases z2_cases (b r) with h0 | h1; exact h0; exact absurd h1 (hbk r hrm)
        · simp only [Pi.single_eq_of_ne hmj]
          rcases z2_cases (b m) with h0 | h1; exact h0; exact absurd h1 (hbk m hmj)
      have ha_ne : a ≠ Pi.single j 1 := fun h => hnc j ⟨h, hb_eq⟩
      have ha_other : ∃ j' : Fin 6, j' ≠ j ∧ a j' = 1 := by
        by_contra h; push Not at h; apply ha_ne; ext m
        by_cases hmj : m = j
        · rw [hmj, Pi.single_eq_same, haj]
        · rw [Pi.single_eq_of_ne hmj]
          rcases z2_cases (a m) with h0 | h1; exact h0; exact absurd h1 (h m hmj)
      obtain ⟨j', hj'j, haj'⟩ := ha_other
      exact ⟨j', j, hj'j, haj', by rw [hb_eq, Pi.single_eq_same]⟩
  obtain ⟨j0, k0, hjk, haj0, hbk0⟩ := hex
  let rest : Finset (Fin 6) := (Finset.univ.erase j0).erase k0
  have hrest_card : rest.card = 4 := by
    have hk_mem : k0 ∈ (Finset.univ : Finset (Fin 6)).erase j0 :=
      Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem hk_mem, Finset.card_erase_of_mem (Finset.mem_univ j0),
        Finset.card_univ, Fintype.card_fin]
  let Good6 := {uv : (Fin 6 → F2) × (Fin 6 → F2) // ∀ j : Fin 6, uv.1 j * uv.2 j = 0}
  let GoodExtra := {uv : (Fin 6 → F2) × (Fin 6 → F2) //
    (∀ j : Fin 6, uv.1 j * uv.2 j = 0) ∧
    (∑ j : Fin 6, a j * uv.1 j) * (∑ j : Fin 6, b j * uv.2 j) = 0}
  let Bad := {uv : (Fin 6 → F2) × (Fin 6 → F2) //
    (∀ j : Fin 6, uv.1 j * uv.2 j = 0) ∧
    (∑ j : Fin 6, a j * uv.1 j) * (∑ j : Fin 6, b j * uv.2 j) ≠ 0}
  have hcard6 : Nat.card Good6 = 729 := by
    let e : Good6 ≃ (Fin 6 → {p : F2 × F2 // p.1 * p.2 = 0}) :=
      ⟨fun uv j => ⟨(uv.1.1 j, uv.1.2 j), uv.2 j⟩,
       fun f => ⟨(fun j => (f j).1.1, fun j => (f j).1.2), fun j => (f j).2⟩,
       fun _ => rfl, fun _ => rfl⟩
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, card_z2_zero_prod]
    norm_num
  let RestValid := rest → {p : F2 × F2 // p.1 * p.2 = 0}
  have hcard_rest : Nat.card RestValid = 81 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, hrest_card, card_z2_zero_prod]
    norm_num
  let mkBad : RestValid → Bad := fun f =>
    let ca : F2 := ∑ m ∈ rest, if h : m ∈ rest then a m * (f ⟨m, h⟩).1.1 else 0
    let cb : F2 := ∑ m ∈ rest, if h : m ∈ rest then b m * (f ⟨m, h⟩).1.2 else 0
    let u : Fin 6 → F2 := fun m =>
      if m = j0 then 1 + ca else if m = k0 then 0 else if h : m ∈ rest then (f ⟨m, h⟩).1.1 else 0
    let v : Fin 6 → F2 := fun m =>
      if m = j0 then 0 else if m = k0 then 1 + cb else if h : m ∈ rest then (f ⟨m, h⟩).1.2 else 0
    ⟨(u, v), by
      constructor
      · intro m
        dsimp only [u, v]
        by_cases hm1 : m = j0
        · simp [hm1]
        · by_cases hm2 : m = k0
          · rw [if_neg hm1, if_pos hm2, if_neg hm1, if_pos hm2, zero_mul]
          · have hmr : m ∈ rest := Finset.mem_erase.mpr ⟨hm2, Finset.mem_erase.mpr ⟨hm1, Finset.mem_univ _⟩⟩
            simp [hm1, hm2, hmr, (f ⟨m, hmr⟩).2]
      · have hsum_u : (∑ m : Fin 6, a m * u m) = 1 := by
          have hmemk : k0 ∈ (Finset.univ : Finset (Fin 6)).erase j0 :=
            Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), ← Finset.add_sum_erase _ _ hmemk]
          have hjv : a j0 * u j0 = 1 + ca := by simp [u, haj0]
          have hkv : a k0 * u k0 = 0 := by simp [u, hjk.symm]
          have hrv : (∑ m ∈ rest, a m * u m) = ca := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hm2 : m ≠ k0 := Finset.ne_of_mem_erase hm
            have hm1 : m ≠ j0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
            simp [u, hm1, hm2, hm]
          rw [hjv, hkv, zero_add]
          change (1 + ca) + ∑ m ∈ rest, a m * u m = 1
          rw [hrv, add_assoc, z2_add_self, add_zero]
        have hsum_v : (∑ m : Fin 6, b m * v m) = 1 := by
          have hmemk : k0 ∈ (Finset.univ : Finset (Fin 6)).erase j0 :=
            Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), ← Finset.add_sum_erase _ _ hmemk]
          have hjv : b j0 * v j0 = 0 := by simp [v]
          have hkv : b k0 * v k0 = 1 + cb := by simp [v, hjk.symm, hbk0]
          have hrv : (∑ m ∈ rest, b m * v m) = cb := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hm2 : m ≠ k0 := Finset.ne_of_mem_erase hm
            have hm1 : m ≠ j0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
            simp [v, hm1, hm2, hm]
          rw [hjv, hkv, zero_add]
          change (1 + cb) + ∑ m ∈ rest, b m * v m = 1
          rw [hrv, add_assoc, z2_add_self, add_zero]
        rw [hsum_u, hsum_v, mul_one]
        exact z2_one_ne_zero⟩
  have hmk_inj : Function.Injective mkBad := by
    intro f1 f2 heq
    funext ⟨m, hm⟩
    have hm2 : m ≠ k0 := Finset.ne_of_mem_erase hm
    have hm1 : m ≠ j0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
    have h1 := congrFun (congrArg (fun z => z.1.1) heq) m
    have h2 := congrFun (congrArg (fun z => z.1.2) heq) m
    simp only [mkBad, hm1, hm2, hm, ↓reduceIte, ↓reduceDIte] at h1 h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hbad_ge : 81 ≤ Nat.card Bad := by
    rw [← hcard_rest]
    exact Nat.card_le_card_of_injective mkBad hmk_inj
  have hsum_card : Nat.card GoodExtra + Nat.card Bad = Nat.card Good6 := by
    let e : GoodExtra ⊕ Bad ≃ Good6 :=
      ⟨fun s => s.elim (fun x => ⟨x.1, x.2.1⟩) (fun x => ⟨x.1, x.2.1⟩),
       fun x => if h : (∑ j : Fin 6, a j * x.1.1 j) * (∑ j : Fin 6, b j * x.1.2 j) = 0
                then Sum.inl ⟨x.1, x.2, h⟩ else Sum.inr ⟨x.1, x.2, h⟩,
       fun s => by
         cases s with
         | inl x => simp [x.2.2]
         | inr x => simp [x.2.2],
       fun x => by
         by_cases h : (∑ j : Fin 6, a j * x.1.1 j) * (∑ j : Fin 6, b j * x.1.2 j) = 0
         · simp [h]
         · simp [h]⟩
    rw [← Nat.card_sum, Nat.card_congr e]
  change Nat.card GoodExtra ≤ 648
  omega

set_option maxHeartbeats 2000000 in
lemma card_six_indep_extra_half (a : Fin 6 → F2) (ha : a ≠ 0) :
    Nat.card {uv : (Fin 6 → F2) × (Fin 7 → F2) //
      (∀ j : Fin 6, uv.1 j * uv.2 ⟨j.val, by omega⟩ = 0) ∧
      (∑ j : Fin 6, a j * uv.1 j) * uv.2 ⟨6, by omega⟩ = 0} ≤ 1215 := by
  have ha1 : ∃ j0 : Fin 6, a j0 = 1 := by
    by_contra h; push Not at h; apply ha; ext j
    rcases z2_cases (a j) with h0 | h1; exact h0; exact absurd h1 (h j)
  obtain ⟨j0, haj0⟩ := ha1
  let Good := {uv : (Fin 6 → F2) × (Fin 7 → F2) //
    (∀ j : Fin 6, uv.1 j * uv.2 ⟨j.val, by omega⟩ = 0) ∧
    (∑ j : Fin 6, a j * uv.1 j) * uv.2 ⟨6, by omega⟩ = 0}
  let All := {uv : (Fin 6 → F2) × (Fin 7 → F2) //
    ∀ j : Fin 6, uv.1 j * uv.2 ⟨j.val, by omega⟩ = 0}
  let Bad := {uv : (Fin 6 → F2) × (Fin 7 → F2) //
    (∀ j : Fin 6, uv.1 j * uv.2 ⟨j.val, by omega⟩ = 0) ∧
    (∑ j : Fin 6, a j * uv.1 j) * uv.2 ⟨6, by omega⟩ ≠ 0}
  have hcardAll : Nat.card All = 1458 := by
    let e : All ≃ (Fin 6 → {p : F2 × F2 // p.1 * p.2 = 0}) × F2 :=
      ⟨fun uv => (fun j => ⟨(uv.1.1 j, uv.1.2 ⟨j.val, by omega⟩), uv.2 j⟩, uv.1.2 ⟨6, by omega⟩),
       fun p => ⟨(fun j => (p.1 j).1.1, fun j => if h : j.val < 6 then (p.1 ⟨j.val, h⟩).1.2 else p.2),
         fun j => by simp [j.isLt, (p.1 j).2]⟩,
       fun uv => by
         ext j
         · rfl
         · by_cases h : j.val < 6
           · simp [h]
           · have hj6 : j = (⟨6, by omega⟩ : Fin 7) := Fin.ext (by have := j.isLt; dsimp; omega)
             simp [h, hj6],
       fun p => by
         ext j
         · rfl
         · simp
         · simp⟩
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fun, Fintype.card_fin, card_z2_zero_prod]
    norm_num
  let rest : Finset (Fin 6) := Finset.univ.erase j0
  let RestValid := rest → {p : F2 × F2 // p.1 * p.2 = 0}
  have hcard_rest : Nat.card RestValid = 243 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe,
        Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin, card_z2_zero_prod]
    norm_num
  let mkBad : RestValid → Bad := fun f =>
    let ca : F2 := ∑ m ∈ rest, if h : m ∈ rest then a m * (f ⟨m, h⟩).1.1 else 0
    let u : Fin 6 → F2 := fun m =>
      if m = j0 then 1 + ca else if h : m ∈ rest then (f ⟨m, h⟩).1.1 else 0
    let v : Fin 7 → F2 := fun m =>
      if h : m.val < 6 then
        if (⟨m.val, h⟩ : Fin 6) = j0 then 0
        else if hr : (⟨m.val, h⟩ : Fin 6) ∈ rest then (f ⟨⟨m.val, h⟩, hr⟩).1.2 else 0
      else 1
    ⟨(u, v), by
      constructor
      · intro m
        dsimp only [u, v]
        simp only [m.isLt, ↓reduceDIte]
        by_cases hm : m = j0
        · simp [hm]
        · have hmr : m ∈ rest := Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩
          simp [hm, hmr, (f ⟨m, hmr⟩).2]
      · have hsum_u : (∑ m : Fin 6, a m * u m) = 1 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
          have hjv : a j0 * u j0 = 1 + ca := by simp [u, haj0]
          have hrv : (∑ m ∈ rest, a m * u m) = ca := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hm1 : m ≠ j0 := Finset.ne_of_mem_erase hm
            simp [u, hm1, hm]
          rw [hjv]
          change (1 + ca) + ∑ m ∈ rest, a m * u m = 1
          rw [hrv, add_assoc, z2_add_self, add_zero]
        have hv6 : v ⟨6, by omega⟩ = 1 := by simp [v]
        change (∑ m, a m * u m) * v ⟨6, by decide⟩ ≠ 0
        rw [hsum_u, hv6, mul_one]
        exact z2_one_ne_zero⟩
  have hmk_inj : Function.Injective mkBad := by
    intro f1 f2 heq
    funext ⟨m, hm⟩
    have hm1 : m ≠ j0 := Finset.ne_of_mem_erase hm
    have h1 := congrFun (congrArg (fun z => z.1.1) heq) m
    have h2 := congrFun (congrArg (fun z => z.1.2) heq) ⟨m.val, by omega⟩
    simp only [mkBad, hm1, hm, m.isLt, ↓reduceIte, ↓reduceDIte] at h1 h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hbad_ge : 243 ≤ Nat.card Bad := by
    rw [← hcard_rest]
    exact Nat.card_le_card_of_injective mkBad hmk_inj
  have hsum_card : Nat.card Good + Nat.card Bad = Nat.card All := by
    let p := fun uv : (Fin 6 → F2) × (Fin 7 → F2) =>
      ∀ j : Fin 6, uv.1 j * uv.2 j.castSucc = 0
    let q := fun uv : (Fin 6 → F2) × (Fin 7 → F2) =>
      (∑ j, a j * uv.1 j) * uv.2 (Fin.last 6) = 0
    let eg : {x : Subtype p // q x.val} ≃ Good := Equiv.subtypeSubtypeEquivSubtypeInter p q
    let eb : {x : Subtype p // ¬ q x.val} ≃ Bad := Equiv.subtypeSubtypeEquivSubtypeInter p (fun x => ¬ q x)
    let e : Good ⊕ Bad ≃ All := (Equiv.sumCongr eg.symm eb.symm).trans (Equiv.sumCompl (fun x : Subtype p => q x.val))
    rw [← Nat.card_sum, Nat.card_congr e]
  change Nat.card Good ≤ 1215
  omega

lemma card_seven_indep :
    Nat.card {uv : (Fin 7 → F2) × (Fin 7 → F2) // ∀ j : Fin 7, uv.1 j * uv.2 j = 0} = 2187 := by
  let e : {uv : (Fin 7 → F2) × (Fin 7 → F2) // ∀ j : Fin 7, uv.1 j * uv.2 j = 0} ≃
      (Fin 7 → {p : F2 × F2 // p.1 * p.2 = 0}) :=
    ⟨fun uv j => ⟨(uv.1.1 j, uv.1.2 j), uv.2 j⟩,
     fun f => ⟨(fun j => (f j).1.1, fun j => (f j).1.2), fun j => (f j).2⟩,
     fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, card_z2_zero_prod]
  norm_num

lemma extra_product_bound {X Y : Type*} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X] [Finite X]
    [AddCommGroup Y] [Module F2 Y] [FiniteDimensional F2 Y] [Finite Y]
    (L : Fin 6 → (X →ₗ[F2] F2)) (M : Fin 6 → (Y →ₗ[F2] F2))
    (hL : LinearIndependent F2 L) (hM : LinearIndependent F2 M)
    (L' : X →ₗ[F2] F2) (M' : Y →ₗ[F2] F2)
    (hL'0 : L' ≠ 0) (hM'0 : M' ≠ 0)
    (hnew : ∀ j : Fin 6, ¬ (L' = L j ∧ M' = M j))
    (H : X → Y → Prop)
    (hH : ∀ x y, H x y → (∀ j : Fin 6, L j x * M j y = 0) ∧ L' x * M' y = 0) :
    2048 * Nat.card {w : X × Y // H w.1 w.2} ≤ 324 * (Nat.card X * Nat.card Y) := by
  by_cases hLin : L' ∈ Submodule.span F2 (Set.range L)
  · rw [Finsupp.mem_span_range_iff_exists_finsupp] at hLin
    obtain ⟨ca, hca⟩ := hLin
    have hca_eq : L' = ∑ j : Fin 6, ca j • L j := by
      exact hca.symm.trans (Finsupp.sum_fintype ca (fun j z => z • L j) (fun j => zero_smul _ _))
    have ha0 : (fun j => ca j) ≠ 0 := by
      intro h0
      apply hL'0
      rw [hca_eq]
      exact Finset.sum_eq_zero fun j _ => by simp only [congrFun h0 j, Pi.zero_apply, zero_smul]
    by_cases hMin : M' ∈ Submodule.span F2 (Set.range M)
    · rw [Finsupp.mem_span_range_iff_exists_finsupp] at hMin
      obtain ⟨cb, hcb⟩ := hMin
      have hcb_eq : M' = ∑ j : Fin 6, cb j • M j := by
        exact hcb.symm.trans (Finsupp.sum_fintype cb (fun j z => z • M j) (fun j => zero_smul _ _))
      have hb0 : (fun j => cb j) ≠ 0 := by
        intro h0
        apply hM'0
        rw [hcb_eq]
        exact Finset.sum_eq_zero fun j _ => by simp only [congrFun h0 j, Pi.zero_apply, zero_smul]
      have hnc : ∀ j : Fin 6, ¬ ((fun r => ca r) = Pi.single j 1 ∧ (fun r => cb r) = Pi.single j 1) := by
        rintro j ⟨h1, h2⟩
        apply hnew j
        constructor
        · rw [hca_eq, Finset.sum_eq_single j]
          · have := congrFun h1 j; simp at this; simp [this]
          · intro r _ hr; have := congrFun h1 r; simp [hr] at this; simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [hcb_eq, Finset.sum_eq_single j]
          · have := congrFun h2 j; simp at this; simp [this]
          · intro r _ hr; have := congrFun h2 r; simp [hr] at this; simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
      have hbd := card_linear_constraint_bound L M hL hM H
        (fun u v => (∀ j : Fin 6, u j * v j = 0) ∧
          (∑ j : Fin 6, ca j * u j) * (∑ j : Fin 6, cb j * v j) = 0)
        (fun x y hxy => by
          have h := hH x y hxy
          refine ⟨h.1, ?_⟩
          have h1 : (∑ j : Fin 6, ca j * L j x) = L' x := by
            rw [hca_eq]; simp [LinearMap.sum_apply, smul_eq_mul]
          have h2 : (∑ j : Fin 6, cb j * M j y) = M' y := by
            rw [hcb_eq]; simp [LinearMap.sum_apply, smul_eq_mul]
          simpa [LinearMap.pi_apply, h1, h2] using h.2)
      have h648 := card_six_indep_extra_in_span (fun j => ca j) (fun j => cb j) ha0 hb0 hnc
      have hmul : Nat.card {w : X × Y // H w.1 w.2} * 4096 ≤ 648 * (Nat.card X * Nat.card Y) :=
        hbd.trans (Nat.mul_le_mul_right _ h648)
      linarith
    · let M7 : Fin 7 → (Y →ₗ[F2] F2) := Fin.snoc M M'
      have hM7 : LinearIndependent F2 M7 := hM.finSnoc hMin
      have hbd := card_linear_constraint_bound L M7 hL hM7 H
        (fun u v => (∀ j : Fin 6, u j * v ⟨j.val, by omega⟩ = 0) ∧
          (∑ j : Fin 6, ca j * u j) * v ⟨6, by omega⟩ = 0)
        (fun x y hxy => by
          have h := hH x y hxy
          refine ⟨fun j => by simpa [LinearMap.pi_apply, M7, Fin.snoc, j.isLt] using h.1 j, ?_⟩
          have h1 : (∑ j : Fin 6, ca j * L j x) = L' x := by
            rw [hca_eq]; simp [LinearMap.sum_apply, smul_eq_mul]
          simpa [LinearMap.pi_apply, M7, Fin.snoc, h1] using h.2)
      have h1215 := card_six_indep_extra_half (fun j => ca j) ha0
      have hmul : Nat.card {w : X × Y // H w.1 w.2} * 8192 ≤ 1215 * (Nat.card X * Nat.card Y) :=
        hbd.trans (Nat.mul_le_mul_right _ h1215)
      linarith
  · let L7 : Fin 7 → (X →ₗ[F2] F2) := Fin.snoc L L'
    have hL7 : LinearIndependent F2 L7 := hL.finSnoc hLin
    by_cases hMin : M' ∈ Submodule.span F2 (Set.range M)
    · rw [Finsupp.mem_span_range_iff_exists_finsupp] at hMin
      obtain ⟨cb, hcb⟩ := hMin
      have hcb_eq : M' = ∑ j : Fin 6, cb j • M j := by
        exact hcb.symm.trans (Finsupp.sum_fintype cb (fun j z => z • M j) (fun j => zero_smul _ _))
      have hb0 : (fun j => cb j) ≠ 0 := by
        intro h0
        apply hM'0
        rw [hcb_eq]
        exact Finset.sum_eq_zero fun j _ => by simp only [congrFun h0 j, Pi.zero_apply, zero_smul]
      have hbd := card_linear_constraint_bound M L7 hM hL7 (fun y x => H x y)
        (fun v u => (∀ j : Fin 6, v j * u ⟨j.val, by omega⟩ = 0) ∧
          (∑ j : Fin 6, cb j * v j) * u ⟨6, by omega⟩ = 0)
        (fun y x hxy => by
          have h := hH x y hxy
          refine ⟨fun j => by simpa [LinearMap.pi_apply, L7, Fin.snoc, j.isLt, mul_comm] using h.1 j, ?_⟩
          have h2 : (∑ j : Fin 6, cb j * M j y) = M' y := by
            rw [hcb_eq]; simp [LinearMap.sum_apply, smul_eq_mul]
          change (∑ j, cb j * M j y) * L' x = 0
          rw [h2, mul_comm]; exact h.2)
      have hswap : Nat.card {w : Y × X // H w.2 w.1} = Nat.card {w : X × Y // H w.1 w.2} :=
        Nat.card_congr ((Equiv.prodComm Y X).subtypeEquiv fun _ => Iff.rfl)
      rw [hswap, mul_comm (Nat.card Y) (Nat.card X)] at hbd
      have h1215 := card_six_indep_extra_half (fun j => cb j) hb0
      have hmul : Nat.card {w : X × Y // H w.1 w.2} * 8192 ≤ 1215 * (Nat.card X * Nat.card Y) :=
        hbd.trans (Nat.mul_le_mul_right _ h1215)
      linarith
    · let M7 : Fin 7 → (Y →ₗ[F2] F2) := Fin.snoc M M'
      have hM7 : LinearIndependent F2 M7 := hM.finSnoc hMin
      have hbd := card_linear_constraint_bound L7 M7 hL7 hM7 H
        (fun u v => ∀ j : Fin 7, u j * v j = 0)
        (fun x y hxy => by
          have h := hH x y hxy
          intro j
          by_cases hj : j.val < 6
          · simpa [LinearMap.pi_apply, L7, Fin.snoc, M7, Fin.castLT, hj] using h.1 ⟨j.val, hj⟩
          · simpa [LinearMap.pi_apply, L7, Fin.snoc, M7, Fin.castLT, hj] using h.2)
      rw [card_seven_indep] at hbd
      have hmul : Nat.card {w : X × Y // H w.1 w.2} * 16384 ≤ 2187 * (Nat.card X * Nat.card Y) := hbd
      linarith

lemma card_filter_mod_three_eq (t : ℕ) (a : ℕ) :
    (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a)).card ≤ t := by
  by_cases ha : a < 3
  · have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) ⊆
        (Finset.univ : Finset (Fin t)).image (fun q : Fin t =>
          (⟨3 * q.val + a, by omega⟩ : Fin (3 * t))) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨i.val / 3, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp
      omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  · have hemp : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    simp [hemp]

lemma exists_orth_zmod2 (S : Submodule (ZMod 2) (Fin 2 → ZMod 2))
    (hlt : Module.finrank (ZMod 2) S < 2) :
    ∃ α0 α1 : ZMod 2, (α0 ≠ 0 ∨ α1 ≠ 0) ∧ ∀ z ∈ S, α0 * z 0 + α1 * z 1 = 0 := by
  have hnot_top : S ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hlt
    have h2 : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := by simp
    omega
  by_cases h0 : ∀ z ∈ S, z 0 = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fun z hz => by simp [h0 z hz]⟩
  · by_cases h1 : ∀ z ∈ S, z 1 = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, fun z hz => by simp [h1 z hz]⟩
    · by_cases h01 : ∀ z ∈ S, z 0 + z 1 = 0
      · exact ⟨1, 1, Or.inl one_ne_zero, fun z hz => by simpa using h01 z hz⟩
      · exfalso
        push Not at h0 h1 h01
        rcases h0 with ⟨z0, hz0S, hz0⟩
        rcases h1 with ⟨z1, hz1S, hz1⟩
        rcases h01 with ⟨z2, hz2S, hz2⟩
        apply hnot_top
        rw [eq_top_iff]
        intro w _
        let e0 : Fin 2 → ZMod 2 := fun e => if e = 0 then 1 else 0
        let e1 : Fin 2 → ZMod 2 := fun e => if e = 1 then 1 else 0
        have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        have h10_01 : e0 ∈ S ∧ e1 ∈ S := by
          have hz0_0 : z0 0 = 1 := (hz (z0 0)).resolve_left hz0
          have hz1_1 : z1 1 = 1 := (hz (z1 1)).resolve_left hz1
          rcases hz (z2 0) with h2a | h2a <;> rcases hz (z2 1) with h2b | h2b
          · exfalso; apply hz2; simp [h2a, h2b]
          · have hz2_e1 : z2 = e1 := by ext e; fin_cases e <;> simp [e1, h2a, h2b]
            have he1 : e1 ∈ S := hz2_e1 ▸ hz2S
            refine ⟨?_, he1⟩
            rcases hz (z0 1) with h0b | h0b
            · have : z0 = e0 := by ext e; fin_cases e <;> simp [e0, hz0_0, h0b]
              exact this ▸ hz0S
            · have : z0 + z2 = e0 := by ext e; fin_cases e <;> simp [e0, hz0_0, h0b, h2a, h2b, h11]
              exact this ▸ S.add_mem hz0S hz2S
          · have hz2_e0 : z2 = e0 := by ext e; fin_cases e <;> simp [e0, h2a, h2b]
            have he0 : e0 ∈ S := hz2_e0 ▸ hz2S
            refine ⟨he0, ?_⟩
            rcases hz (z1 0) with h1a | h1a
            · have : z1 = e1 := by ext e; fin_cases e <;> simp [e1, h1a, hz1_1]
              exact this ▸ hz1S
            · have : z1 + z2 = e1 := by ext e; fin_cases e <;> simp [e1, h1a, hz1_1, h2a, h2b, h11]
              exact this ▸ S.add_mem hz1S hz2S
          · exfalso; apply hz2
            simp [h2a, h2b, h11]
        have hw_eq : w = w 0 • e0 + w 1 • e1 := by
          ext e; fin_cases e <;> simp [e0, e1]
        rw [hw_eq]
        exact S.add_mem (S.smul_mem _ h10_01.1) (S.smul_mem _ h10_01.2)

lemma finrank_le_card_add_k_sub_syndrome
    (t k : ℕ)
    (P : Submodule (ZMod 2) (Fin (3 * t) → ZMod 2))
    (hcode : ∀ x ∈ P, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0)
    (ZP AL IL : Finset (Fin (3 * t)))
    (hpart1 : Disjoint ZP AL) (hpart2 : Disjoint ZP IL) (hpart3 : Disjoint AL IL)
    (hcov : ZP ∪ AL ∪ IL = Finset.univ)
    (hZP : ∀ i ∈ ZP, ∀ x ∈ P, x i = 0)
    (rep : Fin k → Fin (3 * t))
    (cL : Fin (3 * t) → Fin k)
    (hrep : ∀ c : Fin k, rep c ∈ AL ∧ cL (rep c) = c)
    (hAL : ∀ i ∈ AL, ∀ x ∈ P, x i = x (rep (cL i))) :
    ∃ rP : ℕ, rP ≤ 2 ∧
      Module.finrank (ZMod 2) P + rP ≤ IL.card + k ∧
      (rP = 0 → ∀ c : Fin k, 2 ≤ (AL.filter (fun i => cL i = c)).card) ∧
      (rP = 1 → (∀ c : Fin k, (AL.filter (fun i => cL i = c)).card = 1) →
        ∃ a : ℕ, ∀ i ∈ AL ∪ IL, i.val % 3 = a) := by
  classical
  let F := ZMod 2
  let n := 3 * t
  let V := (IL → F) × (Fin k → F)
  let φ : P →ₗ[F] V :=
    { toFun := fun x => (fun i => x.1 i.1, fun c => x.1 (rep c))
      map_add' := fun x y => by ext <;> rfl
      map_smul' := fun a x => by ext <;> rfl }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : i ∈ ZP ∪ AL ∪ IL := hcov ▸ Finset.mem_univ i
    simp only [Finset.mem_union] at hi
    rcases hi with (hi | hi) | hi
    · rw [hZP i hi x.1 x.2, hZP i hi y.1 y.2]
    · rw [hAL i hi x.1 x.2, hAL i hi y.1 y.2]
      exact congrFun (congrArg Prod.snd hxy) (cL i)
    · exact congrFun (congrArg Prod.fst hxy) ⟨i, hi⟩
  let wt (c : Fin k) (e : Fin 2) : F :=
    ∑ i ∈ AL.filter (fun i => cL i = c), if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0
  let σ : V →ₗ[F] (Fin 2 → F) :=
    { toFun := fun v e =>
        (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
        (∑ c : Fin k, wt c e * v.2 c)
      map_add' := fun u v => by
        ext e
        change (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i + v.1 i else (0 : F)) +
            (∑ c : Fin k, wt c e * (u.2 c + v.2 c)) =
          ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i else 0) +
            (∑ c : Fin k, wt c e * u.2 c)) +
          ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
            (∑ c : Fin k, wt c e * v.2 c))
        have h1 : ∀ i : IL, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i + v.1 i else (0 : F)) =
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i else 0) +
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, Finset.sum_add_distrib, mul_add]
        ring
      map_smul' := fun a v => by
        ext e
        change (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v.1 i else (0 : F)) +
            (∑ c : Fin k, wt c e * (a * v.2 c)) =
          a * ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
            (∑ c : Fin k, wt c e * v.2 c))
        have h1 : ∀ i : IL, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v.1 i else (0 : F)) =
            a * (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, ← Finset.mul_sum]
        have h2 : ∀ c : Fin k, wt c e * (a * v.2 c) = a * (wt c e * v.2 c) := fun c => by ring
        simp only [h2, ← Finset.mul_sum]
        ring }
  have hcomp : σ.comp φ = 0 := by
    apply LinearMap.ext
    intro x
    ext e
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, σ, φ,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hsum_all : (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) = 0 :=
      hcode x.1 x.2 e
    have hsplit : (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) =
        (∑ i ∈ ZP, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) +
        (∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) +
        (∑ i ∈ IL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) := by
      rw [← Finset.sum_union hpart1, ← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hpart2, hpart3⟩),
        hcov]
    have hZ0 : (∑ i ∈ ZP, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hZP i hi x.1 x.2]
    have hIL_eq : (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then x.1 i.1 else (0 : F)) =
        ∑ i ∈ IL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) :=
      Finset.sum_coe_sort IL (fun i => if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F))
    have hAL_eq : (∑ c : Fin k, wt c e * x.1 (rep c)) =
        ∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) := by
      have hfib : ∑ c : Fin k, ∑ i ∈ AL.filter (fun i => cL i = c),
          (if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) =
          ∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) := by
        rw [← Finset.sum_biUnion]
        · congr 1
          ext i
          simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
          exact ⟨fun ⟨_, hi, _⟩ => hi, fun hi => ⟨cL i, hi, rfl⟩⟩
        · intro c1 _ c2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro i h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← hfib]
      refine Finset.sum_congr rfl fun c _ => ?_
      dsimp [wt]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hci : cL i = c := (Finset.mem_filter.mp hi).2
      have hxi : x.1 i = x.1 (rep c) := hci ▸ hAL i (Finset.mem_filter.mp hi).1 x.1 x.2
      rw [hxi]
      split_ifs <;> simp
    rw [hIL_eq, hAL_eq]
    rw [hZ0, zero_add] at hsplit
    rw [add_comm, ← hsplit, hsum_all]
  let rP := Module.finrank F (LinearMap.range σ)
  refine ⟨rP, ?_, ?_, ?_, ?_⟩
  · have hle := Submodule.finrank_le (LinearMap.range σ)
    simpa using hle
  · have hsub : LinearMap.range φ ≤ LinearMap.ker σ := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      exact LinearMap.congr_fun hcomp x
    have h1 : Module.finrank F P = Module.finrank F (LinearMap.range φ) :=
      (LinearEquiv.ofInjective φ hφ_inj).finrank_eq
    have h2 : Module.finrank F (LinearMap.range φ) ≤ Module.finrank F (LinearMap.ker σ) :=
      Submodule.finrank_mono hsub
    have h3 : Module.finrank F (LinearMap.range σ) + Module.finrank F (LinearMap.ker σ) =
        Module.finrank F V := LinearMap.finrank_range_add_finrank_ker σ
    have hV : Module.finrank F V = IL.card + k := by
      simp [V, Module.finrank_prod, Fintype.card_coe]
    change Module.finrank F P + rP ≤ IL.card + k
    omega
  · intro hr0 c
    have hker_all : LinearMap.range σ = ⊥ := Submodule.finrank_eq_zero.mp hr0
    have hσ0 : ∀ v : V, σ v = 0 := fun v =>
      (Submodule.mem_bot F).mp (hker_all ▸ ⟨v, rfl⟩)
    have hwt0 : ∀ e : Fin 2, wt c e = 0 := fun e => by
      let v : V := (0, fun c' => if c' = c then 1 else 0)
      have hv := congrFun (hσ0 v) e
      simpa [σ, v] using hv
    by_contra hlt
    push Not at hlt
    have hmem : rep c ∈ AL.filter (fun i => cL i = c) :=
      Finset.mem_filter.mpr (hrep c)
    have hsing : AL.filter (fun i => cL i = c) = {rep c} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hmem, fun j hj => ?_⟩
      by_contra hne
      have h2 : ({rep c, j} : Finset (Fin n)).card ≤ (AL.filter (fun i => cL i = c)).card :=
        Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair (Ne.symm hne)] at h2
      omega
    have h0 := hwt0 0
    have h1 := hwt0 1
    dsimp [wt] at h0 h1
    rw [hsing, Finset.sum_singleton] at h0 h1
    have hmod : (rep c).val % 3 = 0 ∨ (rep c).val % 3 = 1 ∨ (rep c).val % 3 = 2 := by omega
    rcases hmod with hm | hm | hm
    · simp [hm] at h0
    · simp [hm] at h1
    · simp [hm] at h0
  · intro hr1 hcard1
    obtain ⟨α0, α1, hαne, horthS⟩ := exists_orth_zmod2 (LinearMap.range σ) (by change rP < 2; omega)
    have horth : ∀ v : V, α0 * σ v 0 + α1 * σ v 1 = 0 := fun v => horthS (σ v) ⟨v, rfl⟩
    have hcoeff : ∀ i ∈ AL ∪ IL,
        α0 * (if i.val % 3 = 0 ∨ i.val % 3 = 2 then (1 : F) else 0) +
        α1 * (if i.val % 3 = 1 ∨ i.val % 3 = 2 then (1 : F) else 0) = 0 := by
      intro i hi
      rcases Finset.mem_union.mp hi with hiA | hiI
      · let c := cL i
        have hsing : AL.filter (fun j => cL j = c) = {i} := by
          have hc1 := hcard1 c
          have hmem : i ∈ AL.filter (fun j => cL j = c) := Finset.mem_filter.mpr ⟨hiA, rfl⟩
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hmem, fun j hj => ?_⟩
          by_contra hne
          have h2 : ({i, j} : Finset (Fin n)).card ≤ (AL.filter (fun x => cL x = c)).card :=
            Finset.card_le_card (by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
          rw [Finset.card_pair (Ne.symm hne)] at h2
          omega
        let v : V := (0, fun c' => if c' = c then 1 else 0)
        have hv := horth v
        have hσv : ∀ e : Fin 2, σ v e = if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0 := by
          intro e
          have h1 : σ v e = wt c e := by simp [σ, v]
          rw [h1]
          dsimp [wt]
          rw [hsing, Finset.sum_singleton]
        rw [hσv 0, hσv 1] at hv
        simpa using hv
      · let v : V := (fun j : IL => if j.1 = i then 1 else 0, 0)
        have hv := horth v
        have hsum_e : ∀ e : Fin 2,
            (∑ j : IL, if j.1.val % 3 = e.val ∨ j.1.val % 3 = 2 then v.1 j else (0 : F)) =
            if i.val % 3 = e.val ∨ i.val % 3 = 2 then 1 else 0 := by
          intro e
          rw [Finset.sum_eq_single ⟨i, hiI⟩]
          · simp [v]
          · intro b _ hbi
            have hne : b.1 ≠ i := fun h => hbi (Subtype.ext h)
            simp [v, hne]
          · intro h; exact (h (Finset.mem_univ _)).elim
        simp only [σ, LinearMap.coe_mk, AddHom.coe_mk, hsum_e, v] at hv
        simpa using hv
    have hz2 : ∀ x : F, x = 0 ∨ x = 1 := by decide
    rcases hz2 α0 with rfl | rfl <;> rcases hz2 α1 with rfl | rfl
    · simp at hαne
    · refine ⟨0, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm <;> simp [hm] at hc ⊢
    · refine ⟨1, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm <;> simp [hm] at hc ⊢
    · refine ⟨2, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm
      · simp [hm] at hc
      · simp [hm] at hc
      · exact hm

lemma cycle_ends_bound
    (n k : ℕ) (hn_pos : 0 < n) (hk : 3 ≤ k)
    (ZP ZQ AL AR IL IR : Finset (Fin n))
    (hAL_disj_ZP : Disjoint ZP AL) (hIL_disj_ZP : Disjoint ZP IL) (hIL_disj_AL : Disjoint AL IL)
    (hPcov : ZP ∪ AL ∪ IL = Finset.univ)
    (hAR_disj_ZQ : Disjoint ZQ AR) (hIR_disj_ZQ : Disjoint ZQ IR) (hIR_disj_AR : Disjoint AR IR)
    (hQcov : ZQ ∪ AR ∪ IR = Finset.univ)
    (Eact : Finset (Fin (2 * n)))
    (left right : Fin (2 * n) → Fin n)
    (hleft : ∀ e : Fin (2 * n), left e = ⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩)
    (hright : ∀ e : Fin (2 * n), right e = ⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩)
    (hEact_def : ∀ e : Fin (2 * n), e ∈ Eact ↔ left e ∉ ZP ∧ right e ∉ ZQ)
    (hAL_mem : ∀ e ∈ Eact, left e ∈ AL)
    (hAR_mem : ∀ e ∈ Eact, right e ∈ AR)
    (s : Fin k → Fin (2 * n))
    (hs_act : ∀ c : Fin k, s c ∈ Eact)
    (cL cR : Fin n → Fin k)
    (hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c)
    (hedge_same_col : ∀ e ∈ Eact, cL (left e) = cR (right e)) :
    ∃ nLive nDead nEnds : ℕ,
      nLive + nDead = 2 * n ∧
      nLive = (AL.card + IL.card) + (AR.card + IR.card) ∧
      nEnds ≤ nDead ∧
      nEnds ≤ nLive ∧
      IL.card + IR.card + k ≤ nEnds := by
  classical
  have hkpos : 0 < k := by omega
  let nxt : Fin (2 * n) → Fin (2 * n) := fun v => ⟨(v.val + 1) % (2 * n), Nat.mod_lt _ (by omega)⟩
  have hnxt_inj : Function.Injective nxt := by
    intro v1 v2 heq
    have hval : (v1.val + 1) % (2 * n) = (v2.val + 1) % (2 * n) := congrArg Fin.val heq
    apply Fin.ext
    have hv1 := v1.2; have hv2 := v2.2
    by_cases h1 : v1.val + 1 < 2 * n <;> by_cases h2 : v2.val + 1 < 2 * n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
    · have h2eq : v2.val + 1 = 2 * n := by omega
      rw [Nat.mod_eq_of_lt h1, h2eq, Nat.mod_self] at hval; omega
    · have h1eq : v1.val + 1 = 2 * n := by omega
      rw [h1eq, Nat.mod_self, Nat.mod_eq_of_lt h2] at hval; omega
    · omega
  let isLive : Fin (2 * n) → Prop := fun v =>
    if v.val % 2 = 0 then (⟨v.val / 2, by omega⟩ : Fin n) ∉ ZP
    else (⟨v.val / 2, by omega⟩ : Fin n) ∉ ZQ
  let Live : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => isLive v)
  let Dead : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => ¬ isLive v)
  have hLive_Dead : Live.card + Dead.card = 2 * n := by
    have hdisj : Disjoint Live Dead := by
      rw [Finset.disjoint_filter]; intro v _ h1 h2; exact h2 h1
    have hun : Live ∪ Dead = Finset.univ := by
      ext v; simp only [Live, Dead, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
    rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ, Fintype.card_fin]
  have hLive_card : Live.card = (AL.card + IL.card) + (AR.card + IR.card) := by
    let UP := AL ∪ IL
    let UQ := AR ∪ IR
    have hUP : UP.card = AL.card + IL.card := Finset.card_union_of_disjoint hIL_disj_AL
    have hUQ : UQ.card = AR.card + IR.card := Finset.card_union_of_disjoint hIR_disj_AR
    have hUP_iff : ∀ i : Fin n, i ∈ UP ↔ i ∉ ZP := by
      intro i
      have hi : i ∈ ZP ∪ AL ∪ IL := hPcov ▸ Finset.mem_univ i
      simp only [UP, Finset.mem_union] at hi ⊢
      constructor
      · rintro (hA | hI) hZ
        · exact Finset.disjoint_left.mp hAL_disj_ZP hZ hA
        · exact Finset.disjoint_left.mp hIL_disj_ZP hZ hI
      · intro hnotZ
        rcases hi with (hZ | hA) | hI
        · exact absurd hZ hnotZ
        · exact Or.inl hA
        · exact Or.inr hI
    have hUQ_iff : ∀ j : Fin n, j ∈ UQ ↔ j ∉ ZQ := by
      intro j
      have hj : j ∈ ZQ ∪ AR ∪ IR := hQcov ▸ Finset.mem_univ j
      simp only [UQ, Finset.mem_union] at hj ⊢
      constructor
      · rintro (hA | hI) hZ
        · exact Finset.disjoint_left.mp hAR_disj_ZQ hZ hA
        · exact Finset.disjoint_left.mp hIR_disj_ZQ hZ hI
      · intro hnotZ
        rcases hj with (hZ | hA) | hI
        · exact absurd hZ hnotZ
        · exact Or.inl hA
        · exact Or.inr hI
    let Leven := UP.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n)))
    let Lodd := UQ.image (fun j : Fin n => (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)))
    have hLeven_card : Leven.card = UP.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    have hLodd_card : Lodd.card = UQ.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    have hdisj_eo : Disjoint Leven Lodd := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
      have := congrArg Fin.val heq; dsimp at this; omega
    have hLive_eq : Live = Leven ∪ Lodd := by
      ext v
      simp only [Live, Leven, Lodd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, isLive]
      by_cases hv : v.val % 2 = 0
      · simp only [hv, ↓reduceIte]
        constructor
        · intro hnotZ
          left
          refine ⟨⟨v.val / 2, by omega⟩, (hUP_iff _).mpr hnotZ, Fin.ext (by dsimp; omega)⟩
        · rintro (⟨i, hi, heq⟩ | ⟨j, _, heq⟩)
          · have hval : 2 * i.val = v.val := congrArg Fin.val heq
            have hi' : (⟨v.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
            rw [hi']; exact (hUP_iff i).mp hi
          · have hval : 2 * j.val + 1 = v.val := congrArg Fin.val heq; omega
      · simp only [hv, ↓reduceIte]
        constructor
        · intro hnotZ
          right
          refine ⟨⟨v.val / 2, by omega⟩, (hUQ_iff _).mpr hnotZ, Fin.ext (by dsimp; omega)⟩
        · rintro (⟨i, _, heq⟩ | ⟨j, hj, heq⟩)
          · have hval : 2 * i.val = v.val := congrArg Fin.val heq; omega
          · have hval : 2 * j.val + 1 = v.val := congrArg Fin.val heq
            have hj' : (⟨v.val / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
            rw [hj']; exact (hUQ_iff j).mp hj
    rw [hLive_eq, Finset.card_union_of_disjoint hdisj_eo, hLeven_card, hLodd_card, hUP, hUQ]
  have hEact_iff : ∀ e : Fin (2 * n), e ∈ Eact ↔ isLive e ∧ isLive (nxt e) := by
    intro e
    rw [hEact_def e, hleft e, hright e]
    simp only [isLive, nxt]
    by_cases he : e.val % 2 = 0
    · have he1 : (e.val + 1) % (2 * n) = e.val + 1 := Nat.mod_eq_of_lt (by omega)
      have he1odd : (e.val + 1) % 2 ≠ 0 := by omega
      simp only [he, he1, he1odd, ↓reduceIte]
      have hL : (⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨e.val / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : (⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨(e.val + 1) / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [hL, hR]
    · have hne2 : (e.val + 1) % (2 * n) % 2 = 0 := by
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop]; omega
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
      simp only [he, hne2, ↓reduceIte]
      have hR : (⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨e.val / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)])
      have hmod_lt : (e.val + 1) % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
      have hL : (⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) =
          ⟨((e.val + 1) % (2 * n)) / 2, by omega⟩ := by
        apply Fin.ext; dsimp
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop, Nat.mod_eq_of_lt (by omega)]
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
          have : (2 * n) / 2 = n := by omega
          rw [this, Nat.mod_self]
      rw [hL, hR, and_comm]
  let Ends : Finset (Fin (2 * n)) := Live.filter (fun v => ¬ isLive (nxt v))
  have hEnds_le_Dead : Ends.card ≤ Dead.card := by
    refine Finset.card_le_card_of_injOn nxt ?_ (fun x _ y _ h => hnxt_inj h)
    intro v hv
    simp only [Finset.mem_coe, Ends, Dead, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hEnds_le_Live : Ends.card ≤ Live.card := Finset.card_filter_le _ _
  let isColV : Fin (2 * n) → Prop := fun v =>
    if v.val % 2 = 0 then (⟨v.val / 2, by omega⟩ : Fin n) ∈ AL
    else (⟨v.val / 2, by omega⟩ : Fin n) ∈ AR
  let vcol : Fin (2 * n) → Fin k := fun v =>
    if v.val % 2 = 0 then cL ⟨v.val / 2, by omega⟩
    else cR ⟨v.val / 2, by omega⟩
  have hstep_col : ∀ e : Fin (2 * n), isLive e → isLive (nxt e) →
      isColV e ∧ isColV (nxt e) ∧ vcol e = vcol (nxt e) := by
    intro e h1 h2
    have heA : e ∈ Eact := (hEact_iff e).mpr ⟨h1, h2⟩
    have hcol := hedge_same_col e heA
    have hmemL : left e ∈ AL := hAL_mem e heA
    have hmemR : right e ∈ AR := hAR_mem e heA
    simp only [isColV, vcol, nxt]
    by_cases he : e.val % 2 = 0
    · have he1 : (e.val + 1) % (2 * n) = e.val + 1 := Nat.mod_eq_of_lt (by omega)
      have he1odd : (e.val + 1) % 2 ≠ 0 := by omega
      simp only [he, he1, he1odd, ↓reduceIte]
      have hL : left e = ⟨e.val / 2, by omega⟩ := by
        rw [hleft e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : right e = ⟨(e.val + 1) / 2, by omega⟩ := by
        rw [hright e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [← hL, ← hR]
      exact ⟨hmemL, hmemR, hcol⟩
    · have hne2 : (e.val + 1) % (2 * n) % 2 = 0 := by
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop]; omega
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
      simp only [he, hne2, ↓reduceIte]
      have hR : right e = ⟨e.val / 2, by omega⟩ := by
        rw [hright e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)])
      have hmod_lt : (e.val + 1) % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
      have hL : left e = ⟨((e.val + 1) % (2 * n)) / 2, by omega⟩ := by
        rw [hleft e]; apply Fin.ext; dsimp
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop, Nat.mod_eq_of_lt (by omega)]
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
          have : (2 * n) / 2 = n := by omega
          rw [this, Nat.mod_self]
      rw [← hL, ← hR]
      exact ⟨hmemR, hmemL, hcol.symm⟩
  have hEnds_color : ∀ c : Fin k, ∃ v ∈ Ends, isColV v ∧ vcol v = c := by
    intro c
    let v0 : Fin (2 * n) := ⟨2 * (left (s c)).val, by omega⟩
    have hv0_live : isLive v0 := by
      simp only [isLive, v0, Nat.mul_mod_right, ↓reduceIte]
      have h1 : (⟨2 * (left (s c)).val / 2, by omega⟩ : Fin n) = left (s c) :=
        Fin.ext (by dsimp; omega)
      rw [h1]
      exact ((hEact_def (s c)).mp (hs_act c)).1
    have hv0_col : isColV v0 ∧ vcol v0 = c := by
      simp only [isColV, vcol, v0, Nat.mul_mod_right, ↓reduceIte]
      have h1 : (⟨2 * (left (s c)).val / 2, by omega⟩ : Fin n) = left (s c) :=
        Fin.ext (by dsimp; omega)
      rw [h1]
      exact hrepL c
    have hex_dead : ∃ d : ℕ, ¬ isLive (nxt^[d] v0) := by
      by_contra hall
      push Not at hall
      have hsame : ∀ d : ℕ, vcol (nxt^[d] v0) = c := by
        intro d
        induction d with
        | zero => exact hv0_col.2
        | succ d ih =>
          rw [Function.iterate_succ_apply']
          have hst := hstep_col (nxt^[d] v0) (hall d)
            ((Function.iterate_succ_apply' nxt d v0).symm ▸ hall (d + 1))
          rw [← hst.2.2, ih]
      have hiter_val : ∀ d : ℕ, (nxt^[d] v0).val = (v0.val + d) % (2 * n) := by
        intro d
        induction d with
        | zero => simp [Nat.mod_eq_of_lt v0.2]
        | succ d ih =>
          rw [Function.iterate_succ_apply']
          dsimp [nxt]
          rw [ih, Nat.mod_add_mod, add_assoc]
      let c' : Fin k := ⟨(c.val + 1) % k, Nat.mod_lt _ hkpos⟩
      have hc'ne : c' ≠ c := by
        intro heq
        have hv : (c.val + 1) % k = c.val := congrArg Fin.val heq
        have hc2 := c.2
        by_cases htop : c.val + 1 < k
        · rw [Nat.mod_eq_of_lt htop] at hv; omega
        · have : c.val + 1 = k := by omega
          rw [this, Nat.mod_self] at hv; omega
      let w0 : Fin (2 * n) := ⟨2 * (left (s c')).val, by omega⟩
      let d0 : ℕ := (w0.val + 2 * n - v0.val) % (2 * n)
      have hhit : nxt^[d0] v0 = w0 := by
        apply Fin.ext
        rw [hiter_val d0]
        have hv0lt := v0.2; have hw0lt := w0.2
        dsimp [d0]
        rw [Nat.add_mod_mod]
        have : v0.val + (w0.val + 2 * n - v0.val) = w0.val + 2 * n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hw0lt]
      have h1 := hsame d0
      rw [hhit] at h1
      have h2 : vcol w0 = c' := by
        simp only [vcol, w0, Nat.mul_mod_right, ↓reduceIte]
        have heq : (⟨2 * (left (s c')).val / 2, by omega⟩ : Fin n) = left (s c') :=
          Fin.ext (by dsimp; omega)
        rw [heq]
        exact (hrepL c').2
      rw [h2] at h1
      exact hc'ne h1
    let d0 := Nat.find hex_dead
    have hd0_spec : ¬ isLive (nxt^[d0] v0) := Nat.find_spec hex_dead
    have hd0_pos : 0 < d0 := by
      by_contra h0
      have : d0 = 0 := by omega
      rw [this] at hd0_spec
      exact hd0_spec hv0_live
    have hlive_lt : ∀ m < d0, isLive (nxt^[m] v0) := fun m hm =>
      by_contra fun h => Nat.find_min hex_dead hm h
    have hprop_lt : ∀ m < d0, isColV (nxt^[m] v0) ∧ vcol (nxt^[m] v0) = c := by
      intro m hm
      induction m with
      | zero => exact hv0_col
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        have hst := hstep_col (nxt^[m] v0) (hlive_lt m (by omega))
          ((Function.iterate_succ_apply' nxt m v0).symm ▸ hlive_lt (m + 1) hm)
        exact ⟨hst.2.1, hst.2.2.symm.trans (ih (by omega)).2⟩
    let v := nxt^[d0 - 1] v0
    have hv_live : isLive v := hlive_lt (d0 - 1) (by omega)
    have hv_nxt : ¬ isLive (nxt v) := by
      have : nxt v = nxt^[d0] v0 := by
        dsimp [v]
        rw [← Function.iterate_succ_apply' nxt (d0 - 1) v0]
        congr 1; omega
      rw [this]; exact hd0_spec
    have hv_col := hprop_lt (d0 - 1) (by omega)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_live⟩, hv_nxt⟩,
      hv_col.1, hv_col.2⟩
  let E_IL := IL.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n)))
  let E_IR := IR.image (fun j : Fin n => (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)))
  let E_C := (Finset.univ : Finset (Fin k)).image (fun c => Classical.choose (hEnds_color c))
  have hEIL_sub : E_IL ⊆ Ends := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    have hi_notZ : i ∉ ZP := Finset.disjoint_right.mp hIL_disj_ZP hi
    have hi_notA : i ∉ AL := Finset.disjoint_right.mp hIL_disj_AL hi
    have hlive : isLive ⟨2 * i.val, by omega⟩ := by
      simp only [isLive, Nat.mul_mod_right, ↓reduceIte]
      have : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
      rw [this]; exact hi_notZ
    have hdead : ¬ isLive (nxt ⟨2 * i.val, by omega⟩) := by
      intro hl2
      have heA : (⟨2 * i.val, by omega⟩ : Fin (2 * n)) ∈ Eact := (hEact_iff _).mpr ⟨hlive, hl2⟩
      have hleft_i : left ⟨2 * i.val, by omega⟩ = i := by
        rw [hleft]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      exact hi_notA (hleft_i ▸ hAL_mem _ heA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlive⟩, hdead⟩
  have hEIR_sub : E_IR ⊆ Ends := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    have hj_notZ : j ∉ ZQ := Finset.disjoint_right.mp hIR_disj_ZQ hj
    have hj_notA : j ∉ AR := Finset.disjoint_right.mp hIR_disj_AR hj
    have hlive : isLive ⟨2 * j.val + 1, by omega⟩ := by
      have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
      simp only [isLive, hodd, ↓reduceIte]
      have : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
      rw [this]; exact hj_notZ
    have hdead : ¬ isLive (nxt ⟨2 * j.val + 1, by omega⟩) := by
      intro hl2
      have heA : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)) ∈ Eact := (hEact_iff _).mpr ⟨hlive, hl2⟩
      have hright_j : right ⟨2 * j.val + 1, by omega⟩ = j := by
        rw [hright]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      exact hj_notA (hright_j ▸ hAR_mem _ heA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlive⟩, hdead⟩
  have hEC_sub : E_C ⊆ Ends := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨c, _, rfl⟩
    exact (Classical.choose_spec (hEnds_color c)).1
  have hEIL_card : E_IL.card = IL.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hEIR_card : E_IR.card = IR.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hEC_card : E_C.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro c1 c2 h
      dsimp only at h
      have h1 := (Classical.choose_spec (hEnds_color c1)).2.2
      have h2 := (Classical.choose_spec (hEnds_color c2)).2.2
      rw [h] at h1
      exact h1.symm.trans h2
  have hd1 : Disjoint E_IL E_IR := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
    have := congrArg Fin.val heq; dsimp at this; omega
  have hd2 : Disjoint E_IL E_C := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, heq⟩
    have hcolV := (Classical.choose_spec (hEnds_color c)).2.1
    rw [heq] at hcolV
    simp only [isColV, Nat.mul_mod_right, ↓reduceIte] at hcolV
    have hi' : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
    rw [hi'] at hcolV
    exact Finset.disjoint_right.mp hIL_disj_AL hi hcolV
  have hd3 : Disjoint E_IR E_C := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, heq⟩
    have hcolV := (Classical.choose_spec (hEnds_color c)).2.1
    rw [heq] at hcolV
    have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
    simp only [isColV, hodd, ↓reduceIte] at hcolV
    have hj' : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
    rw [hj'] at hcolV
    exact Finset.disjoint_right.mp hIR_disj_AR hj hcolV
  have hEnds_ge : IL.card + IR.card + k ≤ Ends.card := by
    have hsub : E_IL ∪ E_IR ∪ E_C ⊆ Ends :=
      Finset.union_subset (Finset.union_subset hEIL_sub hEIR_sub) hEC_sub
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd2, hd3⟩),
      Finset.card_union_of_disjoint hd1, hEIL_card, hEIR_card, hEC_card] at hcard
    exact hcard
  exact ⟨Live.card, Dead.card, Ends.card, hLive_Dead, hLive_card, hEnds_le_Dead, hEnds_le_Live, hEnds_ge⟩

lemma pure_slots_dim :
    ∀ (t : ℕ) (ht : 0 < t) (k : ℕ), 3 ≤ k →
      let F := ZMod 2
      let n := 3*t
      let W := Fin n → F
      let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
      let code := fun (x : W) => ∀ e : Fin 2,
        (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
      ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
        let left := fun (e : Fin (2*n)) => ix ((e.val+1)/2)
        let right := fun (e : Fin (2*n)) => ix (e.val/2)
        ∀ s : Fin k → Fin (2*n),
          Function.Surjective (fun x : P => fun c : Fin k => x.val (left (s c))) →
          Function.Surjective (fun y : Q => fun c : Fin k => y.val (right (s c))) →
          (∀ e : Fin (2*n), (∀ x : P, x.val (left e) = 0) ∨ (∀ y : Q, y.val (right e) = 0) ∨
            ∃ c : Fin k, (∀ x : P, x.val (left e) = x.val (left (s c))) ∧
              (∀ y : Q, y.val (right e) = y.val (right (s c)))) →
          2*(Module.finrank F P + Module.finrank F Q)+5 ≤ 2*n+k := by
  classical
  dsimp only
  intro t ht k hk P Q hPcode hQcode s hPsurj hQsurj hedge
  let F := ZMod 2
  let n := 3 * t
  have hn_pos : 0 < n := by omega
  let ix : ℕ → Fin n := fun j => ⟨j % n, Nat.mod_lt _ hn_pos⟩
  let left : Fin (2 * n) → Fin n := fun e => ix ((e.val + 1) / 2)
  let right : Fin (2 * n) → Fin n := fun e => ix (e.val / 2)
  have hPdist : ∀ c1 c2 : Fin k, (∀ x : P, x.val (left (s c1)) = x.val (left (s c2))) → c1 = c2 := by
    intro c1 c2 heq
    by_contra hne
    obtain ⟨x, hx⟩ := hPsurj (fun c => if c = c1 then (1 : F) else 0)
    have h1 : x.val (left (s c1)) = 1 := by simpa using congrFun hx c1
    have h2 : x.val (left (s c2)) = 0 := by simpa [Ne.symm hne] using congrFun hx c2
    rw [heq x] at h1
    rw [h1] at h2
    exact one_ne_zero h2
  have hQdist : ∀ c1 c2 : Fin k, (∀ y : Q, y.val (right (s c1)) = y.val (right (s c2))) → c1 = c2 := by
    intro c1 c2 heq
    by_contra hne
    obtain ⟨y, hy⟩ := hQsurj (fun c => if c = c1 then (1 : F) else 0)
    have h1 : y.val (right (s c1)) = 1 := by simpa using congrFun hy c1
    have h2 : y.val (right (s c2)) = 0 := by simpa [Ne.symm hne] using congrFun hy c2
    rw [heq y] at h1
    rw [h1] at h2
    exact one_ne_zero h2
  have hPnz : ∀ c : Fin k, ¬ (∀ x : P, x.val (left (s c)) = 0) := by
    intro c h0
    obtain ⟨x, hx⟩ := hPsurj (fun _ => (1 : F))
    have h1 : x.val (left (s c)) = 1 := congrFun hx c
    rw [h0 x] at h1
    exact zero_ne_one h1
  have hQnz : ∀ c : Fin k, ¬ (∀ y : Q, y.val (right (s c)) = 0) := by
    intro c h0
    obtain ⟨y, hy⟩ := hQsurj (fun _ => (1 : F))
    have h1 : y.val (right (s c)) = 1 := congrFun hy c
    rw [h0 y] at h1
    exact zero_ne_one h1
  let ZP : Finset (Fin n) := Finset.univ.filter (fun i => ∀ x : P, x.val i = 0)
  let ZQ : Finset (Fin n) := Finset.univ.filter (fun j => ∀ y : Q, y.val j = 0)
  let Eact : Finset (Fin (2 * n)) :=
    Finset.univ.filter (fun e => left e ∉ ZP ∧ right e ∉ ZQ)
  have hEact_col : ∀ e ∈ Eact,
      ∃ c : Fin k, (∀ x : P, x.val (left e) = x.val (left (s c))) ∧
        (∀ y : Q, y.val (right e) = y.val (right (s c))) := by
    intro e he
    simp only [Eact, ZP, ZQ, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases hedge e with h1 | h2 | h3
    · exact absurd h1 he.1
    · exact absurd h2 he.2
    · exact h3
  have hs_act : ∀ c : Fin k, s c ∈ Eact := by
    intro c
    simp only [Eact, ZP, ZQ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hPnz c, hQnz c⟩
  let AL : Finset (Fin n) := Finset.univ.filter (fun i => ∃ e ∈ Eact, left e = i)
  let AR : Finset (Fin n) := Finset.univ.filter (fun j => ∃ e ∈ Eact, right e = j)
  let IL : Finset (Fin n) := Finset.univ.filter (fun i => i ∉ ZP ∧ i ∉ AL)
  let IR : Finset (Fin n) := Finset.univ.filter (fun j => j ∉ ZQ ∧ j ∉ AR)
  have hAL_disj_ZP : Disjoint ZP AL := by
    rw [Finset.disjoint_left]
    intro i hiZ hiA
    rcases (Finset.mem_filter.mp hiA).2 with ⟨e, he, rfl⟩
    exact (Finset.mem_filter.mp he).2.1 hiZ
  have hAR_disj_ZQ : Disjoint ZQ AR := by
    rw [Finset.disjoint_left]
    intro j hjZ hjA
    rcases (Finset.mem_filter.mp hjA).2 with ⟨e, he, rfl⟩
    exact (Finset.mem_filter.mp he).2.2 hjZ
  have hIL_disj_ZP : Disjoint ZP IL := by
    rw [Finset.disjoint_left]; intro i hiZ hiI; exact (Finset.mem_filter.mp hiI).2.1 hiZ
  have hIL_disj_AL : Disjoint AL IL := by
    rw [Finset.disjoint_left]; intro i hiA hiI; exact (Finset.mem_filter.mp hiI).2.2 hiA
  have hIR_disj_ZQ : Disjoint ZQ IR := by
    rw [Finset.disjoint_left]; intro j hjZ hjI; exact (Finset.mem_filter.mp hjI).2.1 hjZ
  have hIR_disj_AR : Disjoint AR IR := by
    rw [Finset.disjoint_left]; intro j hjA hjI; exact (Finset.mem_filter.mp hjI).2.2 hjA
  have hPcov : ZP ∪ AL ∪ IL = Finset.univ := by
    ext i
    simp only [Finset.mem_union, IL, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    tauto
  have hQcov : ZQ ∪ AR ∪ IR = Finset.univ := by
    ext j
    simp only [Finset.mem_union, IR, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    tauto
  have hAL_col_ex : ∀ i ∈ AL, ∃ c : Fin k, ∀ x : P, x.val i = x.val (left (s c)) := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, hcL, _⟩
    exact ⟨c, hcL⟩
  have hAR_col_ex : ∀ j ∈ AR, ∃ c : Fin k, ∀ y : Q, y.val j = y.val (right (s c)) := by
    intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, _, hcR⟩
    exact ⟨c, hcR⟩
  have hkpos : 0 < k := by omega
  let c0 : Fin k := ⟨0, hkpos⟩
  let cL : Fin n → Fin k := fun i =>
    if h : i ∈ AL then Classical.choose (hAL_col_ex i h) else c0
  let cR : Fin n → Fin k := fun j =>
    if h : j ∈ AR then Classical.choose (hAR_col_ex j h) else c0
  have hcL_spec : ∀ i ∈ AL, ∀ x : P, x.val i = x.val (left (s (cL i))) := by
    intro i hi
    simp only [cL, hi, ↓reduceDIte]
    exact Classical.choose_spec (hAL_col_ex i hi)
  have hcR_spec : ∀ j ∈ AR, ∀ y : Q, y.val j = y.val (right (s (cR j))) := by
    intro j hj
    simp only [cR, hj, ↓reduceDIte]
    exact Classical.choose_spec (hAR_col_ex j hj)
  have hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c := by
    intro c
    have hmem : left (s c) ∈ AL :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    refine ⟨hmem, hPdist _ _ fun x => (hcL_spec _ hmem x).symm⟩
  have hrepR : ∀ c : Fin k, right (s c) ∈ AR ∧ cR (right (s c)) = c := by
    intro c
    have hmem : right (s c) ∈ AR :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    refine ⟨hmem, hQdist _ _ fun y => (hcR_spec _ hmem y).symm⟩
  have hedge_same_col : ∀ e ∈ Eact, cL (left e) = cR (right e) := by
    intro e he
    rcases hEact_col e he with ⟨c, hcL, hcR⟩
    have hmemL : left e ∈ AL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩
    have hmemR : right e ∈ AR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩
    have h1 : cL (left e) = c := hPdist _ _ fun x => (hcL_spec _ hmemL x).symm.trans (hcL x)
    have h2 : cR (right e) = c := hQdist _ _ fun y => (hcR_spec _ hmemR y).symm.trans (hcR y)
    rw [h1, h2]
  obtain ⟨rP, hrP2, hdimP, hrP0, hrP1⟩ :=
    finrank_le_card_add_k_sub_syndrome t k P hPcode ZP AL IL
      hAL_disj_ZP hIL_disj_ZP hIL_disj_AL hPcov
      (fun i hi x hx => (Finset.mem_filter.mp hi).2 ⟨x, hx⟩)
      (fun c => left (s c)) cL hrepL
      (fun i hi x hx => hcL_spec i hi ⟨x, hx⟩)
  obtain ⟨rQ, hrQ2, hdimQ, hrQ0, hrQ1⟩ :=
    finrank_le_card_add_k_sub_syndrome t k Q hQcode ZQ AR IR
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      (fun j hj y hy => (Finset.mem_filter.mp hj).2 ⟨y, hy⟩)
      (fun c => right (s c)) cR hrepR
      (fun j hj y hy => hcR_spec j hj ⟨y, hy⟩)
  have hAL_sum : AL.card = ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hi => ⟨cL i, hi, rfl⟩, fun ⟨_, hi, _⟩ => hi⟩
    · intro c1 _ c2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAR_sum : AR.card = ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hj => ⟨cR j, hj, rfl⟩, fun ⟨_, hj, _⟩ => hj⟩
    · intro c1 _ c2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAL_ge_k : k ≤ AL.card := by
    rw [hAL_sum]
    have : ∑ _c : Fin k, 1 ≤ ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card :=
      Finset.sum_le_sum fun c _ => Finset.card_pos.mpr ⟨left (s c), Finset.mem_filter.mpr (hrepL c)⟩
    simpa using this
  have hAR_ge_k : k ≤ AR.card := by
    rw [hAR_sum]
    have : ∑ _c : Fin k, 1 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
      Finset.sum_le_sum fun c _ => Finset.card_pos.mpr ⟨right (s c), Finset.mem_filter.mpr (hrepR c)⟩
    simpa using this
  obtain ⟨nLive, nDead, nEnds, hLive_Dead, hLive_card, hEnds_le_Dead, hEnds_le_Live, hEnds_ge⟩ :=
    cycle_ends_bound n k hn_pos hk ZP ZQ AL AR IL IR
      hAL_disj_ZP hIL_disj_ZP hIL_disj_AL hPcov
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      Eact left right (fun _ => rfl) (fun _ => rfl)
      (fun e => by simp only [Eact, Finset.mem_filter, Finset.mem_univ, true_and])
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩)
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩)
      s hs_act cL cR hrepL hedge_same_col
  have hdimP' : Module.finrank F P + rP ≤ IL.card + k := hdimP
  have hdimQ' : Module.finrank F Q + rQ ≤ IR.card + k := hdimQ
  have hn_eq : n = 3 * t := rfl
  change 2 * (Module.finrank F P + Module.finrank F Q) + 5 ≤ 2 * n + k
  have hmaster : 2 * (Module.finrank F P + Module.finrank F Q) +
      (AL.card - k) + (AR.card - k) + (nDead - nEnds) +
      (nEnds - (IL.card + IR.card + k)) + 2 * (rP + rQ) ≤ 2 * n + k := by
    omega
  by_cases hsum3 : 3 ≤ rP + rQ
  · omega
  · by_cases hrP0_case : rP = 0
    · have hAL_2k : 2 * k ≤ AL.card := by
        rw [hAL_sum]
        have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card :=
          Finset.sum_le_sum fun c _ => hrP0 hrP0_case c
        simpa [mul_comm] using this
      by_cases hrQ0_case : rQ = 0
      · have hAR_2k : 2 * k ≤ AR.card := by
          rw [hAR_sum]
          have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
            Finset.sum_le_sum fun c _ => hrQ0 hrQ0_case c
          simpa [mul_comm] using this
        omega
      · omega
    · by_cases hrQ0_case : rQ = 0
      · have hAR_2k : 2 * k ≤ AR.card := by
          rw [hAR_sum]
          have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
            Finset.sum_le_sum fun c _ => hrQ0 hrQ0_case c
          simpa [mul_comm] using this
        omega
      · have hrP1_eq : rP = 1 := by omega
        have hrQ1_eq : rQ = 1 := by omega
        by_cases hex0 : (AL.card - k) + (AR.card - k) + (nDead - nEnds) = 0
        · exfalso
          have hAL_eq_k : AL.card = k := by omega
          have hAR_eq_k : AR.card = k := by omega
          have hDead_eq : nDead = nEnds := by omega
          have hAL_c1 : ∀ c : Fin k, (AL.filter (fun i => cL i = c)).card = 1 := by
            intro c
            by_contra hne1
            have hge1 : 1 ≤ (AL.filter (fun i => cL i = c)).card :=
              Finset.card_pos.mpr ⟨left (s c), Finset.mem_filter.mpr (hrepL c)⟩
            have hge2 : 2 ≤ (AL.filter (fun i => cL i = c)).card := by omega
            have hsum_gt : k < ∑ c' : Fin k, (AL.filter (fun i => cL i = c')).card := by
              have h1 : ∑ c' : Fin k, (if c' = c then 2 else 1) ≤
                  ∑ c' : Fin k, (AL.filter (fun i => cL i = c')).card := by
                refine Finset.sum_le_sum fun c' _ => ?_
                by_cases hc' : c' = c
                · subst hc'; simpa using hge2
                · simp only [hc', ↓reduceIte]
                  exact Finset.card_pos.mpr ⟨left (s c'), Finset.mem_filter.mpr (hrepL c')⟩
              have h2 : ∑ c' : Fin k, (if c' = c then 2 else 1) = k + 1 := by
                rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
                have hf1 : (Finset.univ.filter (fun c' : Fin k => c' = c)).card = 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => c' = c) = {c} := by ext x; simp
                  rw [this, Finset.card_singleton]
                have hf2 : (Finset.univ.filter (fun c' : Fin k => ¬ c' = c)).card = k - 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => ¬ c' = c) = Finset.univ.erase c := by ext x; simp
                  rw [this, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
                rw [hf1, hf2]
                simp only [smul_eq_mul]
                omega
              omega
            omega
          have hAR_c1 : ∀ c : Fin k, (AR.filter (fun j => cR j = c)).card = 1 := by
            intro c
            by_contra hne1
            have hge1 : 1 ≤ (AR.filter (fun j => cR j = c)).card :=
              Finset.card_pos.mpr ⟨right (s c), Finset.mem_filter.mpr (hrepR c)⟩
            have hge2 : 2 ≤ (AR.filter (fun j => cR j = c)).card := by omega
            have hsum_gt : k < ∑ c' : Fin k, (AR.filter (fun j => cR j = c')).card := by
              have h1 : ∑ c' : Fin k, (if c' = c then 2 else 1) ≤
                  ∑ c' : Fin k, (AR.filter (fun j => cR j = c')).card := by
                refine Finset.sum_le_sum fun c' _ => ?_
                by_cases hc' : c' = c
                · subst hc'; simpa using hge2
                · simp only [hc', ↓reduceIte]
                  exact Finset.card_pos.mpr ⟨right (s c'), Finset.mem_filter.mpr (hrepR c')⟩
              have h2 : ∑ c' : Fin k, (if c' = c then 2 else 1) = k + 1 := by
                rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
                have hf1 : (Finset.univ.filter (fun c' : Fin k => c' = c)).card = 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => c' = c) = {c} := by ext x; simp
                  rw [this, Finset.card_singleton]
                have hf2 : (Finset.univ.filter (fun c' : Fin k => ¬ c' = c)).card = k - 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => ¬ c' = c) = Finset.univ.erase c := by ext x; simp
                  rw [this, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
                rw [hf1, hf2]
                simp only [smul_eq_mul]
                omega
              omega
            omega
          obtain ⟨a, ha⟩ := hrP1 hrP1_eq hAL_c1
          obtain ⟨b, hb⟩ := hrQ1 hrQ1_eq hAR_c1
          have hUP_le_t : AL.card + IL.card ≤ t := by
            rw [← Finset.card_union_of_disjoint hIL_disj_AL]
            have hsub : AL ∪ IL ⊆ Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) :=
              fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha i hi⟩
            exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq t a)
          have hUQ_le_t : AR.card + IR.card ≤ t := by
            rw [← Finset.card_union_of_disjoint hIR_disj_AR]
            have hsub : AR ∪ IR ⊆ Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = b) :=
              fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb j hj⟩
            exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq t b)
          omega
        · omega

lemma pure_copy_dim_bound {t : ℕ} (ht : 0 < t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (L : Fin 6 → (P →ₗ[F2] F2)) (M : Fin 6 → (Q →ₗ[F2] F2))
    (hL : LinearIndependent F2 L) (hM : LinearIndependent F2 M)
    (hocc : ∀ c : Fin 6, ∃ i : Fin (3 * t),
      ((LinearMap.proj i).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c) ∨
      ((LinearMap.proj (nxt ht i)).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c))
    (hpure : ∀ i : Fin (3 * t),
      (((LinearMap.proj i).comp P.subtype = 0 ∨ (LinearMap.proj i).comp Q.subtype = 0) ∨
        ∃ c : Fin 6, (LinearMap.proj i).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c) ∧
      (((LinearMap.proj (nxt ht i)).comp P.subtype = 0 ∨ (LinearMap.proj i).comp Q.subtype = 0) ∨
        ∃ c : Fin 6, (LinearMap.proj (nxt ht i)).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c)) :
    Module.finrank F2 P + Module.finrank F2 Q ≤ 3 * t := by
  let left (e : Fin (2 * (3 * t))) := ix ht ((e.val + 1) / 2)
  let right (e : Fin (2 * (3 * t))) := ix ht (e.val / 2)
  let X (e) := (LinearMap.proj (left e)).comp P.subtype
  let Y (e) := (LinearMap.proj (right e)).comp Q.subtype
  have pick : ∀ c, ∃ e, X e = L c ∧ Y e = M c := by
    intro c
    obtain ⟨i, hi | hi⟩ := hocc c
    · let e : Fin (2 * (3 * t)) := ⟨2 * i.val, by have := i.isLt; omega⟩
      have hiL : left e = i := by
        apply Fin.ext; change ((2 * i.val + 1) / 2) % _ = _
        rw [show (2 * i.val + 1) / 2 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
      have hiR : right e = i := by
        apply Fin.ext; change (2 * i.val / 2) % _ = _
        rw [show 2 * i.val / 2 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
      exact ⟨e, by simpa only [X, hiL] using hi.1, by simpa only [Y, hiR] using hi.2⟩
    · let e : Fin (2 * (3 * t)) := ⟨2 * i.val + 1, by have := i.isLt; omega⟩
      have hiL : left e = nxt ht i := by
        apply Fin.ext; change ((2 * i.val + 1 + 1) / 2) % _ = (i.val + 1) % _
        rw [show (2 * i.val + 1 + 1) / 2 = i.val + 1 by omega]
      have hiR : right e = i := by
        apply Fin.ext; change ((2 * i.val + 1) / 2) % _ = _
        rw [show (2 * i.val + 1) / 2 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
      exact ⟨e, by simpa only [X, hiL] using hi.1, by simpa only [Y, hiR] using hi.2⟩
  choose s hsX hsY using pick
  have hsL : Function.Surjective (fun x : P => fun c => x.val (left (s c))) := by
    change Function.Surjective (LinearMap.pi (fun c => X (s c)))
    simpa only [hsX] using pi_surjective_of_linearIndependent L hL
  have hsR : Function.Surjective (fun y : Q => fun c => y.val (right (s c))) := by
    change Function.Surjective (LinearMap.pi (fun c => Y (s c)))
    simpa only [hsY] using pi_surjective_of_linearIndependent M hM
  have h := pure_slots_dim t ht 6 (by decide) P Q hP hQ s hsL hsR
  suffices hdim : 2 * (Module.finrank F2 P + Module.finrank F2 Q) + 5 ≤ 2 * (3 * t) + 6 by omega
  apply h
  intro e
  let i : Fin (3 * t) := ⟨e.val / 2, by have := e.isLt; omega⟩
  have hiR : right e = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have branches : (X e = 0 ∨ Y e = 0) ∨ ∃ c, X e = L c ∧ Y e = M c := by
    by_cases hev : e.val % 2 = 0
    · have hiL : left e = i := by
        apply Fin.ext; change ((e.val + 1) / 2) % _ = e.val / 2
        rw [show (e.val + 1) / 2 = e.val / 2 by omega, Nat.mod_eq_of_lt i.isLt]
      simpa only [X, Y, hiL, hiR] using (hpure i).1
    · have hiL : left e = nxt ht i := by
        apply Fin.ext; change ((e.val + 1) / 2) % _ = (e.val / 2 + 1) % _
        rw [show (e.val + 1) / 2 = e.val / 2 + 1 by omega]
      simpa only [X, Y, hiL, hiR] using (hpure i).2
  rcases branches with (h0 | h0) | ⟨c, hx, hy⟩
  · exact Or.inl (fun x => LinearMap.congr_fun h0 x)
  · exact Or.inr (Or.inl (fun y => LinearMap.congr_fun h0 y))
  · exact Or.inr (Or.inr ⟨c, fun x => LinearMap.congr_fun (hx.trans (hsX c).symm) x,
                           fun y => LinearMap.congr_fun (hy.trans (hsY c).symm) y⟩)

lemma finrank_eval_le_span {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (forms : ι → V →ₗ[K] K) (A : Finset ι) :
    Module.finrank K (LinearMap.range (LinearMap.pi fun i : A => forms i.val)) ≤
      Module.finrank K (Submodule.span K (forms '' (A : Set ι))) := by
  classical
  let S := Submodule.span K (forms '' (A : Set ι))
  let φ := LinearMap.pi fun i : A => forms i.val
  have hk : S.dualCoannihilator ≤ LinearMap.ker φ := by
    intro x hx
    have hx' : x ∈ (S.dualCoannihilator : Set V) := hx
    dsimp only [S] at hx'
    rw [Submodule.coe_dualCoannihilator_span] at hx'
    exact LinearMap.mem_ker.mpr (funext fun i => hx' _ ⟨i.val, i.property, rfl⟩)
  have hr := LinearMap.finrank_range_add_finrank_ker φ
  have hs := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  have hle := Submodule.finrank_mono hk
  calc
    Module.finrank K (LinearMap.range φ) = Module.finrank K V - Module.finrank K (LinearMap.ker φ) :=
      Nat.eq_sub_of_add_eq hr
    _ ≤ Module.finrank K V - Module.finrank K S.dualCoannihilator := Nat.sub_le_sub_left hle _
    _ = Module.finrank K S := (Nat.eq_sub_of_add_eq hs).symm

lemma two_large_lanes {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hP6 : 6 ≤ Module.finrank F2 P) (hQ6 : 6 ≤ Module.finrank F2 Q) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      324 * (Nat.card P * Nat.card Q) := by
  let n := 3 * t
  let a : Fin (2 * n) → (P →ₗ[F2] F2) := fun e =>
    let i : Fin n := ⟨e.val / 2, by omega⟩
    if e.val % 2 = 0 then (LinearMap.proj i).comp P.subtype
    else (LinearMap.proj (nxt ht i)).comp P.subtype
  let b : Fin (2 * n) → (Q →ₗ[F2] F2) := fun e =>
    let i : Fin n := ⟨e.val / 2, by omega⟩
    (LinearMap.proj i).comp Q.subtype
  have hspan_rk : ∀ (U : Submodule F2 (Fin n → F2)) (A : Finset (Fin n)),
      Module.finrank F2 U ≤
        Module.finrank F2 (Submodule.span F2 ((fun i : Fin n => (LinearMap.proj i).comp U.subtype) '' (A : Set (Fin n)))) +
        Module.finrank F2 (U ⊓ suppSub Aᶜ : Submodule F2 (Fin n → F2)) := by
    intro U A
    let φ : U →ₗ[F2] (A → F2) :=
      { toFun := fun u i => u.1 i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hker : Module.finrank F2 (LinearMap.ker φ) =
        Module.finrank F2 (U ⊓ suppSub Aᶜ : Submodule F2 (Fin n → F2)) := by
      let e : LinearMap.ker φ ≃ₗ[F2] (U ⊓ suppSub Aᶜ : Submodule F2 (Fin n → F2)) :=
        { toFun := fun u => ⟨u.1.1, u.1.2, fun i hi => by
            have hiA : i ∈ A := by simpa using hi
            exact congrFun (LinearMap.mem_ker.mp u.2) ⟨i, hiA⟩⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := fun u => ⟨⟨u.1, u.2.1⟩, LinearMap.mem_ker.mpr (funext fun i => u.2.2 i.1 (by simp))⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact e.finrank_eq
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker] at hrk
    have hrange_le := finrank_eval_le_span (K := F2) (fun i : Fin n => (LinearMap.proj i).comp U.subtype) A
    change Module.finrank F2 (LinearMap.range φ) ≤ _ at hrange_le
    omega
  have hcut : ∀ S : Finset (Fin (2 * n)),
      6 ≤ Module.finrank F2 (Submodule.span F2 (a '' (S : Set (Fin (2 * n))))) +
          Module.finrank F2 (Submodule.span F2 (b '' ((Sᶜ : Finset (Fin (2 * n))) : Set (Fin (2 * n))))) := by
    intro S
    have hn : n = 3 * t := rfl
    let A : Finset (Fin n) := Finset.univ.filter fun i =>
      (⟨2 * i.val, by omega⟩ : Fin (2 * n)) ∈ S ∨
      (⟨2 * (prv i).val + 1, by omega⟩ : Fin (2 * n)) ∈ S
    let B : Finset (Fin n) := Finset.univ.filter fun j =>
      (⟨2 * j.val, by omega⟩ : Fin (2 * n)) ∈ Sᶜ ∨
      (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)) ∈ Sᶜ
    let X : Finset (Fin n) := Aᶜ
    let Y : Finset (Fin n) := Bᶜ
    have hA_sub : (fun i : Fin n => (LinearMap.proj i).comp P.subtype) '' (A : Set (Fin n)) ⊆
        a '' (S : Set (Fin (2 * n))) := by
      rintro _ ⟨i, hiA, rfl⟩
      rcases (Finset.mem_filter.mp hiA).2 with h1 | h2
      · refine ⟨⟨2 * i.val, by omega⟩, h1, ?_⟩
        dsimp only [a]
        have hev : (2 * i.val) % 2 = 0 := by omega
        have hdiv : (⟨(2 * i.val) / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; omega)
        rw [if_pos hev, hdiv]
      · refine ⟨⟨2 * (prv i).val + 1, by omega⟩, h2, ?_⟩
        dsimp only [a]
        have hodd : ¬ (2 * (prv i).val + 1) % 2 = 0 := by omega
        have hdiv : (⟨(2 * (prv i).val + 1) / 2, by omega⟩ : Fin n) = prv i := Fin.ext (by dsimp only; omega)
        rw [if_neg hodd, hdiv, nxt_prv ht]
    have hB_sub : (fun j : Fin n => (LinearMap.proj j).comp Q.subtype) '' (B : Set (Fin n)) ⊆
        b '' ((Sᶜ : Finset (Fin (2 * n))) : Set (Fin (2 * n))) := by
      rintro _ ⟨j, hjB, rfl⟩
      rcases (Finset.mem_filter.mp hjB).2 with h1 | h2
      · refine ⟨⟨2 * j.val, by omega⟩, h1, ?_⟩
        dsimp only [b]
        have hdiv : (⟨(2 * j.val) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
        rw [hdiv]
      · refine ⟨⟨2 * j.val + 1, by omega⟩, h2, ?_⟩
        dsimp only [b]
        have hdiv : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
        rw [hdiv]
    have hrkP : Module.finrank F2 P - Module.finrank F2 (codeSub t ⊓ suppSub X : Submodule F2 (Fin n → F2)) ≤
        Module.finrank F2 (Submodule.span F2 (a '' (S : Set (Fin (2 * n))))) := by
      have h1 := hspan_rk P A
      have h2 := Submodule.finrank_mono (Submodule.span_mono (R := F2) hA_sub)
      have h3 : (P ⊓ suppSub X : Submodule F2 (Fin n → F2)) ≤ codeSub t ⊓ suppSub X :=
        inf_le_inf_right _ (fun x hx => mem_codeSub.mpr (hP x hx))
      have h4 := Submodule.finrank_mono h3
      exact Nat.sub_le_of_le_add (h1.trans (Nat.add_le_add h2 h4))
    have hrkQ : Module.finrank F2 Q - Module.finrank F2 (codeSub t ⊓ suppSub Y : Submodule F2 (Fin n → F2)) ≤
        Module.finrank F2 (Submodule.span F2 (b '' ((Sᶜ : Finset (Fin (2 * n))) : Set (Fin (2 * n))))) := by
      have h1 := hspan_rk Q B
      have h2 := Submodule.finrank_mono (Submodule.span_mono (R := F2) hB_sub)
      have h3 : (Q ⊓ suppSub Y : Submodule F2 (Fin n → F2)) ≤ codeSub t ⊓ suppSub Y :=
        inf_le_inf_right _ (fun y hy => mem_codeSub.mpr (hQ y hy))
      have h4 := Submodule.finrank_mono h3
      exact Nat.sub_le_of_le_add (h1.trans (Nat.add_le_add h2 h4))
    have hdisj_XY : Disjoint X (Y ∪ Y.image (nxt ht)) := by
      rw [Finset.disjoint_left]
      intro i hiX hiY
      have hiA : i ∉ A := Finset.mem_compl.mp hiX
      rcases Finset.mem_union.mp hiY with hj | hj
      · have hjB : i ∉ B := Finset.mem_compl.mp hj
        by_cases hmem : (⟨2 * i.val, by omega⟩ : Fin (2 * n)) ∈ S
        · exact hiA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hmem⟩)
        · exact hjB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_compl.mpr hmem)⟩)
      · obtain ⟨j, hjY, rfl⟩ := Finset.mem_image.mp hj
        have hjB : j ∉ B := Finset.mem_compl.mp hjY
        by_cases hmem : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)) ∈ S
        · exact hiA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by
          convert hmem using 1 <;> congr 1 <;> simp [prv_nxt ht])⟩)
        · exact hjB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_compl.mpr hmem)⟩)
    have hdisj_YX : Disjoint Y (X ∪ X.image prv) := by
      rw [Finset.disjoint_left]
      intro j hjY hjX
      rcases Finset.mem_union.mp hjX with hi | hi
      · exact Finset.disjoint_left.mp hdisj_XY hi (Finset.mem_union_left _ hjY)
      · obtain ⟨i, hiX, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.disjoint_left.mp hdisj_XY hiX
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨prv i, hjY, nxt_prv ht i⟩))
    have hXY_sum : X.card + (Y ∪ Y.image (nxt ht)).card ≤ n := by
      rw [← Finset.card_union_of_disjoint hdisj_XY]
      have := Finset.card_le_univ (X ∪ (Y ∪ Y.image (nxt ht)))
      rwa [Fintype.card_fin] at this
    have hYX_sum : Y.card + (X ∪ X.image prv).card ≤ n := by
      rw [← Finset.card_union_of_disjoint hdisj_YX]
      have := Finset.card_le_univ (Y ∪ (X ∪ X.image prv))
      rwa [Fintype.card_fin] at this
    by_cases hX0 : Module.finrank F2 (codeSub t ⊓ suppSub X : Submodule F2 (Fin n → F2)) = 0
    · omega
    by_cases hY0 : Module.finrank F2 (codeSub t ⊓ suppSub Y : Submodule F2 (Fin n → F2)) = 0
    · omega
    have hXne : X.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      apply hX0
      have hbot : (codeSub t ⊓ suppSub X : Submodule F2 (Fin n → F2)) = ⊥ := by
        ext x; simp only [Submodule.mem_inf, Submodule.mem_bot]
        exact ⟨fun hx => funext fun i => hx.2 i (by simp [hem]), fun h => by rw [h]; exact ⟨zero_mem _, zero_mem _⟩⟩
      rw [hbot, finrank_bot]
    have hYne : Y.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      apply hY0
      have hbot : (codeSub t ⊓ suppSub Y : Submodule F2 (Fin n → F2)) = ⊥ := by
        ext x; simp only [Submodule.mem_inf, Submodule.mem_bot]
        exact ⟨fun hx => funext fun i => hx.2 i (by simp [hem]), fun h => by rw [h]; exact ⟨zero_mem _, zero_mem _⟩⟩
      rw [hbot, finrank_bot]
    by_cases hX1 : ∃ r : Fin 3, ∀ i ∈ X, i.val % 3 = r.val
    · obtain ⟨rX, hrX⟩ := hX1
      have hdX := finrank_code_inf_suppSub_one_res X hXne rX hrX
      rw [hdX] at hrkP
      have hXge2 : 2 ≤ X.card := by rw [hdX] at hX0; omega
      have hXnbr : (X ∪ X.image prv).card = 2 * X.card := by
        have hdisj : Disjoint X (X.image prv) := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj2
          have h1 := hrX (prv i) hj1; have h2 := hrX i hi; have h3 := prv_mod3 i
          have := rX.isLt; omega
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (prv_inj ht)]
        ring
      by_cases hY1 : ∃ r : Fin 3, ∀ j ∈ Y, j.val % 3 = r.val
      · obtain ⟨rY, hrY⟩ := hY1
        have hdY := finrank_code_inf_suppSub_one_res Y hYne rY hrY
        rw [hdY] at hrkQ
        have hXlet : X.card ≤ t := by
          have hsub : X ⊆ Finset.univ.filter (fun i : Fin n => i.val % 3 = rX.val) :=
            fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrX i hi⟩
          exact (Finset.card_le_card hsub).trans_eq (card_resClass (t := t) rX)
        have hYlet : Y.card ≤ t := by
          have hsub : Y ⊆ Finset.univ.filter (fun j : Fin n => j.val % 3 = rY.val) :=
            fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrY j hj⟩
          exact (Finset.card_le_card hsub).trans_eq (card_resClass (t := t) rY)
        omega
      · push Not at hY1
        obtain ⟨j1, hj1⟩ := hYne
        have hex2 : ∃ j2 ∈ Y, j1.val % 3 ≠ j2.val % 3 := by
          by_contra hall; push Not at hall
          obtain ⟨j, hj, hne⟩ := hY1 ⟨j1.val % 3, Nat.mod_lt _ (by omega)⟩
          exact hne (hall j hj).symm
        obtain ⟨j2, hj2, hmod⟩ := hex2
        have hdY := finrank_code_inf_suppSub_two_res Y j1 j2 hj1 hj2 hmod
        rw [hdY] at hrkQ
        omega
    · push Not at hX1
      obtain ⟨i1, hi1⟩ := hXne
      have hexX : ∃ i2 ∈ X, i1.val % 3 ≠ i2.val % 3 := by
        by_contra hall; push Not at hall
        obtain ⟨i, hi, hne⟩ := hX1 ⟨i1.val % 3, Nat.mod_lt _ (by omega)⟩
        exact hne (hall i hi).symm
      obtain ⟨i2, hi2, hmodX⟩ := hexX
      have hdX := finrank_code_inf_suppSub_two_res X i1 i2 hi1 hi2 hmodX
      rw [hdX] at hrkP
      by_cases hY1 : ∃ r : Fin 3, ∀ j ∈ Y, j.val % 3 = r.val
      · obtain ⟨rY, hrY⟩ := hY1
        have hdY := finrank_code_inf_suppSub_one_res Y hYne rY hrY
        rw [hdY] at hrkQ
        have hYge2 : 2 ≤ Y.card := by rw [hdY] at hY0; omega
        have hYnbr : (Y ∪ Y.image (nxt ht)).card = 2 * Y.card := by
          have hdisj : Disjoint Y (Y.image (nxt ht)) := by
            rw [Finset.disjoint_left]
            intro j hj1 hj2
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj2
            have h1 := hrY (nxt ht i) hj1; have h2 := hrY i hi; have h3 := nxt_mod3 ht i
            have := rY.isLt; omega
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (nxt_inj ht)]
          ring
        omega
      · push Not at hY1
        obtain ⟨j1, hj1⟩ := hYne
        have hexY : ∃ j2 ∈ Y, j1.val % 3 ≠ j2.val % 3 := by
          by_contra hall; push Not at hall
          obtain ⟨j, hj, hne⟩ := hY1 ⟨j1.val % 3, Nat.mod_lt _ (by omega)⟩
          exact hne (hall j hj).symm
        obtain ⟨j2, hj2, hmodY⟩ := hexY
        have hdY := finrank_code_inf_suppSub_two_res Y j1 j2 hj1 hj2 hmodY
        rw [hdY] at hrkQ
        have hXnotuniv : X ≠ Finset.univ := by
          intro hu
          have := Finset.disjoint_left.mp hdisj_YX hj1 (Finset.mem_union_left _ (by rw [hu]; exact Finset.mem_univ _))
          exact this
        have hXgt : X.card + 1 ≤ (X ∪ X.image prv).card := by
          let indX : Fin n → F2 := fun i => if i ∈ X then 1 else 0
          have hsupp : suppF indX = X := by ext i; simp [suppF, indX]
          have hind0 : indX ≠ 0 := by
            intro h0; have : X = ∅ := by rw [← hsupp, h0]; simp [suppF]
            exact (Finset.nonempty_iff_ne_empty.mp ⟨i1, hi1⟩) this
          have h := card_nbrF_gt_card_suppF ht hind0 (by rwa [hsupp])
          rwa [nbrF, hsupp] at h
        omega
  obtain ⟨I, hIcard, hI_a, hI_b⟩ := linear_matroid_intersection a b 6 hcut
  let eI : Fin 6 ≃ I := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hIcard])).symm
  let L : Fin 6 → (P →ₗ[F2] F2) := fun c => a (eI c).1
  let M : Fin 6 → (Q →ₗ[F2] F2) := fun c => b (eI c).1
  have hL : LinearIndependent F2 L := hI_a.comp eI eI.injective
  have hM : LinearIndependent F2 M := hI_b.comp eI eI.injective
  have hedge_hit : ∀ (e : Fin (2 * n)) (x : P) (y : Q), hitP ht x.val y.val → a e x * b e y = 0 := by
    intro e x y hxy
    dsimp only [a, b]
    split_ifs
    · exact (hxy ⟨e.val / 2, by omega⟩).1
    · exact (hxy ⟨e.val / 2, by omega⟩).2
  by_cases hextra : ∃ e : Fin (2 * n), a e ≠ 0 ∧ b e ≠ 0 ∧ ∀ c : Fin 6, ¬ (a e = L c ∧ b e = M c)
  · obtain ⟨e0, ha0, hb0, hnew⟩ := hextra
    exact extra_product_bound L M hL hM (a e0) (b e0) ha0 hb0 hnew
      (fun x y => hitP ht x.val y.val)
      (fun x y hxy => ⟨fun c => hedge_hit (eI c).1 x y hxy, hedge_hit e0 x y hxy⟩)
  · push Not at hextra
    exfalso
    have hocc : ∀ c : Fin 6, ∃ i : Fin n,
        ((LinearMap.proj i).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c) ∨
        ((LinearMap.proj (nxt ht i)).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c) := by
      intro c
      let e := (eI c).1
      refine ⟨⟨e.val / 2, by omega⟩, ?_⟩
      by_cases hev : e.val % 2 = 0
      · left; exact ⟨by simp [L, a, e, hev], rfl⟩
      · right; exact ⟨by simp [L, a, e, hev], rfl⟩
    have hpure : ∀ i : Fin n,
        (((LinearMap.proj i).comp P.subtype = 0 ∨ (LinearMap.proj i).comp Q.subtype = 0) ∨
          ∃ c : Fin 6, (LinearMap.proj i).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c) ∧
        (((LinearMap.proj (nxt ht i)).comp P.subtype = 0 ∨ (LinearMap.proj i).comp Q.subtype = 0) ∨
          ∃ c : Fin 6, (LinearMap.proj (nxt ht i)).comp P.subtype = L c ∧ (LinearMap.proj i).comp Q.subtype = M c) := by
      intro i
      constructor
      · let e : Fin (2 * n) := ⟨2 * i.val, by omega⟩
        have hae : a e = (LinearMap.proj i).comp P.subtype := by
          dsimp only [a, e]
          have hev : (2 * i.val) % 2 = 0 := by omega
          have hdiv : (⟨(2 * i.val) / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; omega)
          rw [if_pos hev, hdiv]
        have hbe : b e = (LinearMap.proj i).comp Q.subtype := by
          dsimp only [b, e]
          have hdiv : (⟨(2 * i.val) / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; omega)
          rw [hdiv]
        by_cases h1 : a e = 0
        · exact Or.inl (Or.inl (hae ▸ h1))
        · by_cases h2 : b e = 0
          · exact Or.inl (Or.inr (hbe ▸ h2))
          · obtain ⟨c, hc⟩ := hextra e h1 h2
            exact Or.inr ⟨c, hae ▸ hc.1, hbe ▸ hc.2⟩
      · let e : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩
        have hae : a e = (LinearMap.proj (nxt ht i)).comp P.subtype := by
          dsimp only [a, e]
          have hodd : ¬ (2 * i.val + 1) % 2 = 0 := by omega
          have hdiv : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; omega)
          rw [if_neg hodd, hdiv]
        have hbe : b e = (LinearMap.proj i).comp Q.subtype := by
          dsimp only [b, e]
          have hdiv : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; omega)
          rw [hdiv]
        by_cases h1 : a e = 0
        · exact Or.inl (Or.inl (hae ▸ h1))
        · by_cases h2 : b e = 0
          · exact Or.inl (Or.inr (hbe ▸ h2))
          · obtain ⟨c, hc⟩ := hextra e h1 h2
            exact Or.inr ⟨c, hae ▸ hc.1, hbe ▸ hc.2⟩
    have hbd := pure_copy_dim_bound ht hP hQ L M hL hM hocc hpure
    omega

end two_large_lanes

section small_side

lemma wt8_le_of_ge {r k : ℕ} (hk : k ≤ r) (hk8 : k ≤ 8) : wt8 r ≤ 2 ^ (8 - k) := by
  unfold wt8
  split_ifs with h
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact Nat.one_le_pow _ _ (by norm_num)

lemma wt8_eq_16 {r : ℕ} (hr : r = 4) : wt8 r = 16 := by subst hr; unfold wt8; norm_num
lemma wt8_le_8 {r : ℕ} (hr : 5 ≤ r) : wt8 r ≤ 8 := wt8_le_of_ge hr (by omega)
lemma wt8_le_4 {r : ℕ} (hr : 6 ≤ r) : wt8 r ≤ 4 := wt8_le_of_ge hr (by omega)
lemma wt8_le_2 {r : ℕ} (hr : 7 ≤ r) : wt8 r ≤ 2 := wt8_le_of_ge hr (by omega)

lemma small_side_row_sum_bound {t : ℕ} (ht : 0 < t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hQ : Q ≤ codeSub t)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hdP_ge : 3 ≤ Module.finrank F2 P) (hdP_le : Module.finrank F2 P ≤ 5) :
    letI : Fintype P := Fintype.ofFinite P
    let d := Module.finrank F2 P
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      (2 ^ (11 - d) + ∑ x ∈ (Finset.univ : Finset P).erase ⟨0, zero_mem P⟩,
        wt8 (rkC (nbrF x.val))) * (Nat.card P * Nat.card Q) := by
  letI : Fintype P := Fintype.ofFinite P
  let d := Module.finrank F2 P
  have hcardP : Nat.card P = 2 ^ d := card_eq_two_pow_finrank
  have h2048 : 2048 = 2 ^ (11 - d) * 2 ^ d := by
    rw [← pow_add, show 11 - d + d = 11 by omega]; norm_num
  have htarget : 2 ^ (11 - d) * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      (2 ^ (11 - d) + ∑ x ∈ (Finset.univ : Finset P).erase ⟨0, zero_mem P⟩,
        wt8 (rkC (nbrF x.val))) * Nat.card Q := by
    rw [card_rows (P := fun (x : P) (y : Q) => hitP ht x.val y.val), Finset.mul_sum]
    let p0 : P := ⟨0, zero_mem P⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0), add_mul, Finset.sum_mul]
    apply Nat.add_le_add
    · have h0 : Nat.card {y : Q // hitP ht p0.val y.val} = Nat.card Q :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun y i => by simp [p0])
      rw [h0]
    · refine Finset.sum_le_sum fun x _ => ?_
      have hsub := card_hit_sub_le_code ht hQ x.val
      have hcodim : 3 * t - 2 - Module.finrank F2 Q ≤ d - 3 := by omega
      have hpow_le : 2 ^ (11 - d) * 2 ^ (3 * t - 2 - Module.finrank F2 Q) ≤ 256 := by
        rw [← pow_add]
        calc 2 ^ (11 - d + (3 * t - 2 - Module.finrank F2 Q))
            ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 256 := by norm_num
      have hmul1 : 2 ^ (11 - d) * Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val) ≤
          256 * Nat.card Q := by
        calc 2 ^ (11 - d) * Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val)
            = 2 ^ (11 - d) * (Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val)) := by ring
          _ ≤ 2 ^ (11 - d) * (2 ^ (3 * t - 2 - Module.finrank F2 Q) * Nat.card Q) :=
              Nat.mul_le_mul_left _ hsub
          _ = (2 ^ (11 - d) * 2 ^ (3 * t - 2 - Module.finrank F2 Q)) * Nat.card Q := by ring
          _ ≤ 256 * Nat.card Q := Nat.mul_le_mul_right _ hpow_le
      have hpow_pos : 0 < 2 ^ rkC (nbrF x.val) := Nat.pos_of_ne_zero (by positivity)
      refine Nat.le_of_mul_le_mul_right ?_ hpow_pos
      calc 2 ^ (11 - d) * Nat.card {y : Q // hitP ht x.val y.val} * 2 ^ rkC (nbrF x.val)
          ≤ 256 * Nat.card Q := hmul1
        _ ≤ wt8 (rkC (nbrF x.val)) * 2 ^ rkC (nbrF x.val) * Nat.card Q := by
            refine Nat.mul_le_mul_right _ ?_
            unfold wt8
            split_ifs with h8
            · rw [← pow_add, show 8 - rkC (nbrF x.val) + rkC (nbrF x.val) = 8 by omega]; norm_num
            · rw [one_mul]
              calc 256 = 2 ^ 8 := by norm_num
                _ ≤ 2 ^ rkC (nbrF x.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = wt8 (rkC (nbrF x.val)) * Nat.card Q * 2 ^ rkC (nbrF x.val) := by ring
  dsimp only
  rw [h2048, hcardP, mul_comm (2 ^ (11 - d)) (2 ^ d), mul_assoc]
  calc 2 ^ d * (2 ^ (11 - d) * Nat.card {w : P × Q // hitP ht w.1.val w.2.val})
      ≤ 2 ^ d * ((2 ^ (11 - d) + ∑ x ∈ (Finset.univ : Finset P).erase ⟨0, zero_mem P⟩,
          wt8 (rkC (nbrF x.val))) * Nat.card Q) := Nat.mul_le_mul_left _ htarget
    _ = (2 ^ (11 - d) + ∑ x ∈ (Finset.univ : Finset P).erase ⟨0, zero_mem P⟩,
          wt8 (rkC (nbrF x.val))) * (2 ^ d * Nat.card Q) := by ring

lemma sum_eq_zero_iff_even {t : ℕ} (x : Fin (3 * t) → F2) :
    (∑ i : Fin (3 * t), x i) = 0 ↔ (suppF x).card % 2 = 0 := by
  have h : (∑ i : Fin (3 * t), x i) = ((suppF x).card : F2) := by
    rw [← z2_sum_const_mod2, suppF]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx0 : x i = 0
    · simp [hx0]
    · simp [hx0, z2_eq_one_of_ne_zero hx0]
  rw [h, z2_natCast_eq_zero_iff]

def evenSub {t : ℕ} (P : Submodule F2 (Fin (3 * t) → F2)) : Submodule F2 (Fin (3 * t) → F2) :=
  { add_mem' := fun ha hb => ⟨P.add_mem ha.1 hb.1, by simp [Finset.sum_add_distrib, ha.2, hb.2]⟩
    carrier := {x | x ∈ P ∧ (∑ i, x i) = 0}
    zero_mem' := ⟨zero_mem P, by simp⟩
    smul_mem' := fun c x hx => ⟨P.smul_mem c hx.1, by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx.2, mul_zero]⟩ }

lemma evenSub_dichotomy {t : ℕ} (P : Submodule F2 (Fin (3 * t) → F2)) :
    (evenSub P = P) ∨
    (Module.finrank F2 (evenSub P) + 1 = Module.finrank F2 P ∧
      ∃ u : P, (suppF u.1).card % 2 = 1) := by
  let par : P →ₗ[F2] F2 :=
    { toFun := fun x => ∑ i, x.1 i
      map_add' := fun a b => by simp [Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [smul_eq_mul, ← Finset.mul_sum] }
  by_cases h0 : par = 0
  · left
    ext x
    simp only [evenSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    exact ⟨fun h => h.1, fun hx => ⟨hx, congrArg (fun f : P →ₗ[F2] F2 => f ⟨x, hx⟩) h0⟩⟩
  · right
    obtain ⟨u, hu⟩ : ∃ u : P, par u ≠ 0 := by
      by_contra h; push Not at h; exact h0 (LinearMap.ext h)
    have hsurj : LinearMap.range par = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨a • u, by rw [map_smul, z2_eq_one_of_ne_zero hu, smul_eq_mul, mul_one]⟩
    have hker : Module.finrank F2 (LinearMap.ker par) = Module.finrank F2 (evenSub P) := by
      let e : LinearMap.ker par ≃ₗ[F2] evenSub P :=
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact e.finrank_eq
    have hrk := LinearMap.finrank_range_add_finrank_ker par
    rw [hsurj, finrank_top, Module.finrank_self, hker] at hrk
    refine ⟨by omega, u, ?_⟩
    have hne : (suppF u.1).card % 2 ≠ 0 := fun h => hu ((sum_eq_zero_iff_even u.1).mpr h)
    omega

def pairVec {t : ℕ} (a b : Fin (3 * t)) : Fin (3 * t) → F2 :=
  Pi.single a 1 + Pi.single b 1

lemma suppF_pairVec {t : ℕ} {a b : Fin (3 * t)} (hab : a ≠ b) :
    suppF (pairVec a b) = {a, b} := by
  ext i
  rw [mem_suppF]
  simp only [Finset.mem_insert, Finset.mem_singleton, pairVec, Pi.add_apply, Pi.single_apply]
  by_cases ha : i = a
  · subst ha; simp [hab]
  · by_cases hb : i = b
    · subst hb; simp [hab.symm]
    · simp [ha, hb]

lemma eq_pairVec_of_suppF_eq_pair {t : ℕ} {x : Fin (3 * t) → F2} {a b : Fin (3 * t)}
    (hab : a ≠ b) (h : suppF x = {a, b}) : x = pairVec a b := by
  ext i
  by_cases hi : i ∈ suppF x
  · have hx1 := z2_eq_one_of_ne_zero (mem_suppF.mp hi)
    rw [h, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp [pairVec, hx1, hab]
    · simp [pairVec, hx1, hab.symm]
  · have hx0 : x i = 0 := by by_contra hne; exact hi (mem_suppF.mpr hne)
    rw [h, Finset.mem_insert, Finset.mem_singleton] at hi
    push Not at hi
    simp [pairVec, hx0, hi.1, hi.2]

lemma pair_classes_structure {t : ℕ} (ht : 0 < t)
    {E : Submodule F2 (Fin (3 * t) → F2)}
    (hEcode : ∀ x ∈ E, codeP t x)
    (hEeven : ∀ x ∈ E, (suppF x).card % 2 = 0) :
    letI : Fintype E := Fintype.ofFinite E
    let pairsE := (Finset.univ : Finset E).filter (fun x => (suppF x.1).card = 2)
    ∃ Cs : Finset (Finset (Fin (3 * t))),
      (∀ K ∈ Cs, K.Nonempty ∧ K.card ≤ t ∧
        ∃ e : Fin 3, (∀ i ∈ K, i.val % 3 = e.val) ∧
          (∀ i ∈ K, ∀ j ∈ K, i ≠ j → pairVec i j ∈ E)) ∧
      (∑ K ∈ Cs, (K.card - 1)) ≤ Module.finrank F2 E ∧
      2 * pairsE.card = ∑ K ∈ Cs, K.card * (K.card - 1) := by
  letI : Fintype E := Fintype.ofFinite E
  let pairsE := (Finset.univ : Finset E).filter (fun x => (suppF x.1).card = 2)
  let rel : Fin (3 * t) → Fin (3 * t) → Prop := fun i j => i = j ∨ pairVec i j ∈ E
  have hrefl : ∀ i, rel i i := fun _ => Or.inl rfl
  have hsymm : ∀ {i j}, rel i j → rel j i := by
    rintro i j (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (by simpa [pairVec, add_comm] using h)
  have htrans : ∀ {i j k}, rel i j → rel j k → rel i k := by
    rintro i j k (rfl | h1) h2
    · exact h2
    · rcases h2 with rfl | h2
      · exact Or.inr h1
      · right
        have hadd : pairVec i k = pairVec i j + pairVec j k := by
          ext m
          simp only [pairVec, Pi.add_apply]
          have h2j : (Pi.single j (1 : F2) : Fin (3 * t) → F2) m + (Pi.single j 1 : Fin (3 * t) → F2) m = 0 := z2_add_self _
          linear_combination -h2j
        rw [hadd]
        exact E.add_mem h1 h2
  let cls : Fin (3 * t) → Finset (Fin (3 * t)) := fun i => Finset.univ.filter (rel i)
  have hmem_cls : ∀ i j, j ∈ cls i ↔ rel i j := fun i j => by simp [cls]
  have hcls_eq : ∀ {i j}, rel i j → cls i = cls j := by
    intro i j hij
    ext k
    rw [hmem_cls, hmem_cls]
    exact ⟨fun hik => htrans (hsymm hij) hik, fun hjk => htrans hij hjk⟩
  let Cs : Finset (Finset (Fin (3 * t))) := Finset.univ.image cls
  have hCs_props : ∀ K ∈ Cs, K.Nonempty ∧ K.card ≤ t ∧
      ∃ e : Fin 3, (∀ i ∈ K, i.val % 3 = e.val) ∧
        (∀ i ∈ K, ∀ j ∈ K, i ≠ j → pairVec i j ∈ E) := by
    intro K hK
    obtain ⟨i0, _, rfl⟩ := Finset.mem_image.mp hK
    have hne : (cls i0).Nonempty := ⟨i0, (hmem_cls i0 i0).mpr (hrefl i0)⟩
    have hres : ∀ j ∈ cls i0, j.val % 3 = i0.val % 3 := by
      intro j hj
      rcases (hmem_cls i0 j).mp hj with rfl | hp
      · rfl
      · by_cases hij : i0 = j
        · rw [hij]
        · have hw2 : (suppF (pairVec i0 j)).card = 2 := by
            rw [suppF_pairVec hij, Finset.card_pair hij]
          obtain ⟨a, b, hab, hmod, hset⟩ := codeP_weight2_same_res (hEcode _ hp) hw2
          rw [suppF_pairVec hij] at hset
          have ha : i0 = a ∨ i0 = b := by
            have : i0 ∈ ({a, b} : Finset (Fin (3 * t))) := hset ▸ Finset.mem_insert_self i0 {j}
            simpa using this
          have hb : j = a ∨ j = b := by
            have : j ∈ ({a, b} : Finset (Fin (3 * t))) :=
              hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
            simpa using this
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
    let e : Fin 3 := ⟨i0.val % 3, Nat.mod_lt _ (by omega)⟩
    have hle_t : (cls i0).card ≤ t := by
      have hsub : cls i0 ⊆ Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = e.val) :=
        fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hres j hj⟩
      exact (Finset.card_le_card hsub).trans_eq (card_resClass (t := t) e)
    refine ⟨hne, hle_t, e, hres, fun a ha b hb hab => ?_⟩
    rcases htrans (hsymm ((hmem_cls i0 a).mp ha)) ((hmem_cls i0 b).mp hb) with h | h
    · exact absurd h hab
    · exact h
  have hrep_ex : ∀ K ∈ Cs, ∃ r : Fin (3 * t), r ∈ K := fun K hK => (hCs_props K hK).1
  let rep : Fin (3 * t) → Fin (3 * t) := fun i =>
    Classical.choose (hrep_ex (cls i) (Finset.mem_image_of_mem cls (Finset.mem_univ i)))
  have hrep_mem : ∀ i, rep i ∈ cls i := fun i =>
    Classical.choose_spec (hrep_ex (cls i) (Finset.mem_image_of_mem cls (Finset.mem_univ i)))
  have hrep_eq : ∀ {i j}, cls i = cls j → rep i = rep j := by
    intro i j h
    dsimp only [rep]
    congr 1
    rw [h]
  have hrep_idem : ∀ i, rep (rep i) = rep i := fun i =>
    hrep_eq (hcls_eq ((hmem_cls i (rep i)).mp (hrep_mem i))).symm
  let B : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i ≠ rep i)
  have hB_card : B.card = ∑ K ∈ Cs, (K.card - 1) := by
    have hdisj : Set.PairwiseDisjoint (Cs : Set (Finset (Fin (3 * t)))) id := by
      intro K1 hK1 K2 hK2 hne
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp hK1
      obtain ⟨i2, _, rfl⟩ := Finset.mem_image.mp hK2
      exact hne ((hcls_eq ((hmem_cls i1 x).mp hx1)).trans (hcls_eq ((hmem_cls i2 x).mp hx2)).symm)
    have hBeq : B = Cs.biUnion (fun K => K.filter (fun i => i ≠ rep i)) := by
      ext i
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hi
        exact ⟨cls i, Finset.mem_image_of_mem cls (Finset.mem_univ i),
               (hmem_cls i i).mpr (hrefl i), hi⟩
      · rintro ⟨_, _, _, hi⟩; exact hi
    rw [hBeq, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun K hK => ?_
      obtain ⟨i0, _, rfl⟩ := Finset.mem_image.mp hK
      have hfil : (cls i0).filter (fun i => i ≠ rep i) = (cls i0).erase (rep i0) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hi, hne⟩
          have hceq : cls i = cls i0 := (hcls_eq ((hmem_cls i0 i).mp hi)).symm
          exact ⟨by rwa [← hrep_eq hceq], hi⟩
        · rintro ⟨hne, hi⟩
          have hceq : cls i = cls i0 := (hcls_eq ((hmem_cls i0 i).mp hi)).symm
          exact ⟨hi, by rwa [hrep_eq hceq]⟩
      rw [hfil, Finset.card_erase_of_mem (hrep_mem i0)]
    · intro K1 hK1 K2 hK2 hne
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hdisj hK1 hK2 hne)
  have hB_dim : B.card ≤ Module.finrank F2 E := by
    let vecs : B → E := fun i => ⟨pairVec i.1 (rep i.1), by
      have hi_ne : i.1 ≠ rep i.1 := (Finset.mem_filter.mp i.2).2
      rcases (hmem_cls i.1 (rep i.1)).mp (hrep_mem i.1) with h | h
      · exact absurd h hi_ne
      · exact h⟩
    have hli : LinearIndependent F2 vecs := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum j
      have heval := congrFun (congrArg Subtype.val hsum) j.1
      rw [Submodule.coe_sum, Finset.sum_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at heval
      rw [Finset.sum_eq_single j] at heval
      · have hj_ne : j.1 ≠ rep j.1 := (Finset.mem_filter.mp j.2).2
        simp only [vecs, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, pairVec,
          Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hj_ne, add_zero, mul_one] at heval
        exact heval
      · intro i _ hij
        have hji : j.1 ≠ i.1 := fun h => hij (Subtype.ext h.symm)
        have hjr : j.1 ≠ rep i.1 := by
          intro h
          have hjB : j.1 ≠ rep j.1 := (Finset.mem_filter.mp j.2).2
          apply hjB
          rw [h, hrep_idem]
        simp [vecs, pairVec, hji, hjr]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcard := hli.fintype_card_le_finrank
    rwa [Fintype.card_coe] at hcard
  have hpairs_eq : 2 * pairsE.card = ∑ K ∈ Cs, K.card * (K.card - 1) := by
    let ordPairs : Finset (Fin (3 * t) × Fin (3 * t)) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ rel p.1 p.2)
    have hord_card : ordPairs.card = ∑ K ∈ Cs, K.card * (K.card - 1) := by
      have hdisj : Set.PairwiseDisjoint (Cs : Set (Finset (Fin (3 * t)))) id := by
        intro K1 hK1 K2 hK2 hne
        apply Finset.disjoint_left.mpr
        intro x hx1 hx2
        obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp hK1
        obtain ⟨i2, _, rfl⟩ := Finset.mem_image.mp hK2
        exact hne ((hcls_eq ((hmem_cls i1 x).mp hx1)).trans (hcls_eq ((hmem_cls i2 x).mp hx2)).symm)
      have hord_eq : ordPairs = Cs.biUnion (fun K => K.offDiag) := by
        ext ⟨a, b⟩
        simp only [ordPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_offDiag]
        constructor
        · rintro ⟨hab, hrel⟩
          exact ⟨cls a, Finset.mem_image_of_mem cls (Finset.mem_univ a),
                 (hmem_cls a a).mpr (hrefl a), (hmem_cls a b).mpr hrel, hab⟩
        · rintro ⟨K, hK, ha, hb, hab⟩
          obtain ⟨i0, _, rfl⟩ := Finset.mem_image.mp hK
          exact ⟨hab, htrans (hsymm ((hmem_cls i0 a).mp ha)) ((hmem_cls i0 b).mp hb)⟩
      rw [hord_eq, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun K _ => ?_
        rw [Finset.offDiag_card]
        cases hc : K.card with
        | zero => simp
        | succ m =>
          change (m + 1) * (m + 1) - (m + 1) = (m + 1) * m
          rw [Nat.mul_succ, Nat.add_sub_cancel]
      · intro K1 hK1 K2 hK2 hne
        apply Finset.disjoint_left.mpr
        intro p hp1 hp2
        exact Finset.disjoint_left.mp (hdisj hK1 hK2 hne) (Finset.mem_offDiag.mp hp1).1
          (Finset.mem_offDiag.mp hp2).1
    rw [← hord_card]
    let f : Fin (3 * t) × Fin (3 * t) → E := fun p =>
      if h : pairVec p.1 p.2 ∈ E then ⟨pairVec p.1 p.2, h⟩ else ⟨0, zero_mem E⟩
    have hmap : ∀ p ∈ ordPairs, f p ∈ pairsE := by
      intro p hp
      obtain ⟨hne, hrel⟩ := (Finset.mem_filter.mp hp).2
      have hmem : pairVec p.1 p.2 ∈ E := by rcases hrel with h | h; exact absurd h hne; exact h
      simp only [pairsE, Finset.mem_filter, Finset.mem_univ, true_and, f, dif_pos hmem]
      rw [suppF_pairVec hne, Finset.card_pair hne]
    have hfib2 : ∀ x ∈ pairsE, (ordPairs.filter (fun p => f p = x)).card = 2 := by
      intro x hx
      have hw2 : (suppF x.1).card = 2 := (Finset.mem_filter.mp hx).2
      obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hw2
      have hxeq : x.1 = pairVec a b := eq_pairVec_of_suppF_eq_pair hab hset
      have heq_fib : ordPairs.filter (fun p => f p = x) = {(a, b), (b, a)} := by
        ext ⟨u, v⟩
        simp only [Finset.mem_filter, ordPairs, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨huv, hrel⟩, hfx⟩
          have hmem : pairVec u v ∈ E := by rcases hrel with h | h; exact absurd h huv; exact h
          simp only [f, dif_pos hmem] at hfx
          have hpeq : pairVec u v = x.1 := congrArg Subtype.val hfx
          have hsupp : ({u, v} : Finset (Fin (3 * t))) = {a, b} := by
            rw [← suppF_pairVec huv, hpeq, hset]
          have hu : u = a ∨ u = b := by
            have : u ∈ ({a, b} : Finset (Fin (3 * t))) := hsupp ▸ Finset.mem_insert_self u {v}
            simpa using this
          have hv : v = a ∨ v = b := by
            have : v ∈ ({a, b} : Finset (Fin (3 * t))) :=
              hsupp ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
            simpa using this
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact absurd rfl huv
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl huv
        · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩) <;> subst u <;> subst v
          · have hmem : pairVec a b ∈ E := hxeq ▸ x.2
            exact ⟨⟨hab, Or.inr hmem⟩, Subtype.ext (by simp [f, dif_pos hmem, hxeq])⟩
          · have hmem : pairVec b a ∈ E := by
              have : pairVec b a = x.1 := by rw [hxeq]; simp [pairVec, add_comm]
              exact this.symm ▸ x.2
            exact ⟨⟨hab.symm, Or.inr hmem⟩, Subtype.ext (by
              change (f (b,a)).val = x.val
              unfold f; rw [dif_pos hmem, hxeq]; exact add_comm _ _)⟩
      rw [heq_fib, Finset.card_pair]
      intro h; exact hab (congrArg Prod.fst h)
    have hsum := Finset.card_eq_sum_card_fiberwise hmap
    rw [hsum]
    have hconst : ∑ x ∈ pairsE, (ordPairs.filter (fun p => f p = x)).card = ∑ _x ∈ pairsE, 2 :=
      Finset.sum_congr rfl hfib2
    rw [hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  exact ⟨Cs, hCs_props, hB_card ▸ hB_dim, hpairs_eq⟩

lemma pair_count_le_of_max_size {α : Type*} (Cs : Finset α) (sz : α → ℕ) (d M : ℕ)
    (hsum : (∑ K ∈ Cs, (sz K - 1)) ≤ d) (hM : ∀ K ∈ Cs, sz K ≤ M) :
    (∑ K ∈ Cs, sz K * (sz K - 1)) ≤ M * d := by
  calc ∑ K ∈ Cs, sz K * (sz K - 1)
      ≤ ∑ K ∈ Cs, M * (sz K - 1) := Finset.sum_le_sum fun K hK => Nat.mul_le_mul_right _ (hM K hK)
    _ = M * ∑ K ∈ Cs, (sz K - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ M * d := Nat.mul_le_mul_left _ hsum

lemma evenSub_eq_of_class_size {t : ℕ} (ht : 0 < t)
    {E : Submodule F2 (Fin (3 * t) → F2)}
    (hEcode : ∀ x ∈ E, codeP t x)
    (K : Finset (Fin (3 * t))) (e : Fin 3)
    (hKne : K.Nonempty) (hKres : ∀ i ∈ K, i.val % 3 = e.val)
    (hKmem : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → pairVec i j ∈ E)
    (hdim : Module.finrank F2 E = K.card - 1) :
    ∀ x : Fin (3 * t) → F2, x ∈ E ↔ (∀ i, i ∉ K → x i = 0) ∧ (∑ i, x i) = 0 := by
  let U : Submodule F2 (Fin (3 * t) → F2) := codeSub t ⊓ suppSub K
  have hUdim : Module.finrank F2 U = K.card - 1 :=
    finrank_code_inf_suppSub_one_res K hKne e hKres
  have hU_iff : ∀ x : Fin (3 * t) → F2, x ∈ U ↔ (∀ i, i ∉ K → x i = 0) ∧ (∑ i, x i) = 0 := by
    intro x
    simp only [U, Submodule.mem_inf, mem_codeSub, suppSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxc, hxK⟩
      refine ⟨hxK, ?_⟩
      have hother : ∃ r : Fin 3, r ≠ e := by
        fin_cases e
        · exact ⟨1, fin3_one_ne_zero⟩
        · exact ⟨0, fin3_zero_ne_one⟩
        · exact ⟨0, fin3_zero_ne_two⟩
      obtain ⟨r, hre⟩ := hother
      rw [← codeP_resSum_eq_total hxc r]
      unfold resSum
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hiK : i ∈ K
      · have : i.val % 3 ≠ r.val := by rw [hKres i hiK]; intro h; exact hre (Fin.ext h.symm)
        simp [this]
      · simp [hxK i hiK]
    · rintro ⟨hxK, hsum0⟩
      refine ⟨?_, hxK⟩
      rw [codeP_iff_resSum]
      have hzero : ∀ r : Fin 3, resSum t r.val x = 0 := by
        intro r
        unfold resSum
        by_cases hre : r = e
        · subst hre
          have : (∑ i : Fin (3 * t), if i.val % 3 = r.val then x i else 0) = ∑ i, x i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hiK : i ∈ K
            · rw [if_pos (hKres i hiK)]
            · simp [hxK i hiK]
          rw [this, hsum0]
        · refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hiK : i ∈ K
          · have : i.val % 3 ≠ r.val := by rw [hKres i hiK]; intro h; exact hre (Fin.ext h.symm)
            simp [this]
          · simp [hxK i hiK]
      exact ⟨(hzero 0).trans (hzero 2).symm, (hzero 1).trans (hzero 2).symm⟩
  have hUleE : U ≤ E := by
    intro x hx
    obtain ⟨hxK, hsum0⟩ := (hU_iff x).mp hx
    obtain ⟨r0, hr0⟩ := hKne
    have hdecomp : x = ∑ i ∈ K.erase r0, x i • pairVec i r0 := by
      ext j
      rw [Finset.sum_apply]
      by_cases hjK : j ∈ K
      · by_cases hjr : j = r0
        · subst hjr
          have hsumK : ∑ i ∈ K, x i = 0 := by
            rw [← hsum0]
            refine Finset.sum_subset (Finset.subset_univ K) fun i _ hi => hxK i hi
          rw [← Finset.add_sum_erase _ _ hr0] at hsumK
          have hx0 : x j = ∑ i ∈ K.erase j, x i := by
            linear_combination hsumK - z2_add_self (∑ i ∈ K.erase j, x i)
          rw [hx0]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : j ≠ i := (Finset.ne_of_mem_erase hi).symm
          simp [pairVec, hne]
        · rw [Finset.sum_eq_single j]
          · simp [pairVec, hjr]
          · intro i hi hij
            have hne : j ≠ i := hij.symm
            simp [pairVec, hne, hjr]
          · intro h; exact absurd (Finset.mem_erase.mpr ⟨hjr, hjK⟩) h
      · rw [hxK j hjK]
        symm
        refine Finset.sum_eq_zero fun i hi => ?_
        have h1 : j ≠ i := fun h => hjK (h ▸ Finset.mem_of_mem_erase hi)
        have h2 : j ≠ r0 := fun h => hjK (h ▸ hr0)
        simp [pairVec, h1, h2]
    rw [hdecomp]
    exact Submodule.sum_mem E fun i hi =>
      E.smul_mem _ (hKmem i (Finset.mem_of_mem_erase hi) r0 hr0 (Finset.ne_of_mem_erase hi))
  have hUE : U = E := Submodule.eq_of_le_of_finrank_eq hUleE (by omega)
  intro x
  rw [← hUE]
  exact hU_iff x

lemma suppF_tripVec {t : ℕ} (ht : 0 < t) (s : Fin (3 * t)) :
    suppF (tripVec ht s) = {s, nxt ht s, nxt ht (nxt ht s)} := by
  ext i
  rw [mem_suppF]
  simp only [tripVec, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp_all

lemma isTriple_iff_exists_tripVec {t : ℕ} (ht : 0 < t) (x : Fin (3 * t) → F2) :
    isTriple ht x ↔ ∃ s : Fin (3 * t), x = tripVec ht s := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    ext i
    by_cases hi : i ∈ suppF x
    · have h1 := z2_eq_one_of_ne_zero (mem_suppF.mp hi)
      rw [hs] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp [tripVec, hi, h1]
    · have h0 : x i = 0 := by by_contra hne; exact hi (mem_suppF.mpr hne)
      rw [hs] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp [tripVec, hi, h0]
  · rintro ⟨s, rfl⟩
    exact ⟨s, suppF_tripVec ht s⟩

lemma tripVec_kernel_char {t : ℕ} (ht : 0 < t) (c : Fin (3 * t) → F2)
    (hsum : ∑ s : Fin (3 * t), c s • tripVec ht s = 0) :
    c = 0 ∨ ∃ r : Fin 3, ∀ i : Fin (3 * t), c i = if i.val % 3 = r.val then 0 else 1 := by
  have heq : ∀ i : Fin (3 * t), c i + c (prv i) + c (prv (prv i)) = 0 := by
    intro i
    have hi := congrFun hsum i
    rw [Finset.sum_apply, Pi.zero_apply] at hi
    have hrew : ∀ s : Fin (3 * t), (c s • tripVec ht s) i =
        (if s = i then c i else 0) + (if s = prv i then c (prv i) else 0) +
        (if s = prv (prv i) then c (prv (prv i)) else 0) := by
      intro s
      have h1 : i = s ↔ s = i := eq_comm
      have h2 : i = nxt ht s ↔ s = prv i :=
        ⟨fun h => by rw [h, prv_nxt ht], fun h => by rw [h, nxt_prv ht]⟩
      have h3 : i = nxt ht (nxt ht s) ↔ s = prv (prv i) :=
        ⟨fun h => by rw [h, prv_nxt ht, prv_nxt ht], fun h => by rw [h, nxt_prv ht, nxt_prv ht]⟩
      have hne01 : i ≠ prv i := by
        intro h; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
        rw [prv_mod3] at this; omega
      have hne02 : i ≠ prv (prv i) := by
        intro h; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
        have hm1 := prv_mod3 (prv i); have hm2 := prv_mod3 i; omega
      have hne12 : prv i ≠ prv (prv i) := fun h => hne01 (prv_inj ht h)
      simp only [Pi.smul_apply, smul_eq_mul, tripVec, h1, h2, h3]
      by_cases hs0 : s = i
      · subst hs0; simp [hne01, hne02]
      · by_cases hs1 : s = prv i
        · subst hs1; simp [hs0, hne12]
        · by_cases hs2 : s = prv (prv i)
          · subst hs2; simp [hs0, hs1]
          · simp [hs0, hs1, hs2]
    simp only [hrew, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi
    exact hi
  have hper : ∀ i : Fin (3 * t), c (nxt ht i) = c (prv (prv i)) := by
    intro i
    have h1 := heq i
    have h2 := heq (nxt ht i)
    rw [prv_nxt ht] at h2
    linear_combination h2 - h1
  have hmod3 : ∀ i : Fin (3 * t), c i = c ⟨i.val % 3, by omega⟩ := by
    intro i
    have hstep3 : ∀ k : ℕ, (hk : k + 3 < 3 * t) →
        c ⟨k + 3, hk⟩ = c ⟨k, by omega⟩ := by
      intro k hk
      have h := hper (⟨k + 2, by omega⟩ : Fin (3 * t))
      have h1 : nxt ht ⟨k + 2, by omega⟩ = ⟨k + 3, hk⟩ := by
        apply Fin.ext; exact Nat.mod_eq_of_lt hk
      have h2 : prv (prv (⟨k + 2, by omega⟩ : Fin (3 * t))) = ⟨k, by omega⟩ := by
        apply Fin.ext; simp [prv]
      rwa [h1, h2] at h
    have hind : ∀ q r : ℕ, (hqr : 3 * q + r < 3 * t) → r < 3 →
        c ⟨3 * q + r, hqr⟩ = c ⟨r, by omega⟩ := by
      intro q
      induction q with
      | zero => intro r _ _; simp
      | succ q ih =>
        intro r hqr hr
        have h1 := hstep3 (3 * q + r) (by omega)
        have heq1 : (⟨3 * (q + 1) + r, hqr⟩ : Fin (3 * t)) = ⟨3 * q + r + 3, by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [heq1, h1]
        exact ih r (by omega) hr
    have := hind (i.val / 3) (i.val % 3) (by have := i.isLt; omega) (Nat.mod_lt _ (by omega))
    have heqi : (⟨3 * (i.val / 3) + i.val % 3, by have := i.isLt; omega⟩ : Fin (3 * t)) = i :=
      Fin.ext (by dsimp only; omega)
    rwa [heqi] at this
  have hc012 : c ⟨0, by omega⟩ + c ⟨1, by omega⟩ + c ⟨2, by omega⟩ = 0 := by
    have h := heq ⟨2, by omega⟩
    have h1 : prv (⟨2, by omega⟩ : Fin (3 * t)) = ⟨1, by omega⟩ := rfl
    have h2 : prv (⟨1, by omega⟩ : Fin (3 * t)) = ⟨0, by omega⟩ := rfl
    rw [h1, h2] at h
    linear_combination h
  rcases z2_cases (c ⟨0, by omega⟩) with h0 | h0 <;>
    rcases z2_cases (c ⟨1, by omega⟩) with h1 | h1 <;>
    rcases z2_cases (c ⟨2, by omega⟩) with h2 | h2
  · left
    ext i
    rw [hmod3 i]
    have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases hm with hm | hm | hm
    · simpa [hm] using h0
    · simpa [hm] using h1
    · simpa [hm] using h2
  · rw [h0, h1, h2] at hc012; simp only [zero_add, add_zero, z2_one_add_one] at hc012; exact (z2_one_ne_zero hc012).elim
  · rw [h0, h1, h2] at hc012; simp only [zero_add, add_zero, z2_one_add_one] at hc012; exact (z2_one_ne_zero hc012).elim
  · right; refine ⟨0, fun i => ?_⟩
    rw [hmod3 i]
    have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases hm with hm | hm | hm <;> simp [hm, h0, h1, h2]
  · rw [h0, h1, h2] at hc012; simp only [zero_add, add_zero, z2_one_add_one] at hc012; exact (z2_one_ne_zero hc012).elim
  · right; refine ⟨1, fun i => ?_⟩
    rw [hmod3 i]
    have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases hm with hm | hm | hm <;> simp [hm, h0, h1, h2]
  · right; refine ⟨2, fun i => ?_⟩
    rw [hmod3 i]
    have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases hm with hm | hm | hm <;> simp [hm, h0, h1, h2]
  · rw [h0, h1, h2] at hc012; simp only [zero_add, add_zero, z2_one_add_one] at hc012; exact (z2_one_ne_zero hc012).elim

lemma tripVec_linearIndependent_of_card_lt {t : ℕ} (ht : 0 < t)
    (S : Finset (Fin (3 * t))) (hlt : S.card < 2 * t) :
    LinearIndependent F2 (fun s : S => tripVec ht s.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  let cExt : Fin (3 * t) → F2 := fun s => if h : s ∈ S then c ⟨s, h⟩ else 0
  have hsumExt : ∑ s : Fin (3 * t), cExt s • tripVec ht s = 0 := by
    rw [← hsum]
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun s _ hs => by simp [cExt, hs])]
    refine Finset.sum_bij (fun s hs => (⟨s, hs⟩ : S)) (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h) (fun s _ => ⟨s.1, s.2, rfl⟩)
      (fun s hs => by simp [cExt, hs])
  rcases tripVec_kernel_char ht cExt hsumExt with h0 | ⟨r, hr⟩
  · intro s
    have := congrFun h0 s.1
    simpa [cExt, s.2] using this
  · exfalso
    have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 ≠ r.val) ⊆ S := by
      intro i hi
      by_contra hni
      have := hr i
      simp [cExt, hni, (Finset.mem_filter.mp hi).2] at this
    have hle := Finset.card_le_card hsub
    rw [card_compl_resClass r] at hle
    omega

lemma tripVec_add_wt2_iff {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) (s1 s2 : Fin (3 * t)) :
    (suppF (tripVec ht s1 + tripVec ht s2)).card = 2 ↔ s2 = nxt ht s1 ∨ s1 = nxt ht s2 := by
  have hsymm_diff : suppF (tripVec ht s1 + tripVec ht s2) =
      symmDiff (suppF (tripVec ht s1)) (suppF (tripVec ht s2)) := by
    ext i
    simp only [mem_suppF, Pi.add_apply, Finset.mem_symmDiff, Finset.mem_sdiff]
    rcases z2_cases (tripVec ht s1 i) with h1 | h1 <;>
      rcases z2_cases (tripVec ht s2 i) with h2 | h2 <;>
      simp [h1, h2, z2_add_self]
  have hcard3 : ∀ s : Fin (3 * t), (suppF (tripVec ht s)).card = 3 := fun s => by
    rw [suppF_tripVec ht s]
    have h01 : s ≠ nxt ht s := fun h => by
      have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; rw [nxt_mod3 ht] at this; omega
    have h02 : s ≠ nxt ht (nxt ht s) := fun h => by
      have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
      have hm1 := nxt_mod3 ht (nxt ht s); have hm2 := nxt_mod3 ht s; omega
    have h12 : nxt ht s ≠ nxt ht (nxt ht s) := fun h => h01 (nxt_inj ht h)
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h12]
    · simp [h01, h02]
  have hcard_sd : (suppF (tripVec ht s1 + tripVec ht s2)).card +
      2 * (suppF (tripVec ht s1) ∩ suppF (tripVec ht s2)).card = 6 := by
    rw [hsymm_diff]
    have h1 := Finset.card_sdiff_add_card_inter (suppF (tripVec ht s1)) (suppF (tripVec ht s2))
    have h2 := Finset.card_sdiff_add_card_inter (suppF (tripVec ht s2)) (suppF (tripVec ht s1))
    rw [Finset.inter_comm] at h2
    have hdisj : Disjoint (suppF (tripVec ht s1) \ suppF (tripVec ht s2))
        (suppF (tripVec ht s2) \ suppF (tripVec ht s1)) :=
      Finset.disjoint_left.mpr fun x hx hy => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
    have hsd : (symmDiff (suppF (tripVec ht s1)) (suppF (tripVec ht s2))).card =
        (suppF (tripVec ht s1) \ suppF (tripVec ht s2)).card +
        (suppF (tripVec ht s2) \ suppF (tripVec ht s1)).card := by
      rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
    rw [hcard3 s1] at h1
    rw [hcard3 s2] at h2
    omega
  constructor
  · intro hw2
    have hint2 : (suppF (tripVec ht s1) ∩ suppF (tripVec ht s2)).card = 2 := by omega
    have hne : s1 ≠ s2 := by
      intro h; subst h; rw [Finset.inter_self, hcard3] at hint2; omega
    have h1 : ∀ a b : Fin (3 * t), (nxt ht a).val = (a.val + 1) % (3 * t) := fun a _ => rfl
    have h2 : ∀ a : Fin (3 * t), (nxt ht (nxt ht a)).val = (a.val + 2) % (3 * t) := fun a => by
      change ((a.val + 1) % (3 * t) + 1) % (3 * t) = _
      rw [Nat.mod_add_mod]
    by_contra hnot
    push Not at hnot
    have hdist_vals : (s1.val + 1) % (3 * t) ≠ s2.val ∧ (s2.val + 1) % (3 * t) ≠ s1.val ∧ s1.val ≠ s2.val :=
      ⟨fun h => hnot.1 (Fin.ext h.symm), fun h => hnot.2 (Fin.ext h.symm), fun h => hne (Fin.ext h)⟩
    have hsub1 : (suppF (tripVec ht s1) ∩ suppF (tripVec ht s2)).card ≤ 1 := by
      rw [suppF_tripVec ht s1, suppF_tripVec ht s2]
      have hcard_le : ∀ x y : Fin (3 * t), x ∈ ({s1, nxt ht s1, nxt ht (nxt ht s1)} : Finset _) ∩
          {s2, nxt ht s2, nxt ht (nxt ht s2)} →
          y ∈ ({s1, nxt ht s1, nxt ht (nxt ht s1)} : Finset _) ∩
          {s2, nxt ht s2, nxt ht (nxt ht s2)} → x = y := by
        intro x y hx hy
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
        have hs1lt := s1.isLt; have hs2lt := s2.isLt
        have hx1 : x.val = s1.val ∨ x.val = (s1.val + 1) % (3 * t) ∨ x.val = (s1.val + 2) % (3 * t) := by
          rcases hx.1 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (h2 s1))
        have hx2 : x.val = s2.val ∨ x.val = (s2.val + 1) % (3 * t) ∨ x.val = (s2.val + 2) % (3 * t) := by
          rcases hx.2 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (h2 s2))
        have hy1 : y.val = s1.val ∨ y.val = (s1.val + 1) % (3 * t) ∨ y.val = (s1.val + 2) % (3 * t) := by
          rcases hy.1 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (h2 s1))
        have hy2 : y.val = s2.val ∨ y.val = (s2.val + 1) % (3 * t) ∨ y.val = (s2.val + 2) % (3 * t) := by
          rcases hy.2 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (h2 s2))
        have translate (a : Fin (3 * t)) (k : ℕ) (hk : k ≤ 3) :
            (a.val + k) % (3 * t) = if a.val + k < 3 * t then a.val + k else a.val + k - 3 * t := by
          have ha := a.isLt
          split_ifs with h
          · exact Nat.mod_eq_of_lt h
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        simp only [translate _ 1 (by omega), translate _ 2 (by omega)] at hx1 hx2 hy1 hy2 hdist_vals
        apply Fin.ext
        split_ifs at * <;> omega
      exact Finset.card_le_one.mpr fun x hx y hy => hcard_le x y hx hy
    omega
  · have adj (s : Fin (3 * t)) :
        (suppF (tripVec ht s) ∩ suppF (tripVec ht (nxt ht s))).card = 2 := by
      have distinct : s ≠ nxt ht s ∧ s ≠ nxt ht (nxt ht s) ∧
          s ≠ nxt ht (nxt ht (nxt ht s)) ∧ nxt ht s ≠ nxt ht (nxt ht s) := by
        have h1 := nxt_val ht s
        have h2 := nxt_val ht (nxt ht s)
        have h3 := nxt_val ht (nxt ht (nxt ht s))
        have hs := s.isLt
        constructor
        · intro h; have := congrArg Fin.val h; split_ifs at h1 <;> omega
        constructor
        · intro h; have := congrArg Fin.val h; split_ifs at h1 h2 <;> omega
        constructor
        · intro h; have := congrArg Fin.val h; split_ifs at h1 h2 h3 <;> omega
        · intro h; have := congrArg Fin.val (nxt_inj ht h); split_ifs at h1 <;> omega
      have inter_eq : suppF (tripVec ht s) ∩ suppF (tripVec ht (nxt ht s)) =
          {nxt ht s, nxt ht (nxt ht s)} := by
        ext i
        simp only [suppF_tripVec, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        grind
      rw [inter_eq, Finset.card_pair distinct.2.2.2]
    rintro (h | h)
    · subst s2; rw [adj] at hcard_sd; omega
    · subst s1; rw [Finset.inter_comm, adj] at hcard_sd; omega

lemma threeTrip_inj (a b c : Fin 9) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    Function.Injective (threeTrip a b c) := by
  let v : Fin 3 → Fin 9 := ![a,b,c]
  have hi : Function.Injective v := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [v, eq_comm]
  let S := Finset.univ.image v
  have hc : S.card = 3 := by rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  let inc : Fin 3 → S := fun i => ⟨v i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hli := (tripVec_linearIndependent_of_card_lt (by decide : 0 < 3) S (by omega)).comp inc
    (fun _ _ he => hi (congrArg Subtype.val he))
  intro x y he
  apply hli.fintypeLinearCombination_injective
  change (∑ j, x j • tripVec (by decide : 0 < 3) (v j)) = ∑ j, y j • tripVec (by decide : 0 < 3) (v j)
  have ha : v 0 = a := rfl
  have hb : v 1 = b := rfl
  have hc' : v 2 = c := rfl
  simp only [Fin.sum_univ_three, ha, hb, hc']
  exact he

lemma short_triples_card {t : ℕ} (ht : 0 < t) {P : Submodule F2 (Fin (3 * t) → F2)}
    (T : Finset P) (hsize : T.card < 2 * t) (hT : ∀ x ∈ T, isTriple ht x.val) :
    T.card ≤ Module.finrank F2 P := by
  choose start hstart using fun x : T => (isTriple_iff_exists_tripVec ht x.val.val).mp (hT x.val x.property)
  have hinj : Function.Injective start := by
    intro x y h
    exact Subtype.ext (Subtype.ext ((hstart x).trans ((congrArg (tripVec ht) h).trans (hstart y).symm)))
  let S := Finset.univ.image start
  have hcard : S.card = T.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  let inc : T → S := fun x => ⟨start x, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hi : Function.Injective inc := fun x y h => hinj (congrArg (fun z : S => z.val) h)
  have hli := (tripVec_linearIndependent_of_card_lt ht S (hcard ▸ hsize)).comp inc hi
  have hliP : LinearIndependent F2 (fun x : T => x.val) := by
    apply LinearIndependent.of_comp P.subtype
    convert hli using 1
    exact funext hstart
  simpa only [Fintype.card_coe] using hliP.fintype_card_le_finrank

lemma dim3_not_top {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hdimP : Module.finrank F2 P = 3)
    (hnt : ¬ formP ht P Q) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      (if t = 3 then 344 else 352) * (Nat.card P * Nat.card Q) := by
  letI : Fintype P := Fintype.ofFinite P
  have hPsub : P ≤ codeSub t := fun x hx => mem_codeSub.mpr (hP x hx)
  have hQsub : Q ≤ codeSub t := fun y hy => mem_codeSub.mpr (hQ y hy)
  have hdimQ : Module.finrank F2 Q = 3 * t - 2 := by
    have hle := Submodule.finrank_mono hQsub
    rw [finrank_codeSub ht] at hle
    omega
  have hQeq : Q = codeSub t :=
    Submodule.eq_of_le_of_finrank_eq hQsub (by rw [hdimQ, finrank_codeSub ht])
  have hQiff : ∀ y, y ∈ Q ↔ codeP t y := fun y => by rw [hQeq, mem_codeSub]
  have hbase := small_side_row_sum_bound ht hQsub hdim (by omega) (by omega)
  rw [hdimP] at hbase
  have hcardP : Nat.card P = 8 := by rw [card_eq_two_pow_finrank, hdimP]; norm_num
  let p0 : P := ⟨0, zero_mem P⟩
  refine hbase.trans (Nat.mul_le_mul_right _ ?_)
  change _ + ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤ _
  rcases evenSub_dichotomy P with hAllEven | ⟨hE2, u0, hu0_odd⟩
  · have hP_even : ∀ x ∈ P, (suppF x).card % 2 = 0 := by
      intro x hx
      have : x ∈ evenSub P := hAllEven.symm ▸ hx
      exact (sum_eq_zero_iff_even x).mp this.2
    obtain ⟨Cs, hCs, hsum_dim, hpairs_eq⟩ := pair_classes_structure ht hP hP_even
    let pairsP := (Finset.univ : Finset P).filter (fun x => (suppF x.1).card = 2)
    change 2 * pairsP.card = _ at hpairs_eq
    have hpairs_le4 : pairsP.card ≤ 4 := by
      by_cases hge4 : ∃ K ∈ Cs, 4 ≤ K.card
      · exfalso
        obtain ⟨K, hK, hK4⟩ := hge4
        obtain ⟨hKne, hKt, e, hKres, hKmem⟩ := hCs K hK
        have hK_le : K.card - 1 ≤ 3 := by
          have := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
          omega
        have hKeq4 : K.card = 4 := by omega
        have ht4 : 4 ≤ t := by omega
        have hP_iff := evenSub_eq_of_class_size ht hP K e hKne hKres hKmem (by omega)
        exact hnt ⟨hQiff, Or.inr (Or.inr ⟨ht4, K, e, hKeq4, hKres, hP_iff⟩)⟩
      · push Not at hge4
        have hle3 : ∀ K ∈ Cs, K.card ≤ 3 := fun K hK => by have := hge4 K hK; omega
        have hbd := pair_count_le_of_max_size Cs Finset.card 3 3 (by omega) hle3
        omega
    have hsum_le : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤
        16 * pairsP.card + 4 * (7 - pairsP.card) := by
      have hterm : ∀ x ∈ (Finset.univ : Finset P).erase p0,
          wt8 (rkC (nbrF x.val)) ≤ 4 + if (suppF x.val).card = 2 then 12 else 0 := by
        intro x hx
        have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase hx (Subtype.ext h)
        have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
        have hev := hP_even x.val x.2
        by_cases hw2 : (suppF x.val).card = 2
        · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
        · rw [if_neg hw2, add_zero]
          exact wt8_le_4 (rkC_even_ge6 ht ht3 (hP x.val x.2) hev (by omega))
      calc ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ (Finset.univ : Finset P).erase p0, (4 + if (suppF x.val).card = 2 then 12 else 0) :=
            Finset.sum_le_sum hterm
        _ = 4 * 7 + 12 * pairsP.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
                Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ,
                ← Nat.card_eq_fintype_card, hcardP]
            have hp0_not : p0 ∉ pairsP := by simp [pairsP, p0, suppF]
            have hfeq : ((Finset.univ : Finset P).erase p0).filter (fun x => (suppF x.val).card = 2) =
                pairsP := by
              ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, pairsP, true_and]
              exact ⟨fun h => h.2, fun h => ⟨fun h0 => hp0_not (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), h⟩⟩
            rw [← Finset.sum_filter, hfeq, Finset.sum_const, smul_eq_mul]
            ring
        _ = 16 * pairsP.card + 4 * (7 - pairsP.card) := by omega
    split_ifs <;> omega
  · let E := evenSub P
    letI : Fintype E := Fintype.ofFinite E
    have hEdim : Module.finrank F2 E = 2 := by dsimp only [E]; omega
    have hEcard : Nat.card E = 4 := by rw [card_eq_two_pow_finrank, hEdim]; norm_num
    have hEcode : ∀ x ∈ E, codeP t x := fun x hx => hP x hx.1
    have hEeven : ∀ x ∈ E, (suppF x).card % 2 = 0 := fun x hx => (sum_eq_zero_iff_even x).mp hx.2
    obtain ⟨Cs, hCs, hsum_dim, hpairs_eq⟩ := pair_classes_structure ht hEcode hEeven
    let pairsE := (Finset.univ : Finset E).filter (fun x => (suppF x.1).card = 2)
    change 2 * pairsE.card = _ at hpairs_eq
    let evenSet : Finset P := (Finset.univ.erase p0).filter (fun x => (suppF x.val).card % 2 = 0)
    let oddSet : Finset P := (Finset.univ.erase p0).filter (fun x => (suppF x.val).card % 2 = 1)
    have hsplit : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) =
        (∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))) + ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val)) := by
      have hodd_eq : oddSet = (Finset.univ.erase p0).filter (fun x => ¬ (suppF x.val).card % 2 = 0) := by
        ext x; simp only [oddSet, Finset.mem_filter]; exact and_congr_right fun _ => by omega
      rw [hodd_eq, Finset.sum_filter_add_sum_filter_not]
    have heven_card : evenSet.card = 3 := by
      let eE : {x : E // x.1 ≠ 0} ≃ evenSet :=
        { toFun := fun x => ⟨⟨x.1.1, x.1.2.1⟩, Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨fun h => x.2 (congrArg Subtype.val h), Finset.mem_univ _⟩,
             hEeven x.1.1 x.1.2⟩⟩
          invFun := fun x => ⟨⟨x.1.1, x.1.2, (sum_eq_zero_iff_even x.1.1).mpr (Finset.mem_filter.mp x.2).2⟩,
            fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp x.2).1 (Subtype.ext h)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hcard_nz : Nat.card {x : E // x.1 ≠ 0} = 3 := by
        have : Nat.card {x : E // x.1 ≠ 0} = ((Finset.univ : Finset E).erase ⟨0, zero_mem E⟩).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          congr 1; ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
          exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            ← Nat.card_eq_fintype_card, hEcard]
      have := Nat.card_congr eE
      rw [hcard_nz, Nat.card_eq_fintype_card, Fintype.card_coe] at this
      exact this.symm
    have hodd_card : oddSet.card = 4 := by
      have htot : evenSet.card + oddSet.card = 7 := by
        have hodd_eq : oddSet = (Finset.univ.erase p0).filter (fun x => ¬ (suppF x.val).card % 2 = 0) := by
          ext x; simp only [oddSet, Finset.mem_filter]; exact and_congr_right fun _ => by omega
        rw [hodd_eq, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem (Finset.mem_univ p0),
            Finset.card_univ, ← Nat.card_eq_fintype_card, hcardP]
      omega
    have heven_sum : ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 12 + 12 * pairsE.card := by
      have hterm : ∀ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 4 + if (suppF x.val).card = 2 then 12 else 0 := by
        intro x hx
        have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hx).1 (Subtype.ext h)
        have hev := (Finset.mem_filter.mp hx).2
        have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
        by_cases hw2 : (suppF x.val).card = 2
        · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
        · rw [if_neg hw2, add_zero]
          exact wt8_le_4 (rkC_even_ge6 ht ht3 (hP x.val x.2) hev (by omega))
      have hpair_card_eq : (evenSet.filter (fun x => (suppF x.val).card = 2)).card = pairsE.card := by
        refine Finset.card_bij (fun x hx => ⟨x.1, x.2, (sum_eq_zero_iff_even x.1).mpr
            (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2⟩)
          (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
          (fun a _ b _ h => Subtype.ext (congrArg (fun y : E => y.val) h))
          (fun y hy => ⟨⟨y.1, y.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨fun h => by
              have h0 : y.1 = 0 := congrArg Subtype.val h
              have := (Finset.mem_filter.mp hy).2
              rw [h0] at this; simp [suppF] at this, Finset.mem_univ _⟩,
             hEeven y.1 y.2⟩, (Finset.mem_filter.mp hy).2⟩, rfl⟩)
      calc ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ evenSet, (4 + if (suppF x.val).card = 2 then 12 else 0) := Finset.sum_le_sum hterm
        _ = 4 * evenSet.card + 12 * (evenSet.filter (fun x => (suppF x.val).card = 2)).card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
                Finset.sum_const, smul_eq_mul]; ring
        _ = 12 + 12 * pairsE.card := by rw [heven_card, hpair_card_eq]
    let trips : Finset P := oddSet.filter (fun x => isTriple ht x.val)
    have htrips_le3 : trips.card ≤ 3 := by
      by_contra h
      obtain ⟨T, hT, h4⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ trips.card)
      have hdimT := short_triples_card ht T (by omega) (fun x hx => (Finset.mem_filter.mp (hT hx)).2)
      omega
    have hodd_sum_gen : ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val)) ≤ 32 + 8 * trips.card := by
      have hterm : ∀ x ∈ oddSet, wt8 (rkC (nbrF x.val)) ≤ 8 + if isTriple ht x.val then 8 else 0 := by
        intro x hx
        have hodd := (Finset.mem_filter.mp hx).2
        have hge4 := rkC_odd_ge4 ht ht3 (hP x.val x.2) hodd
        by_cases htr : isTriple ht x.val
        · rw [if_pos htr, (rkC_odd_eq4_iff_isTriple ht ht3 (hP x.val x.2) hodd).mpr htr, wt8_eq_16 rfl]
        · rw [if_neg htr, add_zero]
          have hne4 : rkC (nbrF x.val) ≠ 4 := fun h =>
            htr ((rkC_odd_eq4_iff_isTriple ht ht3 (hP x.val x.2) hodd).mp h)
          exact wt8_le_8 (by omega)
      calc ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ oddSet, (8 + if isTriple ht x.val then 8 else 0) := Finset.sum_le_sum hterm
        _ = 8 * oddSet.card + 8 * trips.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
                Finset.sum_const, smul_eq_mul]; ring
        _ = 32 + 8 * trips.card := by rw [hodd_card]
    have hpairs_le3 : pairsE.card ≤ 3 := by
      have hle3 : ∀ K ∈ Cs, K.card ≤ 3 := fun K hK => by
        have := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
        omega
      have hbd := pair_count_le_of_max_size Cs Finset.card 2 3 (by omega) hle3
      omega
    rw [hsplit]
    by_cases hp1 : pairsE.card ≤ 1
    · split_ifs <;> omega
    · by_cases hp2 : pairsE.card = 2
      · by_cases ht3eq : t = 3
        · rw [if_pos ht3eq]
          by_cases htr2 : trips.card ≤ 2
          · omega
          · have htr3 : trips.card = 3 := by omega
            obtain ⟨t1, t2, t3, h12, h13, h23, htr_eq⟩ := Finset.card_eq_three.mp htr3
            have ht1_m : t1 ∈ trips := htr_eq ▸ Finset.mem_insert_self _ _
            have ht2_m : t2 ∈ trips := htr_eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            have ht3_m : t3 ∈ trips := htr_eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            obtain ⟨s1, hs1⟩ := (isTriple_iff_exists_tripVec ht t1.1).mp (Finset.mem_filter.mp ht1_m).2
            obtain ⟨s2, hs2⟩ := (isTriple_iff_exists_tripVec ht t2.1).mp (Finset.mem_filter.mp ht2_m).2
            obtain ⟨s3, hs3⟩ := (isTriple_iff_exists_tripVec ht t3.1).mp (Finset.mem_filter.mp ht3_m).2
            subst t
            have hd : s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 :=
              ⟨fun h => h12 (Subtype.ext (hs1.trans ((congrArg _ h).trans hs2.symm))),
               fun h => h13 (Subtype.ext (hs1.trans ((congrArg _ h).trans hs3.symm))),
               fun h => h23 (Subtype.ext (hs2.trans ((congrArg _ h).trans hs3.symm)))⟩
            let g : (Fin 3 → F2) → P := fun f => ⟨threeTrip s1 s2 s3 f,
              P.add_mem (P.add_mem (P.smul_mem _ (hs1 ▸ t1.2)) (P.smul_mem _ (hs2 ▸ t2.2)))
                (P.smul_mem _ (hs3 ▸ t3.2))⟩
            have hg : Function.Injective g := fun a b h => threeTrip_inj s1 s2 s3 hd (congrArg Subtype.val h)
            have hbij : Function.Bijective g :=
              (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by
                rw [← (Nat.card_eq_fintype_card (α := P)), hcardP]; decide⟩
            let e := Equiv.ofBijective g hbij
            have he0 : e 0 = p0 := by apply Subtype.ext; simp [e, g, threeTrip, p0]
            have hsum : (∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val))) =
                ∑ f ∈ (Finset.univ : Finset (Fin 3 → F2)).erase 0, wt8 (rkC (nbrF (t := 3) (threeTrip s1 s2 s3 f))) := by
              symm
              apply Finset.sum_nbij' e e.symm
              · intro f hf
                exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hf).1 (e.injective (h.trans he0.symm)), Finset.mem_univ _⟩
              · intro x hx
                exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hx).1 (by rw [← e.apply_symm_apply x, h, he0]), Finset.mem_univ _⟩
              · intro f _; exact e.symm_apply_apply f
              · intro x _; exact e.apply_symm_apply x
              · intro f _; rfl
            rw [← hsplit, hsum]
            have hbound := threeTrip_bound s1 s2 s3 hd
            omega
        · rw [if_neg ht3eq]; omega
      · have hp3 : pairsE.card = 3 := by omega
        have hK3_ex : ∃ K ∈ Cs, K.card = 3 := by
          by_contra hno
          push Not at hno
          have hle2 : ∀ K ∈ Cs, K.card ≤ 2 := fun K hK => by
            have h1 := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
            have h2 := hno K hK
            omega
          have hbd := pair_count_le_of_max_size Cs Finset.card 2 2 (by omega) hle2
          omega
        obtain ⟨K, hK, hK3⟩ := hK3_ex
        obtain ⟨hKne, _, e, hKres, hKmem⟩ := hCs K hK
        have hE_iff := evenSub_eq_of_class_size ht hEcode K e hKne hKres hKmem (by omega)
        have htrips_le2 : trips.card ≤ 2 := by
          by_contra hge3
          have htr3 : trips.card = 3 := by omega
          obtain ⟨t1, t2, t3, h12, h13, h23, htr_eq⟩ := Finset.card_eq_three.mp htr3
          have ht1_m : t1 ∈ trips := htr_eq ▸ Finset.mem_insert_self _ _
          have ht2_m : t2 ∈ trips := htr_eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          have ht3_m : t3 ∈ trips := htr_eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          obtain ⟨s1, hs1⟩ := (isTriple_iff_exists_tripVec ht t1.1).mp (Finset.mem_filter.mp ht1_m).2
          obtain ⟨s2, hs2⟩ := (isTriple_iff_exists_tripVec ht t2.1).mp (Finset.mem_filter.mp ht2_m).2
          obtain ⟨s3, hs3⟩ := (isTriple_iff_exists_tripVec ht t3.1).mp (Finset.mem_filter.mp ht3_m).2
          have hall_wt2 : ∀ a b : P, a ∈ trips → b ∈ trips → a ≠ b → (suppF (a.1 + b.1)).card = 2 := by
            intro a b ha hb hab
            have hmemE : a.1 + b.1 ∈ E := ⟨P.add_mem a.2 b.2, by
              have ha1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even a.1).not.mpr (by have := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2; omega))
              have hb1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even b.1).not.mpr (by have := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2; omega))
              simp only [Pi.add_apply, Finset.sum_add_distrib, ha1, hb1]; exact z2_one_add_one⟩
            have hne0 : a.1 + b.1 ≠ 0 := fun h0 => hab (Subtype.ext (funext fun i => by
              have hi := congrFun h0 i; simp only [Pi.add_apply, Pi.zero_apply] at hi
              have := z2_add_self (b.1 i); linear_combination (norm := (ring_nf <;> simp [z2_two_eq_zero])) hi - this))
            have hsubK : suppF (a.1 + b.1) ⊆ K := fun i hi => by
              by_contra hiK; exact mem_suppF.mp hi (((hE_iff _).mp hmemE).1 i hiK)
            have hle3 : (suppF (a.1 + b.1)).card ≤ 3 := (Finset.card_le_card hsubK).trans_eq hK3
            have hev := hEeven _ hmemE
            have hge2 := suppF_card_ge_two (hEcode _ hmemE) hne0
            omega
          have h12a := (tripVec_add_wt2_iff ht ht3 s1 s2).mp (by rw [← hs1, ← hs2]; exact hall_wt2 t1 t2 ht1_m ht2_m h12)
          have h13a := (tripVec_add_wt2_iff ht ht3 s1 s3).mp (by rw [← hs1, ← hs3]; exact hall_wt2 t1 t3 ht1_m ht3_m h13)
          have h23a := (tripVec_add_wt2_iff ht ht3 s2 s3).mp (by rw [← hs2, ← hs3]; exact hall_wt2 t2 t3 ht2_m ht3_m h23)
          have hne12s : s1 ≠ s2 := fun h => h12 (Subtype.ext (by rw [hs1, hs2, h]))
          have hne13s : s1 ≠ s3 := fun h => h13 (Subtype.ext (by rw [hs1, hs3, h]))
          have hne23s : s2 ≠ s3 := fun h => h23 (Subtype.ext (by rw [hs2, hs3, h]))
          have hnxt3_ne : ∀ a : Fin (3 * t), nxt ht (nxt ht (nxt ht a)) ≠ a := fun a h => by
            have hv := congrArg Fin.val h
            rw [nxt_val, nxt_val, nxt_val] at hv
            have ha := a.isLt
            split_ifs at hv <;> omega
          rcases h12a with h12a | h12a <;> rcases h13a with h13a | h13a <;>
            rcases h23a with h23a | h23a <;>
            grind [nxt_inj ht]
        by_cases ht3eq : t = 3
        · rw [if_pos ht3eq]
          by_cases htr1 : trips.card ≤ 1
          · omega
          · exfalso
            have htr2 : trips.card = 2 := by omega
            obtain ⟨t1, t2, h12, htr_eq⟩ := Finset.card_eq_two.mp htr2
            have ht1_m : t1 ∈ trips := htr_eq ▸ Finset.mem_insert_self _ _
            have ht2_m : t2 ∈ trips := htr_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            obtain ⟨s1, hs1⟩ := (isTriple_iff_exists_tripVec ht t1.1).mp (Finset.mem_filter.mp ht1_m).2
            obtain ⟨s2, hs2⟩ := (isTriple_iff_exists_tripVec ht t2.1).mp (Finset.mem_filter.mp ht2_m).2
            have hmemE : t1.1 + t2.1 ∈ E := ⟨P.add_mem t1.2 t2.2, by
              have h1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even t1.1).not.mpr (by have := (Finset.mem_filter.mp (Finset.mem_filter.mp ht1_m).1).2; omega))
              have h2 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even t2.1).not.mpr (by have := (Finset.mem_filter.mp (Finset.mem_filter.mp ht2_m).1).2; omega))
              simp only [Pi.add_apply, Finset.sum_add_distrib, h1, h2]; exact z2_one_add_one⟩
            have hne0 : t1.1 + t2.1 ≠ 0 := fun h0 => h12 (Subtype.ext (funext fun i => by
              have hi := congrFun h0 i; simp only [Pi.add_apply, Pi.zero_apply] at hi
              have := z2_add_self (t2.1 i); linear_combination (norm := (ring_nf <;> simp [z2_two_eq_zero])) hi - this))
            have hsubK : suppF (t1.1 + t2.1) ⊆ K := fun i hi => by
              by_contra hiK; exact mem_suppF.mp hi (((hE_iff _).mp hmemE).1 i hiK)
            have hw2 : (suppF (t1.1 + t2.1)).card = 2 := by
              have hle3 : (suppF (t1.1 + t2.1)).card ≤ 3 := (Finset.card_le_card hsubK).trans_eq hK3
              have hev := hEeven _ hmemE
              have hge2 := suppF_card_ge_two (hEcode _ hmemE) hne0
              omega
            have hadj := (tripVec_add_wt2_iff ht ht3 s1 s2).mp (by rw [← hs1, ← hs2]; exact hw2)
            let s : Fin (3 * t) := if s2 = nxt ht s1 then s1 else s2
            have hs_trip : tripVec ht s ∈ P := by
              dsimp only [s]; split_ifs
              · exact hs1 ▸ t1.2
              · exact hs2 ▸ t2.2
            have hs_mod : s.val % 3 = e.val := by
              have hsin : s ∈ suppF (t1.1 + t2.1) := by
                have hmem : ∀ a : Fin (3 * t), a ∈ suppF (tripVec ht a + tripVec ht (nxt ht a)) := by
                  intro a
                  rw [mem_suppF, Pi.add_apply]
                  have h1 : tripVec ht a a = 1 := by simp [tripVec]
                  have h2 : tripVec ht (nxt ht a) a = 0 := by
                    simp only [tripVec, ite_eq_right_iff, one_ne_zero, imp_false]
                    rintro (h | h | h)
                    · have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; rw [nxt_mod3 ht] at this; omega
                    · have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; change a.val % 3 = (nxt ht (nxt ht a)).val % 3 at this; have hm1 := nxt_mod3 ht (nxt ht a); have hm2 := nxt_mod3 ht a; omega
                    · have hv := congrArg Fin.val h; rw [nxt_val, nxt_val, nxt_val] at hv
                      have := a.isLt; split_ifs at hv <;> omega
                  rw [h1, h2, add_zero]; exact z2_one_ne_zero
                dsimp only [s]
                split_ifs with h
                · rw [hs1, hs2, h]; exact hmem s1
                · have h' : s1 = nxt ht s2 := hadj.resolve_left h
                  have hcomm : t1.1 + t2.1 = tripVec ht s2 + tripVec ht (nxt ht s2) := by
                    rw [hs1, hs2, h', add_comm]
                  rw [hcomm]; exact hmem s2
              exact hKres s (hsubK hsin)
            have hKeq : K = Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = s.val % 3) := by
              refine Finset.eq_of_subset_of_card_le (fun i hi => Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (hKres i hi).trans hs_mod.symm⟩) ?_
              rw [card_resClass ⟨s.val % 3, Nat.mod_lt _ (by omega)⟩, hK3, ht3eq]
            subst t
            have hmem : ∀ f, top3Vec s f ∈ P := by
              intro f
              let z := top3Vec s f + f 2 • tripVec ht s
              have hz : z ∈ E := (hE_iff z).mpr ⟨fun i hi => (top3_remainder s f).1 i (by simpa [hKeq] using hi),
                (top3_remainder s f).2⟩
              have he : z + f 2 • tripVec ht s = top3Vec s f := by
                ext j; change (top3Vec s f j + _) + _ = _; rw [add_assoc, z2_add_self, add_zero]
              exact he ▸ P.add_mem hz.1 (P.smul_mem _ hs_trip)
            let g : (Fin 3 → F2) → P := fun f => ⟨top3Vec s f, hmem f⟩
            have hinj : Function.Injective g := fun a b h => (top3_encode s a).2.symm.trans
              ((congrArg (top3Read s) (congrArg Subtype.val h)).trans (top3_encode s b).2)
            have hbij : Function.Bijective g :=
              (Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj, by
                rw [← (Nat.card_eq_fintype_card (α := P)), hcardP]; decide⟩
            apply hnt
            refine ⟨hQiff, Or.inr (Or.inl ⟨rfl, s, fun x => ?_⟩)⟩
            constructor
            · intro hx
              obtain ⟨f,hf⟩ := hbij.surjective ⟨x,hx⟩
              have he : top3Vec s f = x := congrArg Subtype.val hf
              rw [← he]; exact (top3_encode s f).1
            · intro hx
              exact top3_decode s x hx ▸ hmem (top3Read s x)
        · rw [if_neg ht3eq]; omega

lemma dim4_bound {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hdimP : Module.finrank F2 P = 4) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      344 * (Nat.card P * Nat.card Q) := by
  letI : Fintype P := Fintype.ofFinite P
  have hQsub : Q ≤ codeSub t := fun y hy => mem_codeSub.mpr (hQ y hy)
  have hbase := small_side_row_sum_bound ht hQsub hdim (by omega) (by omega)
  rw [hdimP] at hbase
  have hcardP : Nat.card P = 16 := by rw [card_eq_two_pow_finrank, hdimP]; norm_num
  let p0 : P := ⟨0, zero_mem P⟩
  refine hbase.trans (Nat.mul_le_mul_right _ ?_)
  change _ + ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤ _
  rcases evenSub_dichotomy P with hAllEven | ⟨hE3, u0, hu0_odd⟩
  · have hP_even : ∀ x ∈ P, (suppF x).card % 2 = 0 := fun x hx =>
      (sum_eq_zero_iff_even x).mp (hAllEven.symm ▸ hx).2
    obtain ⟨Cs, _, hsum_dim, hpairs_eq⟩ := pair_classes_structure ht hP hP_even
    let pairsP := (Finset.univ : Finset P).filter (fun x => (suppF x.1).card = 2)
    change 2 * pairsP.card = _ at hpairs_eq
    have hle5 : ∀ K ∈ Cs, K.card ≤ 5 := fun K hK => by
      have := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
      omega
    have hpairs_le10 : pairsP.card ≤ 10 := by
      have hbd := pair_count_le_of_max_size Cs Finset.card 4 5 (by omega) hle5
      omega
    have hsum_le : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤ 60 + 12 * pairsP.card := by
      have hterm : ∀ x ∈ (Finset.univ : Finset P).erase p0,
          wt8 (rkC (nbrF x.val)) ≤ 4 + if (suppF x.val).card = 2 then 12 else 0 := by
        intro x hx
        have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase hx (Subtype.ext h)
        have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
        have hev := hP_even x.val x.2
        by_cases hw2 : (suppF x.val).card = 2
        · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
        · rw [if_neg hw2, add_zero]
          exact wt8_le_4 (rkC_even_ge6 ht ht3 (hP x.val x.2) hev (by omega))
      calc ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ (Finset.univ : Finset P).erase p0, (4 + if (suppF x.val).card = 2 then 12 else 0) :=
            Finset.sum_le_sum hterm
        _ = 60 + 12 * pairsP.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
                Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ,
                ← Nat.card_eq_fintype_card, hcardP]
            have hp0_not : p0 ∉ pairsP := by simp [pairsP, p0, suppF]
            have hfeq : ((Finset.univ : Finset P).erase p0).filter (fun x => (suppF x.val).card = 2) =
                pairsP := by
              ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, pairsP, true_and]
              exact ⟨fun h => h.2, fun h => ⟨fun h0 => hp0_not (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), h⟩⟩
            rw [← Finset.sum_filter, hfeq, Finset.sum_const, smul_eq_mul]
            ring
    omega
  · let E := evenSub P
    letI : Fintype E := Fintype.ofFinite E
    have hEdim : Module.finrank F2 E = 3 := by dsimp only [E]; omega
    have hEcard : Nat.card E = 8 := by rw [card_eq_two_pow_finrank, hEdim]; norm_num
    have hEcode : ∀ x ∈ E, codeP t x := fun x hx => hP x hx.1
    have hEeven : ∀ x ∈ E, (suppF x).card % 2 = 0 := fun x hx => (sum_eq_zero_iff_even x).mp hx.2
    obtain ⟨Cs, _, hsum_dim, hpairs_eq⟩ := pair_classes_structure ht hEcode hEeven
    let pairsE := (Finset.univ : Finset E).filter (fun x => (suppF x.1).card = 2)
    change 2 * pairsE.card = _ at hpairs_eq
    have hle4 : ∀ K ∈ Cs, K.card ≤ 4 := fun K hK => by
      have := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
      omega
    have hpairs_le6 : pairsE.card ≤ 6 := by
      have hbd := pair_count_le_of_max_size Cs Finset.card 3 4 (by omega) hle4
      omega
    let evenSet : Finset P := (Finset.univ.erase p0).filter (fun x => (suppF x.val).card % 2 = 0)
    let oddSet : Finset P := (Finset.univ.erase p0).filter (fun x => (suppF x.val).card % 2 = 1)
    have hsplit : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) =
        (∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))) + ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val)) := by
      have hodd_eq : oddSet = (Finset.univ.erase p0).filter (fun x => ¬ (suppF x.val).card % 2 = 0) := by
        ext x; simp only [oddSet, Finset.mem_filter]; exact and_congr_right fun _ => by omega
      rw [hodd_eq, Finset.sum_filter_add_sum_filter_not]
    have heven_card : evenSet.card = 7 := by
      let eE : {x : E // x.1 ≠ 0} ≃ evenSet :=
        { toFun := fun x => ⟨⟨x.1.1, x.1.2.1⟩, Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨fun h => x.2 (congrArg Subtype.val h), Finset.mem_univ _⟩,
             hEeven x.1.1 x.1.2⟩⟩
          invFun := fun x => ⟨⟨x.1.1, x.1.2, (sum_eq_zero_iff_even x.1.1).mpr (Finset.mem_filter.mp x.2).2⟩,
            fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp x.2).1 (Subtype.ext h)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hcard_nz : Nat.card {x : E // x.1 ≠ 0} = 7 := by
        have : Nat.card {x : E // x.1 ≠ 0} = ((Finset.univ : Finset E).erase ⟨0, zero_mem E⟩).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          congr 1; ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
          exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            ← Nat.card_eq_fintype_card, hEcard]
      have := Nat.card_congr eE
      rw [hcard_nz, Nat.card_eq_fintype_card, Fintype.card_coe] at this
      exact this.symm
    have hodd_card : oddSet.card = 8 := by
      have htot : evenSet.card + oddSet.card = 15 := by
        have hodd_eq : oddSet = (Finset.univ.erase p0).filter (fun x => ¬ (suppF x.val).card % 2 = 0) := by
          ext x; simp only [oddSet, Finset.mem_filter]; exact and_congr_right fun _ => by omega
        rw [hodd_eq, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem (Finset.mem_univ p0),
            Finset.card_univ, ← Nat.card_eq_fintype_card, hcardP]
      omega
    have heven_sum : ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 28 + 12 * pairsE.card := by
      have hterm : ∀ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 4 + if (suppF x.val).card = 2 then 12 else 0 := by
        intro x hx
        have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hx).1 (Subtype.ext h)
        have hev := (Finset.mem_filter.mp hx).2
        have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
        by_cases hw2 : (suppF x.val).card = 2
        · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
        · rw [if_neg hw2, add_zero]
          exact wt8_le_4 (rkC_even_ge6 ht ht3 (hP x.val x.2) hev (by omega))
      have hpair_card_eq : (evenSet.filter (fun x => (suppF x.val).card = 2)).card = pairsE.card := by
        refine Finset.card_bij (fun x hx => ⟨x.1, x.2, (sum_eq_zero_iff_even x.1).mpr
            (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2⟩)
          (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
          (fun a _ b _ h => Subtype.ext (congrArg (fun y : E => y.val) h))
          (fun y hy => ⟨⟨y.1, y.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨fun h => by
              have h0 : y.1 = 0 := congrArg Subtype.val h
              have := (Finset.mem_filter.mp hy).2
              rw [h0] at this; simp [suppF] at this, Finset.mem_univ _⟩,
             hEeven y.1 y.2⟩, (Finset.mem_filter.mp hy).2⟩, rfl⟩)
      calc ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ evenSet, (4 + if (suppF x.val).card = 2 then 12 else 0) := Finset.sum_le_sum hterm
        _ = 4 * evenSet.card + 12 * (evenSet.filter (fun x => (suppF x.val).card = 2)).card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
                Finset.sum_const, smul_eq_mul]; ring
        _ = 28 + 12 * pairsE.card := by rw [heven_card, hpair_card_eq]
    let trips : Finset P := oddSet.filter (fun x => isTriple ht x.val)
    have htrips_le4 : trips.card ≤ 4 := by
      by_contra h
      obtain ⟨T, hT, hsz⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ trips.card)
      have hd := short_triples_card ht T (by omega) (fun x hx => (Finset.mem_filter.mp (hT hx)).2)
      omega
    have hodd_sum : ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val)) ≤ 64 + 8 * trips.card := by
      have hterm : ∀ x ∈ oddSet, wt8 (rkC (nbrF x.val)) ≤ 8 + if isTriple ht x.val then 8 else 0 := by
        intro x hx
        have hodd := (Finset.mem_filter.mp hx).2
        have hge4 := rkC_odd_ge4 ht ht3 (hP x.val x.2) hodd
        by_cases htr : isTriple ht x.val
        · rw [if_pos htr, (rkC_odd_eq4_iff_isTriple ht ht3 (hP x.val x.2) hodd).mpr htr, wt8_eq_16 rfl]
        · rw [if_neg htr, add_zero]
          have hne4 : rkC (nbrF x.val) ≠ 4 := fun h =>
            htr ((rkC_odd_eq4_iff_isTriple ht ht3 (hP x.val x.2) hodd).mp h)
          exact wt8_le_8 (by omega)
      calc ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ oddSet, (8 + if isTriple ht x.val then 8 else 0) := Finset.sum_le_sum hterm
        _ = 8 * oddSet.card + 8 * trips.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
                Finset.sum_const, smul_eq_mul]; ring
        _ = 64 + 8 * trips.card := by rw [hodd_card]
    rw [hsplit]
    omega

lemma wt_le_one_card_in_submodule {α : Type*} [Fintype α] [DecidableEq α]
    (V : Submodule F2 (α → F2)) :
    letI : Fintype V := Fintype.ofFinite V
    ((Finset.univ : Finset V).filter (fun v => (Finset.univ.filter (fun i => v.1 i ≠ 0)).card ≤ 1)).card ≤
      Module.finrank F2 V + 1 := by
  letI : Fintype V := Fintype.ofFinite V
  let S1 := (Finset.univ : Finset V).filter (fun v => (Finset.univ.filter (fun i => v.1 i ≠ 0)).card = 1)
  have hS1_le : S1.card ≤ Module.finrank F2 V := by
    have hli : LinearIndependent F2 (fun v : S1 => v.1) := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum v0
      have hw1 : (Finset.univ.filter (fun i => v0.1.1 i ≠ 0)).card = 1 :=
        (Finset.mem_filter.mp v0.2).2
      obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hw1
      have hv0_eq : v0.1.1 = Pi.single i0 1 := by
        ext i
        by_cases hi : i = i0
        · subst hi
          have : i ∈ Finset.univ.filter (fun j => v0.1.1 j ≠ 0) := hi0.symm ▸ Finset.mem_singleton_self i
          simp [z2_eq_one_of_ne_zero (Finset.mem_filter.mp this).2]
        · have : i ∉ Finset.univ.filter (fun j => v0.1.1 j ≠ 0) := by simp [hi0, hi]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
          simp [this, hi]
      have heval := congrFun (congrArg Subtype.val hsum) i0
      rw [Submodule.coe_sum, Finset.sum_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at heval
      rw [Finset.sum_eq_single v0] at heval
      · simp [hv0_eq] at heval; exact heval
      · intro v _ hvne
        have hv1 : (Finset.univ.filter (fun i => v.1.1 i ≠ 0)).card = 1 :=
          (Finset.mem_filter.mp v.2).2
        obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hv1
        have hv_eq : v.1.1 = Pi.single j0 1 := by
          ext i
          by_cases hi : i = j0
          · subst hi
            have : i ∈ Finset.univ.filter (fun j => v.1.1 j ≠ 0) := hj0.symm ▸ Finset.mem_singleton_self i
            simp [z2_eq_one_of_ne_zero (Finset.mem_filter.mp this).2]
          · have : i ∉ Finset.univ.filter (fun j => v.1.1 j ≠ 0) := by simp [hj0, hi]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
            simp [this, hi]
        have hjne : i0 ≠ j0 := fun h => hvne (Subtype.ext (Subtype.ext (by rw [hv_eq, hv0_eq, h])))
        simp [hv_eq, hjne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcard := hli.fintype_card_le_finrank
    rwa [Fintype.card_coe] at hcard
  have hsub : (Finset.univ : Finset V).filter (fun v => (Finset.univ.filter (fun i => v.1 i ≠ 0)).card ≤ 1) ⊆
      insert ⟨0, zero_mem V⟩ S1 := by
    intro v hv
    have hle1 := (Finset.mem_filter.mp hv).2
    by_cases h0 : (Finset.univ.filter (fun i => v.1 i ≠ 0)).card = 0
    · apply Finset.mem_insert.mpr; left
      apply Subtype.ext; ext i
      by_contra hne
      have : i ∈ Finset.univ.filter (fun j => v.1 j ≠ 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [Finset.card_eq_zero.mp h0] at this
      exact Finset.notMem_empty _ this
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  calc ((Finset.univ : Finset V).filter (fun v => (Finset.univ.filter (fun i => v.1 i ≠ 0)).card ≤ 1)).card
      ≤ (insert (⟨0, zero_mem V⟩ : V) S1).card := Finset.card_le_card hsub
    _ ≤ S1.card + 1 := Finset.card_insert_le _ _
    _ ≤ Module.finrank F2 V + 1 := by omega

set_option maxHeartbeats 5000000 in
lemma dim5_bound {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hdimP : Module.finrank F2 P = 5) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      (if t = 3 then 344 else 352) * (Nat.card P * Nat.card Q) := by
  letI : Fintype P := Fintype.ofFinite P
  have hQsub : Q ≤ codeSub t := fun y hy => mem_codeSub.mpr (hQ y hy)
  have hbase := small_side_row_sum_bound ht hQsub hdim (by omega) (by omega)
  rw [hdimP] at hbase
  have hcardP : Nat.card P = 32 := by rw [card_eq_two_pow_finrank, hdimP]; norm_num
  let p0 : P := ⟨0, zero_mem P⟩
  refine hbase.trans (Nat.mul_le_mul_right _ ?_)
  change _ + ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤ _
  rcases evenSub_dichotomy P with hAllEven | ⟨hE4, u0, hu0_odd⟩
  · have hP_even : ∀ x ∈ P, (suppF x).card % 2 = 0 := fun x hx =>
      (sum_eq_zero_iff_even x).mp (hAllEven.symm ▸ hx).2
    obtain ⟨Cs, hCs, hsum_dim, hpairs_eq⟩ := pair_classes_structure ht hP hP_even
    let pairsP := (Finset.univ : Finset P).filter (fun x => (suppF x.1).card = 2)
    change 2 * pairsP.card = _ at hpairs_eq
    by_cases hK6 : ∃ K ∈ Cs, 6 ≤ K.card
    · obtain ⟨K, hK, hKge6⟩ := hK6
      obtain ⟨hKne, _, e, hKres, hKmem⟩ := hCs K hK
      have hKle6 : K.card - 1 ≤ 5 := by
        have := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
        omega
      have hKeq6 : K.card = 6 := by omega
      have hP_iff := evenSub_eq_of_class_size ht hP K e hKne hKres hKmem (by omega)
      have hpairs_le15 : pairsP.card ≤ 15 := by
        have hle6 : ∀ C ∈ Cs, C.card ≤ 6 := fun C hC => by
          have := Finset.single_le_sum (f := fun D => D.card - 1) (fun _ _ => Nat.zero_le _) hC
          omega
        have hbd := pair_count_le_of_max_size Cs Finset.card 5 6 (by omega) hle6
        omega
      have hsum_le : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤ 62 + 14 * pairsP.card := by
        have hterm : ∀ x ∈ (Finset.univ : Finset P).erase p0,
            wt8 (rkC (nbrF x.val)) ≤ 2 + if (suppF x.val).card = 2 then 14 else 0 := by
          intro x hx
          have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase hx (Subtype.ext h)
          have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
          have hev := hP_even x.val x.2
          by_cases hw2 : (suppF x.val).card = 2
          · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
          · rw [if_neg hw2, add_zero]
            have hres : ∀ i ∈ suppF x.val, i.val % 3 = e.val := fun i hi =>
              hKres i (by by_contra hiK; exact mem_suppF.mp hi (((hP_iff x.val).mp x.2).1 i hiK))
            exact wt8_le_2 (rkC_even_one_res_ge7 ht e hres (by omega))
        calc ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val))
            ≤ ∑ x ∈ (Finset.univ : Finset P).erase p0, (2 + if (suppF x.val).card = 2 then 14 else 0) :=
              Finset.sum_le_sum hterm
          _ = 62 + 14 * pairsP.card := by
              rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
                  Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ,
                  ← Nat.card_eq_fintype_card, hcardP]
              have hp0_not : p0 ∉ pairsP := by simp [pairsP, p0, suppF]
              have hfeq : ((Finset.univ : Finset P).erase p0).filter (fun x => (suppF x.val).card = 2) =
                  pairsP := by
                ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, pairsP, true_and]
                exact ⟨fun h => h.2, fun h => ⟨fun h0 => hp0_not (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), h⟩⟩
              rw [← Finset.sum_filter, hfeq, Finset.sum_const, smul_eq_mul]
              ring
      split_ifs <;> omega
    · push Not at hK6
      have hpairs_le11 : pairsP.card ≤ 11 := by
        by_cases hK5 : ∃ K ∈ Cs, K.card = 5
        · obtain ⟨K, hK, hK5eq⟩ := hK5
          have hrem_sum : ∑ C ∈ Cs.erase K, (C.card - 1) ≤ 1 := by
            have := Finset.add_sum_erase Cs (fun C => C.card - 1) hK
            omega
          have hrem_le2 : ∀ C ∈ Cs.erase K, C.card ≤ 2 := fun C hC => by
            have := Finset.single_le_sum (f := fun D => D.card - 1) (fun _ _ => Nat.zero_le _) hC
            omega
          have hrem_pairs := pair_count_le_of_max_size (Cs.erase K) Finset.card 1 2 hrem_sum hrem_le2
          have htot := Finset.add_sum_erase Cs (fun C => C.card * (C.card - 1)) hK
          change K.card * (K.card - 1) + _ = _ at htot
          rw [hK5eq] at htot
          omega
        · push Not at hK5
          have hle4 : ∀ C ∈ Cs, C.card ≤ 4 := fun C hC => by
            have h1 := hK6 C hC; have h2 := hK5 C hC; omega
          have hbd := pair_count_le_of_max_size Cs Finset.card 5 4 (by omega) hle4
          omega
      have hsum_le : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) ≤ 124 + 12 * pairsP.card := by
        have hterm : ∀ x ∈ (Finset.univ : Finset P).erase p0,
            wt8 (rkC (nbrF x.val)) ≤ 4 + if (suppF x.val).card = 2 then 12 else 0 := by
          intro x hx
          have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase hx (Subtype.ext h)
          have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
          have hev := hP_even x.val x.2
          by_cases hw2 : (suppF x.val).card = 2
          · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
          · rw [if_neg hw2, add_zero]
            exact wt8_le_4 (rkC_even_ge6 ht ht3 (hP x.val x.2) hev (by omega))
        calc ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val))
            ≤ ∑ x ∈ (Finset.univ : Finset P).erase p0, (4 + if (suppF x.val).card = 2 then 12 else 0) :=
              Finset.sum_le_sum hterm
          _ = 124 + 12 * pairsP.card := by
              rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
                  Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ,
                  ← Nat.card_eq_fintype_card, hcardP]
              have hp0_not : p0 ∉ pairsP := by simp [pairsP, p0, suppF]
              have hfeq : ((Finset.univ : Finset P).erase p0).filter (fun x => (suppF x.val).card = 2) =
                  pairsP := by
                ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, pairsP, true_and]
                exact ⟨fun h => h.2, fun h => ⟨fun h0 => hp0_not (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), h⟩⟩
              rw [← Finset.sum_filter, hfeq, Finset.sum_const, smul_eq_mul]
              ring
      split_ifs <;> omega
  · let E := evenSub P
    letI : Fintype E := Fintype.ofFinite E
    have hEdim : Module.finrank F2 E = 4 := by dsimp only [E]; omega
    have hEcard : Nat.card E = 16 := by rw [card_eq_two_pow_finrank, hEdim]; norm_num
    have hEcode : ∀ x ∈ E, codeP t x := fun x hx => hP x hx.1
    have hEeven : ∀ x ∈ E, (suppF x).card % 2 = 0 := fun x hx => (sum_eq_zero_iff_even x).mp hx.2
    obtain ⟨Cs, hCs, hsum_dim, hpairs_eq⟩ := pair_classes_structure ht hEcode hEeven
    let pairsE := (Finset.univ : Finset E).filter (fun x => (suppF x.1).card = 2)
    change 2 * pairsE.card = _ at hpairs_eq
    let evenSet : Finset P := (Finset.univ.erase p0).filter (fun x => (suppF x.val).card % 2 = 0)
    let oddSet : Finset P := (Finset.univ.erase p0).filter (fun x => (suppF x.val).card % 2 = 1)
    have hsplit : ∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val)) =
        (∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))) + ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val)) := by
      have hodd_eq : oddSet = (Finset.univ.erase p0).filter (fun x => ¬ (suppF x.val).card % 2 = 0) := by
        ext x; simp only [oddSet, Finset.mem_filter]; exact and_congr_right fun _ => by omega
      rw [hodd_eq, Finset.sum_filter_add_sum_filter_not]
    have heven_card : evenSet.card = 15 := by
      let eE : {x : E // x.1 ≠ 0} ≃ evenSet :=
        { toFun := fun x => ⟨⟨x.1.1, x.1.2.1⟩, Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨fun h => x.2 (congrArg Subtype.val h), Finset.mem_univ _⟩,
             hEeven x.1.1 x.1.2⟩⟩
          invFun := fun x => ⟨⟨x.1.1, x.1.2, (sum_eq_zero_iff_even x.1.1).mpr (Finset.mem_filter.mp x.2).2⟩,
            fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp x.2).1 (Subtype.ext h)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hcard_nz : Nat.card {x : E // x.1 ≠ 0} = 15 := by
        have : Nat.card {x : E // x.1 ≠ 0} = ((Finset.univ : Finset E).erase ⟨0, zero_mem E⟩).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          congr 1; ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
          exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            ← Nat.card_eq_fintype_card, hEcard]
      have := Nat.card_congr eE
      rw [hcard_nz, Nat.card_eq_fintype_card, Fintype.card_coe] at this
      exact this.symm
    have hodd_card : oddSet.card = 16 := by
      have htot : evenSet.card + oddSet.card = 31 := by
        have hodd_eq : oddSet = (Finset.univ.erase p0).filter (fun x => ¬ (suppF x.val).card % 2 = 0) := by
          ext x; simp only [oddSet, Finset.mem_filter]; exact and_congr_right fun _ => by omega
        rw [hodd_eq, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem (Finset.mem_univ p0),
            Finset.card_univ, ← Nat.card_eq_fintype_card, hcardP]
      omega
    have heven_sum : ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 60 + 12 * pairsE.card := by
      have hterm : ∀ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 4 + if (suppF x.val).card = 2 then 12 else 0 := by
        intro x hx
        have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hx).1 (Subtype.ext h)
        have hev := (Finset.mem_filter.mp hx).2
        have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
        by_cases hw2 : (suppF x.val).card = 2
        · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
        · rw [if_neg hw2, add_zero]
          exact wt8_le_4 (rkC_even_ge6 ht ht3 (hP x.val x.2) hev (by omega))
      have hpair_card_eq : (evenSet.filter (fun x => (suppF x.val).card = 2)).card = pairsE.card := by
        refine Finset.card_bij (fun x hx => ⟨x.1, x.2, (sum_eq_zero_iff_even x.1).mpr
            (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2⟩)
          (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
          (fun a _ b _ h => Subtype.ext (congrArg (fun y : E => y.val) h))
          (fun y hy => ⟨⟨y.1, y.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨fun h => by
              have h0 : y.1 = 0 := congrArg Subtype.val h
              have := (Finset.mem_filter.mp hy).2
              rw [h0] at this; simp [suppF] at this, Finset.mem_univ _⟩,
             hEeven y.1 y.2⟩, (Finset.mem_filter.mp hy).2⟩, rfl⟩)
      calc ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ evenSet, (4 + if (suppF x.val).card = 2 then 12 else 0) := Finset.sum_le_sum hterm
        _ = 4 * evenSet.card + 12 * (evenSet.filter (fun x => (suppF x.val).card = 2)).card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
                Finset.sum_const, smul_eq_mul]; ring
        _ = 60 + 12 * pairsE.card := by rw [heven_card, hpair_card_eq]
    let trips : Finset P := oddSet.filter (fun x => isTriple ht x.val)
    let W3 : Finset P := oddSet.filter (fun x => (suppF x.val).card = 3)
    have htrips_sub_W3 : trips ⊆ W3 := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩
      obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hx).2
      rw [hs]
      have h01 : s ≠ nxt ht s := fun h => by
        have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; rw [nxt_mod3 ht] at this; omega
      have h02 : s ≠ nxt ht (nxt ht s) := fun h => by
        have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; have hm1 := nxt_mod3 ht (nxt ht s); have hm2 := nxt_mod3 ht s; omega
      have h12 : nxt ht s ≠ nxt ht (nxt ht s) := fun h => h01 (nxt_inj ht h)
      rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
          Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
    have hodd_sum_W3 : ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val)) ≤
        64 + 4 * W3.card + 8 * trips.card := by
      have hterm : ∀ x ∈ oddSet, wt8 (rkC (nbrF x.val)) ≤
          4 + (if (suppF x.val).card = 3 then 4 else 0) + (if isTriple ht x.val then 8 else 0) := by
        intro x hx
        have hodd := (Finset.mem_filter.mp hx).2
        have hge4 := rkC_odd_ge4 ht ht3 (hP x.val x.2) hodd
        by_cases htr : isTriple ht x.val
        · have hw3 : (suppF x.val).card = 3 :=
            (Finset.mem_filter.mp (htrips_sub_W3 (Finset.mem_filter.mpr ⟨hx, htr⟩))).2
          rw [if_pos hw3, if_pos htr, (rkC_odd_eq4_iff_isTriple ht ht3 (hP x.val x.2) hodd).mpr htr,
              wt8_eq_16 rfl]
        · rw [if_neg htr, add_zero]
          by_cases hw3 : (suppF x.val).card = 3
          · rw [if_pos hw3]
            have hne4 : rkC (nbrF x.val) ≠ 4 := fun h =>
              htr ((rkC_odd_eq4_iff_isTriple ht ht3 (hP x.val x.2) hodd).mp h)
            exact wt8_le_8 (by omega)
          · rw [if_neg hw3, add_zero]
            have hge3 : 3 ≤ (suppF x.val).card := by
              have h2 := suppF_card_ge_two (hP x.val x.2) (fun h0 => by
                rw [h0] at hodd; simp [suppF] at hodd)
              omega
            exact wt8_le_4 (rkC_odd_ge6_of_wt_ge5 ht ht3 (hP x.val x.2) hodd (by omega))
      calc ∑ x ∈ oddSet, wt8 (rkC (nbrF x.val))
          ≤ ∑ x ∈ oddSet, (4 + (if (suppF x.val).card = 3 then 4 else 0) +
              (if isTriple ht x.val then 8 else 0)) := Finset.sum_le_sum hterm
        _ = 4 * oddSet.card + 4 * W3.card + 8 * trips.card := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
                ← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
                ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]; ring
        _ = 64 + 4 * W3.card + 8 * trips.card := by rw [hodd_card]
    have hW3_bound_gen : ∀ (u : P), u ∈ W3 →
        ∃ (A : (r : Fin 3) → E →ₗ[F2] ({i : Fin (3 * t) // i.val % 3 = r.val ∧ i ∉ suppF u.1} → F2)),
          (∀ r : Fin 3, W3.card ≤
            (Module.finrank F2 (LinearMap.range (A r)) + 1) *
              2 ^ (4 - Module.finrank F2 (LinearMap.range (A r)))) ∧
          4 ≤ ∑ r : Fin 3, Module.finrank F2 (LinearMap.range (A r)) ∧
          (∀ (K : Finset (Fin (3 * t))) (e : Fin 3), K.Nonempty → (∀ i ∈ K, i.val % 3 = e.val) →
            (∀ i ∈ K, ∀ j ∈ K, i ≠ j → pairVec i j ∈ E) →
            K.card - 1 ≤ Module.finrank F2 (LinearMap.range (A e))) := by
      intro u huW3
      have hu3 : (suppF u.1).card = 3 := (Finset.mem_filter.mp huW3).2
      have hu_odd : (suppF u.1).card % 2 = 1 := by omega
      have hu_uniq : ∀ r : Fin 3, ((suppF u.1).filter (fun i => i.val % 3 = r.val)).card = 1 := by
        have hpos : ∀ r : Fin 3, 1 ≤ ((suppF u.1).filter (fun i => i.val % 3 = r.val)).card := fun r => by
          obtain ⟨i, hi, hm⟩ := codeP_odd_hits_all_res (hP u.1 u.2) hu_odd r
          exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hm⟩⟩
        let counts := fun r : Fin 3 => ((suppF u.1).filter (fun i => i.val % 3 = r.val)).card
        have hsum : ∑ r, counts r = 3 := by
          refine Eq.trans ?_ hu3
          rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := fun i : Fin (3*t) =>
            (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) (fun _ _ => Finset.mem_univ _)]
          apply Finset.sum_congr rfl
          intro r _
          rfl
        change ∀ r, counts r = 1
        change ∀ r, 1 ≤ counts r at hpos
        have he := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun _ : Fin 3 => 1)
          (g := counts) (fun j _ => hpos j)).mp (by simpa using hsum.symm)
        exact fun r => (he r (Finset.mem_univ _)).symm
      let A : (r : Fin 3) → E →ₗ[F2] ({i : Fin (3 * t) // i.val % 3 = r.val ∧ i ∉ suppF u.1} → F2) :=
        fun r =>
          { toFun := fun p i => p.1 i.1
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
      have hker_bot : LinearMap.ker (A 0) ⊓ LinearMap.ker (A 1) ⊓ LinearMap.ker (A 2) = ⊥ := by
        rw [eq_bot_iff]
        intro p hp
        simp only [Submodule.mem_inf, LinearMap.mem_ker] at hp
        rw [Submodule.mem_bot]
        apply Subtype.ext; ext i
        let r : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩
        have hAr0 : A r p = 0 := by
          have hall : ∀ k, A k p = 0 := by
            intro k; fin_cases k
            · exact hp.1.1
            · exact hp.1.2
            · exact hp.2
          exact hall r
        have hzero_out : ∀ j : Fin (3 * t), j.val % 3 = r.val → j ∉ suppF u.1 → p.1 j = 0 := by
          intro j hjm hju
          exact congrFun hAr0 ⟨j, hjm, hju⟩
        by_cases hiu : i ∈ suppF u.1
        · have hres0 : resSum t r.val p.1 = 0 := by
            rw [codeP_resSum_eq_total (hEcode p.1 p.2) r, p.2.2]
          unfold resSum at hres0
          rw [Finset.sum_eq_single i] at hres0
          · simpa [r] using hres0
          · intro j _ hji
            by_cases hjm : j.val % 3 = r.val
            · rw [if_pos hjm]
              have hju : j ∉ suppF u.1 := by
                intro hju
                obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp (hu_uniq r)
                have h1 : i = i0 := by
                  have : i ∈ (suppF u.1).filter (fun k => k.val % 3 = r.val) :=
                    Finset.mem_filter.mpr ⟨hiu, rfl⟩
                  rw [hi0, Finset.mem_singleton] at this; exact this
                have h2 : j = i0 := by
                  have : j ∈ (suppF u.1).filter (fun k => k.val % 3 = r.val) :=
                    Finset.mem_filter.mpr ⟨hju, hjm⟩
                  rw [hi0, Finset.mem_singleton] at this; exact this
                exact hji (h2.trans h1.symm)
              exact hzero_out j hjm hju
            · simp [hjm]
          · intro h; exact absurd (Finset.mem_univ _) h
        · exact hzero_out i rfl hiu
      have hW3_wt1 : ∀ (r : Fin 3) (x : P) (hx : x ∈ W3),
          (Finset.univ.filter (fun i : {i : Fin (3 * t) // i.val % 3 = r.val ∧ i ∉ suppF u.1} =>
            A r ⟨u.1 + x.1, P.add_mem u.2 x.2, by
              have hu1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even u.1).not.mpr (by omega))
              have hx1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even x.1).not.mpr (by
                have := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2; omega))
              simp only [Pi.add_apply, Finset.sum_add_distrib, hu1, hx1]; exact z2_one_add_one⟩ i ≠ 0)).card ≤ 1 := by
        intro r x hxW3
        have hx3 : (suppF x.1).card = 3 := (Finset.mem_filter.mp hxW3).2
        have hx_odd : (suppF x.1).card % 2 = 1 := by omega
        have hx_uniq : ((suppF x.1).filter (fun i => i.val % 3 = r.val)).card = 1 := by
          let counts := fun k : Fin 3 => ((suppF x.1).filter (fun i => i.val % 3 = k.val)).card
          have hpos (k : Fin 3) : 1 ≤ counts k := by
            obtain ⟨i, hi, hm⟩ := codeP_odd_hits_all_res (hP x.1 x.2) hx_odd k
            exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hm⟩⟩
          have hsum : ∑ k, counts k = 3 := by
            refine Eq.trans ?_ hx3
            rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := fun i : Fin (3*t) =>
              (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) (fun _ _ => Finset.mem_univ _)]
            apply Finset.sum_congr rfl
            intro k _
            rfl
          have he := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun _ : Fin 3 => 1)
            (g := counts) (fun j _ => hpos j)).mp (by simpa using hsum.symm)
          exact (he r (Finset.mem_univ _)).symm
        refine Nat.le_trans ?_ (Nat.le_of_eq hx_uniq)
        refine Finset.card_le_card_of_injOn Subtype.val ?_ (fun _ _ _ _ h => Subtype.ext h)
        intro i hi
        have hnz := (Finset.mem_filter.mp hi).2
        dsimp only [A, LinearMap.coe_mk, AddHom.coe_mk] at hnz
        have hui0 : u.1 i.1 = 0 := by by_contra h; exact i.2.2 (mem_suppF.mpr h)
        simp only [Pi.add_apply, hui0, zero_add] at hnz
        exact Finset.mem_filter.mpr ⟨mem_suppF.mpr hnz, i.2.1⟩
      have hcard_le_r : ∀ r : Fin 3, W3.card ≤
          (Module.finrank F2 (LinearMap.range (A r)) + 1) *
            2 ^ (4 - Module.finrank F2 (LinearMap.range (A r))) := by
        intro r
        let T := Finset.univ.filter (fun p : E =>
          (Finset.univ.filter (fun i => A r p i ≠ 0)).card ≤ 1)

        have hW3_le_T : W3.card ≤ T.card := by
          have hinj : ∀ x1 ∈ W3, ∀ x2 ∈ W3,
              (if h : u.1 + x1.1 ∈ E then (⟨u.1 + x1.1, h⟩ : E) else ⟨0, zero_mem E⟩) =
              (if h : u.1 + x2.1 ∈ E then (⟨u.1 + x2.1, h⟩ : E) else ⟨0, zero_mem E⟩) → x1 = x2 := by
            intro x1 hx1 x2 hx2 heq
            have h1 : u.1 + x1.1 ∈ E := ⟨P.add_mem u.2 x1.2, by
              have hu1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even u.1).not.mpr (by omega))
              have hx1' := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even x1.1).not.mpr (by
                have := (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2; omega))
              simp only [Pi.add_apply, Finset.sum_add_distrib, hu1, hx1']; exact z2_one_add_one⟩
            have h2 : u.1 + x2.1 ∈ E := ⟨P.add_mem u.2 x2.2, by
              have hu1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even u.1).not.mpr (by omega))
              have hx2' := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even x2.1).not.mpr (by
                have := (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2; omega))
              simp only [Pi.add_apply, Finset.sum_add_distrib, hu1, hx2']; exact z2_one_add_one⟩
            simp only [dif_pos h1, dif_pos h2] at heq
            apply Subtype.ext; ext i
            have hi := congrFun (congrArg Subtype.val heq) i
            simp only [Pi.add_apply] at hi
            have := z2_add_self (u.1 i); linear_combination (norm := (ring_nf <;> simp [z2_two_eq_zero])) hi - this
          refine Finset.card_le_card_of_injOn
            (fun x => if h : u.1 + x.1 ∈ E then (⟨u.1 + x.1, h⟩ : E) else ⟨0, zero_mem E⟩)
            (fun x hx => ?_) hinj
          have hmem : u.1 + x.1 ∈ E := ⟨P.add_mem u.2 x.2, by
            have hu1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even u.1).not.mpr (by omega))
            have hx1' := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even x.1).not.mpr (by
              have := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2; omega))
            simp only [Pi.add_apply, Finset.sum_add_distrib, hu1, hx1']; exact z2_one_add_one⟩
          simp only [dif_pos hmem, T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW3_wt1 r x hx⟩
        let φ := LinearMap.rangeRestrict (A r)
        have hsurj : Function.Surjective φ := LinearMap.surjective_rangeRestrict (A r)
        let S1 : LinearMap.range (A r) → Prop :=
          fun v => (Finset.univ.filter (fun i => v.1 i ≠ 0)).card ≤ 1
        have hfib := card_fiber_of_surjective φ hsurj S1
        have hT_eq : Nat.card {p : E // S1 (φ p)} = T.card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          rfl
        have hS1_le : Nat.card {v : LinearMap.range (A r) // S1 v} ≤
            Module.finrank F2 (LinearMap.range (A r)) + 1 := by
          letI : Fintype (LinearMap.range (A r)) := Fintype.ofFinite _
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          exact wt_le_one_card_in_submodule (LinearMap.range (A r))
        have hcardR : Nat.card (LinearMap.range (A r)) = 2 ^ Module.finrank F2 (LinearMap.range (A r)) :=
          card_eq_two_pow_finrank
        have hdr_le4 : Module.finrank F2 (LinearMap.range (A r)) ≤ 4 := by
          have := LinearMap.finrank_range_le (A r)
          omega
        rw [hT_eq, hcardR, hEcard] at hfib
        have hpow_pos : 0 < 2 ^ Module.finrank F2 (LinearMap.range (A r)) := Nat.pos_of_ne_zero (by positivity)
        have hT_le : T.card ≤ (Module.finrank F2 (LinearMap.range (A r)) + 1) *
            2 ^ (4 - Module.finrank F2 (LinearMap.range (A r))) := by
          refine Nat.le_of_mul_le_mul_right ?_ hpow_pos
          calc T.card * 2 ^ Module.finrank F2 (LinearMap.range (A r))
              = Nat.card {v : LinearMap.range (A r) // S1 v} * 16 := hfib
            _ ≤ (Module.finrank F2 (LinearMap.range (A r)) + 1) * 16 := Nat.mul_le_mul_right _ hS1_le
            _ = (Module.finrank F2 (LinearMap.range (A r)) + 1) *
                (2 ^ (4 - Module.finrank F2 (LinearMap.range (A r))) *
                  2 ^ Module.finrank F2 (LinearMap.range (A r))) := by
                  rw [← pow_add, show 4 - Module.finrank F2 (LinearMap.range (A r)) +
                    Module.finrank F2 (LinearMap.range (A r)) = 4 by omega]
                  norm_num
            _ = (Module.finrank F2 (LinearMap.range (A r)) + 1) *
                2 ^ (4 - Module.finrank F2 (LinearMap.range (A r))) *
                2 ^ Module.finrank F2 (LinearMap.range (A r)) := by ring
        exact hW3_le_T.trans hT_le
      have hsum_rk : 4 ≤ ∑ r : Fin 3, Module.finrank F2 (LinearMap.range (A r)) := by
        let Φ : E →ₗ[F2]
            LinearMap.range (A 0) × (LinearMap.range (A 1) × LinearMap.range (A 2)) :=
          { toFun := fun p => (LinearMap.rangeRestrict (A 0) p,
              (LinearMap.rangeRestrict (A 1) p, LinearMap.rangeRestrict (A 2) p))
            map_add' := fun a b => by simp [Prod.mk_add_mk]
            map_smul' := fun c a => by simp [Prod.smul_mk] }
        have hΦ_inj : Function.Injective Φ := by
          rw [← LinearMap.ker_eq_bot, eq_bot_iff]
          intro p hp
          rw [LinearMap.mem_ker] at hp
          have h0 : A 0 p = 0 := congrArg Subtype.val (congrArg Prod.fst hp)
          have h1 : A 1 p = 0 := congrArg Subtype.val (congrArg (fun z => z.2.1) hp)
          have h2 : A 2 p = 0 := congrArg Subtype.val (congrArg (fun z => z.2.2) hp)
          have hmem : p ∈ LinearMap.ker (A 0) ⊓ LinearMap.ker (A 1) ⊓ LinearMap.ker (A 2) :=
            ⟨⟨h0, h1⟩, h2⟩
          rw [hker_bot] at hmem
          exact hmem
        have hle := LinearMap.finrank_le_finrank_of_injective hΦ_inj
        rw [Module.finrank_prod, Module.finrank_prod, hEdim] at hle
        rw [Fin.sum_univ_three]
        simpa only [Nat.add_assoc] using hle
      have hclass_rk : ∀ (K : Finset (Fin (3 * t))) (e : Fin 3), K.Nonempty →
          (∀ i ∈ K, i.val % 3 = e.val) →
          (∀ i ∈ K, ∀ j ∈ K, i ≠ j → pairVec i j ∈ E) →
          K.card - 1 ≤ Module.finrank F2 (LinearMap.range (A e)) := by
        intro K e hKne hKres hKmem
        let UK : Submodule F2 (Fin (3 * t) → F2) := codeSub t ⊓ suppSub K
        have hUK_dim : Module.finrank F2 UK = K.card - 1 :=
          finrank_code_inf_suppSub_one_res K hKne e hKres
        have hUK_le : UK ≤ E := by
          intro x hx
          obtain ⟨r0, hr0⟩ := hKne
          have hsum0 : (∑ i, x i) = 0 := by
            have hother : ∃ r : Fin 3, r ≠ e := by
              fin_cases e
              · exact ⟨1, fin3_one_ne_zero⟩
              · exact ⟨0, fin3_zero_ne_one⟩
              · exact ⟨0, fin3_zero_ne_two⟩
            obtain ⟨r, hre⟩ := hother
            rw [← codeP_resSum_eq_total (mem_codeSub.mp hx.1) r]
            unfold resSum
            refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hiK : i ∈ K
            · have : i.val % 3 ≠ r.val := by rw [hKres i hiK]; intro h; exact hre (Fin.ext h.symm)
              simp [this]
            · simp [hx.2 i hiK]
          have hdecomp : x = ∑ i ∈ K.erase r0, x i • pairVec i r0 := by
            ext j
            rw [Finset.sum_apply]
            by_cases hjK : j ∈ K
            · by_cases hjr : j = r0
              · subst hjr
                have hsumK : ∑ i ∈ K, x i = 0 := by
                  rw [← hsum0]
                  refine Finset.sum_subset (Finset.subset_univ K) fun i _ hi => hx.2 i hi
                rw [← Finset.add_sum_erase _ _ hr0] at hsumK
                have hx0 : x j = ∑ i ∈ K.erase j, x i := by
                  have := congrArg (· + x j) hsumK
                  have h2 := z2_add_self (x j)
                  linear_combination (norm := (ring_nf <;> simp [z2_two_eq_zero])) this - h2
                rw [hx0]
                refine Finset.sum_congr rfl fun i hi => ?_
                have hne : j ≠ i := (Finset.ne_of_mem_erase hi).symm
                simp [pairVec, hne]
              · rw [Finset.sum_eq_single j]
                · simp [pairVec, hjr]
                · intro i hi hij
                  have hne : j ≠ i := hij.symm
                  simp [pairVec, hne, hjr]
                · intro h; exact absurd (Finset.mem_erase.mpr ⟨hjr, hjK⟩) h
            · rw [hx.2 j hjK]
              symm
              refine Finset.sum_eq_zero fun i hi => ?_
              have h1 : j ≠ i := fun h => hjK (h ▸ Finset.mem_of_mem_erase hi)
              have h2 : j ≠ r0 := fun h => hjK (h ▸ hr0)
              simp [pairVec, h1, h2]
          rw [hdecomp]
          exact Submodule.sum_mem E fun i hi =>
            E.smul_mem _ (hKmem i (Finset.mem_of_mem_erase hi) r0 hr0 (Finset.ne_of_mem_erase hi))
        let incl : UK →ₗ[F2] E := Submodule.inclusion hUK_le
        let ψ := (LinearMap.rangeRestrict (A e)).comp incl
        have hψ_inj : Function.Injective ψ := by
          rw [← LinearMap.ker_eq_bot, eq_bot_iff]
          intro x hx
          rw [LinearMap.mem_ker] at hx
          rw [Submodule.mem_bot]
          apply Subtype.ext
          by_contra hx0
          have hge2 := suppF_card_ge_two (mem_codeSub.mp x.2.1) hx0
          have hsub_u : suppF x.1 ⊆ (suppF u.1).filter (fun i => i.val % 3 = e.val) := by
            intro i hi
            have hiK : i ∈ K := by by_contra hiK; exact mem_suppF.mp hi (x.2.2 i hiK)
            have hmod : i.val % 3 = e.val := hKres i hiK
            have hiu : i ∈ suppF u.1 := by
              by_contra hnu
              have h0 := congrFun (congrArg Subtype.val hx) ⟨i, hmod, hnu⟩
              exact mem_suppF.mp hi h0
            exact Finset.mem_filter.mpr ⟨hiu, hmod⟩
          have hle1 := Finset.card_le_card hsub_u
          rw [hu_uniq e] at hle1
          omega
        rw [← hUK_dim]
        exact LinearMap.finrank_le_finrank_of_injective hψ_inj
      exact ⟨A, hcard_le_r, hsum_rk, hclass_rk⟩
    rw [hsplit]
    by_cases ht3eq : t = 3
    · rw [if_pos ht3eq]
      have hle3 : ∀ K ∈ Cs, K.card ≤ 3 := fun K hK => by have := (hCs K hK).2.1; omega
      have hpairs_le6 : pairsE.card ≤ 6 := by
        have hbd := pair_count_le_of_max_size Cs Finset.card 4 3 (by omega) hle3
        omega
      by_cases htr4 : trips.card ≤ 4
      · by_cases hem : W3 = ∅
        · have : W3.card = 0 := by simp [hem]
          omega
        · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hem
          obtain ⟨A, hcard, hrank, _⟩ := hW3_bound_gen u hu
          let d := fun r => Module.finrank F2 (LinearMap.range (A r))
          change 4 ≤ ∑ r, d r at hrank
          rw [Fin.sum_univ_three] at hrank
          have hsome : ∃ r, 2 ≤ d r := by
            by_contra! h; have := h 0; have := h 1; have := h 2; omega
          obtain ⟨r,hr⟩ := hsome
          have hle : d r ≤ 4 := (LinearMap.finrank_range_le (A r)).trans_eq hEdim
          have hb := hcard r
          change W3.card ≤ (d r + 1) * 2 ^ (4 - d r) at hb
          interval_cases hh : d r <;> simp [hh] at hb <;> omega
      · subst t
        rw [← hsplit]
        obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ trips.card)
        choose start hstart using fun x : T => (isTriple_iff_exists_tripVec ht x.val.val).mp
          (Finset.mem_filter.mp (hTsub x.property)).2
        have hi : Function.Injective start := fun x y h => Subtype.ext (Subtype.ext
          ((hstart x).trans ((congrArg (tripVec ht) h).trans (hstart y).symm)))
        let S := Finset.univ.image start
        have hS : S.card = 5 := by
          rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_coe, hTcard]
        let ind := S.orderEmbOfFin hS
        have hmem (j : Fin 5) : tripVec ht (ind j) ∈ P := by
          obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (S.orderEmbOfFin_mem hS j)
          rw [← hx, ← hstart x]; exact x.val.2
        let B : Fin 5 → P := fun j => ⟨tripVec ht (ind j), hmem j⟩
        have hli : LinearIndependent F2 B := by
          apply LinearIndependent.of_comp P.subtype
          exact (tripVec_linearIndependent_of_card_lt ht S (by omega)).comp
            (fun j => (⟨ind j, S.orderEmbOfFin_mem hS j⟩ : S))
            (fun _ _ h => ind.injective (congrArg Subtype.val h))
        let φ : (Fin 5 → F2) →ₗ[F2] P :=
          { toFun := fun f => ∑ j, f j • B j
            map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
            map_smul' := fun k a => by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul] }
        have hinj : Function.Injective φ := by
          rw [← LinearMap.ker_eq_bot, eq_bot_iff]
          intro f hf
          exact funext (Fintype.linearIndependent_iff.mp hli f hf)
        have hbij := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by
          rw [← (Nat.card_eq_fintype_card (α := P)), hcardP]; decide⟩
        let e := Equiv.ofBijective φ hbij
        have he0 : e 0 = p0 := map_zero φ
        have hsum : (∑ x ∈ (Finset.univ : Finset P).erase p0, wt8 (rkC (nbrF x.val))) =
            ∑ f ∈ (Finset.univ : Finset (Fin 5 → F2)).erase 0,
              wt8 (rkC (nbrF (t := 3) (∑ j, f j • tripVec ht (ind j)))) := by
          symm
          apply Finset.sum_nbij' e e.symm
          · intro f hf
            exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hf).1 (e.injective (h.trans he0.symm)), Finset.mem_univ _⟩
          · intro x hx
            exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hx).1 (by rw [← e.apply_symm_apply x, h, he0]), Finset.mem_univ _⟩
          · intro f _; exact e.symm_apply_apply f
          · intro x _; exact e.apply_symm_apply x
          · intro f _
            change _ = wt8 (rkC (nbrF (↑(∑ j, f j • B j) : Fin (3*3) → F2)))
            rw [Submodule.coe_sum]
            rfl
        rw [hsum]
        have hb := fiveTrip_bound (ind 0) (ind 1) (ind 2) (ind 3) (ind 4)
          ⟨ind.strictMono (by decide), ind.strictMono (by decide), ind.strictMono (by decide), ind.strictMono (by decide)⟩
        have hvec : ![ind 0, ind 1, ind 2, ind 3, ind 4] = (ind : Fin 5 → Fin 9) := by
          funext j; fin_cases j <;> rfl
        rw [hvec] at hb
        omega
    · rw [if_neg ht3eq]
      have ht4 : 4 ≤ t := by omega
      have htrips_le5 : trips.card ≤ 5 := by
        by_contra h
        obtain ⟨T, hT, hsz⟩ := Finset.exists_subset_card_eq (by omega : 6 ≤ trips.card)
        have hd := short_triples_card ht T (by omega) (fun x hx => (Finset.mem_filter.mp (hT hx)).2)
        omega
      by_cases hK5 : ∃ K ∈ Cs, 5 ≤ K.card
      · obtain ⟨K, hK, hKge5⟩ := hK5
        obtain ⟨hKne, _, e, hKres, hKmem⟩ := hCs K hK
        have hKle5 : K.card - 1 ≤ 4 := by
          have := Finset.single_le_sum (f := fun C => C.card - 1) (fun _ _ => Nat.zero_le _) hK
          omega
        have hKeq5 : K.card = 5 := by omega
        have hE_iff := evenSub_eq_of_class_size ht hEcode K e hKne hKres hKmem (by omega)
        have hpairs_le10 : pairsE.card ≤ 10 := by
          have hle5 : ∀ C ∈ Cs, C.card ≤ 5 := fun C hC => by
            have := Finset.single_le_sum (f := fun D => D.card - 1) (fun _ _ => Nat.zero_le _) hC
            omega
          have hbd := pair_count_le_of_max_size Cs Finset.card 4 5 (by omega) hle5
          omega
        have heven_sharp : ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 30 + 14 * pairsE.card := by
          have hterm : ∀ x ∈ evenSet, wt8 (rkC (nbrF x.val)) ≤ 2 + if (suppF x.val).card = 2 then 14 else 0 := by
            intro x hx
            have hne0 : x.val ≠ 0 := fun h => Finset.ne_of_mem_erase (Finset.mem_filter.mp hx).1 (Subtype.ext h)
            have hev := (Finset.mem_filter.mp hx).2
            have hge2 := suppF_card_ge_two (hP x.val x.2) hne0
            by_cases hw2 : (suppF x.val).card = 2
            · rw [if_pos hw2, rkC_even_wt2 ht ht3 (hP x.val x.2) hw2, wt8_eq_16 rfl]
            · rw [if_neg hw2, add_zero]
              have hxE : x.val ∈ E := ⟨x.2, (sum_eq_zero_iff_even x.val).mpr hev⟩
              have hres : ∀ i ∈ suppF x.val, i.val % 3 = e.val := fun i hi =>
                hKres i (by by_contra hiK; exact mem_suppF.mp hi (((hE_iff x.val).mp hxE).1 i hiK))
              exact wt8_le_2 (rkC_even_one_res_ge7 ht e hres (by omega))
          have hpair_card_eq : (evenSet.filter (fun x => (suppF x.val).card = 2)).card = pairsE.card := by
            refine Finset.card_bij (fun x hx => ⟨x.1, x.2, (sum_eq_zero_iff_even x.1).mpr
                (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2⟩)
              (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
              (fun a _ b _ h => Subtype.ext (congrArg (fun y : E => y.val) h))
              (fun y hy => ⟨⟨y.1, y.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨fun h => by
                  have h0 : y.1 = 0 := congrArg Subtype.val h
                  have := (Finset.mem_filter.mp hy).2
                  rw [h0] at this; simp [suppF] at this, Finset.mem_univ _⟩,
                 hEeven y.1 y.2⟩, (Finset.mem_filter.mp hy).2⟩, rfl⟩)
          calc ∑ x ∈ evenSet, wt8 (rkC (nbrF x.val))
              ≤ ∑ x ∈ evenSet, (2 + if (suppF x.val).card = 2 then 14 else 0) := Finset.sum_le_sum hterm
            _ = 2 * evenSet.card + 14 * (evenSet.filter (fun x => (suppF x.val).card = 2)).card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.sum_filter,
                    Finset.sum_const, smul_eq_mul]; ring
            _ = 30 + 14 * pairsE.card := by rw [heven_card, hpair_card_eq]
        by_cases hW3e : W3 = ∅
        · have hW30 : W3.card = 0 := by rw [hW3e]; simp
          have htr0 : trips.card = 0 := by
            have := Finset.card_le_card htrips_sub_W3; omega
          omega
        · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hW3e
          obtain ⟨A, hcard_le_r, _, hclass_rk⟩ := hW3_bound_gen u hu
          have hde_ge4 : 4 ≤ Module.finrank F2 (LinearMap.range (A e)) := by
            have := hclass_rk K e hKne hKres hKmem; omega
          have hde_le4 : Module.finrank F2 (LinearMap.range (A e)) ≤ 4 := by
            have := LinearMap.finrank_range_le (A e); omega
          have hde4 : Module.finrank F2 (LinearMap.range (A e)) = 4 := by omega
          have hW3_le5 : W3.card ≤ 5 := by
            have := hcard_le_r e; rw [hde4] at this; simpa using this
          have htrips_le2 : trips.card ≤ 2 := by
            by_cases htre : trips = ∅
            · rw [htre]; simp
            · obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.mpr htre
              obtain ⟨s0, hs0⟩ := (isTriple_iff_exists_tripVec ht t0.1).mp (Finset.mem_filter.mp ht0).2
              have hsame_other : ∀ x ∈ trips, ∀ i : Fin (3 * t), i.val % 3 ≠ e.val → x.1 i = t0.1 i := by
                intro x hx i hi
                have hdiffE : x.1 + t0.1 ∈ E := ⟨P.add_mem x.2 t0.2, by
                  have h1 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even x.1).not.mpr (by
                    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2; omega))
                  have h2 := z2_eq_one_of_ne_zero ((sum_eq_zero_iff_even t0.1).not.mpr (by
                    have := (Finset.mem_filter.mp (Finset.mem_filter.mp ht0).1).2; omega))
                  simp only [Pi.add_apply, Finset.sum_add_distrib, h1, h2]; exact z2_one_add_one⟩
                have hiK : i ∉ K := fun hiK => hi (hKres i hiK)
                have h0 := ((hE_iff _).mp hdiffE).1 i hiK
                simp only [Pi.add_apply] at h0
                have := z2_add_self (t0.1 i); linear_combination h0 - this
              have ha_ex : ∃ a : Fin (3 * t), a.val % 3 = (e.val + 1) % 3 ∧ t0.1 a = 1 := by
                obtain ⟨a, haS, ham⟩ := codeP_odd_hits_all_res (hP t0.1 t0.2)
                  (Finset.mem_filter.mp (Finset.mem_filter.mp ht0).1).2 ⟨(e.val + 1) % 3, Nat.mod_lt _ (by omega)⟩
                exact ⟨a, ham, z2_eq_one_of_ne_zero (mem_suppF.mp haS)⟩
              have hb_ex : ∃ b : Fin (3 * t), b.val % 3 = (e.val + 2) % 3 ∧ t0.1 b = 1 := by
                obtain ⟨b, hbS, hbm⟩ := codeP_odd_hits_all_res (hP t0.1 t0.2)
                  (Finset.mem_filter.mp (Finset.mem_filter.mp ht0).1).2 ⟨(e.val + 2) % 3, Nat.mod_lt _ (by omega)⟩
                exact ⟨b, hbm, z2_eq_one_of_ne_zero (mem_suppF.mp hbS)⟩
              obtain ⟨a, ha_mod, ha1⟩ := ha_ex
              obtain ⟨b, hb_mod, hb1⟩ := hb_ex
              have hsub2 : trips.image Subtype.val ⊆ {tripVec ht a, tripVec ht (prv a), tripVec ht b} := by
                intro v hv
                obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
                obtain ⟨s, hs⟩ := (isTriple_iff_exists_tripVec ht x.1).mp (Finset.mem_filter.mp hx).2
                have hxa : x.1 a = 1 := by
                  rw [hsame_other x hx a (by have := e.isLt; omega), ha1]
                have hxb : x.1 b = 1 := by
                  rw [hsame_other x hx b (by have := e.isLt; omega), hb1]
                have ha_in : a ∈ suppF (tripVec ht s) := mem_suppF.mpr (by rw [← hs, hxa]; exact z2_one_ne_zero)
                rw [suppF_tripVec ht s, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha_in
                have hb_in : b ∈ suppF (tripVec ht s) := mem_suppF.mpr (by rw [← hs, hxb]; exact z2_one_ne_zero)
                rw [suppF_tripVec ht s, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hb_in
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases ha_in with rfl | h | h
                · exact Or.inl hs
                · have hsp : s = prv a := by rw [h, prv_nxt ht]
                  exact Or.inr (Or.inl (hsp ▸ hs))
                · rcases hb_in with rfl | hb | hb
                  · exact Or.inr (Or.inr hs)
                  · exfalso; have h1 := nxt_mod3 ht s; have h2 := nxt_mod3 ht (nxt ht s)
                    rw [← h] at h2; rw [← hb] at h1; have := e.isLt; omega
                  · exfalso; have h1 := congrArg (fun z : Fin (3 * t) => z.val % 3) (h.trans hb.symm)
                    have := e.isLt; omega
              have hnot_both : ¬ (tripVec ht b ∈ trips.image Subtype.val ∧
                  (tripVec ht a ∈ trips.image Subtype.val ∨ tripVec ht (prv a) ∈ trips.image Subtype.val)) := by
                rintro ⟨hb_in, ha_in⟩
                have ha_b : a ∈ suppF (tripVec ht b) := by
                  obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hb_in
                  have hxa : x.1 a = 1 := by rw [hsame_other x hx a (by have := e.isLt; omega), ha1]
                  exact mem_suppF.mpr (by rw [← hxv, hxa]; exact z2_one_ne_zero)
                rw [suppF_tripVec ht b, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha_b
                have ha_eq : a = nxt ht (nxt ht b) := by
                  rcases ha_b with h | h | h
                  · exfalso; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; have := e.isLt; omega
                  · exfalso; have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
                    rw [nxt_mod3 ht] at this; have := e.isLt; omega
                  · exact h
                rcases ha_in with ha_in | hpa_in
                · have hb_a : b ∈ suppF (tripVec ht a) := by
                    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp ha_in
                    have hxb : x.1 b = 1 := by rw [hsame_other x hx b (by have := e.isLt; omega), hb1]
                    exact mem_suppF.mpr (by rw [← hxv, hxb]; exact z2_one_ne_zero)
                  rw [suppF_tripVec ht a, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hb_a
                  rcases hb_a with h | h | h
                  · have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; have := e.isLt; omega
                  · have h3 : nxt ht (nxt ht (nxt ht b)) = b := by rw [← ha_eq, ← h]
                    have hv := congrArg Fin.val h3
                    have h1 := nxt_val ht b; have h2 := nxt_val ht (nxt ht b)
                    have h3' := nxt_val ht (nxt ht (nxt ht b))
                    have := b.isLt; have := (nxt ht b).isLt; have := (nxt ht (nxt ht b)).isLt
                    split_ifs at h1 h2 h3' <;> omega
                  · have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
                    have h1 := nxt_mod3 ht a; have h2 := nxt_mod3 ht (nxt ht a)
                    have := e.isLt; omega
                · have hb_pa : b ∈ suppF (tripVec ht (prv a)) := by
                    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hpa_in
                    have hxb : x.1 b = 1 := by rw [hsame_other x hx b (by have := e.isLt; omega), hb1]
                    exact mem_suppF.mpr (by rw [← hxv, hxb]; exact z2_one_ne_zero)
                  rw [suppF_tripVec ht (prv a), nxt_prv ht, Finset.mem_insert, Finset.mem_insert,
                      Finset.mem_singleton] at hb_pa
                  rcases hb_pa with h | h | h
                  · have := congrArg (fun z : Fin (3 * t) => z.val % 3) h
                    rw [prv_mod3] at this; have := e.isLt; omega
                  · have := congrArg (fun z : Fin (3 * t) => z.val % 3) h; have := e.isLt; omega
                  · have h3 : nxt ht (nxt ht (nxt ht b)) = b := by rw [← ha_eq, ← h]
                    have hv := congrArg Fin.val h3
                    have h1 := nxt_val ht b; have h2 := nxt_val ht (nxt ht b)
                    have h3' := nxt_val ht (nxt ht (nxt ht b))
                    have := b.isLt; have := (nxt ht b).isLt; have := (nxt ht (nxt ht b)).isLt
                    split_ifs at h1 h2 h3' <;> omega
              have hcard_img : (trips.image Subtype.val).card ≤ 2 := by
                by_cases hbm : tripVec ht b ∈ trips.image Subtype.val
                · have hss : trips.image Subtype.val ⊆ {tripVec ht b} := by
                    intro v hv
                    have := hsub2 hv
                    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
                    rcases this with rfl | rfl | rfl
                    · exact absurd ⟨hbm, Or.inl hv⟩ hnot_both
                    · exact absurd ⟨hbm, Or.inr hv⟩ hnot_both
                    · rfl
                  exact (Finset.card_le_card hss).trans (by simp)
                · have hss : trips.image Subtype.val ⊆ {tripVec ht a, tripVec ht (prv a)} := by
                    intro v hv
                    have := hsub2 hv
                    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
                    rcases this with rfl | rfl | rfl
                    · exact Or.inl rfl
                    · exact Or.inr rfl
                    · exact absurd hv hbm
                  exact (Finset.card_le_card hss).trans (Finset.card_le_two)
              rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hcard_img
          omega
      · push Not at hK5
        by_cases hK4 : ∃ K ∈ Cs, K.card = 4
        · obtain ⟨K, hK, hK4eq⟩ := hK4
          obtain ⟨hKne, _, e, hKres, hKmem⟩ := hCs K hK
          have hpairs_le7 : pairsE.card ≤ 7 := by
            have hrem_sum : ∑ C ∈ Cs.erase K, (C.card - 1) ≤ 1 := by
              have := Finset.add_sum_erase Cs (fun C => C.card - 1) hK; omega
            have hrem_le2 : ∀ C ∈ Cs.erase K, C.card ≤ 2 := fun C hC => by
              have := Finset.single_le_sum (f := fun D => D.card - 1) (fun _ _ => Nat.zero_le _) hC
              omega
            have hrem_pairs := pair_count_le_of_max_size (Cs.erase K) Finset.card 1 2 hrem_sum hrem_le2
            have htot := Finset.add_sum_erase Cs (fun C => C.card * (C.card - 1)) hK
            change K.card * (K.card - 1) + _ = _ at htot
            rw [hK4eq] at htot
            omega
          by_cases hW3e : W3 = ∅
          · have hW30 : W3.card = 0 := by rw [hW3e]; simp
            have htr0 : trips.card = 0 := by have := Finset.card_le_card htrips_sub_W3; omega
            omega
          · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hW3e
            obtain ⟨A, hcard_le_r, _, hclass_rk⟩ := hW3_bound_gen u hu
            have hde_ge3 : 3 ≤ Module.finrank F2 (LinearMap.range (A e)) := by
              have := hclass_rk K e hKne hKres hKmem; omega
            have hde_le4 : Module.finrank F2 (LinearMap.range (A e)) ≤ 4 := by
              have := LinearMap.finrank_range_le (A e); omega
            have hW3_le8 : W3.card ≤ 8 := by
              have h := hcard_le_r e
              have h34 : Module.finrank F2 (LinearMap.range (A e)) = 3 ∨
                  Module.finrank F2 (LinearMap.range (A e)) = 4 := by omega
              rcases h34 with h3 | h3 <;> rw [h3] at h <;> norm_num at h <;> omega
            omega
        · push Not at hK4
          have hle3 : ∀ C ∈ Cs, C.card ≤ 3 := fun C hC => by
            have h1 := hK5 C hC; have h2 := hK4 C hC; omega
          have hpairs_le6 : pairsE.card ≤ 6 := by
            have hbd := pair_count_le_of_max_size Cs Finset.card 4 3 (by omega) hle3
            omega
          by_cases hW3e : W3 = ∅
          · have hW30 : W3.card = 0 := by rw [hW3e]; simp
            have htr0 : trips.card = 0 := by have := Finset.card_le_card htrips_sub_W3; omega
            omega
          · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hW3e
            obtain ⟨A, hcard_le_r, hsum_rk, _⟩ := hW3_bound_gen u hu
            rw [Fin.sum_univ_three] at hsum_rk
            have hex2 : ∃ r : Fin 3, 2 ≤ Module.finrank F2 (LinearMap.range (A r)) := by
              by_contra hno; push Not at hno
              have h0 := hno 0; have h1 := hno 1; have h2 := hno 2; omega
            obtain ⟨r, hr2⟩ := hex2
            have hr_le4 : Module.finrank F2 (LinearMap.range (A r)) ≤ 4 := by
              have := LinearMap.finrank_range_le (A r); omega
            have hW3_le12 : W3.card ≤ 12 := by
              have h := hcard_le_r r
              have h234 : Module.finrank F2 (LinearMap.range (A r)) = 2 ∨
                  Module.finrank F2 (LinearMap.range (A r)) = 3 ∨
                  Module.finrank F2 (LinearMap.range (A r)) = 4 := by omega
              rcases h234 with h2 | h3 | h4
              · rw [h2] at h; norm_num at h; omega
              · rw [h3] at h; norm_num at h; omega
              · rw [h4] at h; norm_num at h; omega
            omega

end small_side

section main_proof

lemma formP_exact {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hform : formP ht P Q) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} =
      (if t = 2 then 416 else if t = 3 then 348 else if t = 4 then 354 else 353) *
        (Nat.card P * Nat.card Q) := by
  rcases hform with ⟨hQ, ⟨ht2eq, hP⟩ | ⟨ht3eq, s, hP⟩ | ⟨ht4, T, e, hTcard, hTres, hP⟩⟩
  · rw [if_pos ht2eq]
    exact top_exact_t2 ht ht2eq hQ hP
  · rw [if_neg (by omega), if_pos ht3eq]
    exact top_exact_t3 ht ht3eq hQ s hP
  · rw [if_neg (by omega), if_neg (by omega)]
    exact top_exact_ge4 ht ht4 hQ T e hTcard hTres hP

lemma main_wlog {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t)
    {P Q : Submodule F2 (Fin (3 * t) → F2)}
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q)
    (hle : Module.finrank F2 P ≤ Module.finrank F2 Q)
    (hnt : ¬ (formP ht P Q ∨ formP ht Q P)) :
    2048 * Nat.card {w : P × Q // hitP ht w.1.val w.2.val} ≤
      (if t = 2 then 400 else if t = 3 then 344 else 352) * (Nat.card P * Nat.card Q) := by
  have hPsub : P ≤ codeSub t := fun x hx => mem_codeSub.mpr (hP x hx)
  have hQsub : Q ≤ codeSub t := fun y hy => mem_codeSub.mpr (hQ y hy)
  have hdimQ_le : Module.finrank F2 Q ≤ 3 * t - 2 := by
    have := Submodule.finrank_mono hQsub
    rwa [finrank_codeSub ht] at this
  have hdimP_ge3 : 3 ≤ Module.finrank F2 P := by omega
  by_cases ht2eq : t = 2
  · rw [if_pos ht2eq]
    exact t2_not_top ht ht2eq hP hQ hdim hle (fun h => hnt (Or.inl h))
  · rw [if_neg ht2eq]
    have ht3 : 3 ≤ t := by omega
    by_cases hP3 : Module.finrank F2 P = 3
    · exact dim3_not_top ht ht3 hP hQ hdim hP3 (fun h => hnt (Or.inl h))
    · by_cases hP4 : Module.finrank F2 P = 4
      · have hbd := dim4_bound ht ht3 hP hQ hdim hP4
        refine hbd.trans (Nat.mul_le_mul_right _ ?_)
        split_ifs <;> omega
      · by_cases hP5 : Module.finrank F2 P = 5
        · exact dim5_bound ht ht3 hP hQ hdim hP5
        · have hP6 : 6 ≤ Module.finrank F2 P := by omega
          have hQ6 : 6 ≤ Module.finrank F2 Q := by omega
          have hbd := two_large_lanes ht ht3 hP hQ hdim hP6 hQ6
          refine hbd.trans (Nat.mul_le_mul_right _ ?_)
          split_ifs <;> omega

lemma main_theorem (t : ℕ) (ht : 0 < t) (ht2 : 2 ≤ t)
    (P Q : Submodule F2 (Fin (3 * t) → F2))
    (hP : ∀ x ∈ P, codeP t x) (hQ : ∀ y ∈ Q, codeP t y)
    (hdim : 3 * t + 1 ≤ Module.finrank F2 P + Module.finrank F2 Q) :
    let hits := Nat.card {w : P × Q // hitP ht w.1.val w.2.val}
    let size := Nat.card P * Nat.card Q
    let top := formP ht P Q ∨ formP ht Q P
    let num := if t = 2 then 416 else if t = 3 then 348 else if t = 4 then 354 else 353
    let nextBound := if t = 2 then 400 else if t = 3 then 344 else 352
    (top → 2048 * hits = num * size) ∧ (¬ top → 2048 * hits ≤ nextBound * size) := by
  have hrev_pair : ∀ (A B : Submodule F2 (Fin (3 * t) → F2)),
      (∀ x ∈ A, codeP t x) → (∀ y ∈ B, codeP t y) →
      let A' := Submodule.map (revEquiv t).toLinearMap B
      let B' := Submodule.map (revEquiv t).toLinearMap A
      Nat.card {w : A' × B' // hitP ht w.1.val w.2.val} =
        Nat.card {w : A × B // hitP ht w.1.val w.2.val} ∧
      Nat.card A' * Nat.card B' = Nat.card A * Nat.card B ∧
      Module.finrank F2 A' = Module.finrank F2 B ∧
      Module.finrank F2 B' = Module.finrank F2 A ∧
      (∀ x ∈ A', codeP t x) ∧ (∀ y ∈ B', codeP t y) ∧
      (formP ht A' B' ↔ formP ht B A) ∧ (formP ht B' A' ↔ formP ht A B) := by
    intro A B hA hB A' B'
    have hrev2 : ∀ x, revEquiv t (revEquiv t x) = x := (revEquiv t).left_inv
    have hmemA' : ∀ x, x ∈ A' ↔ revEquiv t x ∈ B := fun x =>
      ⟨fun ⟨w, hw, h⟩ => by rw [← h, show (revEquiv t).toLinearMap w = revEquiv t w from rfl, hrev2]; exact hw,
       fun h => ⟨revEquiv t x, h, hrev2 x⟩⟩
    have hmemB' : ∀ x, x ∈ B' ↔ revEquiv t x ∈ A := fun x =>
      ⟨fun ⟨w, hw, h⟩ => by rw [← h, show (revEquiv t).toLinearMap w = revEquiv t w from rfl, hrev2]; exact hw,
       fun h => ⟨revEquiv t x, h, hrev2 x⟩⟩
    let eAB : {w : A' × B' // hitP ht w.1.val w.2.val} ≃ {w : A × B // hitP ht w.1.val w.2.val} :=
      { toFun := fun w => ⟨(⟨revEquiv t w.1.2.1, (hmemB' _).mp w.1.2.2⟩,
            ⟨revEquiv t w.1.1.1, (hmemA' _).mp w.1.1.2⟩), by
          have h := (rev_hitP ht (revEquiv t w.1.2.1) (revEquiv t w.1.1.1)).mp
          apply h; simpa only [hrev2] using w.2⟩
        invFun := fun w => ⟨(⟨revEquiv t w.1.2.1, (hmemA' _).mpr (by simpa [hrev2] using w.1.2.2)⟩,
            ⟨revEquiv t w.1.1.1, (hmemB' _).mpr (by simpa [hrev2] using w.1.1.2)⟩),
          (rev_hitP ht w.1.1.1 w.1.2.1).mpr w.2⟩
        left_inv := fun w => by ext i <;> simp [hrev2]
        right_inv := fun w => by ext i <;> simp [hrev2] }
    have hdimA' : Module.finrank F2 A' = Module.finrank F2 B :=
      ((revEquiv t).submoduleMap B).finrank_eq.symm
    have hdimB' : Module.finrank F2 B' = Module.finrank F2 A :=
      ((revEquiv t).submoduleMap A).finrank_eq.symm
    refine ⟨Nat.card_congr eAB, ?_, hdimA', hdimB', ?_, ?_, formP_rev ht B A, formP_rev ht A B⟩
    · rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, card_eq_two_pow_finrank,
          card_eq_two_pow_finrank, hdimA', hdimB', mul_comm]
    · intro x hx; exact rev_codeP.mp (hB _ ((hmemA' x).mp hx))
    · intro y hy; exact rev_codeP.mp (hA _ ((hmemB' y).mp hy))
  constructor
  · rintro (hf | hf)
    · exact formP_exact ht ht2 hf
    · obtain ⟨hhits, hsize, _, _, _, _, hrev1, _⟩ := hrev_pair P Q hP hQ
      rw [← hhits, ← hsize]
      exact formP_exact ht ht2 (hrev1.mpr hf)
  · intro hnt
    rcases le_total (Module.finrank F2 P) (Module.finrank F2 Q) with hle | hle
    · exact main_wlog ht ht2 hP hQ hdim hle hnt
    · obtain ⟨hhits, hsize, hd1, hd2, hP', hQ', hrev1, hrev2⟩ := hrev_pair P Q hP hQ
      rw [← hhits, ← hsize]
      exact main_wlog ht ht2 hP' hQ' (by omega) (by omega)
        (fun h => hnt (h.elim (fun h1 => Or.inr (hrev1.mp h1)) (fun h2 => Or.inl (hrev2.mp h2))))

end main_proof

end PEqualNP.Outside.L_lib_1082

theorem PEqualNP.Outside.L_lib_1082 : (∀ (t : ℕ) (ht : 0 < t), 2 ≤ t →
  let F := ZMod 2
  let n := 3*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
  let code := fun (x : W) => ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
  let form := fun (U V : Submodule F W) =>
    (∀ y, y ∈ V ↔ code y) ∧
      ((t = 2 ∧ ∀ x : W, x ∈ U ↔ ∀ i, x i = x (ix (i.val+3))) ∨
       (t = 3 ∧ ∃ s : Fin n, ∀ x : W, x ∈ U ↔ code x ∧ ∀ i, x i ≠ 0 →
          i.val % 3 = s.val % 3 ∨ i = ix (s.val+1) ∨ i = ix (s.val+2)) ∨
       (4 ≤ t ∧ ∃ (T : Finset (Fin n)) (e : Fin 3),
      T.card = 4 ∧ (∀ i ∈ T, i.val % 3 = e.val) ∧ ∀ x : W,
        x ∈ U ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0))
  ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
    n+1 ≤ Module.finrank F P + Module.finrank F Q →
    let hits := Nat.card {w : P × Q // ∀ i : Fin n,
      w.1.val i * w.2.val i = 0 ∧ w.1.val (ix (i.val+1)) * w.2.val i = 0}
    let size := Nat.card P * Nat.card Q
    let top := form P Q ∨ form Q P
    let num := if t = 2 then 416 else if t = 3 then 348 else if t = 4 then 354 else 353
    let nextBound := if t = 2 then 400 else if t = 3 then 344 else 352
    (top → 2048*hits = num*size) ∧ (¬ top → 2048*hits ≤ nextBound*size)) := by
  intro t ht ht2 F n W ix code form P Q hP hQ hdim
  exact PEqualNP.Outside.L_lib_1082.main_theorem t ht ht2 P Q hP hQ hdim

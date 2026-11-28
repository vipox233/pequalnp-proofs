import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1167_aux

lemma xor16_lt (a b : Fin 16) : (a.val ^^^ b.val) < 16 := by revert a b; decide

def xor16 (a b : Fin 16) : Fin 16 := ⟨a.val ^^^ b.val, xor16_lt a b⟩

lemma xor16_comm (a b : Fin 16) : xor16 a b = xor16 b a := by revert a b; decide
lemma xor16_invol (a b : Fin 16) : xor16 (xor16 a b) b = a := by revert a b; decide

def pop4 (w : Nat) : Nat :=
  (w &&& 1) + ((w >>> 1) &&& 1) + ((w >>> 2) &&& 1) + ((w >>> 3) &&& 1)

def chi1 (u x : Fin 16) : ZMod 11 :=
  if pop4 (u.val &&& x.val) % 2 = 0 then 1 else -1

lemma chi1_xor (u a b : Fin 16) : chi1 u (xor16 a b) = chi1 u a * chi1 u b := by
  revert u a b; decide

lemma chi1_comm (u x : Fin 16) : chi1 u x = chi1 x u := by
  revert u x; decide

lemma chi1_orth (u v : Fin 16) :
    (Finset.univ : Finset (Fin 16)).sum (fun x => chi1 u x * chi1 v x) =
    if u = v then (16 : ZMod 11) else 0 := by
  revert u v; decide

def pass1 (flag : Bool) (w : Nat) : Bool :=
  ((w &&& 3) != 0) && ((w &&& 13) != (if flag then 1 else 0))

def pass1Ind (flag : Bool) (w : Fin 16) : ZMod 11 :=
  if pass1 flag w.val then 1 else 0

def hat1 (flag : Bool) (u : Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin 16)).sum (fun w => chi1 u w * pass1Ind flag w)

def isOnly1 (u : Fin 16) : Bool := u.val == 0

def isOnly0 (u : Fin 16) : Bool :=
  u.val == 6 || u.val == 7 || u.val == 10 || u.val == 11 || u.val == 14 || u.val == 15

def isBoth (u : Fin 16) : Bool := !isOnly1 u && !isOnly0 u

lemma hat1_false_ne_zero (u : Fin 16) : hat1 false u ≠ 0 ↔ isOnly1 u = false := by
  revert u; decide

lemma hat1_true_ne_zero (u : Fin 16) : hat1 true u ≠ 0 ↔ isOnly0 u = false := by
  revert u; decide

def only1Set : Finset (Fin 16) := (Finset.univ : Finset (Fin 16)).filter (fun u => isOnly1 u = true)
def only0Set : Finset (Fin 16) := (Finset.univ : Finset (Fin 16)).filter (fun u => isOnly0 u = true)
def bothSet : Finset (Fin 16) := (Finset.univ : Finset (Fin 16)).filter (fun u => isBoth u = true)

lemma card_only1Set : only1Set.card = 1 := by decide
lemma card_only0Set : only0Set.card = 6 := by decide
lemma card_bothSet : bothSet.card = 9 := by decide

lemma class_excl (u : Fin 16) :
    (isOnly1 u = true ∧ isOnly0 u = false ∧ isBoth u = false) ∨
    (isOnly1 u = false ∧ isOnly0 u = true ∧ isBoth u = false) ∨
    (isOnly1 u = false ∧ isOnly0 u = false ∧ isBoth u = true) := by
  revert u; decide

def xorW {r : Nat} (x y : Fin r → Fin 16) : Fin r → Fin 16 :=
  fun j => xor16 (x j) (y j)

lemma xorW_invol {r : Nat} (x y : Fin r → Fin 16) : xorW (xorW x y) y = x := by
  funext j; exact xor16_invol (x j) (y j)

lemma xorW_comm {r : Nat} (x y : Fin r → Fin 16) : xorW x y = xorW y x := by
  funext j; exact xor16_comm (x j) (y j)

def chiW {r : Nat} (u x : Fin r → Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin r)).prod (fun j => chi1 (u j) (x j))

lemma chiW_xor {r : Nat} (u x y : Fin r → Fin 16) :
    chiW u (xorW x y) = chiW u x * chiW u y := by
  dsimp [chiW, xorW]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => chi1_xor (u j) (x j) (y j)

lemma chiW_comm {r : Nat} (u x : Fin r → Fin 16) : chiW u x = chiW x u := by
  dsimp [chiW]
  refine Finset.prod_congr rfl fun j _ => chi1_comm (u j) (x j)

lemma chiW_orth {r : Nat} (u v : Fin r → Fin 16) :
    (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => chiW u x * chiW v x) =
    if u = v then (16 : ZMod 11) ^ r else 0 := by
  have h1 : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => chiW u x * chiW v x) =
      (Finset.univ : Finset (Fin r)).prod (fun j =>
        (Finset.univ : Finset (Fin 16)).sum (fun a => chi1 (u j) a * chi1 (v j) a)) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [chiW]
    rw [← Finset.prod_mul_distrib]
  rw [h1]
  have h2 : (Finset.univ : Finset (Fin r)).prod (fun j =>
      (Finset.univ : Finset (Fin 16)).sum (fun a => chi1 (u j) a * chi1 (v j) a)) =
      (Finset.univ : Finset (Fin r)).prod (fun j => if u j = v j then (16 : ZMod 11) else 0) :=
    Finset.prod_congr rfl fun j _ => chi1_orth (u j) (v j)
  rw [h2]
  split_ifs with huv
  · subst huv
    simp
  · have hex : ∃ j : Fin r, u j ≠ v j := by
      by_contra hall
      push Not at hall
      exact huv (funext hall)
    rcases hex with ⟨j, hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

def walsh {r : Nat} (d : (Fin r → Fin 16) → ZMod 11) (u : Fin r → Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => chiW u x * d x)

lemma walsh_walsh {r : Nat} (d : (Fin r → Fin 16) → ZMod 11) (x : Fin r → Fin 16) :
    walsh (walsh d) x = (16 : ZMod 11) ^ r * d x := by
  dsimp [walsh]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ y : Fin r → Fin 16,
      (Finset.univ : Finset (Fin r → Fin 16)).sum (fun u => chiW x u * (chiW u y * d y)) =
      (if x = y then (16 : ZMod 11) ^ r else 0) * d y := by
    intro y
    calc
      (Finset.univ : Finset (Fin r → Fin 16)).sum (fun u => chiW x u * (chiW u y * d y))
          = (Finset.univ : Finset (Fin r → Fin 16)).sum (fun u => (chiW x u * chiW y u) * d y) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [chiW_comm u y, mul_assoc]
      _ = ((Finset.univ : Finset (Fin r → Fin 16)).sum (fun u => chiW x u * chiW y u)) * d y := by
              rw [← Finset.sum_mul]
      _ = (if x = y then (16 : ZMod 11) ^ r else 0) * d y := by rw [chiW_orth x y]
  simp_rw [hinner]
  simp

lemma sixteen_ne_zero_zmod11 : (16 : ZMod 11) ≠ 0 := by decide

lemma walsh_inv {r : Nat} (d : (Fin r → Fin 16) → ZMod 11) :
    (fun x => ((16 : ZMod 11) ^ r)⁻¹ * walsh (walsh d) x) = d := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hne : (16 : ZMod 11) ^ r ≠ 0 := pow_ne_zero r sixteen_ne_zero_zmod11
  funext x
  rw [walsh_walsh, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

lemma walsh_bijective {r : Nat} :
    Function.Bijective (walsh (r := r)) := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hne : (16 : ZMod 11) ^ r ≠ 0 := pow_ne_zero r sixteen_ne_zero_zmod11
  constructor
  · intro d₁ d₂ h
    have h1 := congrArg (fun f x => ((16 : ZMod 11) ^ r)⁻¹ * walsh f x) h
    rwa [walsh_inv d₁, walsh_inv d₂] at h1
  · intro f
    refine ⟨fun x => ((16 : ZMod 11) ^ r)⁻¹ * walsh f x, ?_⟩
    funext u
    dsimp [walsh]
    calc
      (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => chiW u x * (((16 : ZMod 11) ^ r)⁻¹ * walsh f x))
          = ((16 : ZMod 11) ^ r)⁻¹ * (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => chiW u x * walsh f x) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => by ring
      _ = ((16 : ZMod 11) ^ r)⁻¹ * walsh (walsh f) u := rfl
      _ = f u := by rw [walsh_walsh, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

noncomputable def passW {r : Nat} (e : Finset (Fin r)) (z x : Fin r → Fin 16) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))

def passWInd {r : Nat} (e : Finset (Fin r)) (w : Fin r → Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin r)).prod (fun j => pass1Ind (decide (j ∈ e)) (w j))

lemma passW_eq_prod {r : Nat} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    (if passW e z x = true then (1 : ZMod 11) else 0) = passWInd e (xorW z x) := by
  by_cases hp : passW e z x = true
  · rw [if_pos hp]
    dsimp [passW] at hp
    dsimp [passWInd]
    rw [List.all_eq_true] at hp
    symm
    refine Finset.prod_eq_one fun j _ => ?_
    have hj := hp j (Finset.mem_toList.mpr (Finset.mem_univ j))
    have hj' : pass1 (decide (j ∈ e)) (xor16 (z j) (x j)).val = true := by
      dsimp [pass1, xor16]
      by_cases hje : j ∈ e <;> simp [hje] at hj ⊢ <;> exact hj
    simp [pass1Ind, xorW, hj']
  · rw [if_neg hp]
    dsimp [passW] at hp
    dsimp [passWInd]
    have hnot : ¬ ∀ j : Fin r,
        (((z j).val ^^^ (x j).val) &&& 3) != 0 ∧
        (((z j).val ^^^ (x j).val) &&& 13) != (if j ∈ e then 1 else 0) := by
      intro hall
      apply hp
      rw [List.all_eq_true]
      intro j _
      have := hall j
      simp [this.1, this.2]
    push Not at hnot
    rcases hnot with ⟨j, hj⟩
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    have hfalse : pass1 (decide (j ∈ e)) (xor16 (z j) (x j)).val = false := by
      dsimp [pass1, xor16]
      by_cases h1 : ((((z j).val ^^^ (x j).val) &&& 3) != 0) = true
      · have h2 := hj h1
        have h2f : ((((z j).val ^^^ (x j).val) &&& 13) != (if j ∈ e then 1 else 0)) = false :=
          Bool.eq_false_iff.mpr h2
        by_cases hje : j ∈ e <;> simp [hje, h1] at h2f ⊢ <;> exact h2f
      · have h1f : ((((z j).val ^^^ (x j).val) &&& 3) != 0) = false := Bool.eq_false_iff.mpr h1
        simp [h1f]
    simp [pass1Ind, xorW, hfalse]

def hatPass {r : Nat} (e : Finset (Fin r)) (u : Fin r → Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin r)).prod (fun j => hat1 (decide (j ∈ e)) (u j))

def convW {r : Nat} (e : Finset (Fin r)) (d : (Fin r → Fin 16) → ZMod 11)
    (z : Fin r → Fin 16) : ZMod 11 :=
  (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => passWInd e (xorW z x) * d x)

lemma walsh_convW {r : Nat} (e : Finset (Fin r)) (d : (Fin r → Fin 16) → ZMod 11)
    (u : Fin r → Fin 16) :
    walsh (convW e d) u = hatPass e u * walsh d u := by
  dsimp [walsh, convW]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ x : Fin r → Fin 16,
      (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z => chiW u z * (passWInd e (xorW z x) * d x)) =
      hatPass e u * (chiW u x * d x) := by
    intro x
    have hbij : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z => chiW u z * passWInd e (xorW z x)) =
        (Finset.univ : Finset (Fin r → Fin 16)).sum (fun w => chiW u (xorW w x) * passWInd e w) := by
      refine Finset.sum_nbij (fun z => xorW z x) ?_ ?_ ?_ ?_
      · intro z _; exact Finset.mem_univ _
      · intro z₁ _ z₂ _ h
        have := congrArg (fun t => xorW t x) h
        rwa [xorW_invol, xorW_invol] at this
      · intro w _
        exact ⟨xorW w x, Finset.mem_univ _, xorW_invol w x⟩
      · intro z _
        rw [xorW_invol]
    have hprod : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun w => chiW u w * passWInd e w) =
        hatPass e u := by
      dsimp [hatPass, hat1]
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      dsimp [chiW, passWInd]
      rw [← Finset.prod_mul_distrib]
    calc
      (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z => chiW u z * (passWInd e (xorW z x) * d x))
          = ((Finset.univ : Finset (Fin r → Fin 16)).sum (fun z => chiW u z * passWInd e (xorW z x))) * d x := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun z _ => by ring
      _ = ((Finset.univ : Finset (Fin r → Fin 16)).sum (fun w => chiW u (xorW w x) * passWInd e w)) * d x := by
              rw [hbij]
      _ = (chiW u x * (Finset.univ : Finset (Fin r → Fin 16)).sum (fun w => chiW u w * passWInd e w)) * d x := by
              congr 1
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [chiW_xor]; ring
      _ = hatPass e u * (chiW u x * d x) := by rw [hprod]; ring
  simp_rw [hinner]

def toZ {r : Nat} (d : (Fin r → Fin 16) → Fin 11) : (Fin r → Fin 16) → ZMod 11 :=
  fun x => ((d x).val : ZMod 11)

def fromZ {r : Nat} (f : (Fin r → Fin 16) → ZMod 11) : (Fin r → Fin 16) → Fin 11 :=
  fun x => ⟨(f x).val, ZMod.val_lt (f x)⟩

lemma toZ_fromZ {r : Nat} (f : (Fin r → Fin 16) → ZMod 11) : toZ (fromZ f) = f := by
  funext x
  dsimp [toZ, fromZ]
  exact ZMod.natCast_zmod_val (f x)

lemma fromZ_toZ {r : Nat} (d : (Fin r → Fin 16) → Fin 11) : fromZ (toZ d) = d := by
  funext x
  apply Fin.ext
  dsimp [toZ, fromZ]
  exact ZMod.val_natCast_of_lt (d x).isLt

lemma zeroRead_iff_convW {r : Nat} (d : (Fin r → Fin 16) → Fin 11)
    (e : Finset (Fin r)) (z : Fin r → Fin 16) :
    (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passW e z x = true)).sum
      (fun x => (d x).val)) % 11 = 0 ↔ convW e (toZ d) z = 0 := by
  have hcast : ((((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passW e z x = true)).sum
      (fun x => (d x).val) : Nat) : ZMod 11) = convW e (toZ d) z := by
    rw [Finset.sum_filter, Nat.cast_sum]
    dsimp [convW, toZ]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← passW_eq_prod]
    split_ifs with h <;> simp
  rw [← hcast, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

def lostSet {r : Nat} (M : Finset (Finset (Fin r))) : Finset (Fin r → Fin 16) :=
  (Finset.univ : Finset (Fin r → Fin 16)).filter (fun u => ∀ e ∈ M, hatPass e u = 0)

lemma kernelSize_eq_pow_lost {r : Nat} (M : Finset (Finset (Fin r))) :
    ((Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passW q.1 q.2 x = true)).sum
          (fun x => (d x).val)) % 11 = 0)).card = 11 ^ (lostSet M).card := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  let ker := (Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
    ∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
      (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passW q.1 q.2 x = true)).sum
        (fun x => (d x).val)) % 11 = 0)
  have hker_iff : ∀ d : (Fin r → Fin 16) → Fin 11,
      d ∈ ker ↔ ∀ u : Fin r → Fin 16, u ∉ lostSet M → walsh (toZ d) u = 0 := by
    intro d
    simp only [ker, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h u hu
      simp only [lostSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      push Not at hu
      rcases hu with ⟨e, heM, hhat⟩
      have hconv0 : convW e (toZ d) = 0 := by
        funext z
        exact (zeroRead_iff_convW d e z).mp (h (e, z) (Finset.mem_product.mpr ⟨heM, Finset.mem_univ z⟩))
      have hw0 : walsh (convW e (toZ d)) u = 0 := by
        rw [hconv0]; simp [walsh]
      rw [walsh_convW] at hw0
      exact (mul_eq_zero.mp hw0).resolve_left hhat
    · intro h q hq
      rcases q with ⟨e, z⟩
      have heM : e ∈ M := (Finset.mem_product.mp hq).1
      apply (zeroRead_iff_convW d e z).mpr
      have hw0 : walsh (convW e (toZ d)) = 0 := by
        funext u
        rw [walsh_convW]
        by_cases hu : u ∈ lostSet M
        · have hhat0 : hatPass e u = 0 := (Finset.mem_filter.mp hu).2 e heM
          simp [hhat0]
        · rw [h u hu]; simp
      have hconv0 : convW e (toZ d) = 0 := by
        apply walsh_bijective.1
        rw [hw0]
        funext u; simp [walsh]
      exact congrFun hconv0 z
  let T := (Finset.univ : Finset (Subtype (fun u : Fin r → Fin 16 => u ∈ lostSet M) → ZMod 11))
  have hT_card : T.card = 11 ^ (lostSet M).card := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
  rw [← hT_card]
  refine Finset.card_nbij (fun d => (fun u : Subtype (fun u => u ∈ lostSet M) => walsh (toZ d) u.val)) ?_ ?_ ?_
  · intro d _; exact Finset.mem_univ _
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 := (hker_iff d₁).mp hd₁
    have h2 := (hker_iff d₂).mp hd₂
    have hw : walsh (toZ d₁) = walsh (toZ d₂) := by
      funext u
      by_cases hu : u ∈ lostSet M
      · exact congrFun heq ⟨u, hu⟩
      · rw [h1 u hu, h2 u hu]
    have hz : toZ d₁ = toZ d₂ := walsh_bijective.1 hw
    have := congrArg fromZ hz
    rwa [fromZ_toZ, fromZ_toZ] at this
  · intro g _
    let f : (Fin r → Fin 16) → ZMod 11 := fun u => if hu : u ∈ lostSet M then g ⟨u, hu⟩ else 0
    rcases walsh_bijective.2 f with ⟨dz, hdz⟩
    let d := fromZ dz
    have hd_ker : d ∈ ker := by
      rw [hker_iff]
      intro u hu
      dsimp [d]
      rw [toZ_fromZ, hdz]
      simp [f, hu]
    refine ⟨d, hd_ker, ?_⟩
    funext ⟨u, hu⟩
    dsimp [d]
    rw [toZ_fromZ, hdz]
    simp [f, hu]

def AOf {r : Nat} (u : Fin r → Fin 16) : Finset (Fin r) :=
  (Finset.univ : Finset (Fin r)).filter (fun j => isOnly0 (u j) = true)

def BOf {r : Nat} (u : Fin r → Fin 16) : Finset (Fin r) :=
  (Finset.univ : Finset (Fin r)).filter (fun j => isBoth (u j) = true)

lemma disjoint_AOf_BOf {r : Nat} (u : Fin r → Fin 16) : Disjoint (AOf u) (BOf u) := by
  rw [Finset.disjoint_left]
  intro j hjA hjB
  have h1 := (Finset.mem_filter.mp hjA).2
  have h2 := (Finset.mem_filter.mp hjB).2
  rcases class_excl (u j) with ⟨_, h0, _⟩ | ⟨_, _, hb⟩ | ⟨_, h0, _⟩ <;> simp_all

lemma hatPass_ne_zero_iff {r : Nat} (e : Finset (Fin r)) (u : Fin r → Fin 16) :
    hatPass e u ≠ 0 ↔ AOf u ⊆ Finset.univ \ e ∧ Finset.univ \ e ⊆ AOf u ∪ BOf u := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  change (Finset.univ : Finset (Fin r)).prod (fun j => hat1 (decide (j ∈ e)) (u j)) ≠ 0 ↔ _
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h
    constructor
    · intro j hjA
      have hne := h j (Finset.mem_univ j)
      have h0 : isOnly0 (u j) = true := (Finset.mem_filter.mp hjA).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩
      intro hje
      rw [decide_eq_true hje] at hne
      have := (hat1_true_ne_zero (u j)).mp hne
      rw [h0] at this; cases this
    · intro j hjS
      have hje : j ∉ e := (Finset.mem_sdiff.mp hjS).2
      have hne := h j (Finset.mem_univ j)
      rw [decide_eq_false hje] at hne
      have h1 : isOnly1 (u j) = false := (hat1_false_ne_zero (u j)).mp hne
      rcases class_excl (u j) with ⟨ha, _, _⟩ | ⟨_, h0, _⟩ | ⟨_, _, hb⟩
      · rw [ha] at h1; cases h1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h0⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hb⟩)
  · rintro ⟨hA, hAB⟩ j _
    by_cases hje : j ∈ e
    · rw [decide_eq_true hje, hat1_true_ne_zero]
      by_contra h0
      have h0t : isOnly0 (u j) = true := by cases h : isOnly0 (u j) <;> simp_all
      have := hA (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h0t⟩)
      exact (Finset.mem_sdiff.mp this).2 hje
    · rw [decide_eq_false hje, hat1_false_ne_zero]
      have hjS : j ∈ Finset.univ \ e := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hje⟩
      rcases Finset.mem_union.mp (hAB hjS) with hjA | hjB
      · have h0 := (Finset.mem_filter.mp hjA).2
        rcases class_excl (u j) with ⟨_, ha, _⟩ | ⟨h1, _, _⟩ | ⟨_, ha, _⟩ <;> simp_all
      · have hb := (Finset.mem_filter.mp hjB).2
        rcases class_excl (u j) with ⟨_, _, ha⟩ | ⟨_, _, ha⟩ | ⟨h1, _, _⟩ <;> simp_all

lemma sdiff_sdiff_univ {r : Nat} (S : Finset (Fin r)) :
    (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ S) = S := by
  ext j; simp

lemma lost_compl_iff {r : Nat} (U : Finset (Finset (Fin r))) (u : Fin r → Fin 16) :
    u ∈ lostSet ((Finset.univ : Finset (Finset (Fin r))) \ U) ↔
      ∀ S : Finset (Fin r), AOf u ⊆ S → S ⊆ AOf u ∪ BOf u → (Finset.univ : Finset (Fin r)) \ S ∈ U := by
  simp only [lostSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · intro h S hAS hSAB
    by_contra hnot
    have h0 := h ((Finset.univ : Finset (Fin r)) \ S) hnot
    have hne : hatPass ((Finset.univ : Finset (Fin r)) \ S) u ≠ 0 := by
      rw [hatPass_ne_zero_iff, sdiff_sdiff_univ]
      exact ⟨hAS, hSAB⟩
    exact hne h0
  · intro h e henot
    by_contra hne
    rcases (hatPass_ne_zero_iff e u).mp hne with ⟨hA, hAB⟩
    have := h ((Finset.univ : Finset (Fin r)) \ e) hA hAB
    rw [sdiff_sdiff_univ] at this
    exact henot this

lemma fiber_AB_card {r : Nat} (A B : Finset (Fin r)) (hdisj : Disjoint A B) :
    ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun u => AOf u = A ∧ BOf u = B)).card =
      6 ^ A.card * 9 ^ B.card := by
  classical
  let t : Fin r → Finset (Fin 16) := fun j =>
    if j ∈ A then only0Set else if j ∈ B then bothSet else only1Set
  have heq : (Finset.univ : Finset (Fin r → Fin 16)).filter (fun u => AOf u = A ∧ BOf u = B) =
      Fintype.piFinset t := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨rfl, rfl⟩ j
      dsimp [t]
      split_ifs with hjA hjB
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hjA).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hjB).2⟩
      · rcases class_excl (u j) with ⟨h1, _, _⟩ | ⟨_, h0, _⟩ | ⟨_, _, hb⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h0⟩) hjA
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hb⟩) hjB
    · intro h
      constructor
      · ext j
        simp only [AOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hj := h j
        dsimp [t] at hj
        split_ifs at hj with hjA hjB
        · exact ⟨fun _ => hjA, fun _ => (Finset.mem_filter.mp hj).2⟩
        · have hb := (Finset.mem_filter.mp hj).2
          have h0f : isOnly0 (u j) = false := by
            rcases class_excl (u j) with ⟨_, _, ha⟩ | ⟨_, _, ha⟩ | ⟨_, h0, _⟩ <;> simp_all
          simp [h0f, hjA]
        · have h1 := (Finset.mem_filter.mp hj).2
          have h0f : isOnly0 (u j) = false := by
            rcases class_excl (u j) with ⟨_, h0, _⟩ | ⟨ha, _, _⟩ | ⟨ha, _, _⟩ <;> simp_all
          simp [h0f, hjA]
      · ext j
        simp only [BOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hj := h j
        dsimp [t] at hj
        split_ifs at hj with hjA hjB
        · have h0 := (Finset.mem_filter.mp hj).2
          have hjB' : j ∉ B := Finset.disjoint_left.mp hdisj hjA
          have hbf : isBoth (u j) = false := by
            rcases class_excl (u j) with ⟨_, ha, _⟩ | ⟨_, _, hb⟩ | ⟨_, ha, _⟩ <;> simp_all
          simp [hbf, hjB']
        · exact ⟨fun _ => hjB, fun _ => (Finset.mem_filter.mp hj).2⟩
        · have h1 := (Finset.mem_filter.mp hj).2
          have hbf : isBoth (u j) = false := by
            rcases class_excl (u j) with ⟨_, _, hb⟩ | ⟨ha, _, _⟩ | ⟨ha, _, _⟩ <;> simp_all
          simp [hbf, hjB]
  rw [heq, Fintype.card_piFinset]
  let R := (Finset.univ : Finset (Fin r)) \ (A ∪ B)
  have huniv : (Finset.univ : Finset (Fin r)) = A ∪ (B ∪ R) := by
    ext j; simp only [R, Finset.mem_univ, Finset.mem_union, Finset.mem_sdiff, true_and, true_iff]
    by_cases hA : j ∈ A
    · exact Or.inl hA
    · by_cases hB : j ∈ B
      · exact Or.inr (Or.inl hB)
      · exact Or.inr (Or.inr (by simp [hA, hB]))
  have hd_BR : Disjoint B R := by
    rw [Finset.disjoint_left]; intro j hjB hjR
    exact (Finset.mem_sdiff.mp hjR).2 (Finset.mem_union_right _ hjB)
  have hd_A_BR : Disjoint A (B ∪ R) := by
    rw [Finset.disjoint_left]; intro j hjA hjBR
    rcases Finset.mem_union.mp hjBR with hjB | hjR
    · exact Finset.disjoint_left.mp hdisj hjA hjB
    · exact (Finset.mem_sdiff.mp hjR).2 (Finset.mem_union_left _ hjA)
  rw [huniv, Finset.prod_union hd_A_BR, Finset.prod_union hd_BR]
  have hpA : A.prod (fun j => (t j).card) = 6 ^ A.card := by
    have : A.prod (fun j => (t j).card) = A.prod (fun _ => 6) :=
      Finset.prod_congr rfl fun j hj => by simp [t, hj, card_only0Set]
    rw [this, Finset.prod_const]
  have hpB : B.prod (fun j => (t j).card) = 9 ^ B.card := by
    have : B.prod (fun j => (t j).card) = B.prod (fun _ => 9) :=
      Finset.prod_congr rfl fun j hj => by
        have hjA : j ∉ A := Finset.disjoint_right.mp hdisj hj
        simp [t, hjA, hj, card_bothSet]
    rw [this, Finset.prod_const]
  have hpR : R.prod (fun j => (t j).card) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have hnot := (Finset.mem_sdiff.mp hj).2
    have hjA : j ∉ A := fun h => hnot (Finset.mem_union_left _ h)
    have hjB : j ∉ B := fun h => hnot (Finset.mem_union_right _ h)
    simp [t, hjA, hjB, card_only1Set]
  rw [hpA, hpB, hpR, mul_one]

lemma card_eq_sum_fibers {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ x ∈ s, f x ∈ t) :
    s.card = t.sum (fun y => (s.filter (fun x => f x = y)).card) := by
  classical
  induction t using Finset.induction_on generalizing s with
  | empty =>
    have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by simpa using hf x hx)
    simp [hs]
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have hsplit : s = s.filter (fun x => f x = a) ∪ s.filter (fun x => f x ≠ a) := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter]; by_cases h : f x = a <;> simp [h]
    have hdisj : Disjoint (s.filter (fun x => f x = a)) (s.filter (fun x => f x ≠ a)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hcard : s.card = (s.filter (fun x => f x = a)).card + (s.filter (fun x => f x ≠ a)).card := by
      conv_lhs => rw [hsplit]
      exact Finset.card_union_of_disjoint hdisj
    rw [hcard, ih (s.filter (fun x => f x ≠ a)) (fun x hx => by
      rcases Finset.mem_filter.mp hx with ⟨hxs, hne⟩
      rcases Finset.mem_insert.mp (hf x hxs) with heq | ht
      · exact absurd heq hne
      · exact ht)]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    congr 1; ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxs, _⟩, rfl⟩; exact ⟨hxs, rfl⟩
    · rintro ⟨hxs, rfl⟩; exact ⟨⟨hxs, fun h => ha (h ▸ hy)⟩, rfl⟩

lemma lost_card_exact {r : Nat} (U : Finset (Finset (Fin r)))
    (hdeg : ∀ e ∈ U, ((Finset.univ : Finset (Fin r)) \ e).card ≤ 2) :
    let sites := (Finset.univ : Finset (Fin r))
    let Ucomp := U.image (fun e => sites \ e)
    let z := (decide (sites ∈ U)).toNat
    let uSet := sites.filter (fun i => ({i} : Finset (Fin r)) ∈ Ucomp)
    let P2 := Ucomp.filter (fun S => S.card = 2)
    let p1 := (P2.filter (fun P => (P ∩ uSet).card = 1)).card
    let p2 := (P2.filter (fun P => (P ∩ uSet).card = 2)).card
    (lostSet ((Finset.univ : Finset (Finset (Fin r))) \ U)).card =
      z + (6 + 9 * z) * uSet.card + 36 * P2.card + 54 * (p1 + p2) + (54 + 81 * z) * p2 := by
  classical
  intro sites Ucomp z uSet P2 p1 p2
  have hmem_Ucomp : ∀ S : Finset (Fin r), S ∈ Ucomp ↔ sites \ S ∈ U := by
    intro S
    simp only [Ucomp, Finset.mem_image]
    constructor
    · rintro ⟨e, heU, rfl⟩
      rwa [sdiff_sdiff_univ]
    · intro h
      exact ⟨sites \ S, h, sdiff_sdiff_univ S⟩
  have hUcomp_card : ∀ S ∈ Ucomp, S.card ≤ 2 := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨e, heU, rfl⟩
    exact hdeg e heU
  let G : Finset (Finset (Fin r) × Finset (Fin r)) :=
    Finset.univ.filter (fun p => Disjoint p.1 p.2 ∧
      ∀ S : Finset (Fin r), p.1 ⊆ S → S ⊆ p.1 ∪ p.2 → S ∈ Ucomp)
  have hlost_eq : (lostSet ((Finset.univ : Finset (Finset (Fin r))) \ U)).card =
      G.sum (fun p => 6 ^ p.1.card * 9 ^ p.2.card) := by
    have hmap : ∀ u ∈ lostSet ((Finset.univ : Finset (Finset (Fin r))) \ U), (AOf u, BOf u) ∈ G := by
      intro u hu
      have hcube := (lost_compl_iff U u).mp hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, disjoint_AOf_BOf u, ?_⟩
      intro S h1 h2
      exact (hmem_Ucomp S).mpr (hcube S h1 h2)
    rw [card_eq_sum_fibers _ G (fun u => (AOf u, BOf u)) hmap]
    refine Finset.sum_congr rfl fun ⟨A, B⟩ hp => ?_
    rcases Finset.mem_filter.mp hp with ⟨_, hdisj, hcube⟩
    have hfilt : (lostSet ((Finset.univ : Finset (Finset (Fin r))) \ U)).filter
        (fun u => (AOf u, BOf u) = (A, B)) =
        (Finset.univ : Finset (Fin r → Fin 16)).filter (fun u => AOf u = A ∧ BOf u = B) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · intro h; exact h.2
      · rintro ⟨hA, hB⟩
        refine ⟨?_, hA, hB⟩
        rw [lost_compl_iff]
        intro S h1 h2
        rw [hA] at h1
        rw [hA, hB] at h2
        exact (hmem_Ucomp S).mp (hcube S h1 h2)
    rw [hfilt, fiber_AB_card A B hdisj]
  have hG_deg : ∀ p ∈ G, p.1.card + p.2.card ≤ 2 := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hdisj, hcube⟩
    have hun : p.1 ∪ p.2 ∈ Ucomp := hcube (p.1 ∪ p.2) Finset.subset_union_left Finset.Subset.rfl
    have hle := hUcomp_card (p.1 ∪ p.2) hun
    rwa [Finset.card_union_of_disjoint hdisj] at hle
  let C00 := G.filter (fun p => p.1.card = 0 ∧ p.2.card = 0)
  let C10 := G.filter (fun p => p.1.card = 1 ∧ p.2.card = 0)
  let C01 := G.filter (fun p => p.1.card = 0 ∧ p.2.card = 1)
  let C20 := G.filter (fun p => p.1.card = 2 ∧ p.2.card = 0)
  let C11 := G.filter (fun p => p.1.card = 1 ∧ p.2.card = 1)
  let C02 := G.filter (fun p => p.1.card = 0 ∧ p.2.card = 2)
  have hG_split : G.sum (fun p => 6 ^ p.1.card * 9 ^ p.2.card) =
      C00.card + 6 * C10.card + 9 * C01.card + 36 * C20.card + 54 * C11.card + 81 * C02.card := by
    let classes : Finset (Nat × Nat) := {(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)}
    have hsum_cls : G.sum (fun p => 6 ^ p.1.card * 9 ^ p.2.card) =
        classes.sum (fun ab => (G.filter (fun p => (p.1.card, p.2.card) = ab)).sum
          (fun p => 6 ^ p.1.card * 9 ^ p.2.card)) := by
      have hmap : ∀ p ∈ G, (p.1.card, p.2.card) ∈ classes := by
        intro p hp
        have hle := hG_deg p hp
        simp only [classes, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega
      rw [← Finset.sum_fiberwise_of_maps_to hmap]
    rw [hsum_cls]
    have hm0 : (0, 0) ∉ ({(1, 0), (0, 1), (2, 0), (1, 1), (0, 2)} : Finset (Nat × Nat)) := by decide
    have hm1 : (1, 0) ∉ ({(0, 1), (2, 0), (1, 1), (0, 2)} : Finset (Nat × Nat)) := by decide
    have hm2 : (0, 1) ∉ ({(2, 0), (1, 1), (0, 2)} : Finset (Nat × Nat)) := by decide
    have hm3 : (2, 0) ∉ ({(1, 1), (0, 2)} : Finset (Nat × Nat)) := by decide
    have hm4 : (1, 1) ∉ ({(0, 2)} : Finset (Nat × Nat)) := by decide
    dsimp only [classes]
    rw [Finset.sum_insert hm0, Finset.sum_insert hm1, Finset.sum_insert hm2,
        Finset.sum_insert hm3, Finset.sum_insert hm4, Finset.sum_singleton]
    have hval : ∀ a b : Nat,
        (G.filter (fun p => (p.1.card, p.2.card) = (a, b))).sum (fun p => 6 ^ p.1.card * 9 ^ p.2.card) =
        (6 ^ a * 9 ^ b) * (G.filter (fun p => p.1.card = a ∧ p.2.card = b)).card := by
      intro a b
      have hf : G.filter (fun p => (p.1.card, p.2.card) = (a, b)) =
          G.filter (fun p => p.1.card = a ∧ p.2.card = b) := by
        ext p; simp [Prod.mk.injEq]
      rw [hf]
      have hconst : (G.filter (fun p => p.1.card = a ∧ p.2.card = b)).sum (fun p => 6 ^ p.1.card * 9 ^ p.2.card) =
          (G.filter (fun p => p.1.card = a ∧ p.2.card = b)).sum (fun _ => 6 ^ a * 9 ^ b) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rcases (Finset.mem_filter.mp hp).2 with ⟨h1, h2⟩
        rw [h1, h2]
      rw [hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hval 0 0, hval 1 0, hval 0 1, hval 2 0, hval 1 1, hval 0 2]
    change 1 * C00.card + (6 * C10.card + (9 * C01.card + (36 * C20.card + (54 * C11.card + 81 * C02.card)))) = _
    omega
  have h0_mem : (∅ : Finset (Fin r)) ∈ Ucomp ↔ sites ∈ U := by
    rw [hmem_Ucomp, Finset.sdiff_empty]
  have hC00 : C00.card = z := by
    by_cases hcent : sites ∈ U
    · have hEq : C00 = {(∅, ∅)} := by
        ext ⟨A, B⟩
        simp only [C00, G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨_, hA0, hB0⟩
          exact ⟨Finset.card_eq_zero.mp hA0, Finset.card_eq_zero.mp hB0⟩
        · rintro ⟨rfl, rfl⟩
          refine ⟨⟨Finset.disjoint_empty_left _, ?_⟩, rfl, rfl⟩
          intro S _ hS
          have hSe : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
          rw [hSe]; exact h0_mem.mpr hcent
      rw [hEq, Finset.card_singleton]
      simp [z, hcent]
    · have hEq : C00 = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr ?_
        rintro ⟨A, B⟩ hmem
        simp only [C00, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨⟨_, hcube⟩, hA0, hB0⟩
        have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
        have hBe : B = ∅ := Finset.card_eq_zero.mp hB0
        subst hAe; subst hBe
        exact hcent (h0_mem.mp (hcube ∅ Finset.Subset.rfl (by simp)))
      rw [hEq, Finset.card_empty]
      simp [z, hcent]
  have hC10 : C10.card = uSet.card := by
    symm
    refine Finset.card_nbij (fun i => ({i}, ∅)) ?_ ?_ ?_
    · intro i hi
      have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_empty_right _, ?_⟩, by simp, rfl⟩
      intro S h1 h2
      have hSe : S = {i} := Finset.Subset.antisymm (by simpa using h2) h1
      rwa [hSe]
    · intro i _ j _ h
      exact Finset.singleton_injective (congrArg Prod.fst h)
    · rintro ⟨A, B⟩ hmem
      simp only [Finset.mem_coe, C10, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨⟨_, hcube⟩, hA1, hB0⟩
      rcases Finset.card_eq_one.mp hA1 with ⟨i, rfl⟩
      have hBe : B = ∅ := Finset.card_eq_zero.mp hB0
      subst hBe
      have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := hcube {i} Finset.Subset.rfl (by simp)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiU⟩, rfl⟩
  have hC01 : C01.card = z * uSet.card := by
    by_cases hcent : sites ∈ U
    · have hz1 : z = 1 := by simp [z, hcent]
      rw [hz1, one_mul]
      symm
      refine Finset.card_nbij (fun i => (∅, {i})) ?_ ?_ ?_
      · intro i hi
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_empty_left _, ?_⟩, rfl, by simp⟩
        intro S _ h2
        rw [Finset.empty_union] at h2
        rcases Finset.subset_singleton_iff.mp h2 with rfl | rfl
        · exact h0_mem.mpr hcent
        · exact hiU
      · intro i _ j _ h
        exact Finset.singleton_injective (congrArg Prod.snd h)
      · rintro ⟨A, B⟩ hmem
        simp only [Finset.mem_coe, C01, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨⟨_, hcube⟩, hA0, hB1⟩
        have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
        rcases Finset.card_eq_one.mp hB1 with ⟨i, rfl⟩
        subst hAe
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := hcube {i} (Finset.empty_subset _) (by simp)
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiU⟩, rfl⟩
    · have hz0 : z = 0 := by simp [z, hcent]
      rw [hz0, zero_mul]
      have hEq : C01 = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr ?_
        rintro ⟨A, B⟩ hmem
        simp only [Finset.mem_coe, C01, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨⟨_, hcube⟩, hA0, _⟩
        have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
        subst hAe
        exact hcent (h0_mem.mp (hcube ∅ Finset.Subset.rfl (Finset.empty_subset _)))
      rw [hEq, Finset.card_empty]
  have hC20 : C20.card = P2.card := by
    symm
    refine Finset.card_nbij (fun P => (P, ∅)) ?_ ?_ ?_
    · intro P hP
      rcases Finset.mem_filter.mp hP with ⟨hPU, hP2⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_empty_right _, ?_⟩, hP2, rfl⟩
      intro S h1 h2
      have hSe : S = P := Finset.Subset.antisymm (by simpa using h2) h1
      rwa [hSe]
    · intro P₁ _ P₂ _ h; exact congrArg Prod.fst h
    · rintro ⟨A, B⟩ hmem
      simp only [Finset.mem_coe, C20, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨⟨_, hcube⟩, hA2, hB0⟩
      have hBe : B = ∅ := Finset.card_eq_zero.mp hB0
      subst hBe
      have hAU : A ∈ Ucomp := hcube A Finset.Subset.rfl (by simp)
      exact ⟨A, Finset.mem_filter.mpr ⟨hAU, hA2⟩, rfl⟩
  have hC11 : C11.card = p1 + 2 * p2 := by
    have hmap : ∀ p ∈ C11, p.1 ∪ p.2 ∈ P2 := by
      intro p hp
      simp only [C11, G, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨⟨hdisj, hcube⟩, h1, h2⟩
      refine Finset.mem_filter.mpr ⟨hcube (p.1 ∪ p.2) Finset.subset_union_left Finset.Subset.rfl, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, h1, h2]
    rw [card_eq_sum_fibers C11 P2 (fun p => p.1 ∪ p.2) hmap]
    have hfib : ∀ P ∈ P2, (C11.filter (fun p => p.1 ∪ p.2 = P)).card = (P ∩ uSet).card := by
      intro P hP
      rcases Finset.mem_filter.mp hP with ⟨hPU, hP2⟩
      symm
      refine Finset.card_nbij (fun i => ({i}, P.erase i)) ?_ ?_ ?_
      · intro i hi
        rcases Finset.mem_inter.mp hi with ⟨hiP, hiu⟩
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := (Finset.mem_filter.mp hiu).2
        have hdisj : Disjoint ({i} : Finset (Fin r)) (P.erase i) := by simp
        have hun : ({i} : Finset (Fin r)) ∪ P.erase i = P := by
          rw [Finset.singleton_union, Finset.insert_erase hiP]
        have her_card : (P.erase i).card = 1 := by
          rw [Finset.card_erase_of_mem hiP, hP2]
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdisj, ?_⟩, by simp, her_card⟩, hun⟩
        intro S h1 h2
        rw [hun] at h2
        have hcard1 : 1 ≤ S.card := by
          have := Finset.card_le_card h1; simpa using this
        have hcard2 : S.card ≤ 2 := by
          have := Finset.card_le_card h2; omega
        by_cases hS1 : S.card = 1
        · have hSe : S = {i} := (Finset.eq_of_subset_of_card_le h1 (by simp [hS1])).symm
          rwa [hSe]
        · have hS2 : S.card = 2 := by omega
          have hSe : S = P := Finset.eq_of_subset_of_card_le h2 (by omega)
          rwa [hSe]
      · intro i _ j _ h
        exact Finset.singleton_injective (congrArg Prod.fst h)
      · rintro ⟨A, B⟩ hmem
        simp only [Finset.mem_coe, C11, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨⟨⟨hdisj, hcube⟩, hA1, hB1⟩, hAB⟩
        rcases Finset.card_eq_one.mp hA1 with ⟨i, rfl⟩
        have hiP : i ∈ P := hAB ▸ Finset.mem_union_left B (Finset.mem_singleton_self i)
        have hiB : i ∉ B := Finset.disjoint_left.mp hdisj (Finset.mem_singleton_self i)
        have hBeq : B = P.erase i := by
          rw [← hAB, Finset.singleton_union, Finset.erase_insert hiB]
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := hcube {i} Finset.Subset.rfl Finset.subset_union_left
        refine ⟨i, Finset.mem_inter.mpr ⟨hiP, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiU⟩⟩, ?_⟩
        simp [hBeq]
    rw [Finset.sum_congr rfl hfib]
    have hmap2 : ∀ P ∈ P2, (P ∩ uSet).card ∈ ({0, 1, 2} : Finset Nat) := by
      intro P hP
      have hle : (P ∩ uSet).card ≤ 2 := by
        have := Finset.card_le_card (Finset.inter_subset_left (s₁ := P) (s₂ := uSet))
        have hP2 := (Finset.mem_filter.mp hP).2
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    rw [← Finset.sum_fiberwise_of_maps_to hmap2]
    have hn0 : (0 : Nat) ∉ ({1, 2} : Finset Nat) := by decide
    have hn1 : (1 : Nat) ∉ ({2} : Finset Nat) := by decide
    rw [Finset.sum_insert hn0, Finset.sum_insert hn1, Finset.sum_singleton]
    have h0 : (P2.filter (fun P => (P ∩ uSet).card = 0)).sum (fun P => (P ∩ uSet).card) = 0 :=
      Finset.sum_eq_zero fun P hP => (Finset.mem_filter.mp hP).2
    have h1 : (P2.filter (fun P => (P ∩ uSet).card = 1)).sum (fun P => (P ∩ uSet).card) = p1 := by
      have : (P2.filter (fun P => (P ∩ uSet).card = 1)).sum (fun P => (P ∩ uSet).card) =
          (P2.filter (fun P => (P ∩ uSet).card = 1)).sum (fun _ => 1) :=
        Finset.sum_congr rfl fun P hP => (Finset.mem_filter.mp hP).2
      rw [this, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : (P2.filter (fun P => (P ∩ uSet).card = 2)).sum (fun P => (P ∩ uSet).card) = 2 * p2 := by
      have : (P2.filter (fun P => (P ∩ uSet).card = 2)).sum (fun P => (P ∩ uSet).card) =
          (P2.filter (fun P => (P ∩ uSet).card = 2)).sum (fun _ => 2) :=
        Finset.sum_congr rfl fun P hP => (Finset.mem_filter.mp hP).2
      rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h0, h1, h2, zero_add]
  have hC02 : C02.card = z * p2 := by
    by_cases hcent : sites ∈ U
    · have hz1 : z = 1 := by simp [z, hcent]
      rw [hz1, one_mul]
      symm
      refine Finset.card_nbij (fun P => (∅, P)) ?_ ?_ ?_
      · intro P hP
        rcases Finset.mem_filter.mp hP with ⟨hPP2, hPu2⟩
        rcases Finset.mem_filter.mp hPP2 with ⟨hPU, hP2⟩
        have hPsub : P ⊆ uSet := by
          have heq : P ∩ uSet = P := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          intro i hi; exact (Finset.mem_inter.mp (heq ▸ hi)).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_empty_left _, ?_⟩, rfl, hP2⟩
        intro S _ h2
        rw [Finset.empty_union] at h2
        have hle : S.card ≤ 2 := (Finset.card_le_card h2).trans hP2.le
        by_cases hS0 : S.card = 0
        · rw [Finset.card_eq_zero.mp hS0]; exact h0_mem.mpr hcent
        · by_cases hS1 : S.card = 1
          · rcases Finset.card_eq_one.mp hS1 with ⟨i, rfl⟩
            have hiP : i ∈ P := h2 (Finset.mem_singleton_self i)
            exact (Finset.mem_filter.mp (hPsub hiP)).2
          · have hSe : S = P := Finset.eq_of_subset_of_card_le h2 (by omega)
            rwa [hSe]
      · intro P₁ _ P₂ _ h; exact congrArg Prod.snd h
      · rintro ⟨A, B⟩ hmem
        simp only [Finset.mem_coe, C02, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨⟨_, hcube⟩, hA0, hB2⟩
        have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
        subst hAe
        have hBU : B ∈ Ucomp := hcube B (Finset.empty_subset _) (by simp)
        have hBsub : B ⊆ uSet := by
          intro i hiB
          have hiU : ({i} : Finset (Fin r)) ∈ Ucomp :=
            hcube {i} (Finset.empty_subset _) (by simpa using Finset.singleton_subset_iff.mpr hiB)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiU⟩
        have hBu2 : (B ∩ uSet).card = 2 := by
          rw [Finset.inter_eq_left.mpr hBsub, hB2]
        exact ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hBU, hB2⟩, hBu2⟩, rfl⟩
    · have hz0 : z = 0 := by simp [z, hcent]
      rw [hz0, zero_mul]
      have hEq : C02 = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr ?_
        rintro ⟨A, B⟩ hmem
        simp only [Finset.mem_coe, C02, G, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨⟨_, hcube⟩, hA0, _⟩
        have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
        subst hAe
        exact hcent (h0_mem.mp (hcube ∅ Finset.Subset.rfl (Finset.empty_subset _)))
      rw [hEq, Finset.card_empty]
  rw [hlost_eq, hG_split, hC00, hC10, hC01, hC20, hC11, hC02]
  ring

theorem main :
∀ (r t pairs : Nat) (center : Bool), t ≤ r → pairs ≤ Nat.choose r 2 →
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let zeroRead := fun (d : Word → Fin 11) (q : Kind × Word) =>
    ((cube.filter (fun x => pass q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0
  let kernelSize := fun (M : Finset Kind) =>
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product cube, zeroRead d q)).card
  let units := r - t
  let cheap := Nat.choose t 2
  let mixed := t * units
  let loss := center.toNat + (6 + 9 * center.toNat) * units + 36 * pairs +
    54 * (pairs - cheap) + (54 + 81 * center.toNat) * (pairs - (cheap + mixed))
  let allowed := fun (U : Finset Kind) =>
    (decide (sites ∈ U) = center) ∧ (∀ e ∈ U, (sites \ e).card ≤ 2) ∧
    (U.filter (fun e => (sites \ e).card = 1)).card = units ∧
    (U.filter (fun e => (sites \ e).card = 2)).card = pairs
  (∀ U : Finset Kind, allowed U → 11 ^ loss ≤ kernelSize (kinds \ U)) ∧
    ∃ U : Finset Kind, allowed U ∧ kernelSize (kinds \ U) = 11 ^ loss := by
  classical
  intro r t pairs center htr hpairs
  dsimp only
  let sites : Finset (Fin r) := Finset.univ
  let kinds : Finset (Finset (Fin r)) := Finset.univ
  let units := r - t
  let cheap := Nat.choose t 2
  let mixed := t * units
  let loss := center.toNat + (6 + 9 * center.toNat) * units + 36 * pairs +
    54 * (pairs - cheap) + (54 + 81 * center.toNat) * (pairs - (cheap + mixed))
  have hker_eq : ∀ M : Finset (Finset (Fin r)),
      ((Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
        ∀ q ∈ M.product (Finset.univ : Finset (Fin r → Fin 16)),
          (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passW q.1 q.2 x = true)).sum
            (fun x => (d x).val)) % 11 = 0)).card = 11 ^ (lostSet M).card :=
    fun M => kernelSize_eq_pow_lost M
  constructor
  · intro U hU
    rcases hU with ⟨hcent_eq, hdeg, hunits_eq, hpairs_eq⟩
    refine le_trans ?_ (le_of_eq (by convert (kernelSize_eq_pow_lost (kinds \ U)).symm <;> rfl))
    apply Nat.pow_le_pow_right (by decide : 0 < 11)
    have hexact := lost_card_exact U hdeg
    dsimp only at hexact
    rw [hexact]
    let Ucomp := U.image (fun e => sites \ e)
    let uSet := sites.filter (fun i => ({i} : Finset (Fin r)) ∈ Ucomp)
    let P2 := Ucomp.filter (fun S => S.card = 2)
    let p0 := (P2.filter (fun P => (P ∩ uSet).card = 0)).card
    let p1 := (P2.filter (fun P => (P ∩ uSet).card = 1)).card
    let p2 := (P2.filter (fun P => (P ∩ uSet).card = 2)).card
    have huSet_card : uSet.card = units := by
      dsimp only [units]
      rw [← hunits_eq]
      refine Finset.card_nbij (fun i => sites \ {i}) ?_ ?_ ?_
      · intro i hi
        dsimp only
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        rcases Finset.mem_image.mp hiU with ⟨e, heU, heq⟩
        have hes : sites \ {i} = e := by rw [← heq]; exact sdiff_sdiff_univ e
        rw [Finset.mem_coe, hes]
        exact Finset.mem_filter.mpr ⟨heU, by rw [heq]; simp⟩
      · intro i _ j _ heq
        dsimp only at heq
        have h1 : ({i} : Finset (Fin r)) = {j} := by
          have := congrArg (fun S => sites \ S) heq
          simpa only [sites, sdiff_sdiff_univ] using this
        exact Finset.singleton_injective h1
      · intro e he
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp he) with ⟨heU, he1⟩
        rcases Finset.card_eq_one.mp he1 with ⟨i, hi⟩
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := Finset.mem_image.mpr ⟨e, heU, hi⟩
        refine ⟨i, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiU⟩), ?_⟩
        dsimp only; rw [← hi]; exact sdiff_sdiff_univ e
    have hP2_card : P2.card = pairs := by
      rw [← hpairs_eq]
      refine Finset.card_nbij (fun S => sites \ S) ?_ ?_ ?_
      · intro S hS
        dsimp only
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp hS) with ⟨hSU, hS2⟩
        rcases Finset.mem_image.mp hSU with ⟨e, heU, heq⟩
        have hes : sites \ S = e := by rw [← heq]; exact sdiff_sdiff_univ e
        rw [Finset.mem_coe, hes]
        exact Finset.mem_filter.mpr ⟨heU, by rw [heq]; exact hS2⟩
      · intro S₁ _ S₂ _ heq
        dsimp only at heq
        have := congrArg (fun S => sites \ S) heq
        simpa only [sites, sdiff_sdiff_univ] using this
      · intro e he
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp he) with ⟨heU, he2⟩
        exact ⟨sites \ e, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e, heU, rfl⟩, he2⟩), sdiff_sdiff_univ e⟩
    have hp_sum : p0 + p1 + p2 = pairs := by
      rw [← hP2_card]
      have hmap : ∀ P ∈ P2, (P ∩ uSet).card ∈ ({0, 1, 2} : Finset Nat) := by
        intro P hP
        have hle : (P ∩ uSet).card ≤ 2 := by
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := P) (s₂ := uSet))
          have hP2 := (Finset.mem_filter.mp hP).2
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hfib := card_eq_sum_fibers P2 ({0, 1, 2} : Finset Nat) (fun P => (P ∩ uSet).card) hmap
      rw [hfib]
      have hn0 : (0 : Nat) ∉ ({1, 2} : Finset Nat) := by decide
      have hn1 : (1 : Nat) ∉ ({2} : Finset Nat) := by decide
      rw [Finset.sum_insert hn0, Finset.sum_insert hn1, Finset.sum_singleton]
      change p0 + p1 + p2 = p0 + (p1 + p2)
      omega
    let tSet := sites \ uSet
    have htSet_card : tSet.card = t := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, huSet_card]
      omega
    have hp0_le : p0 ≤ cheap := by
      have hsub : P2.filter (fun P => (P ∩ uSet).card = 0) ⊆ tSet.powersetCard 2 := by
        intro P hP
        rcases Finset.mem_filter.mp hP with ⟨hPP2, h0⟩
        have hP2 := (Finset.mem_filter.mp hPP2).2
        refine Finset.mem_powersetCard.mpr ⟨?_, hP2⟩
        intro i hiP
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩
        intro hiu
        have hmem : i ∈ P ∩ uSet := Finset.mem_inter.mpr ⟨hiP, hiu⟩
        have := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
      calc
        p0 ≤ (tSet.powersetCard 2).card := Finset.card_le_card hsub
        _ = Nat.choose tSet.card 2 := Finset.card_powersetCard 2 tSet
        _ = cheap := by rw [htSet_card]
    have hp1_le : p1 ≤ mixed := by
      have hsub : P2.filter (fun P => (P ∩ uSet).card = 1) ⊆
          (tSet ×ˢ uSet).image (fun q => ({q.1, q.2} : Finset (Fin r))) := by
        intro P hP
        rcases Finset.mem_filter.mp hP with ⟨hPP2, h1⟩
        have hP2 := (Finset.mem_filter.mp hPP2).2
        rcases Finset.card_eq_one.mp h1 with ⟨b, hb⟩
        have hbP : b ∈ P := (Finset.mem_inter.mp (hb.symm ▸ Finset.mem_singleton_self b)).1
        have hbu : b ∈ uSet := (Finset.mem_inter.mp (hb.symm ▸ Finset.mem_singleton_self b)).2
        have her1 : (P.erase b).card = 1 := by rw [Finset.card_erase_of_mem hbP, hP2]
        rcases Finset.card_eq_one.mp her1 with ⟨a, ha⟩
        have haP : a ∈ P := Finset.mem_of_mem_erase (ha.symm ▸ Finset.mem_singleton_self a)
        have hab : a ≠ b := Finset.ne_of_mem_erase (ha.symm ▸ Finset.mem_singleton_self a)
        have hau : a ∉ uSet := by
          intro h
          have : a ∈ P ∩ uSet := Finset.mem_inter.mpr ⟨haP, h⟩
          rw [hb, Finset.mem_singleton] at this
          exact hab this
        have hat : a ∈ tSet := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, hau⟩
        refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨hat, hbu⟩, ?_⟩
        have : insert b (P.erase b) = P := Finset.insert_erase hbP
        rw [ha] at this
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        rw [← this]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      calc
        p1 ≤ ((tSet ×ˢ uSet).image (fun q => ({q.1, q.2} : Finset (Fin r)))).card := Finset.card_le_card hsub
        _ ≤ (tSet ×ˢ uSet).card := Finset.card_image_le
        _ = tSet.card * uSet.card := Finset.card_product tSet uSet
        _ = mixed := by rw [htSet_card, huSet_card]
    have hcent_nat : (decide (sites ∈ U)).toNat = center.toNat := by rw [hcent_eq]
    change loss ≤ (decide (sites ∈ U)).toNat + (6 + 9 * (decide (sites ∈ U)).toNat) * uSet.card +
      36 * P2.card + 54 * (p1 + p2) + (54 + 81 * (decide (sites ∈ U)).toNat) * p2
    rw [hcent_nat, huSet_card, hP2_card]
    have hge1 : pairs - cheap ≤ p1 + p2 := by omega
    have hge2 : pairs - (cheap + mixed) ≤ p2 := by omega
    have hm1 : 54 * (pairs - cheap) ≤ 54 * (p1 + p2) := Nat.mul_le_mul_left 54 hge1
    have hm2 : (54 + 81 * center.toNat) * (pairs - (cheap + mixed)) ≤ (54 + 81 * center.toNat) * p2 :=
      Nat.mul_le_mul_left _ hge2
    dsimp only [loss]
    omega
  · let tSet : Finset (Fin r) := sites.filter (fun i => i.val < t)
    have htSet_card : tSet.card = t := by
      have hbij : tSet.card = (Finset.univ : Finset (Fin t)).card := by
        symm
        refine Finset.card_nbij (fun i : Fin t => (⟨i.val, by omega⟩ : Fin r)) ?_ ?_ ?_
        · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
        · intro i _ j _ heq; dsimp only at heq; exact Fin.ext (congrArg (fun x : Fin r => x.val) heq)
        · intro i hi
          have hlt := (Finset.mem_filter.mp hi).2
          exact ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    let uSet : Finset (Fin r) := sites \ tSet
    have hdisj_tu : Disjoint tSet uSet := Finset.disjoint_sdiff
    have huSet_card : uSet.card = units := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, htSet_card]
    let All0 : Finset (Finset (Fin r)) := tSet.powersetCard 2
    let All1 : Finset (Finset (Fin r)) := (tSet ×ˢ uSet).image (fun q => ({q.1, q.2} : Finset (Fin r)))
    let All2 : Finset (Finset (Fin r)) := uSet.powersetCard 2
    have hAll0_card : All0.card = cheap := by
      rw [Finset.card_powersetCard, htSet_card]
    have hAll1_card : All1.card = mixed := by
      have hinj : Set.InjOn (fun q : Fin r × Fin r => ({q.1, q.2} : Finset (Fin r))) (↑(tSet ×ˢ uSet) : Set (Fin r × Fin r)) := by
        rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
        dsimp only at heq
        rcases Finset.mem_product.mp (Finset.mem_coe.mp h1) with ⟨ha₁, hb₁⟩
        rcases Finset.mem_product.mp (Finset.mem_coe.mp h2) with ⟨ha₂, hb₂⟩
        have ha₁m : a₁ ∈ ({a₂, b₂} : Finset (Fin r)) := heq ▸ Finset.mem_insert_self a₁ _
        rcases Finset.mem_insert.mp ha₁m with rfl | h12
        · have hb₁m : b₁ ∈ ({a₁, b₂} : Finset (Fin r)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b₁)
          rcases Finset.mem_insert.mp hb₁m with hba | hbb
          · exact absurd (hba ▸ hb₁) (Finset.disjoint_left.mp hdisj_tu ha₁)
          · rw [Finset.mem_singleton.mp hbb]
        · exact absurd (Finset.mem_singleton.mp h12 ▸ hb₂) (Finset.disjoint_left.mp hdisj_tu ha₁)
      rw [Finset.card_image_of_injOn hinj, Finset.card_product, htSet_card, huSet_card]
    have hAll0_inter : ∀ P ∈ All0, P.card = 2 ∧ (P ∩ uSet).card = 0 := by
      intro P hP
      rcases Finset.mem_powersetCard.mp hP with ⟨hsub, hcard⟩
      refine ⟨hcard, Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr ?_)⟩
      intro i hi
      rcases Finset.mem_inter.mp hi with ⟨hiP, hiu⟩
      exact Finset.disjoint_left.mp hdisj_tu (hsub hiP) hiu
    have hAll1_inter : ∀ P ∈ All1, P.card = 2 ∧ (P ∩ uSet).card = 1 := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨⟨a, b⟩, hab, rfl⟩
      rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
      have hne : a ≠ b := fun h => Finset.disjoint_left.mp hdisj_tu ha (h ▸ hb)
      have hau : a ∉ uSet := Finset.disjoint_left.mp hdisj_tu ha
      have hinter : ({a, b} : Finset (Fin r)) ∩ uSet = {b} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hxu⟩
          · exact absurd hxu hau
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, hb⟩
      exact ⟨Finset.card_pair hne, by rw [hinter, Finset.card_singleton]⟩
    have hAll2_inter : ∀ P ∈ All2, P.card = 2 ∧ (P ∩ uSet).card = 2 := by
      intro P hP
      rcases Finset.mem_powersetCard.mp hP with ⟨hsub, hcard⟩
      exact ⟨hcard, by rw [Finset.inter_eq_left.mpr hsub, hcard]⟩
    have hAll_disj01 : Disjoint All0 All1 := by
      rw [Finset.disjoint_left]; intro P h0 h1
      have := (hAll0_inter P h0).2; have := (hAll1_inter P h1).2; omega
    have hAll_disj02 : Disjoint All0 All2 := by
      rw [Finset.disjoint_left]; intro P h0 h2
      have := (hAll0_inter P h0).2; have := (hAll2_inter P h2).2; omega
    have hAll_disj12 : Disjoint All1 All2 := by
      rw [Finset.disjoint_left]; intro P h1 h2
      have := (hAll1_inter P h1).2; have := (hAll2_inter P h2).2; omega
    have hAll_union : All0 ∪ All1 ∪ All2 = sites.powersetCard 2 := by
      ext P
      simp only [Finset.mem_union, Finset.mem_powersetCard]
      constructor
      · rintro ((h0 | h1) | h2)
        · exact ⟨Finset.subset_univ _, (hAll0_inter P h0).1⟩
        · exact ⟨Finset.subset_univ _, (hAll1_inter P h1).1⟩
        · exact ⟨Finset.subset_univ _, (hAll2_inter P h2).1⟩
      · rintro ⟨_, hP2⟩
        have hle : (P ∩ uSet).card ≤ 2 := (Finset.card_le_card Finset.inter_subset_left).trans (by omega)
        by_cases h0 : (P ∩ uSet).card = 0
        · left; left
          refine Finset.mem_powersetCard.mpr ⟨?_, hP2⟩
          intro i hiP
          by_contra hit
          have hiu : i ∈ uSet := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩
          have := Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hiP, hiu⟩⟩
          omega
        · by_cases h1 : (P ∩ uSet).card = 1
          · left; right
            rcases Finset.card_eq_one.mp h1 with ⟨b, hb⟩
            have hbP : b ∈ P := (Finset.mem_inter.mp (hb.symm ▸ Finset.mem_singleton_self b)).1
            have hbu : b ∈ uSet := (Finset.mem_inter.mp (hb.symm ▸ Finset.mem_singleton_self b)).2
            have her1 : (P.erase b).card = 1 := by rw [Finset.card_erase_of_mem hbP, hP2]
            rcases Finset.card_eq_one.mp her1 with ⟨a, ha⟩
            have haP : a ∈ P := Finset.mem_of_mem_erase (ha.symm ▸ Finset.mem_singleton_self a)
            have hab : a ≠ b := Finset.ne_of_mem_erase (ha.symm ▸ Finset.mem_singleton_self a)
            have hau : a ∉ uSet := by
              intro h
              have : a ∈ P ∩ uSet := Finset.mem_inter.mpr ⟨haP, h⟩
              rw [hb, Finset.mem_singleton] at this
              exact hab this
            have hat : a ∈ tSet := by
              by_contra hit
              exact hau (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, hit⟩)
            refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨hat, hbu⟩, ?_⟩
            have : insert b (P.erase b) = P := Finset.insert_erase hbP
            rw [ha] at this
            ext x; rw [← this]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          · right
            have h2 : (P ∩ uSet).card = 2 := by omega
            have heq : P ∩ uSet = P := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
            refine Finset.mem_powersetCard.mpr ⟨?_, hP2⟩
            intro i hiP; exact (Finset.mem_inter.mp (heq ▸ hiP)).2
    have hAll_sum : All0.card + All1.card + All2.card = Nat.choose r 2 := by
      have hc := congrArg Finset.card hAll_union
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAll_disj02, hAll_disj12⟩),
          Finset.card_union_of_disjoint hAll_disj01, Finset.card_powersetCard 2 sites,
          show sites.card = r by simp [sites]] at hc
      exact hc
    let q0 := min pairs cheap
    let q1 := min (pairs - q0) mixed
    let q2 := pairs - q0 - q1
    have hq0_le : q0 ≤ All0.card := by rw [hAll0_card]; exact Nat.min_le_right _ _
    have hq1_le : q1 ≤ All1.card := by rw [hAll1_card]; exact Nat.min_le_right _ _
    have hq2_le : q2 ≤ All2.card := by
      have hq : q0 + q1 + q2 = pairs := by dsimp [q0, q1, q2]; omega
      omega
    obtain ⟨Q0, hQ0_sub, hQ0_card⟩ := Finset.exists_subset_card_eq hq0_le
    obtain ⟨Q1, hQ1_sub, hQ1_card⟩ := Finset.exists_subset_card_eq hq1_le
    obtain ⟨Q2, hQ2_sub, hQ2_card⟩ := Finset.exists_subset_card_eq hq2_le
    let Q := Q0 ∪ Q1 ∪ Q2
    have hQ_disj01 : Disjoint Q0 Q1 := Disjoint.mono hQ0_sub hQ1_sub hAll_disj01
    have hQ_disj02 : Disjoint Q0 Q2 := Disjoint.mono hQ0_sub hQ2_sub hAll_disj02
    have hQ_disj12 : Disjoint Q1 Q2 := Disjoint.mono hQ1_sub hQ2_sub hAll_disj12
    have hQ_card : Q.card = pairs := by
      dsimp [Q]
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hQ_disj02, hQ_disj12⟩),
          Finset.card_union_of_disjoint hQ_disj01, hQ0_card, hQ1_card, hQ2_card]
      dsimp [q0, q1, q2]; omega
    let Ucomp : Finset (Finset (Fin r)) :=
      (if center then {(∅ : Finset (Fin r))} else ∅) ∪ (uSet.image (fun i => ({i} : Finset (Fin r)))) ∪ Q
    let U : Finset (Finset (Fin r)) := Ucomp.image (fun S => sites \ S)
    have hUcomp_eq : U.image (fun e => sites \ e) = Ucomp := by
      ext S
      simp only [U, Finset.mem_image]
      constructor
      · rintro ⟨e, ⟨S', hS', rfl⟩, rfl⟩
        rwa [sdiff_sdiff_univ]
      · intro hS
        exact ⟨sites \ S, ⟨S, hS, rfl⟩, sdiff_sdiff_univ S⟩
    have hQ_mem_card : ∀ P ∈ Q, P.card = 2 := by
      intro P hP
      rcases Finset.mem_union.mp hP with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · exact (hAll0_inter P (hQ0_sub h0)).1
        · exact (hAll1_inter P (hQ1_sub h1)).1
      · exact (hAll2_inter P (hQ2_sub h2)).1
    have hUcomp_deg : ∀ S ∈ Ucomp, S.card ≤ 2 := by
      intro S hS
      rcases Finset.mem_union.mp hS with h01 | hQ
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · split_ifs at h0
          · rw [Finset.mem_singleton.mp h0]; simp
          · simp at h0
        · rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩; simp
      · exact (hQ_mem_card S hQ).le
    have hdeg_U : ∀ e ∈ U, (sites \ e).card ≤ 2 := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨S, hS, rfl⟩
      rw [sdiff_sdiff_univ]
      exact hUcomp_deg S hS
    have hcent_U : decide (sites ∈ U) = center := by
      have hiff : sites ∈ U ↔ (∅ : Finset (Fin r)) ∈ Ucomp := by
        simp only [U, Finset.mem_image]
        constructor
        · rintro ⟨S, hS, hEq⟩
          have : S = ∅ := by
            have := congrArg (fun T => sites \ T) hEq
            simpa only [sites, sdiff_sdiff_univ, Finset.sdiff_self] using this
          rwa [← this]
        · intro h0
          exact ⟨∅, h0, Finset.sdiff_empty⟩
      have h0iff : (∅ : Finset (Fin r)) ∈ Ucomp ↔ center = true := by
        dsimp [Ucomp]
        simp only [Finset.mem_union]
        constructor
        · rintro ((h0 | h1) | hQ)
          · cases center
            · simp at h0
            · rfl
          · rcases Finset.mem_image.mp h1 with ⟨i, _, hi⟩
            exact absurd (congrArg Finset.card hi) (by simp)
          · exact absurd (hQ_mem_card ∅ hQ) (by simp)
        · intro hc
          left; left; simp [hc]
      cases center
      · simp [hiff, h0iff]
      · simp [hiff, h0iff]
    have huSet_eq : sites.filter (fun i => ({i} : Finset (Fin r)) ∈ Ucomp) = uSet := by
      ext i
      simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [Ucomp]
      simp only [Finset.mem_union]
      constructor
      · rintro ((h0 | h1) | hQ)
        · split_ifs at h0
          · exact absurd (congrArg Finset.card (Finset.mem_singleton.mp h0)) (by simp)
          · simp at h0
        · rcases Finset.mem_image.mp h1 with ⟨j, hju, hj⟩
          rwa [Finset.singleton_injective hj] at hju
        · exact absurd (hQ_mem_card {i} hQ) (by simp)
      · intro hi
        left; right; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hP2_eq : Ucomp.filter (fun S => S.card = 2) = Q := by
      ext S
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hSU, hS2⟩
        dsimp [Ucomp] at hSU
        rcases Finset.mem_union.mp hSU with h01 | hQ
        · rcases Finset.mem_union.mp h01 with h0 | h1
          · split_ifs at h0
            · rw [Finset.mem_singleton.mp h0] at hS2; simp at hS2
            · simp at h0
          · rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩; simp at hS2
        · exact hQ
      · intro hSQ
        exact ⟨Finset.mem_union_right _ hSQ, hQ_mem_card S hSQ⟩
    have hQ1_filt : Q.filter (fun P => (P ∩ uSet).card = 1) = Q1 := by
      ext P
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hPQ, h1⟩
        rcases Finset.mem_union.mp hPQ with h01 | h2
        · rcases Finset.mem_union.mp h01 with h0 | h1'
          · have := (hAll0_inter P (hQ0_sub h0)).2; omega
          · exact h1'
        · have := (hAll2_inter P (hQ2_sub h2)).2; omega
      · intro hP1
        exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hP1), (hAll1_inter P (hQ1_sub hP1)).2⟩
    have hQ2_filt : Q.filter (fun P => (P ∩ uSet).card = 2) = Q2 := by
      ext P
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hPQ, h2⟩
        rcases Finset.mem_union.mp hPQ with h01 | h2'
        · rcases Finset.mem_union.mp h01 with h0 | h1
          · have := (hAll0_inter P (hQ0_sub h0)).2; omega
          · have := (hAll1_inter P (hQ1_sub h1)).2; omega
        · exact h2'
      · intro hP2
        exact ⟨Finset.mem_union_right _ hP2, (hAll2_inter P (hQ2_sub hP2)).2⟩
    have hU_units : (U.filter (fun e => (sites \ e).card = 1)).card = units := by
      rw [← huSet_card]
      symm
      refine Finset.card_nbij (fun i => sites \ {i}) ?_ ?_ ?_
      · intro i hi
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := by
          rw [← huSet_eq] at hi; exact (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨{i}, hiU, rfl⟩, ?_⟩
        rw [sdiff_sdiff_univ]; simp
      · intro i _ j _ heq
        dsimp only at heq
        have h1 : ({i} : Finset (Fin r)) = {j} := by
          have := congrArg (fun S => sites \ S) heq
          simpa only [sites, sdiff_sdiff_univ] using this
        exact Finset.singleton_injective h1
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heU, he1⟩
        rcases Finset.card_eq_one.mp he1 with ⟨i, hi⟩
        have hiU : ({i} : Finset (Fin r)) ∈ Ucomp := by
          rw [← hUcomp_eq]; exact Finset.mem_image.mpr ⟨e, heU, hi⟩
        have hiu : i ∈ uSet := by
          rw [← huSet_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiU⟩
        exact ⟨i, hiu, by dsimp only; rw [← hi]; exact sdiff_sdiff_univ e⟩
    have hU_pairs : (U.filter (fun e => (sites \ e).card = 2)).card = pairs := by
      rw [← hQ_card]
      symm
      refine Finset.card_nbij (fun S => sites \ S) ?_ ?_ ?_
      · intro S hS
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨S, Finset.mem_union_right _ hS, rfl⟩, ?_⟩
        rw [sdiff_sdiff_univ]; exact hQ_mem_card S hS
      · intro S₁ _ S₂ _ heq
        dsimp only at heq
        have := congrArg (fun S => sites \ S) heq
        simpa only [sites, sdiff_sdiff_univ] using this
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heU, he2⟩
        have hSU : sites \ e ∈ Ucomp := by
          rw [← hUcomp_eq]; exact Finset.mem_image.mpr ⟨e, heU, rfl⟩
        have hSQ : sites \ e ∈ Q := by
          rw [← hP2_eq]; exact Finset.mem_filter.mpr ⟨hSU, he2⟩
        exact ⟨sites \ e, hSQ, sdiff_sdiff_univ e⟩
    refine ⟨U, ⟨hcent_U, hdeg_U, hU_units, hU_pairs⟩, ?_⟩
    trans 11 ^ (lostSet (kinds \ U)).card
    · convert kernelSize_eq_pow_lost (kinds \ U) <;> rfl
    · congr 1
      have hexact := lost_card_exact U hdeg_U
      dsimp only at hexact
      rw [hexact, hUcomp_eq, huSet_eq, hP2_eq, hQ1_filt, hQ2_filt, hcent_U, huSet_card, hQ_card, hQ1_card, hQ2_card]
      have h12 : q1 + q2 = pairs - cheap := by dsimp [q0, q1, q2]; omega
      have h2 : q2 = pairs - (cheap + mixed) := by dsimp [q0, q1, q2]; omega
      rw [h12, h2]

end PEqualNP.Outside.L_lib_1167_aux

theorem PEqualNP.Outside.L_lib_1167 : ∀ (r t pairs : Nat) (center : Bool), t ≤ r → pairs ≤ Nat.choose r 2 →
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let zeroRead := fun (d : Word → Fin 11) (q : Kind × Word) =>
    ((cube.filter (fun x => pass q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0
  let kernelSize := fun (M : Finset Kind) =>
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product cube, zeroRead d q)).card
  let units := r - t
  let cheap := Nat.choose t 2
  let mixed := t * units
  let loss := center.toNat + (6 + 9 * center.toNat) * units + 36 * pairs +
    54 * (pairs - cheap) + (54 + 81 * center.toNat) * (pairs - (cheap + mixed))
  let allowed := fun (U : Finset Kind) =>
    (decide (sites ∈ U) = center) ∧ (∀ e ∈ U, (sites \ e).card ≤ 2) ∧
    (U.filter (fun e => (sites \ e).card = 1)).card = units ∧
    (U.filter (fun e => (sites \ e).card = 2)).card = pairs
  (∀ U : Finset Kind, allowed U → 11 ^ loss ≤ kernelSize (kinds \ U)) ∧
    ∃ U : Finset Kind, allowed U ∧ kernelSize (kinds \ U) = 11 ^ loss :=
  PEqualNP.Outside.L_lib_1167_aux.main

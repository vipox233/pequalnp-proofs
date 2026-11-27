import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic

namespace PEqualNP.Outside.L_lib_437_aux

def chi (bit : ZMod 2) : ℤ :=
  if bit = 0 then 1 else -1

lemma chi_add (u v : ZMod 2) : chi (u + v) = chi u * chi v := by
  fin_cases u <;> fin_cases v <;> decide

lemma chi_add_one (u : ZMod 2) : chi (u + 1) = -chi u := by
  fin_cases u <;> decide

lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ b = a := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := fun x => by fin_cases x <;> rfl
  constructor
  · intro h
    calc b = 0 + b := (zero_add b).symm
      _ = (a + a) + b := by rw [h2 a]
      _ = a + (a + b) := add_assoc a a b
      _ = a + 0 := by rw [h]
      _ = a := add_zero a
  · intro h
    rw [h]
    exact h2 a

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma sum_chi_dotProduct (m : ℕ) (u : Fin m → ZMod 2) :
    (∑ b : Fin m → ZMod 2, chi (dotProduct b u)) = if u = 0 then (2 : ℤ) ^ m else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp only [dotProduct_zero, chi, ↓reduceIte, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow,
      Nat.cast_ofNat]
  · simp only [hu, ↓reduceIte]
    have hex : ∃ j : Fin m, u j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu (funext hall)
    rcases hex with ⟨j, hj⟩
    have huj : u j = 1 := zmod2_eq_one_of_ne_zero hj
    let e : Fin m → ZMod 2 := Pi.single j (1 : ZMod 2)
    have hdot_e : dotProduct e u = 1 := by
      simp [dotProduct, e, Pi.single_apply, huj]
    set S : ℤ := ∑ b : Fin m → ZMod 2, chi (dotProduct b u)
    have hshift : S = -S := by
      calc S = ∑ b : Fin m → ZMod 2, chi (dotProduct (b + e) u) := by
            exact (Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)).symm
        _ = ∑ b : Fin m → ZMod 2, -chi (dotProduct b u) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [add_dotProduct, hdot_e, chi_add_one]
        _ = -S := Finset.sum_neg_distrib (fun b => chi (dotProduct b u))
    omega

end PEqualNP.Outside.L_lib_437_aux

theorem PEqualNP.Outside.L_lib_437 : ∀ n m : ℕ,
  let X := Fin n → ZMod 2
  let Y := Fin m → ZMod 2
  let s := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ (rows : Fin m → X) (h : X → ℤ) (target : Y),
    let Q := fun (x : X) (i : Fin m) => dotProduct (rows i) x
    let adj := fun (b : Y) (j : Fin n) => ∑ i : Fin m, b i * rows i j
    (2:ℤ)^m * (∑ x : X, if Q x = target then h x else 0) =
      ∑ b : Y, s (dotProduct b target) *
        ∑ x : X, h x * s (dotProduct (adj b) x) := by
  intro n m X Y s rows h target Q adj
  have htranspose : ∀ (b : Y) (x : X), dotProduct (adj b) x = dotProduct b (Q x) := by
    intro b x
    simp only [dotProduct, adj, Q, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrhs :
      (∑ b : Y, s (dotProduct b target) * ∑ x : X, h x * s (dotProduct (adj b) x)) =
      ∑ x : X, h x * ∑ b : Y, PEqualNP.Outside.L_lib_437_aux.chi (dotProduct b (target + Q x)) := by
    calc (∑ b : Y, s (dotProduct b target) * ∑ x : X, h x * s (dotProduct (adj b) x))
        = ∑ b : Y, ∑ x : X, h x * (s (dotProduct b target) * s (dotProduct b (Q x))) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [htranspose b x]
          ring
      _ = ∑ x : X, ∑ b : Y, h x * (s (dotProduct b target) * s (dotProduct b (Q x))) :=
          Finset.sum_comm
      _ = ∑ x : X, h x * ∑ b : Y, PEqualNP.Outside.L_lib_437_aux.chi (dotProduct b (target + Q x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          congr 1
          rw [dotProduct_add]
          exact (PEqualNP.Outside.L_lib_437_aux.chi_add _ _).symm
  rw [hrhs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [PEqualNP.Outside.L_lib_437_aux.sum_chi_dotProduct m (target + Q x)]
  have hiff : target + Q x = 0 ↔ Q x = target := by
    constructor
    · intro hz
      funext i
      have hi := congrFun hz i
      exact (PEqualNP.Outside.L_lib_437_aux.zmod2_add_eq_zero_iff (target i) (Q x i)).mp hi
    · intro heq
      funext i
      exact (PEqualNP.Outside.L_lib_437_aux.zmod2_add_eq_zero_iff (target i) (Q x i)).mpr
        (congrFun heq i)
  by_cases hq : Q x = target
  · have hz : target + Q x = 0 := hiff.mpr hq
    rw [hz]
    simp only [hq, ↓reduceIte]
    ring
  · have hnz : target + Q x ≠ 0 := fun hz => hq (hiff.mp hz)
    simp only [hq, hnz, ↓reduceIte, mul_zero]

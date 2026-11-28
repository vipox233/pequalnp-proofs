import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_929_aux

abbrev F := ZMod 2

lemma zmod2_add_self (a : F) : a + a = 0 := by fin_cases a <;> rfl
lemma zmod2_neg_eq (a : F) : -a = a := by fin_cases a <;> rfl
lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by fin_cases a <;> fin_cases b <;> rfl
lemma zmod2_eq_one_of_ne_zero {a : F} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

def diff {E : Type*} [Add E] (f : E → F) (v x : E) : F := f (x + v) - f x

def Vanishes {E : Type*} [Add E] : ℕ → (E → F) → Prop
  | 0, f => ∀ x, f x = 0
  | n + 1, f => ∀ v, Vanishes n (diff f v)

section Differences

variable {E : Type*} [AddCommGroup E]

lemma vanishes_iff_foldl : ∀ (n : ℕ) (f : E → F),
    Vanishes n f ↔ ∀ (v : Fin n → E) (x : E), (List.ofFn v).foldl diff f x = 0
  | 0, f => by
    simp only [Vanishes, List.ofFn_zero, List.foldl_nil]
    exact ⟨fun h _ x => h x, fun h x => h Fin.elim0 x⟩
  | n + 1, f => by
    constructor
    · intro h v x
      rw [List.ofFn_succ, List.foldl_cons]
      exact (vanishes_iff_foldl n (diff f (v 0))).1 (h (v 0)) (fun i => v i.succ) x
    · intro h u
      rw [vanishes_iff_foldl n (diff f u)]
      intro v x
      have := h (Fin.cons u v) x
      rw [List.ofFn_succ, List.foldl_cons] at this
      simpa [Fin.cons_zero, Fin.cons_succ] using this

lemma vanishes_zero (n : ℕ) : Vanishes n (fun _ : E => (0 : F)) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro u
    have h : diff (fun _ : E => (0 : F)) u = fun _ => 0 := by funext x; simp [diff]
    rw [h]; exact ih

lemma vanishes_succ {n : ℕ} {f : E → F} (h : Vanishes n f) : Vanishes (n + 1) f := by
  induction n generalizing f with
  | zero =>
    have hf : f = fun _ => 0 := funext h
    rw [hf]; exact vanishes_zero 1
  | succ n ih => intro u; exact ih (h u)

lemma vanishes_mono {n m : ℕ} {f : E → F} (h : Vanishes n f) (hnm : n ≤ m) : Vanishes m f := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact vanishes_succ ih

lemma vanishes_const (c : F) : Vanishes 1 (fun _ : E => c) := by
  intro u x; simp [diff]

lemma vanishes_add {n : ℕ} {f g : E → F} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero => intro x; simp [hf x, hg x]
  | succ n ih =>
    intro u
    have h : diff (fun x => f x + g x) u = fun x => diff f u x + diff g u x := by
      funext x; simp only [diff]; ring
    rw [h]; exact ih (hf u) (hg u)

lemma vanishes_sub {n : ℕ} {f g : E → F} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (fun x => f x - g x) := by
  induction n generalizing f g with
  | zero => intro x; simp [hf x, hg x]
  | succ n ih =>
    intro u
    have h : diff (fun x => f x - g x) u = fun x => diff f u x - diff g u x := by
      funext x; simp only [diff]; ring
    rw [h]; exact ih (hf u) (hg u)

lemma vanishes_mul_const {n : ℕ} (c : F) {f : E → F} (hf : Vanishes n f) :
    Vanishes n (fun x => c * f x) := by
  induction n generalizing f with
  | zero => intro x; simp [hf x]
  | succ n ih =>
    intro u
    have h : diff (fun x => c * f x) u = fun x => c * diff f u x := by
      funext x; simp only [diff]; ring
    rw [h]; exact ih (hf u)

lemma vanishes_sum {ι : Type*} (s : Finset ι) {n : ℕ} (f : ι → E → F)
    (hf : ∀ i ∈ s, Vanishes n (f i)) : Vanishes n (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vanishes_zero n
  | insert a s ha ih =>
    have h1 : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; exact Finset.sum_insert ha
    rw [h1]
    exact vanishes_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma vanishes_comp_affine {E' : Type*} [AddCommGroup E'] {n : ℕ} {f : E → F}
    (hf : Vanishes n f) (L : E' →+ E) (c : E) : Vanishes n (fun x => f (L x + c)) := by
  induction n generalizing f with
  | zero => intro x; exact hf (L x + c)
  | succ n ih =>
    intro u
    have h : diff (fun x => f (L x + c)) u = fun x => diff f (L u) (L x + c) := by
      funext x; simp only [diff, map_add, add_right_comm]
    rw [h]; exact ih (hf (L u))

lemma vanishes_shift {n : ℕ} {f : E → F} (hf : Vanishes n f) (c : E) :
    Vanishes n (fun x => f (x + c)) :=
  vanishes_comp_affine hf (AddMonoidHom.id E) c

lemma vanishes_addHom (L : E →+ F) : Vanishes 2 (fun x => L x) := by
  intro u v x
  simp only [diff, map_add]; ring

lemma vanishes_affine (L : E →+ F) (c : F) : Vanishes 2 (fun x => L x + c) :=
  vanishes_add (vanishes_addHom L) (vanishes_mono (vanishes_const c) (by omega))

lemma vanishes_mul_addHom {n : ℕ} (L : E →+ F) {f : E → F} (hf : Vanishes n f) :
    Vanishes (n + 1) (fun x => L x * f x) := by
  induction n generalizing f with
  | zero =>
    have h0 : (fun x => L x * f x) = fun _ => 0 := by funext x; simp [hf x]
    rw [h0]; exact vanishes_zero 1
  | succ n ih =>
    intro u
    have h : diff (fun x => L x * f x) u =
        fun x => L x * diff f u x + L u * f (x + u) := by
      funext x; simp only [diff, map_add]; ring
    rw [h]
    exact vanishes_add (ih (hf u)) (vanishes_mul_const (L u) (vanishes_shift hf u))

lemma vanishes_prod_addHom {ι : Type*} (I : Finset ι) (L : ι → (E →+ F)) :
    Vanishes (I.card + 1) (fun x => ∏ a ∈ I, L a x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using vanishes_const (E := E) 1
  | insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    have h : (fun x => ∏ b ∈ insert a s, L b x) = fun x => L a x * ∏ b ∈ s, L b x := by
      funext x; exact Finset.prod_insert ha
    rw [h]
    exact vanishes_mul_addHom (L a) ih

end Differences

def chi (x : F) : ℤ := if x = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl
lemma chi_one : chi 1 = -1 := rfl

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_sub (a b : F) : chi (a - b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma sum_chi_mul (a : F) : (∑ x : F, chi (x * a)) = if a = 0 then 2 else 0 := by
  fin_cases a <;> decide

lemma sum_chi_dot (m : ℕ) (v : Fin m → F) :
    (∑ c : Fin m → F, chi (∑ j : Fin m, c j * v j)) = if v = 0 then (2 : ℤ) ^ m else 0 := by
  have h1 : (∑ c : Fin m → F, chi (∑ j : Fin m, c j * v j)) =
      ∏ j : Fin m, ∑ x : F, chi (x * v j) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chi_sum]
  rw [h1]
  by_cases hv : v = 0
  · subst hv
    simp [sum_chi_mul, chi_zero]
  · rw [if_neg hv]
    have hex : ∃ j : Fin m, v j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext h)
    obtain ⟨j₀, hj₀⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
    rw [sum_chi_mul, if_neg hj₀]

def blockProd {q r : ℕ} (S : Finset (Fin q)) (u : Fin q → Fin r → F) : F :=
  ∑ i ∈ S, ∏ a : Fin r, u i a

lemma prod_snoc_eq {r : ℕ} (u : Fin r → F) (z : F) :
    (∏ a : Fin (r + 1), Fin.snoc u z a) = z * ∏ a : Fin r, u a := by
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, mul_comm]

lemma scalar_bias_base (q : ℕ) (S : Finset (Fin q)) (g : (Fin q → Fin 1 → F) → F)
    (hg : Vanishes 1 g) :
    |∑ u : Fin q → Fin 1 → F, chi (blockProd S u + g u)| ≤
      ((2 : ℤ) ^ 1 - 2) ^ S.card * ((2 : ℤ) ^ 1) ^ (q - S.card) := by
  have hg0 : ∀ u, g u = g 0 := by
    intro u
    have := hg u 0
    simp only [diff, zero_add, sub_eq_zero] at this
    exact this
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hcard : S.card ≠ 0 := Finset.card_ne_zero.2 ⟨i₀, hi₀⟩
    have hzero : ((2 : ℤ) ^ 1 - 2) ^ S.card * ((2 : ℤ) ^ 1) ^ (q - S.card) = 0 := by
      norm_num [zero_pow hcard]
    rw [hzero]
    let flip : (Fin q → Fin 1 → F) → (Fin q → Fin 1 → F) :=
      fun u i a => if i = i₀ then u i a + 1 else u i a
    have hflip_inv : Function.Involutive flip := by
      intro u; funext i a; dsimp only [flip]
      split_ifs <;> simp [add_assoc, zmod2_add_self]
    have hflip_bp : ∀ u, blockProd S (flip u) = blockProd S u + 1 := by
      intro u
      unfold blockProd
      rw [← Finset.add_sum_erase _ _ hi₀, ← Finset.add_sum_erase _ _ hi₀]
      have hother : ∑ i ∈ S.erase i₀, ∏ a : Fin 1, flip u i a =
          ∑ i ∈ S.erase i₀, ∏ a : Fin 1, u i a := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i₀ := (Finset.mem_erase.1 hi).1
        simp [flip, hne]
      rw [hother]
      simp [flip, Fin.prod_univ_one]
      ring
    have hsum_neg : (∑ u : Fin q → Fin 1 → F, chi (blockProd S u + g u)) =
        -(∑ u : Fin q → Fin 1 → F, chi (blockProd S u + g u)) := by
      conv_lhs =>
        rw [← Equiv.sum_comp hflip_inv.toPerm (fun u => chi (blockProd S u + g u))]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      change chi (blockProd S (flip u) + g (flip u)) = -chi (blockProd S u + g u)
      rw [hflip_bp, hg0 (flip u), hg0 u, add_right_comm, chi_add, chi_one]
      ring
    have hsum0 : (∑ u : Fin q → Fin 1 → F, chi (blockProd S u + g u)) = 0 := by omega
    rw [hsum0, abs_zero]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    simp only [Finset.card_empty, pow_zero, one_mul, Nat.sub_zero, blockProd, Finset.sum_empty,
      zero_add, pow_one]
    have hconst : ∀ u, chi (g u) = chi (g 0) := fun u => congrArg chi (hg0 u)
    rw [Finset.sum_congr rfl (fun u _ => hconst u), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]
    simp only [pow_one, nsmul_eq_mul, abs_mul]
    have habs : |chi (g 0)| = 1 := by
      generalize g 0 = x; fin_cases x <;> decide
    rw [habs, mul_one, abs_of_nonneg (by positivity)]
    push_cast; rfl

lemma scalar_bias : ∀ (r' q : ℕ) (S : Finset (Fin q)) (g : (Fin q → Fin (r' + 1) → F) → F),
    Vanishes (r' + 1) g →
    |∑ u : Fin q → Fin (r' + 1) → F, chi (blockProd S u + g u)| ≤
      ((2 : ℤ) ^ (r' + 1) - 2) ^ S.card * ((2 : ℤ) ^ (r' + 1)) ^ (q - S.card)
  | 0, q, S, g, hg => scalar_bias_base q S g hg
  | r' + 1, q, S, g, hg => by
    classical
    let r := r' + 1
    let U := Fin q → Fin (r + 1) → F
    let E : ℤ := ∑ u : U, chi (blockProd S u + g u)
    let B : ℤ := ((2 : ℤ) ^ (r + 1) - 2) ^ S.card * ((2 : ℤ) ^ (r + 1)) ^ (q - S.card)
    have hB_nonneg : 0 ≤ B := by
      have h1 : (2 : ℤ) ≤ (2 : ℤ) ^ (r + 1) := by
        have : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (r + 1) := by gcongr <;> omega
        simpa using this
      have h2 : 0 ≤ (2 : ℤ) ^ (r + 1) - 2 := by omega
      positivity
    have hE2 : E ^ 2 = ∑ v : U, ∑ u : U,
        chi ((blockProd S (u + v) - blockProd S u) + diff g v u) := by
      have hmul : E ^ 2 = ∑ u : U, ∑ u' : U,
          chi (blockProd S u' + g u') * chi (blockProd S u + g u) := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u' _ => mul_comm _ _
      rw [hmul]
      have hshift : ∀ u : U, (∑ u' : U, chi (blockProd S u' + g u') * chi (blockProd S u + g u)) =
          ∑ v : U, chi ((blockProd S (u + v) - blockProd S u) + diff g v u) := by
        intro u
        rw [← Equiv.sum_comp (Equiv.addLeft u)]
        refine Finset.sum_congr rfl fun v _ => ?_
        change chi (blockProd S (u + v) + g (u + v)) * chi (blockProd S u + g u) =
          chi (blockProd S (u + v) - blockProd S u + (g (u + v) - g u))
        rw [← chi_sub]
        congr 1; ring
      simp_rw [hshift]
      exact Finset.sum_comm
    have hshift_bound : ∀ v : U,
        |∑ u : U, chi ((blockProd S (u + v) - blockProd S u) + diff g v u)| ≤
          ∏ i : Fin q, (2 : ℤ) * (if i ∈ S ∧ v i ≠ 0 then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r) := by
      intro v
      let T : Finset (Fin q) := S.filter (fun i => v i ≠ 0)
      have hchoose : ∀ i : Fin q, v i ≠ 0 → ∃ a : Fin (r + 1), v i a = 1 := by
        intro i hi
        by_contra h
        push_neg at h
        exact hi (funext fun a => by
          by_contra ha
          exact h a (zmod2_eq_one_of_ne_zero ha))
      let a₀ : Fin q → Fin (r + 1) := fun i =>
        if h : v i ≠ 0 then Classical.choose (hchoose i h) else Fin.last r
      have ha₀_spec : ∀ i, v i ≠ 0 → v i (a₀ i) = 1 := by
        intro i hi
        dsimp only [a₀]
        rw [dif_pos hi]
        exact Classical.choose_spec (hchoose i hi)
      let e : Fin q → Equiv.Perm (Fin (r + 1)) := fun i =>
        if v i ≠ 0 then Equiv.swap (a₀ i) (Fin.last r) else Equiv.refl _
      have he_symm : ∀ i a, e i (e i a) = a := by
        intro i a; dsimp only [e]; split_ifs <;> simp [Equiv.swap_apply_self]
      have he_a0 : ∀ i, v i ≠ 0 → e i (a₀ i) = Fin.last r := by
        intro i hi; simp [e, hi]
      let ymap : (Fin q → Fin r → F) → (Fin q → F) → U := fun u' z i a =>
        Fin.snoc (α := fun _ => F) (u' i) (z i) (e i a)
      let Φ : (Fin q → Fin r → F) × (Fin q → F) → U := fun p i a =>
        if v i ≠ 0 then
          if a = a₀ i then ymap p.1 p.2 i a else ymap p.1 p.2 i a + v i a * (ymap p.1 p.2 i (a₀ i) + 1)
        else ymap p.1 p.2 i a
      let Ψ : U → (Fin q → Fin r → F) × (Fin q → F) := fun w =>
        (fun i b =>
          let a := e i b.castSucc
          if v i ≠ 0 then
            if a = a₀ i then w i a else w i a + v i a * (w i (a₀ i) + 1)
          else w i a,
         fun i =>
          let a := e i (Fin.last r)
          if v i ≠ 0 then
            if a = a₀ i then w i a else w i a + v i a * (w i (a₀ i) + 1)
          else w i a)
      have hΦ_bij : Function.Bijective Φ := by
        refine Function.bijective_iff_has_inverse.2 ⟨Ψ, ?_, ?_⟩
        · rintro ⟨u', z⟩
          apply Prod.ext
          · funext i b
            dsimp only [Ψ, Φ]
            by_cases hi : v i ≠ 0
            · simp only [ite_eq_left hi]
              have hne : e i b.castSucc ≠ a₀ i := by
                intro h
                have := congrArg (e i) h
                rw [he_symm, he_a0 i hi] at this
                exact Fin.castSucc_ne_last b this
              rw [ite_eq_right hne, ite_eq_right hne]
              simp only [↓reduceIte]
              have : ymap u' z i (e i b.castSucc) = u' i b := by
                simp [ymap, he_symm, Fin.snoc_castSucc]
              rw [this, add_assoc, zmod2_add_self, add_zero]
            · simp only [ite_eq_right hi, ymap, he_symm, Fin.snoc_castSucc]
          · funext i
            dsimp only [Ψ, Φ]
            by_cases hi : v i ≠ 0
            · simp only [ite_eq_left hi]
              have heq : e i (Fin.last r) = a₀ i := by simp [e, hi]
              rw [ite_eq_left heq, ite_eq_left heq]
              simp [ymap, he_symm, Fin.snoc_last]
            · simp only [ite_eq_right hi, ymap, he_symm, Fin.snoc_last]
        · intro w
          funext i a
          dsimp only [Ψ, Φ, ymap]
          by_cases hi : v i ≠ 0
          · simp only [ite_eq_left hi]
            have h1 : ∀ c : Fin (r + 1),
                Fin.snoc (α := fun _ => F) (fun b : Fin r =>
                  if e i b.castSucc = a₀ i then w i (e i b.castSucc)
                  else w i (e i b.castSucc) + v i (e i b.castSucc) * (w i (a₀ i) + 1))
                (if e i (Fin.last r) = a₀ i then w i (e i (Fin.last r))
                 else w i (e i (Fin.last r)) + v i (e i (Fin.last r)) * (w i (a₀ i) + 1)) (e i c) =
                (if c = a₀ i then w i c else w i c + v i c * (w i (a₀ i) + 1)) := by
              intro c
              cases hc : e i c using Fin.lastCases with
              | last =>
                have hc' : c = e i (Fin.last r) := by rw [← hc, he_symm]
                rw [Fin.snoc_last, ← hc']
              | cast b =>
                have hc' : c = e i b.castSucc := by rw [← hc, he_symm]
                rw [Fin.snoc_castSucc, ← hc']
            rw [h1 a, h1 (a₀ i), ite_eq_left rfl]
            by_cases ha : a = a₀ i
            · rw [ite_eq_left ha, ite_eq_left ha]
            · rw [ite_eq_right ha, ite_eq_right ha, add_assoc, zmod2_add_self, add_zero]
          · simp only [ite_eq_right hi]
            cases ha : e i a using Fin.lastCases with
            | last =>
              have ha' : a = e i (Fin.last r) := by rw [← ha, he_symm]
              rw [Fin.snoc_last, ← ha']
            | cast b =>
              have ha' : a = e i b.castSucc := by rw [← ha, he_symm]
              rw [Fin.snoc_castSucc, ← ha']
      have hΦ_affine : ∀ z : Fin q → F,
          ∃ (L : (Fin q → Fin r → F) →+ U) (c : U), ∀ u', Φ (u', z) = L u' + c := by
        intro z
        let L : (Fin q → Fin r → F) →+ U :=
          { toFun := fun u' i a =>
              if v i ≠ 0 then
                if a = a₀ i then 0 else Fin.snoc (α := fun _ => F) (u' i) 0 (e i a)
              else Fin.snoc (α := fun _ => F) (u' i) 0 (e i a)
            map_zero' := by
              funext i a
              have h0 : Fin.snoc (α := fun _ => F) (0 : Fin r → F) (0 : F) (e i a) = 0 := by
                cases e i a using Fin.lastCases <;> simp [Fin.snoc_last, Fin.snoc_castSucc]
              split_ifs
              · rfl
              · exact h0
              · exact h0
            map_add' := fun u1 u2 => by
              funext i a
              have ha' : Fin.snoc (α := fun _ => F) (u1 i + u2 i) (0 : F) (e i a) =
                  Fin.snoc (α := fun _ => F) (u1 i) 0 (e i a) + Fin.snoc (α := fun _ => F) (u2 i) 0 (e i a) := by
                cases e i a using Fin.lastCases <;> simp [Fin.snoc_last, Fin.snoc_castSucc]
              change _ = (if v i ≠ 0 then if a = a₀ i then 0 else Fin.snoc (α := fun _ => F) (u1 i) 0 (e i a) else Fin.snoc (α := fun _ => F) (u1 i) 0 (e i a)) +
                         (if v i ≠ 0 then if a = a₀ i then 0 else Fin.snoc (α := fun _ => F) (u2 i) 0 (e i a) else Fin.snoc (α := fun _ => F) (u2 i) 0 (e i a))
              split_ifs <;> simp [ha'] }
        let c : U := fun i a =>
          if v i ≠ 0 then
            if a = a₀ i then z i else v i a * (z i + 1)
          else Fin.snoc (α := fun _ => F) (0 : Fin r → F) (z i) (e i a)
        refine ⟨L, c, fun u' => ?_⟩
        funext i a
        change Φ (u', z) i a = L u' i a + c i a
        dsimp only [Φ, L, c, ymap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        by_cases hi : v i ≠ 0
        · simp only [ite_eq_left hi]
          have hya0 : Fin.snoc (α := fun _ => F) (u' i) (z i) (e i (a₀ i)) = z i := by
            rw [he_a0 i hi, Fin.snoc_last]
          rw [hya0]
          by_cases ha : a = a₀ i
          · rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left ha, ha, hya0, zero_add]
          · rw [ite_eq_right ha, ite_eq_right ha, ite_eq_right ha]
            have hne : e i a ≠ Fin.last r := by
              intro h; exact ha (by rw [← he_symm i a, h]; simp [e, hi])
            obtain ⟨b, hb⟩ := Fin.exists_castSucc_eq.2 hne
            rw [← hb, Fin.snoc_castSucc, Fin.snoc_castSucc]
        · simp only [ite_eq_right hi]
          cases e i a using Fin.lastCases <;> simp [Fin.snoc_last, Fin.snoc_castSucc]
      have hΦ_bp : ∀ (u' : Fin q → Fin r → F) (z : Fin q → F),
          blockProd S (Φ (u', z) + v) - blockProd S (Φ (u', z)) = blockProd T u' := by
        intro u' z
        unfold blockProd
        rw [← Finset.sum_sub_distrib]
        have hsplit : ∀ i ∈ S,
            (∏ a : Fin (r + 1), (Φ (u', z) + v) i a) - (∏ a : Fin (r + 1), Φ (u', z) i a) =
            if v i ≠ 0 then ∏ b : Fin r, u' i b else 0 := by
          intro i _
          by_cases hi : v i ≠ 0
          · rw [ite_eq_left hi]
            have hv1 : v i (a₀ i) = 1 := ha₀_spec i hi
            have hya0 : ymap u' z i (a₀ i) = z i := by
              simp [ymap, he_a0 i hi, Fin.snoc_last]
            have hprod_y : (∏ a ∈ Finset.univ.erase (a₀ i), ymap u' z i a) = ∏ b : Fin r, u' i b := by
              refine Finset.prod_bij (fun a _ => (e i a).castPred (by
                intro h; exact (Finset.mem_erase.1 ‹_›).1 (by rw [← he_symm i a, h]; simp [e, hi])))
                ?_ ?_ ?_ ?_
              · intro a _; exact Finset.mem_univ _
              · intro a₁ ha₁ a₂ ha₂ heq
                have h1 : e i a₁ = e i a₂ := by
                  have hlt1 : e i a₁ ≠ Fin.last r := fun h =>
                    (Finset.mem_erase.1 ha₁).1 (by rw [← he_symm i a₁, h]; simp [e, hi])
                  have hlt2 : e i a₂ ≠ Fin.last r := fun h =>
                    (Finset.mem_erase.1 ha₂).1 (by rw [← he_symm i a₂, h]; simp [e, hi])
                  rw [← Fin.castSucc_castPred (e i a₁) hlt1, ← Fin.castSucc_castPred (e i a₂) hlt2, heq]
                exact (e i).injective h1
              · intro b _
                refine ⟨e i b.castSucc, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, ?_⟩
                · intro h
                  have := congrArg (e i) h
                  rw [he_symm, he_a0 i hi] at this
                  exact Fin.castSucc_ne_last b this
                · simp [he_symm]
              · intro a ha
                have hlt : e i a ≠ Fin.last r := fun h =>
                  (Finset.mem_erase.1 ha).1 (by rw [← he_symm i a, h]; simp [e, hi])
                dsimp only [ymap]
                conv_lhs => rw [← Fin.castSucc_castPred (e i a) hlt]
                rw [Fin.snoc_castSucc]
            have hz01 : z i = 0 ∨ z i = 1 := by
              generalize z i = x
              fin_cases x
              · exact Or.inl rfl
              · exact Or.inr rfl
            rcases hz01 with hz | hz
            · have hp2 : (∏ a : Fin (r + 1), Φ (u', z) i a) = 0 := by
                refine Finset.prod_eq_zero (Finset.mem_univ (a₀ i)) ?_
                simp [Φ, ite_eq_left hi, hya0, hz]
              have hp1 : (∏ a : Fin (r + 1), (Φ (u', z) + v) i a) = ∏ b : Fin r, u' i b := by
                rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (a₀ i))]
                have h0 : (Φ (u', z) + v) i (a₀ i) = 1 := by
                  change Φ (u', z) i (a₀ i) + v i (a₀ i) = 1
                  simp [Φ, ite_eq_left hi, hya0, hz, hv1]
                rw [h0, one_mul, ← hprod_y]
                refine Finset.prod_congr rfl fun a ha => ?_
                have hne : a ≠ a₀ i := (Finset.mem_erase.1 ha).1
                change Φ (u', z) i a + v i a = ymap u' z i a
                dsimp only [Φ]
                rw [ite_eq_left hi, ite_eq_right hne, hya0, hz, zero_add, mul_one, add_assoc, zmod2_add_self, add_zero]
              rw [hp1, hp2, sub_zero]
            · have hp1 : (∏ a : Fin (r + 1), (Φ (u', z) + v) i a) = 0 := by
                refine Finset.prod_eq_zero (Finset.mem_univ (a₀ i)) ?_
                change Φ (u', z) i (a₀ i) + v i (a₀ i) = 0
                dsimp only [Φ]
                rw [ite_eq_left hi, ite_eq_left rfl, hya0, hz, hv1, zmod2_add_self]
              have hp2 : (∏ a : Fin (r + 1), Φ (u', z) i a) = ∏ b : Fin r, u' i b := by
                rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (a₀ i))]
                have h0 : Φ (u', z) i (a₀ i) = 1 := by
                  dsimp only [Φ]; rw [ite_eq_left hi, ite_eq_left rfl, hya0, hz]
                rw [h0, one_mul, ← hprod_y]
                refine Finset.prod_congr rfl fun a ha => ?_
                have hne : a ≠ a₀ i := (Finset.mem_erase.1 ha).1
                dsimp only [Φ]
                rw [ite_eq_left hi, ite_eq_right hne, hya0, hz, zmod2_add_self, mul_zero, add_zero]
              rw [hp1, hp2, zero_sub, zmod2_neg_eq]
          · rw [ite_eq_right hi]
            have hv0 : v i = 0 := not_not.1 hi
            have heq : ∀ a, (Φ (u', z) + v) i a = Φ (u', z) i a := fun a => by
              change Φ (u', z) i a + v i a = Φ (u', z) i a
              rw [hv0]; simp
            simp_rw [heq]; rw [sub_self]
        rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter]
      have hreindex : (∑ u : U, chi ((blockProd S (u + v) - blockProd S u) + diff g v u)) =
          ∑ z : Fin q → F, ∑ u' : Fin q → Fin r → F,
            chi (blockProd T u' + diff g v (Φ (u', z))) := by
        rw [← Fintype.sum_bijective Φ hΦ_bij
          (fun p => chi ((blockProd S (Φ p + v) - blockProd S (Φ p)) + diff g v (Φ p))) _ (fun _ => rfl)]
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u' _ => ?_
        rw [hΦ_bp]
      rw [hreindex]
      have hslice : ∀ z : Fin q → F,
          |∑ u' : Fin q → Fin r → F, chi (blockProd T u' + diff g v (Φ (u', z)))| ≤
            ((2 : ℤ) ^ r - 2) ^ T.card * ((2 : ℤ) ^ r) ^ (q - T.card) := by
        intro z
        obtain ⟨L, c, hLc⟩ := hΦ_affine z
        have hfun : (fun u' => diff g v (Φ (u', z))) = fun u' => diff g v (L u' + c) :=
          funext fun u' => congrArg (diff g v) (hLc u')
        have hvan : Vanishes r (fun u' => diff g v (Φ (u', z))) := by
          rw [hfun]
          exact vanishes_comp_affine (hg v) L c
        exact scalar_bias r' q T (fun u' => diff g v (Φ (u', z))) hvan
      calc |∑ z : Fin q → F, ∑ u' : Fin q → Fin r → F,
              chi (blockProd T u' + diff g v (Φ (u', z)))|
          ≤ ∑ z : Fin q → F, |∑ u' : Fin q → Fin r → F,
              chi (blockProd T u' + diff g v (Φ (u', z)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _z : Fin q → F, ((2 : ℤ) ^ r - 2) ^ T.card * ((2 : ℤ) ^ r) ^ (q - T.card) :=
            Finset.sum_le_sum fun z _ => hslice z
        _ = (2 : ℤ) ^ q * (((2 : ℤ) ^ r - 2) ^ T.card * ((2 : ℤ) ^ r) ^ (q - T.card)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
            simp
        _ = ∏ i : Fin q, (2 : ℤ) * (if i ∈ S ∧ v i ≠ 0 then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            congr 1
            have hTsub : T ⊆ Finset.univ := Finset.subset_univ _
            have hcond : ∀ i : Fin q, (if i ∈ S ∧ v i ≠ 0 then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r) =
                if i ∈ T then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r := fun i => by
              simp [T, Finset.mem_filter]
            simp_rw [hcond]
            rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
            have hc1 : (Finset.univ.filter (· ∈ T)).card = T.card := by
              congr 1; ext i; simp
            have hc2 : (Finset.univ.filter (· ∉ T)).card = q - T.card := by
              have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
              rw [Finset.card_univ, Fintype.card_fin] at this
              have hfeq : Finset.univ.filter (· ∉ T) = Finset.univ \ T := by ext i; simp
              rw [hfeq]; omega
            rw [hc1, hc2]
    have hE2_le : E ^ 2 ≤ B ^ 2 := by
      calc E ^ 2
          = ∑ v : U, ∑ u : U, chi ((blockProd S (u + v) - blockProd S u) + diff g v u) := hE2
        _ ≤ ∑ v : U, |∑ u : U, chi ((blockProd S (u + v) - blockProd S u) + diff g v u)| :=
            Finset.sum_le_sum fun v _ => le_abs_self _
        _ ≤ ∑ v : U, ∏ i : Fin q, (2 : ℤ) * (if i ∈ S ∧ v i ≠ 0 then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r) :=
            Finset.sum_le_sum fun v _ => hshift_bound v
        _ = ∏ i : Fin q, ∑ x : Fin (r + 1) → F,
              (2 : ℤ) * (if i ∈ S ∧ x ≠ 0 then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r) := by
            rw [Fintype.prod_sum]
        _ = ∏ i : Fin q, (if i ∈ S then ((2 : ℤ) ^ (r + 1) - 2) ^ 2 else ((2 : ℤ) ^ (r + 1)) ^ 2) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            have hcardx : Fintype.card (Fin (r + 1) → F) = 2 ^ (r + 1) := by
              rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
            by_cases hi : i ∈ S
            · rw [if_pos hi]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (r + 1) → F))]
              have hne : ∀ x ∈ Finset.univ.erase (0 : Fin (r + 1) → F),
                  (2 : ℤ) * (if i ∈ S ∧ x ≠ 0 then (2 : ℤ) ^ r - 2 else (2 : ℤ) ^ r) =
                    2 * ((2 : ℤ) ^ r - 2) := fun x hx => by
                have hxz : x ≠ 0 := (Finset.mem_erase.1 hx).1
                simp [hi, hxz]
              rw [Finset.sum_congr rfl hne, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, hcardx]
              simp only [hi, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
              have hpos : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
              rw [nsmul_eq_mul, Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
              simp only [pow_succ]
              ring
            · rw [ite_eq_right hi]
              simp only [hi, false_and, ↓reduceIte, Finset.sum_const, Finset.card_univ, hcardx,
                nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
              simp only [pow_succ]
              ring
        _ = B ^ 2 := by
            rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
            have hc1 : (Finset.univ.filter (· ∈ S)).card = S.card := by congr 1; ext i; simp
            have hc2 : (Finset.univ.filter (· ∉ S)).card = q - S.card := by
              have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
              rw [Finset.card_univ, Fintype.card_fin] at this
              have hfeq : Finset.univ.filter (· ∉ S) = Finset.univ \ S := by ext i; simp
              rw [hfeq]; omega
            rw [hc1, hc2]
            dsimp only [B]
            rw [mul_pow]
            congr 1
            · rw [← pow_mul, ← pow_mul, mul_comm]
            · simp only [← pow_mul]; congr 1; ring
    have habs2 : |E| ^ 2 ≤ B ^ 2 := by simpa [sq_abs] using hE2_le
    nlinarith [abs_nonneg E]

def valueFn {r s m : ℕ} (C : Fin s → Fin m → F) (w : Fin s → Fin r → F) (j : Fin m) : F :=
  ∑ i : Fin s, C i j * ∏ a : Fin r, w i a

def scoreFn (r : ℕ) {s m : ℕ} (C : Fin s → Fin m → F) (D : Finset (Fin s)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin s))).filter (fun H =>
    Disjoint H D ∧ ∀ j : Fin m, (∑ i ∈ H, C i j) = 0)).sum (fun H =>
      (2 ^ r) ^ D.card * (2 ^ r - 1) ^ (s - D.card - H.card))

lemma hits_zero_queries {r s m : ℕ} (hr : 1 ≤ r) (C : Fin s → Fin m → F)
    (out : Fin m → (Fin s → Fin r → F) → F) (hlow : ∀ j, Vanishes r (out j)) :
    Nat.card {w : Fin s → Fin r → F // ∀ j, valueFn C w j = out j w} ≤ scoreFn r C ∅ := by
  classical
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  let W := Fin s → Fin (r' + 1) → F
  let hits := Finset.univ.filter (fun w : W => ∀ j, valueFn C w j = out j w)
  have hcard_eq : Nat.card {w : W // ∀ j, valueFn C w j = out j w} = hits.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard_eq]
  have h2m_pos : (0 : ℤ) < (2 : ℤ) ^ m := by positivity
  suffices hZ : (2 : ℤ) ^ m * (hits.card : ℤ) ≤ (2 : ℤ) ^ m * (scoreFn (r' + 1) C ∅ : ℤ) by
    have : (hits.card : ℤ) ≤ (scoreFn (r' + 1) C ∅ : ℤ) := le_of_mul_le_mul_left hZ h2m_pos
    exact_mod_cast this
  have hlhs : (2 : ℤ) ^ m * (hits.card : ℤ) =
      ∑ c : Fin m → F, ∑ w : W, chi (∑ j : Fin m, c j * (valueFn C w j - out j w)) := by
    rw [Finset.sum_comm]
    have hinner : ∀ w : W, (∑ c : Fin m → F, chi (∑ j : Fin m, c j * (valueFn C w j - out j w))) =
        if (∀ j, valueFn C w j = out j w) then (2 : ℤ) ^ m else 0 := by
      intro w
      rw [sum_chi_dot m (fun j => valueFn C w j - out j w)]
      have heq : ((fun j => valueFn C w j - out j w) = 0) ↔ (∀ j, valueFn C w j = out j w) := by
        constructor
        · intro h j; have := congrFun h j; simpa [sub_eq_zero] using this
        · intro h; funext j; simp [h j]
      simp [heq]
    simp_rw [hinner]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hterm : ∀ c : Fin m → F,
      (∑ w : W, chi (∑ j : Fin m, c j * (valueFn C w j - out j w))) ≤
        ∏ i : Fin s, ((2 : ℤ) ^ (r' + 1) - 1 + chi (∑ j : Fin m, c j * C i j)) := by
    intro c
    let wc : Fin s → F := fun i => ∑ j : Fin m, c j * C i j
    let S : Finset (Fin s) := Finset.univ.filter (fun i => wc i ≠ 0)
    let g : W → F := fun w => -∑ j : Fin m, c j * out j w
    have hg : Vanishes (r' + 1) g := by
      have hneg : g = fun w => ∑ j : Fin m, c j * out j w := by
        funext w; exact zmod2_neg_eq _
      rw [hneg]
      exact vanishes_sum Finset.univ _ fun j _ => vanishes_mul_const (c j) (hlow j)
    have harg : ∀ w : W, (∑ j : Fin m, c j * (valueFn C w j - out j w)) = blockProd S w + g w := by
      intro w
      have h1 : (∑ j : Fin m, c j * (valueFn C w j - out j w)) =
          (∑ j : Fin m, c j * valueFn C w j) + g w := by
        dsimp only [g]
        simp_rw [mul_sub, Finset.sum_sub_distrib, sub_eq_add_neg]
      rw [h1]
      congr 1
      unfold valueFn blockProd
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hfactor : ∀ i : Fin s, (∑ j : Fin m, c j * (C i j * ∏ a : Fin (r' + 1), w i a)) =
          wc i * ∏ a : Fin (r' + 1), w i a := fun i => by
        dsimp only [wc]; rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hfactor]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin s => wc i ≠ 0)]
      have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬wc i ≠ 0),
          wc i * ∏ a : Fin (r' + 1), w i a = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have := (Finset.mem_filter.1 hi).2; push_neg at this; simp [this]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h1' : wc i = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.1 hi).2
      rw [h1', one_mul]
    simp_rw [harg]
    calc (∑ w : W, chi (blockProd S w + g w))
        ≤ |∑ w : W, chi (blockProd S w + g w)| := le_abs_self _
      _ ≤ ((2 : ℤ) ^ (r' + 1) - 2) ^ S.card * ((2 : ℤ) ^ (r' + 1)) ^ (s - S.card) :=
          scalar_bias r' s S g hg
      _ = ∏ i : Fin s, ((2 : ℤ) ^ (r' + 1) - 1 + chi (wc i)) := by
          have heq : ∀ i : Fin s, ((2 : ℤ) ^ (r' + 1) - 1 + chi (wc i)) =
              if i ∈ S then (2 : ℤ) ^ (r' + 1) - 2 else (2 : ℤ) ^ (r' + 1) := by
            intro i
            by_cases hi : wc i = 0
            · have hns : i ∉ S := by simp [S, hi]
              rw [if_neg hns, hi, chi_zero]; ring
            · have hs : i ∈ S := by simp [S, hi]
              rw [if_pos hs, zmod2_eq_one_of_ne_zero hi, chi_one]; ring
          simp_rw [heq]
          rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
          have hc1 : (Finset.univ.filter (· ∈ S)).card = S.card := by congr 1; ext i; simp
          have hc2 : (Finset.univ.filter (· ∉ S)).card = s - S.card := by
            have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
            rw [Finset.card_univ, Fintype.card_fin] at this
            have hfeq : Finset.univ.filter (· ∉ S) = Finset.univ \ S := by ext i; simp
            rw [hfeq]; omega
          rw [hc1, hc2]
  have hrhs : (∑ c : Fin m → F, ∏ i : Fin s, ((2 : ℤ) ^ (r' + 1) - 1 + chi (∑ j : Fin m, c j * C i j))) =
      (2 : ℤ) ^ m * (scoreFn (r' + 1) C ∅ : ℤ) := by
    have hexp : ∀ c : Fin m → F,
        (∏ i : Fin s, ((2 : ℤ) ^ (r' + 1) - 1 + chi (∑ j : Fin m, c j * C i j))) =
        ∑ H : Finset (Fin s), ((2 : ℤ) ^ (r' + 1) - 1) ^ (s - H.card) *
          chi (∑ j : Fin m, c j * ∑ i ∈ H, C i j) := by
      intro c
      have hcomm0 : (∏ i : Fin s, ((2 : ℤ) ^ (r' + 1) - 1 + chi (∑ j : Fin m, c j * C i j))) =
          ∏ i : Fin s, (chi (∑ j : Fin m, c j * C i j) + ((2 : ℤ) ^ (r' + 1) - 1)) :=
        Finset.prod_congr rfl fun i _ => add_comm _ _
      rw [hcomm0, Finset.prod_add]
      rw [show (Finset.univ : Finset (Fin s)).powerset = Finset.univ by ext H; simp]
      refine Finset.sum_congr rfl fun H _ => ?_
      rw [Finset.prod_const]
      have hc : (Finset.univ \ H).card = s - H.card := by
        have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H)
        rw [Finset.card_univ, Fintype.card_fin] at this; omega
      rw [hc]
      have hcomm : (∏ i ∈ H, chi (∑ j : Fin m, c j * C i j)) * ((2 : ℤ) ^ (r' + 1) - 1) ^ (s - H.card) =
          ((2 : ℤ) ^ (r' + 1) - 1) ^ (s - H.card) * (∏ i ∈ H, chi (∑ j : Fin m, c j * C i j)) :=
        mul_comm _ _
      rw [hcomm]
      congr 1
      rw [← chi_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hswap : ∀ H : Finset (Fin s),
        (∑ c : Fin m → F, ((2 : ℤ) ^ (r' + 1) - 1) ^ (s - H.card) *
          chi (∑ j : Fin m, c j * ∑ i ∈ H, C i j)) =
        if (∀ j : Fin m, ∑ i ∈ H, C i j = 0) then
          (2 : ℤ) ^ m * ((2 : ℤ) ^ (r' + 1) - 1) ^ (s - H.card)
        else 0 := by
      intro H
      rw [← Finset.mul_sum, sum_chi_dot m (fun j => ∑ i ∈ H, C i j)]
      have heq : ((fun j : Fin m => ∑ i ∈ H, C i j) = 0) ↔ (∀ j : Fin m, ∑ i ∈ H, C i j = 0) :=
        ⟨fun h j => congrFun h j, fun h => funext h⟩
      simp only [heq]
      split_ifs <;> ring
    simp_rw [hswap]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.mul_sum]
    congr 1
    unfold scoreFn
    simp only [Finset.disjoint_empty_right, true_and, Finset.card_empty, pow_zero, one_mul,
      Nat.sub_zero, Nat.cast_sum, Nat.cast_pow]
    refine Finset.sum_congr rfl fun H _ => ?_
    have hpos : 1 ≤ 2 ^ (r' + 1) := Nat.one_le_two_pow
    rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [hlhs, ← hrhs]
  exact Finset.sum_le_sum fun c _ => hterm c

inductive DT (U : Type*) [AddCommGroup U] [Module F U] (m : ℕ) : ℕ → Type _
  | leaf (out : Fin m → U → F) : DT U m 0
  | branch {h : ℕ} (q : U →ₗ[F] F) (c : F) (t0 t1 : DT U m h) : DT U m (h + 1)

def DT.eval {U : Type*} [AddCommGroup U] [Module F U] {m : ℕ} :
    ∀ {h : ℕ}, DT U m h → U → Fin m → F
  | _, .leaf out, u, j => out j u
  | _, .branch q c t0 t1, u, j => if q u + c = 0 then t0.eval u j else t1.eval u j

def DT.allLow {U : Type*} [AddCommGroup U] [Module F U] {m : ℕ} (r : ℕ) :
    ∀ {h : ℕ}, DT U m h → Prop
  | _, .leaf out => ∀ j, Vanishes r (out j)
  | _, .branch _ _ t0 t1 => t0.allLow r ∧ t1.allLow r

def DT.compAffine {U U' : Type*} [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
    {m : ℕ} (L : U' →ₗ[F] U) (a : U) : ∀ {h : ℕ}, DT U m h → DT U' m h
  | _, .leaf out => .leaf (fun j u' => out j (L u' + a))
  | _, .branch q c t0 t1 =>
      .branch (q.comp L) (q a + c) (t0.compAffine L a) (t1.compAffine L a)

lemma DT.eval_compAffine {U U' : Type*} [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
    {m : ℕ} (L : U' →ₗ[F] U) (a : U) :
    ∀ {h : ℕ} (t : DT U m h) (u' : U') (j : Fin m),
      (t.compAffine L a).eval u' j = t.eval (L u' + a) j
  | _, .leaf _, _, _ => rfl
  | _, .branch q c t0 t1, u', j => by
    simp only [DT.compAffine, DT.eval, LinearMap.comp_apply, map_add, add_assoc]
    split_ifs <;> simp [DT.eval_compAffine]

lemma DT.allLow_compAffine {U U' : Type*} [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
    {m r : ℕ} (L : U' →ₗ[F] U) (a : U) :
    ∀ {h : ℕ} {t : DT U m h}, t.allLow r → (t.compAffine L a).allLow r
  | _, .leaf _, ht => fun j => vanishes_comp_affine (ht j) L.toAddMonoidHom a
  | _, .branch _ _ _ _, ht => ⟨DT.allLow_compAffine L a ht.1, DT.allLow_compAffine L a ht.2⟩

def DT.subAffine {U : Type*} [AddCommGroup U] [Module F U] {m : ℕ} (A : Fin m → U → F) :
    ∀ {h : ℕ}, DT U m h → DT U m h
  | _, .leaf out => .leaf (fun j u => out j u - A j u)
  | _, .branch q c t0 t1 => .branch q c (t0.subAffine A) (t1.subAffine A)

lemma DT.eval_subAffine {U : Type*} [AddCommGroup U] [Module F U] {m : ℕ} (A : Fin m → U → F) :
    ∀ {h : ℕ} (t : DT U m h) (u : U) (j : Fin m),
      (t.subAffine A).eval u j = t.eval u j - A j u
  | _, .leaf _, _, _ => rfl
  | _, .branch _ _ t0 t1, u, j => by
    simp only [DT.subAffine, DT.eval]
    split_ifs <;> simp [DT.eval_subAffine]

lemma DT.allLow_subAffine {U : Type*} [AddCommGroup U] [Module F U] {m r : ℕ} {A : Fin m → U → F}
    (hA : ∀ j, Vanishes r (A j)) :
    ∀ {h : ℕ} {t : DT U m h}, t.allLow r → (t.subAffine A).allLow r
  | _, .leaf _, ht => fun j => vanishes_sub (ht j) (hA j)
  | _, .branch _ _ _ _, ht => ⟨DT.allLow_subAffine hA ht.1, DT.allLow_subAffine hA ht.2⟩

lemma scoreFn_insert_succAbove {r s' m : ℕ} (C : Fin (s' + 1) → Fin m → F)
    (i₀ : Fin (s' + 1)) (D' : Finset (Fin s')) :
    scoreFn r C (insert i₀ (D'.map (Fin.succAboveEmb i₀))) =
      2 ^ r * scoreFn r (fun i j => C (i₀.succAbove i) j) D' := by
  classical
  unfold scoreFn
  rw [Finset.mul_sum]
  let C' : Fin s' → Fin m → F := fun i j => C (i₀.succAbove i) j
  let D : Finset (Fin (s' + 1)) := insert i₀ (D'.map (Fin.succAboveEmb i₀))
  have hi₀_not : i₀ ∉ D'.map (Fin.succAboveEmb i₀) := by
    simp only [Finset.mem_map, Fin.succAboveEmb_apply]
    rintro ⟨x, _, hx⟩
    exact Fin.succAbove_ne i₀ x hx
  have hDcard : D.card = D'.card + 1 := by
    rw [Finset.card_insert_of_notMem hi₀_not, Finset.card_map]
  refine Finset.sum_bij (fun H _ => H.preimage (i₀.succAbove) (fun a _ b _ h => Fin.succAbove_right_injective h)) ?_ ?_ ?_ ?_
  · intro H hH
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
    obtain ⟨hdisj, hsyn⟩ := hH
    have hi₀H : i₀ ∉ H := fun hm => Finset.disjoint_left.1 hdisj hm (Finset.mem_insert_self _ _)
    constructor
    · rw [Finset.disjoint_left]
      intro a ha haD'
      have hma : i₀.succAbove a ∈ H := Finset.mem_preimage.1 ha
      have hmd : i₀.succAbove a ∈ D := Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨a, haD', rfl⟩)
      exact Finset.disjoint_left.1 hdisj hma hmd
    · intro j
      have hmap : (H.preimage i₀.succAbove (fun a _ b _ h => Fin.succAbove_right_injective h)).map
          (Fin.succAboveEmb i₀) = H := by
        ext x
        simp only [Finset.mem_map, Fin.succAboveEmb_apply]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact Finset.mem_preimage.1 ha
        · intro hx
          have hne : x ≠ i₀ := fun e => hi₀H (e ▸ hx)
          obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hne
          exact ⟨a, Finset.mem_preimage.2 hx, rfl⟩
      have hsum := hsyn j
      rw [← hmap, Finset.sum_map] at hsum
      exact hsum
  · intro H₁ hH₁ H₂ hH₂ heq
    have hdisj1 := (Finset.mem_filter.1 hH₁).2.1
    have hdisj2 := (Finset.mem_filter.1 hH₂).2.1
    have hi1 : i₀ ∉ H₁ := fun hm => Finset.disjoint_left.1 hdisj1 hm (Finset.mem_insert_self _ _)
    have hi2 : i₀ ∉ H₂ := fun hm => Finset.disjoint_left.1 hdisj2 hm (Finset.mem_insert_self _ _)
    ext x
    by_cases hx : x = i₀
    · subst hx; simp [hi1, hi2]
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hx
      have hmem := Finset.ext_iff.1 heq a
      exact ⟨fun h => Finset.mem_preimage.1 (hmem.1 (Finset.mem_preimage.2 h)),
             fun h => Finset.mem_preimage.1 (hmem.2 (Finset.mem_preimage.2 h))⟩
  · intro H' hH'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH'
    refine ⟨H'.map (Fin.succAboveEmb i₀), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rw [Finset.disjoint_left]
        intro x hx hxd
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
        rcases Finset.mem_insert.1 hxd with h1 | h2
        · exact Fin.succAbove_ne i₀ a h1
        · obtain ⟨b, hb, hba⟩ := Finset.mem_map.1 h2
          have := Fin.succAbove_right_injective hba
          subst this
          exact Finset.disjoint_left.1 hH'.1 ha hb
      · intro j
        rw [Finset.sum_map]
        exact hH'.2 j
    · ext a
      constructor
      · intro h
        have h' := Finset.mem_preimage.1 h
        obtain ⟨b, hb, hba⟩ := Finset.mem_map.1 h'
        exact (Fin.succAbove_right_injective hba) ▸ hb
      · intro h
        exact Finset.mem_preimage.2 (Finset.mem_map.2 ⟨a, h, rfl⟩)
  · intro H hH
    have hdisj := (Finset.mem_filter.1 hH).2.1
    have hi₀H : i₀ ∉ H := fun hm => Finset.disjoint_left.1 hdisj hm (Finset.mem_insert_self _ _)
    have hHcard : (H.preimage i₀.succAbove (fun a _ b _ h => Fin.succAbove_right_injective h)).card = H.card := by
      have hmap : (H.preimage i₀.succAbove (fun a _ b _ h => Fin.succAbove_right_injective h)).map
          (Fin.succAboveEmb i₀) = H := by
        ext x
        simp only [Finset.mem_map, Fin.succAboveEmb_apply]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact Finset.mem_preimage.1 ha
        · intro hx
          have hne : x ≠ i₀ := fun e => hi₀H (e ▸ hx)
          obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hne
          exact ⟨a, Finset.mem_preimage.2 hx, rfl⟩
      conv_rhs => rw [← hmap]
      rw [Finset.card_map]
    change (2 ^ r) ^ D.card * (2 ^ r - 1) ^ (s' + 1 - D.card - H.card) =
      2 ^ r * ((2 ^ r) ^ D'.card * (2 ^ r - 1) ^ (s' - D'.card -
        (H.preimage i₀.succAbove (fun a _ b _ h => Fin.succAbove_right_injective h)).card))
    rw [hDcard, hHcard, pow_succ', mul_assoc]
    congr 2
    rw [Nat.succ_sub_succ_eq_sub]

lemma dt_upper {r m : ℕ} (hr : 2 ≤ r) :
    ∀ (h s : ℕ) (C : Fin s → Fin m → F) (tree : DT (Fin s → Fin r → F) m h),
      tree.allLow r →
      ∃ D : Finset (Fin s), D.card ≤ h ∧
        Nat.card {w : Fin s → Fin r → F // ∀ j, valueFn C w j = tree.eval w j} ≤ scoreFn r C D
  | 0, s, C, .leaf out, hlow =>
    ⟨∅, by simp, hits_zero_queries (by omega) C out hlow⟩
  | h + 1, s, C, .branch q c t0 t1, hlow => by
    classical
    by_cases hq : q = 0
    · subst hq
      by_cases hc : c = 0
      · obtain ⟨D, hDc, hbd⟩ := dt_upper hr h s C t0 hlow.1
        refine ⟨D, by omega, ?_⟩
        have heq : ∀ w, (DT.branch (0 : (Fin s → Fin r → F) →ₗ[F] F) c t0 t1).eval w = t0.eval w := by
          intro w; funext j; simp [DT.eval, hc]
        simpa [heq] using hbd
      · obtain ⟨D, hDc, hbd⟩ := dt_upper hr h s C t1 hlow.2
        refine ⟨D, by omega, ?_⟩
        have heq : ∀ w, (DT.branch (0 : (Fin s → Fin r → F) →ₗ[F] F) c t0 t1).eval w = t1.eval w := by
          intro w; funext j; simp [DT.eval, hc]
        simpa [heq] using hbd
    · let basis : Fin s → Fin r → (Fin s → Fin r → F) := fun i a i' a' =>
        if i' = i ∧ a' = a then 1 else 0
      have hex : ∃ (i₀ : Fin s) (a₀ : Fin r), q (basis i₀ a₀) = 1 := by
        by_contra hnone
        push_neg at hnone
        apply hq
        apply LinearMap.ext
        intro w
        have hw : w = ∑ i : Fin s, ∑ a : Fin r, w i a • basis i a := by
          funext i' a'
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basis]
          rw [Finset.sum_eq_single i']
          · rw [Finset.sum_eq_single a']
            · simp
            · intro a _ ha; simp [ha.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro i _ hi
            refine Finset.sum_eq_zero fun a _ => ?_
            simp [hi.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hw, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_sum]
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [map_smul, smul_eq_mul]
        have h0 : q (basis i a) = 0 := by
          by_contra hnz
          exact hnone i a (zmod2_eq_one_of_ne_zero hnz)
        simp [h0]
      obtain ⟨i₀, a₀, hqa₀⟩ := hex
      cases s with
      | zero => exact Fin.elim0 i₀
      | succ s' =>
        let W := Fin (s' + 1) → Fin r → F
        let W' := Fin s' → Fin r → F
        let C' : Fin s' → Fin m → F := fun i j => C (i₀.succAbove i) j
        let Comp := {a : Fin r // a ≠ a₀}
        let emb : W' →ₗ[F] W :=
          { toFun := fun u => i₀.insertNth (α := fun _ => Fin r → F) (0 : Fin r → F) u
            map_add' := fun u₁ u₂ => by
              funext i
              change i₀.insertNth (α := fun _ => Fin r → F) (0 : Fin r → F) (u₁ + u₂) i =
                i₀.insertNth (α := fun _ => Fin r → F) (0 : Fin r → F) u₁ i +
                i₀.insertNth (α := fun _ => Fin r → F) (0 : Fin r → F) u₂ i
              refine Fin.succAboveCases i₀ ?_ ?_ i
              · simp [Fin.insertNth_apply_same]
              · intro k; simp [Fin.insertNth_apply_succAbove]; rfl
            map_smul' := fun r' u => by
              funext i
              change i₀.insertNth (α := fun _ => Fin r → F) (0 : Fin r → F) (r' • u) i =
                r' • i₀.insertNth (α := fun _ => Fin r → F) (0 : Fin r → F) u i
              refine Fin.succAboveCases i₀ ?_ ?_ i
              · simp [Fin.insertNth_apply_same]
              · intro k; simp [Fin.insertNth_apply_succAbove]; rfl }
        let baseY : (Comp → F) → W := fun y i a =>
          if i = i₀ then
            if ha : a = a₀ then 0 else y ⟨a, ha⟩
          else 0
        let L : W' →ₗ[F] W :=
          { toFun := fun u => emb u + q (emb u) • basis i₀ a₀
            map_add' := fun u₁ u₂ => by
              simp only [map_add, add_smul]
              abel
            map_smul' := fun r' u => by
              simp only [map_smul, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply] }
        let shift : F → (Comp → F) → W := fun b y =>
          baseY y + (b + c + q (baseY y)) • basis i₀ a₀
        let Φ : (F × (Comp → F)) × W' → W := fun p => L p.2 + shift p.1.1 p.1.2
        have hqΦ : ∀ (b : F) (y : Comp → F) (u : W'), q (Φ ((b, y), u)) + c = b := by
          intro b y u
          dsimp only [Φ, L, shift, LinearMap.coe_mk, AddHom.coe_mk]
          rw [map_add, map_add, map_add, map_smul, map_smul, hqa₀, smul_eq_mul, smul_eq_mul,
            mul_one, mul_one]
          calc q (emb u) + q (emb u) + (q (baseY y) + (b + c + q (baseY y))) + c
              = (q (emb u) + q (emb u)) + (q (baseY y) + q (baseY y)) + (c + c) + b := by ring
            _ = b := by simp [zmod2_add_self]
        have hΦ_succ : ∀ b y u k, Φ ((b, y), u) (i₀.succAbove k) = u k := by
          intro b y u k
          have hne : i₀.succAbove k ≠ i₀ := Fin.succAbove_ne i₀ k
          funext a
          change (emb u (i₀.succAbove k) a + q (emb u) * basis i₀ a₀ (i₀.succAbove k) a) +
            (baseY y (i₀.succAbove k) a + (b + c + q (baseY y)) * basis i₀ a₀ (i₀.succAbove k) a) = u k a
          simp [emb, baseY, basis, hne, Fin.insertNth_apply_succAbove]
        have hΦ_comp : ∀ b y u (a : Comp), Φ ((b, y), u) i₀ a.1 = y a := by
          intro b y u a
          change (emb u i₀ a.1 + q (emb u) * basis i₀ a₀ i₀ a.1) +
            (baseY y i₀ a.1 + (b + c + q (baseY y)) * basis i₀ a₀ i₀ a.1) = y a
          simp [emb, baseY, basis, Fin.insertNth_apply_same, a.2]
        have hΦ_a0 : ∀ b y u, Φ ((b, y), u) i₀ a₀ = q (emb u) + (b + c + q (baseY y)) := by
          intro b y u
          change (emb u i₀ a₀ + q (emb u) * basis i₀ a₀ i₀ a₀) +
            (baseY y i₀ a₀ + (b + c + q (baseY y)) * basis i₀ a₀ i₀ a₀) = q (emb u) + (b + c + q (baseY y))
          simp [emb, baseY, basis, Fin.insertNth_apply_same]
        let Ψ : W → (F × (Comp → F)) × W' := fun w =>
          ((q w + c, fun a => w i₀ a.1), fun k => w (i₀.succAbove k))
        have hΦ_bij : Function.Bijective Φ := by
          refine Function.bijective_iff_has_inverse.2 ⟨Ψ, ?_, ?_⟩
          · rintro ⟨⟨b, y⟩, u⟩
            apply Prod.ext
            · apply Prod.ext
              · exact hqΦ b y u
              · funext a; exact hΦ_comp b y u a
            · funext k; exact hΦ_succ b y u k
          · intro w
            funext i
            refine Fin.succAboveCases i₀ ?_ ?_ i
            · funext a
              by_cases ha : a = a₀
              · rw [ha, hΦ_a0]
                have hdecomp : w = emb (fun k => w (i₀.succAbove k)) +
                    baseY (fun a' => w i₀ a'.1) + w i₀ a₀ • basis i₀ a₀ := by
                  funext i'
                  refine Fin.succAboveCases i₀ ?_ ?_ i'
                  · funext a'
                    change w i₀ a' = (emb (fun k => w (i₀.succAbove k)) i₀ a' + baseY (fun a' => w i₀ a'.1) i₀ a') +
                      w i₀ a₀ * basis i₀ a₀ i₀ a'
                    by_cases ha' : a' = a₀
                    · rw [ha']; simp [emb, baseY, basis, Fin.insertNth_apply_same]
                    · simp [emb, baseY, basis, Fin.insertNth_apply_same, ha']
                  · intro k
                    funext a'
                    have hne := Fin.succAbove_ne i₀ k
                    change w (i₀.succAbove k) a' =
                      (emb (fun k => w (i₀.succAbove k)) (i₀.succAbove k) a' + baseY (fun a' => w i₀ a'.1) (i₀.succAbove k) a') +
                      w i₀ a₀ * basis i₀ a₀ (i₀.succAbove k) a'
                    simp [emb, baseY, basis, Fin.insertNth_apply_succAbove, hne]
                have hqw : q w = q (emb (fun k => w (i₀.succAbove k))) +
                    q (baseY (fun a' => w i₀ a'.1)) + w i₀ a₀ := by
                  conv_lhs => rw [hdecomp]
                  rw [map_add, map_add, map_smul, hqa₀, smul_eq_mul, mul_one]
                change q (emb (fun k => w (i₀.succAbove k))) +
                  ((q w + c) + c + q (baseY (fun a' => w i₀ a'.1))) = w i₀ a₀
                rw [hqw]
                calc q (emb fun k => w (i₀.succAbove k)) +
                      (q (emb fun k => w (i₀.succAbove k)) + q (baseY fun a' => w i₀ a'.1) + w i₀ a₀ + c + c +
                        q (baseY fun a' => w i₀ a'.1))
                    = (q (emb fun k => w (i₀.succAbove k)) + q (emb fun k => w (i₀.succAbove k))) +
                      (q (baseY fun a' => w i₀ a'.1) + q (baseY fun a' => w i₀ a'.1)) +
                      (c + c) + w i₀ a₀ := by ring
                  _ = w i₀ a₀ := by simp [zmod2_add_self]
              · exact hΦ_comp _ _ _ ⟨a, ha⟩
            · intro k; exact hΦ_succ _ _ _ k
        have hslice_bound : ∀ p : F × (Comp → F),
            ∃ D' : Finset (Fin s'), D'.card ≤ h ∧
              Nat.card {u : W' // ∀ j, valueFn C (Φ (p, u)) j = (DT.branch q c t0 t1).eval (Φ (p, u)) j} ≤
                scoreFn r C' D' := by
          rintro ⟨b, y⟩
          let py : F := ∏ a : Comp, y a
          let A : Fin m → W' → F := fun j u =>
            C i₀ j * py * (q (emb u) + (b + c + q (baseY y)))
          have hA_low : ∀ j, Vanishes r (A j) := by
            intro j
            let L' : W' →+ F :=
              { toFun := fun u => C i₀ j * py * q (emb u)
                map_zero' := by simp
                map_add' := fun u₁ u₂ => by simp [map_add, mul_add] }
            have hAeq : A j = fun u => L' u + C i₀ j * py * (b + c + q (baseY y)) := by
              funext u; dsimp only [A, L', AddMonoidHom.coe_mk, ZeroHom.coe_mk]; ring
            rw [hAeq]
            exact vanishes_mono (vanishes_affine L' _) hr
          have hval_split : ∀ u j, valueFn C (Φ ((b, y), u)) j = valueFn C' u j + A j u := by
            intro u j
            unfold valueFn
            rw [Fin.sum_univ_succAbove _ i₀]
            have hrest : (∑ k : Fin s', C (i₀.succAbove k) j * ∏ a : Fin r, Φ ((b, y), u) (i₀.succAbove k) a) =
                valueFn C' u j := by
              unfold valueFn
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hΦ_succ]
            rw [hrest, add_comm]
            congr 1
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a₀), hΦ_a0]
            have hprod_comp : (∏ a ∈ Finset.univ.erase a₀, Φ ((b, y), u) i₀ a) = py := by
              dsimp only [py]
              refine Finset.prod_bij (fun a ha => ⟨a, (Finset.mem_erase.1 ha).1⟩) ?_ ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro a₁ _ a₂ _ h; exact congrArg Subtype.val h
              · intro a _; exact ⟨a.1, Finset.mem_erase.2 ⟨a.2, Finset.mem_univ _⟩, rfl⟩
              · intro a ha; exact hΦ_comp b y u ⟨a, (Finset.mem_erase.1 ha).1⟩
            rw [hprod_comp]
            dsimp only [A]; ring
          let child : DT W m h := if b = 0 then t0 else t1
          have hchild_low : child.allLow r := by
            dsimp only [child]; split_ifs
            · exact hlow.1
            · exact hlow.2
          let tree' : DT W' m h := (child.compAffine L (shift b y)).subAffine A
          have htree'_low : tree'.allLow r :=
            DT.allLow_subAffine hA_low (DT.allLow_compAffine L (shift b y) hchild_low)
          obtain ⟨D', hD'c, hD'bd⟩ := dt_upper hr h s' C' tree' htree'_low
          refine ⟨D', hD'c, ?_⟩
          have heq_set : ∀ u : W',
              (∀ j, valueFn C (Φ ((b, y), u)) j = (DT.branch q c t0 t1).eval (Φ ((b, y), u)) j) ↔
              (∀ j, valueFn C' u j = tree'.eval u j) := by
            intro u
            refine forall_congr' fun j => ?_
            rw [hval_split u j]
            have hev : (DT.branch q c t0 t1).eval (Φ ((b, y), u)) j = child.eval (Φ ((b, y), u)) j := by
              simp only [DT.eval, hqΦ b y u, child]
              split_ifs <;> rfl
            rw [hev]
            dsimp only [tree']
            rw [DT.eval_subAffine, DT.eval_compAffine]
            change valueFn C' u j + A j u = child.eval (Φ ((b, y), u)) j ↔
              valueFn C' u j = child.eval (Φ ((b, y), u)) j - A j u
            constructor
            · intro h; rw [← h]; ring
            · intro h; rw [h]; ring
          have hce : Nat.card {u : W' // ∀ j, valueFn C (Φ ((b, y), u)) j = (DT.branch q c t0 t1).eval (Φ ((b, y), u)) j} =
              Nat.card {u : W' // ∀ j, valueFn C' u j = tree'.eval u j} :=
            Nat.card_congr (Equiv.subtypeEquivRight heq_set)
          rw [hce]
          exact hD'bd
        choose Dchoice hDchoice_card hDchoice_bd using hslice_bound
        have hne_param : (Finset.univ : Finset (F × (Comp → F))).Nonempty :=
          ⟨(0, fun _ => 0), Finset.mem_univ _⟩
        obtain ⟨p_max, _, hp_max⟩ := Finset.exists_max_image Finset.univ
          (fun p => scoreFn r C' (Dchoice p)) hne_param
        let D : Finset (Fin (s' + 1)) := insert i₀ ((Dchoice p_max).map (Fin.succAboveEmb i₀))
        have hi₀_not : i₀ ∉ (Dchoice p_max).map (Fin.succAboveEmb i₀) := by
          simp only [Finset.mem_map, Fin.succAboveEmb_apply]
          rintro ⟨x, _, hx⟩
          exact Fin.succAbove_ne i₀ x hx
        have hD_card : D.card ≤ h + 1 := by
          rw [Finset.card_insert_of_notMem hi₀_not, Finset.card_map]
          have := hDchoice_card p_max; omega
        refine ⟨D, hD_card, ?_⟩
        rw [scoreFn_insert_succAbove C i₀ (Dchoice p_max)]
        let eΦ := Equiv.ofBijective Φ hΦ_bij
        have htotal : Nat.card {w : W // ∀ j, valueFn C w j = (DT.branch q c t0 t1).eval w j} =
            ∑ p : F × (Comp → F),
              Nat.card {u : W' // ∀ j, valueFn C (Φ (p, u)) j = (DT.branch q c t0 t1).eval (Φ (p, u)) j} := by
          simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          have h1 : (Finset.univ.filter (fun w : W => ∀ j, valueFn C w j = (DT.branch q c t0 t1).eval w j)).card =
              (Finset.univ.filter (fun pu : (F × (Comp → F)) × W' =>
                ∀ j, valueFn C (Φ pu) j = (DT.branch q c t0 t1).eval (Φ pu) j)).card := by
            refine Finset.card_bij (fun w _ => eΦ.symm w) ?_ ?_ ?_
            · intro w hw
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
              have hΦe : Φ (eΦ.symm w) = w := eΦ.apply_symm_apply w
              rwa [hΦe]
            · intro w₁ _ w₂ _ h; exact eΦ.symm.injective h
            · intro pu hpu
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpu
              refine ⟨Φ pu, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpu⟩, ?_⟩
              exact eΦ.symm_apply_apply pu
          rw [h1]
          simp_rw [Finset.card_filter]
          exact Fintype.sum_prod_type _
        rw [htotal]
        have hcard_param : Fintype.card (F × (Comp → F)) = 2 ^ r := by
          rw [Fintype.card_prod, Fintype.card_fun, ZMod.card]
          have hcomp_card : Fintype.card Comp = r - 1 := by
            rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
          rw [hcomp_card, ← pow_succ']
          congr 1; omega
        calc ∑ p : F × (Comp → F),
              Nat.card {u : W' // ∀ j, valueFn C (Φ (p, u)) j = (DT.branch q c t0 t1).eval (Φ (p, u)) j}
            ≤ ∑ p : F × (Comp → F), scoreFn r C' (Dchoice p) :=
              Finset.sum_le_sum fun p _ => hDchoice_bd p
          _ ≤ ∑ _p : F × (Comp → F), scoreFn r C' (Dchoice p_max) :=
              Finset.sum_le_sum fun p _ => hp_max p (Finset.mem_univ p)
          _ = 2 ^ r * scoreFn r C' (Dchoice p_max) := by
              rw [Finset.sum_const, Finset.card_univ, hcard_param, smul_eq_mul]

def runAsk {U : Type*} [AddCommGroup U] [Module F U] {h : ℕ}
    (ask : Fin h → ℕ → (U →ₗ[F] F)) (w : U) : ℕ :=
  (List.finRange h).foldl (fun t a => 2 * t + (if ask a t w = 0 then 0 else 1)) 0

def dtOfAsk {U : Type*} [AddCommGroup U] [Module F U] {m : ℕ} :
    ∀ {h : ℕ}, (Fin h → ℕ → (U →ₗ[F] F)) → (ℕ → Fin m → U → F) → ℕ → DT U m h
  | 0, _, out, acc => .leaf (out acc)
  | h + 1, ask, out, acc =>
      .branch (ask 0 acc) 0
        (dtOfAsk (fun i => ask i.succ) out (2 * acc))
        (dtOfAsk (fun i => ask i.succ) out (2 * acc + 1))

lemma dtOfAsk_allLow {U : Type*} [AddCommGroup U] [Module F U] {m r : ℕ} :
    ∀ {h : ℕ} (ask : Fin h → ℕ → (U →ₗ[F] F)) (out : ℕ → Fin m → U → F) (acc : ℕ),
      (∀ z j, Vanishes r (out z j)) → (dtOfAsk ask out acc).allLow r
  | 0, _, _, _, hlow => hlow _
  | h + 1, ask, out, acc, hlow =>
      ⟨dtOfAsk_allLow (fun i => ask i.succ) out (2 * acc) hlow,
       dtOfAsk_allLow (fun i => ask i.succ) out (2 * acc + 1) hlow⟩

lemma dtOfAsk_eval {U : Type*} [AddCommGroup U] [Module F U] {m : ℕ} :
    ∀ {h : ℕ} (ask : Fin h → ℕ → (U →ₗ[F] F)) (out : ℕ → Fin m → U → F) (acc : ℕ) (w : U) (j : Fin m),
      (dtOfAsk ask out acc).eval w j =
        out ((List.finRange h).foldl (fun t a => 2 * t + (if ask a t w = 0 then 0 else 1)) acc) j w
  | 0, _, _, _, _, _ => by simp [dtOfAsk, DT.eval]
  | h + 1, ask, out, acc, w, j => by
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    simp only [dtOfAsk, DT.eval, add_zero]
    split_ifs with h0
    · simp only [add_zero]; exact dtOfAsk_eval (fun i => ask i.succ) out (2 * acc) w j
    · exact dtOfAsk_eval (fun i => ask i.succ) out (2 * acc + 1) w j

lemma foldl_nonadaptive_inj {U : Type*} [AddCommGroup U] [Module F U] (l : List (U →ₗ[F] F)) :
    ∀ (a₁ a₂ : ℕ) (w₁ w₂ : U),
      l.foldl (fun t q => 2 * t + (if q w₁ = 0 then 0 else 1)) a₁ =
      l.foldl (fun t q => 2 * t + (if q w₂ = 0 then 0 else 1)) a₂ →
      a₁ = a₂ ∧ ∀ q ∈ l, q w₁ = q w₂ := by
  induction l with
  | nil => intro a₁ a₂ _ _ h; exact ⟨h, by simp⟩
  | cons q qs ih =>
    intro a₁ a₂ w₁ w₂ h
    simp only [List.foldl_cons] at h
    obtain ⟨hstep, hrest⟩ := ih _ _ w₁ w₂ h
    have hboth : a₁ = a₂ ∧ q w₁ = q w₂ := by
      by_cases h1 : q w₁ = 0 <;> by_cases h2 : q w₂ = 0
      · simp only [h1, h2, ↓reduceIte, add_zero] at hstep
        exact ⟨by omega, by rw [h1, h2]⟩
      · simp only [h1, h2, ↓reduceIte, add_zero] at hstep; omega
      · simp only [h1, h2, ↓reduceIte, add_zero] at hstep; omega
      · simp only [h1, h2, ↓reduceIte] at hstep
        exact ⟨by omega, by rw [zmod2_eq_one_of_ne_zero h1, zmod2_eq_one_of_ne_zero h2]⟩
    exact ⟨hboth.1, fun q' hq' => by
      rcases List.mem_cons.1 hq' with rfl | hm
      · exact hboth.2
      · exact hrest q' hm⟩

lemma attainment {r s m h : ℕ} (hr : 2 ≤ r) (C : Fin s → Fin m → F)
    (D : Finset (Fin s)) (hDh : D.card ≤ h) :
    ∃ (ask : Fin h → ℕ → ((Fin s → Fin r → F) →ₗ[F] F))
      (out : ℕ → Fin m → (Fin s → Fin r → F) → F),
      (∀ z j, Vanishes r (out z j)) ∧
      scoreFn r C D ≤ Nat.card {w : Fin s → Fin r → F // ∀ j, valueFn C w j = out (runAsk ask w) j w} := by
  classical
  let W := Fin s → Fin r → F
  let a0 : Fin r := ⟨0, by omega⟩
  let Dlist : List (Fin s) := D.toList
  have hDlen : Dlist.length = D.card := Finset.length_toList D
  let coord (i : Fin s) : W →ₗ[F] F :=
    { toFun := fun w => w i a0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let qs : Fin h → (W →ₗ[F] F) := fun a =>
    if ha : a.val < Dlist.length then coord (Dlist[a.val]) else 0
  let ask : Fin h → ℕ → (W →ₗ[F] F) := fun a _ => qs a
  let rep : ℕ → W := fun z => if hz : ∃ w : W, runAsk ask w = z then Classical.choose hz else 0
  let tailProd (i : Fin s) (w : W) : F := ∏ a ∈ Finset.univ.erase a0, w i a
  let out : ℕ → Fin m → W → F := fun z j w =>
    ∑ i ∈ D, C i j * (rep z i a0) * tailProd i w
  refine ⟨ask, out, ?_, ?_⟩
  · intro z j
    refine vanishes_sum D _ fun i _ => ?_
    have hconst : (fun w : W => C i j * rep z i a0 * tailProd i w) =
        fun w : W => (C i j * rep z i a0) * ∏ a ∈ Finset.univ.erase a0,
          (AddMonoidHom.mk' (fun w : W => w i a) (fun _ _ => rfl)) w := rfl
    rw [hconst]
    apply vanishes_mul_const
    have hcard : (Finset.univ.erase a0).card + 1 ≤ r := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a0), Finset.card_univ, Fintype.card_fin]
      omega
    exact vanishes_mono (vanishes_prod_addHom (Finset.univ.erase a0)
      (fun a => AddMonoidHom.mk' (fun w : W => w i a) (fun _ _ => rfl))) hcard
  · have hrep_eq : ∀ w : W, ∀ i ∈ D, rep (runAsk ask w) i a0 = w i a0 := by
      intro w i hi
      have hex : ∃ w' : W, runAsk ask w' = runAsk ask w := ⟨w, rfl⟩
      have hrun : runAsk ask (rep (runAsk ask w)) = runAsk ask w := by
        dsimp only [rep]; rw [dif_pos hex]; exact Classical.choose_spec hex
      have hfold : ((List.finRange h).map qs).foldl (fun t q => 2 * t + (if q (rep (runAsk ask w)) = 0 then 0 else 1)) 0 =
          ((List.finRange h).map qs).foldl (fun t q => 2 * t + (if q w = 0 then 0 else 1)) 0 := by
        simpa only [runAsk, List.foldl_map] using hrun
      have hall := (foldl_nonadaptive_inj ((List.finRange h).map qs) 0 0 _ _ hfold).2
      have him : i ∈ Dlist := Finset.mem_toList.2 hi
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem him
      have hidx_h : idx < h := by omega
      have hqmem : qs ⟨idx, hidx_h⟩ ∈ (List.finRange h).map qs :=
        List.mem_map_of_mem (List.mem_finRange _)
      have hqeq := hall _ hqmem
      dsimp only [qs] at hqeq
      rw [dif_pos hidx] at hqeq
      exact hqeq
    have hout_eq : ∀ w : W, ∀ j : Fin m,
        out (runAsk ask w) j w = ∑ i ∈ D, C i j * ∏ a : Fin r, w i a := by
      intro w j
      dsimp only [out]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hrep_eq w i hi, mul_assoc]
      congr 1
      dsimp only [tailProd]
      exact Finset.mul_prod_erase Finset.univ (fun a => w i a) (Finset.mem_univ a0)
    have hhit_iff : ∀ w : W,
        (∀ j, valueFn C w j = out (runAsk ask w) j w) ↔
        (∀ j, ∑ i ∈ (Finset.univ \ D).filter (fun i => (∏ a : Fin r, w i a) = 1), C i j = 0) := by
      intro w
      refine forall_congr' fun j => ?_
      rw [hout_eq w j]
      unfold valueFn
      rw [← Finset.sum_sdiff (Finset.subset_univ D), add_comm]
      have hsub : (∑ i ∈ D, C i j * ∏ a : Fin r, w i a) + (∑ i ∈ Finset.univ \ D, C i j * ∏ a : Fin r, w i a) =
          (∑ i ∈ D, C i j * ∏ a : Fin r, w i a) ↔
          (∑ i ∈ Finset.univ \ D, C i j * ∏ a : Fin r, w i a) = 0 := by
        constructor
        · intro h; exact add_left_cancel (h.trans (add_zero _).symm)
        · intro h; rw [h, add_zero]
      rw [hsub]
      have hfilt : (∑ i ∈ Finset.univ \ D, C i j * ∏ a : Fin r, w i a) =
          ∑ i ∈ (Finset.univ \ D).filter (fun i => (∏ a : Fin r, w i a) = 1), C i j := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ \ D) (fun i => (∏ a : Fin r, w i a) = 1)]
        have h0 : ∑ i ∈ (Finset.univ \ D).filter (fun i => ¬(∏ a : Fin r, w i a) = 1),
            C i j * ∏ a : Fin r, w i a = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hne := (Finset.mem_filter.1 hi).2
          have hz : (∏ a : Fin r, w i a) = 0 := by
            by_contra hnz; exact hne (zmod2_eq_one_of_ne_zero hnz)
          simp [hz]
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.1 hi).2, mul_one]
      rw [hfilt]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hcard_eq : (Finset.univ.filter (fun w : W => ∀ j, valueFn C w j = out (runAsk ask w) j w)).card =
        scoreFn r C D := by
      have hfeq : Finset.univ.filter (fun w : W => ∀ j, valueFn C w j = out (runAsk ask w) j w) =
          ((Finset.univ : Finset (Finset (Fin s))).filter (fun H =>
            Disjoint H D ∧ ∀ j : Fin m, (∑ i ∈ H, C i j) = 0)).biUnion
            (fun H => Finset.univ.filter (fun w : W =>
              (Finset.univ \ D).filter (fun i => (∏ a : Fin r, w i a) = 1) = H)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hhit_iff]
        constructor
        · intro hw
          refine ⟨(Finset.univ \ D).filter (fun i => (∏ a : Fin r, w i a) = 1), ⟨?_, hw⟩, rfl⟩
          exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _) Finset.sdiff_disjoint
        · rintro ⟨H, ⟨_, hH⟩, rfl⟩; exact hH
      rw [hfeq, Finset.card_biUnion]
      · unfold scoreFn
        refine Finset.sum_congr rfl fun H hH => ?_
        have hdisj : Disjoint H D := (Finset.mem_filter.1 hH).2.1
        have hsub : ∀ w : W,
            ((Finset.univ \ D).filter (fun i => (∏ a : Fin r, w i a) = 1) = H) ↔
            ∀ i : Fin s, (i ∈ H → (∏ a : Fin r, w i a) = 1) ∧
                         (i ∉ D → i ∉ H → (∏ a : Fin r, w i a) ≠ 1) := by
          intro w
          constructor
          · intro heq i
            constructor
            · intro hiH
              rw [← heq] at hiH
              exact (Finset.mem_filter.1 hiH).2
            · intro hiD hiH h1
              apply hiH
              rw [← heq]
              exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hiD⟩, h1⟩
          · intro hall
            ext i
            simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hiD, h1⟩
              by_contra hiH
              exact (hall i).2 hiD hiH h1
            · intro hiH
              exact ⟨Finset.disjoint_left.1 hdisj hiH, (hall i).1 hiH⟩
        let allowed : Fin s → Finset (Fin r → F) := fun i =>
          if i ∈ D then Finset.univ
          else if i ∈ H then Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) = 1)
          else Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) ≠ 1)
        have hfiber_eq : Finset.univ.filter (fun w : W =>
            (Finset.univ \ D).filter (fun i => (∏ a : Fin r, w i a) = 1) = H) =
            Fintype.piFinset allowed := by
          ext w
          rw [Finset.mem_filter, hsub, Fintype.mem_piFinset]
          simp only [Finset.mem_univ, true_and]
          constructor
          · intro hall i
            dsimp only [allowed]
            by_cases hiD : i ∈ D
            · rw [ite_eq_left hiD]; exact Finset.mem_univ _
            · rw [ite_eq_right hiD]
              by_cases hiH : i ∈ H
              · rw [ite_eq_left hiH, Finset.mem_filter]; exact ⟨Finset.mem_univ _, (hall i).1 hiH⟩
              · rw [ite_eq_right hiH, Finset.mem_filter]; exact ⟨Finset.mem_univ _, (hall i).2 hiD hiH⟩
          · intro hall i
            have hi := hall i
            dsimp only [allowed] at hi
            constructor
            · intro hiH
              have hiD : i ∉ D := Finset.disjoint_left.1 hdisj hiH
              rw [ite_eq_right hiD, ite_eq_left hiH, Finset.mem_filter] at hi
              exact hi.2
            · intro hiD hiH
              rw [ite_eq_right hiD, ite_eq_right hiH, Finset.mem_filter] at hi
              exact hi.2
        rw [hfiber_eq, Fintype.card_piFinset]
        have hones : (Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) = 1)).card = 1 := by
          have heq1 : Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) = 1) = {fun _ => 1} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hp
              funext a
              by_contra hne
              have hx0 : x a = 0 := by
                by_contra hnz; exact hne (zmod2_eq_one_of_ne_zero hnz)
              have := Finset.prod_eq_zero (Finset.mem_univ a) hx0
              rw [this] at hp; exact zero_ne_one hp
            · intro hx; subst hx; simp
          rw [heq1, Finset.card_singleton]
        have hnotones : (Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) ≠ 1)).card = 2 ^ r - 1 := by
          have hsdiff : Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) ≠ 1) =
              Finset.univ \ Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) = 1) := by
            ext x; simp
          rw [hsdiff]
          have htot := Finset.card_sdiff_add_card_eq_card
            (Finset.subset_univ (Finset.univ.filter (fun x : Fin r → F => (∏ a, x a) = 1)))
          rw [hones, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
          omega
        have hall_card : ∀ i : Fin s, (allowed i).card =
            if i ∈ D then 2 ^ r else if i ∈ H then 1 else 2 ^ r - 1 := by
          intro i
          dsimp only [allowed]
          by_cases hiD : i ∈ D
          · rw [ite_eq_left hiD, ite_eq_left hiD, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
          · rw [ite_eq_right hiD, ite_eq_right hiD]
            by_cases hiH : i ∈ H
            · rw [ite_eq_left hiH, ite_eq_left hiH, hones]
            · rw [ite_eq_right hiH, ite_eq_right hiH, hnotones]
        simp_rw [hall_card]
        rw [Finset.prod_ite, Finset.prod_const]
        have hcD : (Finset.univ.filter (· ∈ D)).card = D.card := by congr 1; ext i; simp
        rw [hcD]
        congr 1
        rw [Finset.prod_ite, Finset.prod_const, one_pow, one_mul, Finset.prod_const]
        congr 1
        have hfeq : (Finset.univ.filter (· ∉ D)).filter (· ∉ H) = Finset.univ \ (D ∪ H) := by
          ext i; simp
        rw [hfeq]
        have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (D ∪ H))
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_union_of_disjoint hdisj.symm] at htot
        omega
      · intro H₁ _ H₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro w h1 h2
        exact hne ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
    rw [hcard_eq]

end PEqualNP.Outside.L_lib_929_aux

open PEqualNP.Outside.L_lib_929_aux in
theorem PEqualNP.Outside.L_lib_929 : (∀ (r s m h : ℕ), 2 ≤ r →
  let F := ZMod 2
  let W := Fin s → Fin r → F
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let low := fun (f : W → F) => ∀ (v : Fin r → W) (x : W), (List.ofFn v).foldl diff f x = 0
  ∀ C : Fin s → Fin m → F,
    let value := fun (w : W) (j : Fin m) => ∑ i : Fin s, C i j * ∏ a : Fin r, w i a
    let score := fun (D : Finset (Fin s)) =>
      ((Finset.univ : Finset (Finset (Fin s))).filter (fun H =>
        Disjoint H D ∧ ∀ j : Fin m, (∑ i ∈ H, C i j) = 0)).sum (fun H =>
          (2^r)^D.card * (2^r-1)^(s-D.card-H.card))
    let run := fun (ask : Fin h → ℕ → (W →ₗ[F] F)) (w : W) =>
      (List.finRange h).foldl (fun t a => 2*t + (if ask a t w = 0 then 0 else 1)) (0 : ℕ)
    ∀ t : ℕ, (∃ (ask : Fin h → ℕ → (W →ₗ[F] F)) (out : ℕ → Fin m → W → F),
      (∀ z j, low (out z j)) ∧
      t ≤ Nat.card {w : W // ∀ j, value w j = out (run ask w) j w}) ↔
      ∃ D : Finset (Fin s), D.card ≤ h ∧ t ≤ score D) := by
  intro r s m h hr F W diff_fn low C value score run t
  constructor
  · rintro ⟨ask, out, hlow, ht⟩
    have hlow' : ∀ z j, Vanishes r (out z j) := fun z j =>
      (vanishes_iff_foldl r (out z j)).2 (hlow z j)
    let tree := dtOfAsk ask out 0
    obtain ⟨D, hDc, hbd⟩ := dt_upper hr h s C tree (dtOfAsk_allLow ask out 0 hlow')
    have hev : ∀ w j, tree.eval w j = out (run ask w) j w := fun w j =>
      dtOfAsk_eval ask out 0 w j
    have hce : Nat.card {w : W // ∀ j, value w j = out (run ask w) j w} =
        Nat.card {w : W // ∀ j, valueFn C w j = tree.eval w j} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => forall_congr' fun j => ?_)
      rw [hev w j]; rfl
    exact ⟨D, hDc, ht.trans (hce.le.trans hbd)⟩
  · rintro ⟨D, hDc, ht⟩
    obtain ⟨ask, out, hlow, hbd⟩ := attainment hr C D hDc
    refine ⟨ask, out, fun z j => (vanishes_iff_foldl r (out z j)).1 (hlow z j), ht.trans hbd⟩

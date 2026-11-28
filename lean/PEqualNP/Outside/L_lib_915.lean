import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_915

open Finset

section
variable {k : ℕ}

def dif (f : (Fin k → ZMod 2) → ZMod 2) (v x : Fin k → ZMod 2) : ZMod 2 := f (x + v) - f x

theorem fold_sum {ι : Type*} (S : Finset ι) (l : List (Fin k → ZMod 2)) :
    ∀ (g : ι → (Fin k → ZMod 2) → ZMod 2) (x : Fin k → ZMod 2),
    l.foldl dif (fun w => ∑ j ∈ S, g j w) x = ∑ j ∈ S, l.foldl dif (g j) x := by
  induction l with
  | nil => intro g x; rfl
  | cons v l ih =>
    intro g x
    simp only [List.foldl_cons]
    have : dif (fun w => ∑ j ∈ S, g j w) v = fun w => ∑ j ∈ S, dif (g j) v w := by
      funext w; simp [dif, Finset.sum_sub_distrib]
    rw [this, ih]

def proj (P : Fin k → Prop) [DecidablePred P] (v : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  fun a => if P a then v a else 0

theorem dif_local (P : Fin k → Prop) [DecidablePred P] (g : (Fin k → ZMod 2) → ZMod 2)
    (hg : ∀ w w' : Fin k → ZMod 2, (∀ a, P a → w a = w' a) → g w = g w')
    (v : Fin k → ZMod 2) :
    (∀ w w' : Fin k → ZMod 2, (∀ a, P a → w a = w' a) → dif g v w = dif g v w') ∧
      dif g v = dif g (proj P v) := by
  constructor
  · intro w w' h
    unfold dif
    rw [hg (w + v) (w' + v) (by intro a ha; simp [h a ha]), hg w w' h]
  · funext x
    unfold dif
    rw [hg (x + v) (x + proj P v) (by intro a ha; simp [proj, ha])]

theorem fold_local (P : Fin k → Prop) [DecidablePred P] (l : List (Fin k → ZMod 2)) :
    ∀ g : (Fin k → ZMod 2) → ZMod 2,
    (∀ w w' : Fin k → ZMod 2, (∀ a, P a → w a = w' a) → g w = g w') →
    l.foldl dif g = (l.map (proj P)).foldl dif g := by
  induction l with
  | nil => intro g _; rfl
  | cons v l ih =>
    intro g hg
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← (dif_local P g hg v).2]
    exact ih _ (dif_local P g hg v).1

theorem fold_zero0 (l : List (Fin k → ZMod 2)) :
    l.foldl dif (0 : (Fin k → ZMod 2) → ZMod 2) = 0 := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [List.foldl_cons]
    have : dif (0 : (Fin k → ZMod 2) → ZMod 2) v = 0 := by funext x; simp [dif]
    rw [this, ih]

theorem fold_zero (l : List (Fin k → ZMod 2)) (h : (0 : Fin k → ZMod 2) ∈ l) :
    ∀ g : (Fin k → ZMod 2) → ZMod 2, l.foldl dif g = 0 := by
  induction l with
  | nil => simp at h
  | cons v l ih =>
    intro g
    rcases List.mem_cons.1 h with h0 | h0
    · subst h0
      rw [List.foldl_cons]
      have : dif g (0 : Fin k → ZMod 2) = 0 := by funext x; simp [dif]
      rw [this, fold_zero0]
    · rw [List.foldl_cons]; exact ih h0 _

end

theorem m2 (n k : ℕ) (_hk : 0 < k) (h : n < 2 * k) : (n % k = n ∧ n < k) ∨ (n % k = n - k ∧ k ≤ n) := by
  by_cases hn : n < k
  · left; exact ⟨Nat.mod_eq_of_lt hn, hn⟩
  · right
    refine ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem sep (k b s j X Y u u' : ℕ) (hk : 0 < k) (hs : s < k) (hj : j < k) (hu : u < b)
    (hu' : u' < b) (hX : X < k) (hY : Y < k) (hb : b ≤ k)
    (h1 : Y + b ≤ X) (h2 : X + b ≤ Y + k)
    (e1 : (s + X) % k = (j + u) % k) (e2 : (s + Y) % k = (j + u') % k) : False := by
  rcases m2 (s + X) k hk (by omega) with ⟨a1, _⟩ | ⟨a1, _⟩ <;>
  rcases m2 (s + Y) k hk (by omega) with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
  rcases m2 (j + u) k hk (by omega) with ⟨a3, _⟩ | ⟨a3, _⟩ <;>
  rcases m2 (j + u') k hk (by omega) with ⟨a4, _⟩ | ⟨a4, _⟩ <;> omega

theorem sep0 (k s X Y : ℕ) (hk : 0 < k) (hs : s < k) (hX : X < k) (hY : Y < k)
    (h1 : Y < X) (e1 : (s + X) % k = (s + Y) % k) : False := by
  rcases m2 (s + X) k hk (by omega) with ⟨a1, _⟩ | ⟨a1, _⟩ <;>
  rcases m2 (s + Y) k hk (by omega) with ⟨a2, _⟩ | ⟨a2, _⟩ <;> omega

end PEqualNP.Outside.L_lib_915

open PEqualNP.Outside.L_lib_915 in
theorem PEqualNP.Outside.L_lib_915 : ∀ (k b p t : ℕ) (hk : 0 < k), 0 < b → 0 < p → 2 ≤ t →
  b + t*p + (t+1)*(b-1) ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let unit := fun (a j : Fin k) => if j = a then (1 : F) else 0
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let cube := fun (f : W → F) (v : Fin t → W) => (List.ofFn v).foldl diff f
  ∀ (s : Fin k) (off : Fin t → Fin b),
    let pos := fun i => ix (s.val + (off i).val)
    ∃ (far : Fin t → Fin k), Function.Injective far ∧
      (∀ i (u : Fin b), far i ≠ ix (s.val+u.val)) ∧
      (∀ i, ∃ n : ℕ, far i = ix ((pos i).val + p*n)) ∧
      ∀ (table : Fin k → (Fin b → F) → F) (x : W),
        let f := fun w : W => ∑ j : Fin k, table j (fun u => w (ix (j.val+u.val)))
        cube f (fun i => unit (pos i) + unit (far i)) x =
          cube f (fun i => unit (pos i)) x := by
  intro k b p t hk hb hp ht hkb F W ix unit diff cube s off pos
  classical
  let st : Fin t → ℕ := fun i => 2 * b - 1 + i.val * (p + b - 1)
  let nn : Fin t → ℕ := fun i => (st i - (off i).val + p - 1) / p
  let FF : Fin t → ℕ := fun i => (off i).val + p * nn i
  have hst0 : ∀ i, 2 * b - 1 ≤ st i := fun i => by simp only [st]; omega
  have hF : ∀ i, st i ≤ FF i ∧ FF i + 1 ≤ st i + p := by
    intro i
    have h1 := Nat.div_add_mod (st i - (off i).val + p - 1) p
    have h2 := Nat.mod_lt (st i - (off i).val + p - 1) hp
    have h3 := (off i).isLt
    have h4 := hst0 i
    simp only [FF, nn]
    constructor <;> omega
  have hmono : ∀ i i' : Fin t, i.val < i'.val → st i + p + b - 1 ≤ st i' := by
    intro i i' hii
    have h1 : (i.val + 1) * (p + b - 1) ≤ i'.val * (p + b - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (i.val + 1) * (p + b - 1) = i.val * (p + b - 1) + (p + b - 1) := by ring
    simp only [st]
    omega
  have htop : ∀ i : Fin t, st i + p + b - 1 ≤ k := by
    intro i
    have h1 : (i.val + 1) * (p + b - 1) ≤ t * (p + b - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (i.val + 1) * (p + b - 1) = i.val * (p + b - 1) + (p + b - 1) := by ring
    have h3 : t * (p + b - 1) = t * p + t * (b - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    have h4 : (t + 1) * (b - 1) = t * (b - 1) + (b - 1) := by ring
    simp only [st]
    omega
  -- key separation facts in relative coordinates
  have hFk : ∀ i, FF i + b ≤ k := fun i => by have := hF i; have := htop i; omega
  have hFF : ∀ i i' : Fin t, i.val < i'.val → FF i + b ≤ FF i' := by
    intro i i' h
    have := hF i; have := hF i'; have := hmono i i' h; omega
  have hFoff : ∀ i (i' : Fin t), (off i').val + b ≤ FF i := by
    intro i i'
    have := hF i; have := hst0 i; have := (off i').isLt; omega
  have hbk : b ≤ k := by have := hFk ⟨0, by omega⟩; omega
  refine ⟨fun i => ix (s.val + FF i), ?_, ?_, ?_, ?_⟩
  · intro i i' h
    simp only [ix, Fin.mk.injEq] at h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hl | hl
    · exact sep0 k s.val (FF i') (FF i) hk s.isLt (by have := hFk i'; omega)
        (by have := hFk i; omega) (by have := hFF i i' hl; omega) h.symm
    · exact sep0 k s.val (FF i) (FF i') hk s.isLt (by have := hFk i; omega)
        (by have := hFk i'; omega) (by have := hFF i' i hl; omega) h
  · intro i u h
    simp only [ix, Fin.mk.injEq] at h
    exact sep0 k s.val (FF i) u.val hk s.isLt (by have := hFk i; omega) (by omega)
      (by have := hFoff i ⟨0, by omega⟩; omega) h
  · intro i
    refine ⟨nn i, ?_⟩
    simp only [ix, pos, Fin.mk.injEq, FF]
    rw [Nat.mod_add_mod, Nat.add_assoc]
  · intro table x f
    let P : Fin k → Fin k → Prop := fun j a => ∃ u : Fin b, a = ix (j.val + u.val)
    let g : Fin k → W → F := fun j w => table j (fun u => w (ix (j.val + u.val)))
    have hg : ∀ j (w w' : W), (∀ a, P j a → w a = w' a) → g j w = g j w' := by
      intro j w w' h
      simp only [g]; congr 1; funext u; exact h _ ⟨u, rfl⟩
    show (List.ofFn fun i => unit (pos i) + unit (ix (s.val + FF i))).foldl dif
        (fun w => ∑ j ∈ Finset.univ, g j w) x =
      (List.ofFn fun i => unit (pos i)).foldl dif (fun w => ∑ j ∈ Finset.univ, g j w) x
    rw [fold_sum, fold_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fold_local (P j) (List.ofFn fun i => unit (pos i) + unit (ix (s.val + FF i))) (g j) (hg j),
      fold_local (P j) (List.ofFn fun i => unit (pos i)) (g j) (hg j), List.map_ofFn,
      List.map_ofFn]
    by_cases hA : ∀ i, ¬ P j (ix (s.val + FF i))
    · have heq : (proj (P j) ∘ fun i => unit (pos i) + unit (ix (s.val + FF i))) =
          (proj (P j) ∘ fun i => unit (pos i)) := by
        funext i a
        simp only [Function.comp, proj, Pi.add_apply]
        split_ifs with ha
        · have hne : a ≠ ix (s.val + FF i) := fun e => hA i (e ▸ ha)
          simp [unit, hne]
        · rfl
      rw [heq]
    · push Not at hA
      obtain ⟨i0, u0, hu0⟩ := hA
      have e0 : (s.val + FF i0) % k = (j.val + u0.val) % k := by
        simpa [ix, Fin.ext_iff] using hu0
      let i1 : Fin t := if i0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hi1 : i1.val ≠ i0.val := by
        simp only [i1]; split_ifs with h <;> simp <;> omega
      have npos : ∀ i', ¬ P j (pos i') := by
        rintro i' ⟨u, hu⟩
        have e1 : (s.val + (off i').val) % k = (j.val + u.val) % k := by
          simpa [ix, pos, Fin.ext_iff] using hu
        exact sep k b s.val j.val (FF i0) (off i').val u0.val u.val hk s.isLt j.isLt u0.isLt
          u.isLt (by have := hFk i0; omega) (by have := (off i').isLt; omega) hbk
          (hFoff i0 i') (by have := hFk i0; omega) e0 e1
      have nfar : ¬ P j (ix (s.val + FF i1)) := by
        rintro ⟨u, hu⟩
        have e1 : (s.val + FF i1) % k = (j.val + u.val) % k := by
          simpa [ix, Fin.ext_iff] using hu
        rcases Nat.lt_or_gt_of_ne hi1 with hl | hl
        · exact sep k b s.val j.val (FF i0) (FF i1) u0.val u.val hk s.isLt j.isLt u0.isLt
            u.isLt (by have := hFk i0; omega) (by have := hFk i1; omega) hbk
            (hFF i1 i0 hl) (by have := hFk i0; omega) e0 e1
        · exact sep k b s.val j.val (FF i1) (FF i0) u.val u0.val hk s.isLt j.isLt u.isLt
            u0.isLt (by have := hFk i1; omega) (by have := hFk i0; omega) hbk
            (hFF i0 i1 hl) (by have := hFk i1; omega) e1 e0
      have z1 : (proj (P j) ∘ fun i => unit (pos i) + unit (ix (s.val + FF i))) i1 = 0 := by
        funext a
        simp only [Function.comp, proj, Pi.add_apply, Pi.zero_apply]
        split_ifs with ha
        · have h1 : a ≠ pos i1 := fun e => npos i1 (e ▸ ha)
          have h2 : a ≠ ix (s.val + FF i1) := fun e => nfar (e ▸ ha)
          simp [unit, h1, h2]
        · rfl
      have z2 : (proj (P j) ∘ fun i => unit (pos i)) i1 = 0 := by
        funext a
        simp only [Function.comp, proj, Pi.zero_apply]
        split_ifs with ha
        · have h1 : a ≠ pos i1 := fun e => npos i1 (e ▸ ha)
          simp [unit, h1]
        · rfl
      rw [fold_zero _ (List.mem_ofFn.2 ⟨i1, z1⟩),
        fold_zero _ (List.mem_ofFn.2 ⟨i1, z2⟩)]

import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_614_aux

open Finset

def step {b : ℕ} (t : Fin b → ZMod 2) (bi : ZMod 2) (s : Fin (b + 1) → ZMod 2) :
    Fin (b + 1) → ZMod 2 :=
  let tail := fun j : Fin b => s j.succ
  Fin.snoc (α := fun _ : Fin (b + 1) => ZMod 2) tail
    (s 0 + bi + ∑ j : Fin b, t j * tail j)

def runFold {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) : Fin (b + 1) → ZMod 2 :=
  (List.finRange L).foldl (fun s i => step (tap i) (bias i) s) x

lemma vec_smul_sum_apply {ι : Type*} {w : ℕ} (s : Finset ι) (c : ι → ZMod 2)
    (f : ι → Fin w → ZMod 2) (i : Fin w) :
    (∑ x ∈ s, c x • f x) i = ∑ x ∈ s, c x * f x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change (c a • f a) i + (∑ x ∈ s, c x • f x) i = c a * f a i + ∑ x ∈ s, c x * f x i
    rw [ih]
    rfl

lemma z2_cases (r : ZMod 2) : r = 0 ∨ r = 1 := by
  fin_cases r
  · left; rfl
  · right; rfl

lemma z2_add_self {w : ℕ} (x : Fin w → ZMod 2) : x + x = 0 := by
  funext j
  change x j + x j = 0
  rcases z2_cases (x j) with h | h <;> rw [h] <;> rfl

lemma step_add {b : ℕ} (t : Fin b → ZMod 2) (bi1 bi2 : ZMod 2) (s1 s2 : Fin (b + 1) → ZMod 2) :
    step t (bi1 + bi2) (s1 + s2) = step t bi1 s1 + step t bi2 s2 := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp only [step, Fin.snoc_last, Pi.add_apply]
    have hsum : ∑ j : Fin b, t j * (s1 j.succ + s2 j.succ) =
        ∑ j : Fin b, (t j * s1 j.succ + t j * s2 j.succ) := by
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum, Finset.sum_add_distrib]
    ring
  · intro j
    simp only [step, Fin.snoc_castSucc, Pi.add_apply]

lemma foldl_affine {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2)
    (l : List (Fin L)) (x1 x2 : Fin (b + 1) → ZMod 2) :
    l.foldl (fun s i => step (tap i) (bias i) s) (x1 + x2) =
      l.foldl (fun s i => step (tap i) 0 s) x1 +
      l.foldl (fun s i => step (tap i) (bias i) s) x2 := by
  induction l generalizing x1 x2 with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.foldl_cons]
    have hstep := step_add (tap a) 0 (bias a) x1 x2
    rw [zero_add] at hstep
    rw [hstep]
    exact ih _ _

lemma runFold_split_bias {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) :
    runFold tap bias x = runFold tap 0 x + runFold tap bias 0 := by
  have h := foldl_affine tap bias (List.finRange L) x 0
  simpa [runFold] using h

lemma step_zero_bijective {b : ℕ} (t : Fin b → ZMod 2) :
    Function.Bijective (step t 0) := by
  let inv : (Fin (b + 1) → ZMod 2) → (Fin (b + 1) → ZMod 2) := fun y =>
    Fin.cons (y (Fin.last b) + ∑ j : Fin b, t j * y j.castSucc) (fun j : Fin b => y j.castSucc)
  refine Function.bijective_iff_has_inverse.2 ⟨inv, ?_, ?_⟩
  · intro x
    funext k
    refine Fin.cases ?_ ?_ k
    · simp only [inv, step, Fin.cons_zero, Fin.snoc_last, Fin.snoc_castSucc, add_zero]
      have hsub : x 0 + (∑ j : Fin b, t j * x j.succ) + ∑ j : Fin b, t j * x j.succ = x 0 := by
        have hself : (∑ j : Fin b, t j * x j.succ) + (∑ j : Fin b, t j * x j.succ) = 0 := by
          have := congrFun (z2_add_self (fun _ : Fin 1 => ∑ j : Fin b, t j * x j.succ)) 0
          exact this
        rw [add_assoc, hself, add_zero]
      exact hsub
    · intro j
      simp [inv, step]
  · intro y
    funext k
    refine Fin.lastCases ?_ ?_ k
    · simp only [inv, step, Fin.snoc_last, Fin.cons_zero, Fin.cons_succ, add_zero]
      have hself : (∑ j : Fin b, t j * y j.castSucc) + (∑ j : Fin b, t j * y j.castSucc) = 0 := by
        have := congrFun (z2_add_self (fun _ : Fin 1 => ∑ j : Fin b, t j * y j.castSucc)) 0
        exact this
      rw [add_assoc, hself, add_zero]
    · intro j
      simp [inv, step]

def stepAt {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) : ℕ → Fin (b + 1) → ZMod 2
  | 0 => x
  | k + 1 =>
    if hk : k < L then step (tap ⟨k, hk⟩) (bias ⟨k, hk⟩) (stepAt tap bias x k)
    else stepAt tap bias x k

lemma foldl_take_eq_stepAt {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) : ∀ k ≤ L,
    ((List.finRange L).take k).foldl (fun s i => step (tap i) (bias i) s) x =
      stepAt tap bias x k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hlt : k < L := Nat.lt_of_succ_le hk
    have htake : (List.finRange L).take (k + 1) =
        (List.finRange L).take k ++ [⟨k, hlt⟩] := by
      have hlen : k < (List.finRange L).length := by simp [hlt]
      rw [List.take_succ_eq_append_getElem hlen]
      simp
    rw [htake, List.foldl_append, ih (Nat.le_of_lt hlt)]
    simp [stepAt, hlt]

lemma runFold_eq_stepAt {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) :
    runFold tap bias x = stepAt tap bias x L := by
  have h := foldl_take_eq_stepAt tap bias x L le_rfl
  have htake : (List.finRange L).take L = List.finRange L := by
    rw [List.take_of_length_le]; simp
  rw [htake] at h
  exact h

lemma stepAt_untouched {b L : ℕ} (tap : Fin L → Fin b → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) :
    ∀ (t : ℕ), t ≤ L → ∀ (r : ℕ) (hr : t + r < b + 1),
      stepAt tap 0 x t ⟨r, by omega⟩ = x ⟨t + r, hr⟩ := by
  intro t
  induction t with
  | zero =>
    intro _ r hr
    simp [stepAt]
  | succ t ih =>
    intro ht r hr
    have hlt : t < L := Nat.lt_of_succ_le ht
    simp only [stepAt, hlt, ↓reduceDIte]
    have hrb : r < b := by omega
    have hcast : (⟨r, by omega⟩ : Fin (b + 1)) = (⟨r, hrb⟩ : Fin b).castSucc := rfl
    rw [hcast]
    simp only [step, Fin.snoc_castSucc]
    have hsucc : (⟨r, hrb⟩ : Fin b).succ = ⟨r + 1, by omega⟩ := rfl
    rw [hsucc]
    have hprev := ih (Nat.le_of_lt hlt) (r + 1) (by omega)
    rw [hprev]
    congr 1
    exact Fin.ext (by dsimp; omega)

lemma stepAt_shift_left {b L : ℕ} (tap : Fin L → Fin b → ZMod 2)
    (x : Fin (b + 1) → ZMod 2) (k : ℕ) (hk : k ≤ L) :
    ∀ (d : ℕ), k + d ≤ L → ∀ (r : ℕ) (hr : d + r < b + 1),
      stepAt tap 0 x (k + d) ⟨r, by omega⟩ = stepAt tap 0 x k ⟨d + r, hr⟩ := by
  intro d
  induction d with
  | zero =>
    intro _ r hr
    simp
  | succ d ih =>
    intro hd r hr
    have hlt : k + d < L := by omega
    have heq : k + (d + 1) = (k + d) + 1 := by omega
    rw [heq]
    simp only [stepAt, hlt, ↓reduceDIte]
    have hrb : r < b := by omega
    have hcast : (⟨r, by omega⟩ : Fin (b + 1)) = (⟨r, hrb⟩ : Fin b).castSucc := rfl
    rw [hcast]
    simp only [step, Fin.snoc_castSucc]
    have hsucc : (⟨r, hrb⟩ : Fin b).succ = ⟨r + 1, by omega⟩ := rfl
    rw [hsucc]
    have hprev := ih (by omega) (r + 1) (by omega)
    rw [hprev]
    congr 1
    exact Fin.ext (by dsimp; omega)

lemma stepAt_zero_bijective {b L : ℕ} (tap : Fin L → Fin b → ZMod 2) :
    ∀ t ≤ L, Function.Bijective (fun x => stepAt tap 0 x t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact Function.bijective_id
  | succ t ih =>
    intro ht
    have hlt : t < L := Nat.lt_of_succ_le ht
    have hfun : (fun x => stepAt tap 0 x (t + 1)) =
        (step (tap ⟨t, hlt⟩) 0) ∘ (fun x => stepAt tap 0 x t) := by
      funext x
      simp [stepAt, hlt]
    rw [hfun]
    exact (step_zero_bijective _).comp (ih (Nat.le_of_lt hlt))

lemma only_if_dir (b L : ℕ)
    (hall : ∀ (g : (Fin (b + 1) → ZMod 2) ≃ₗ[ZMod 2] (Fin (b + 1) → ZMod 2))
      (v : Fin (b + 1) → ZMod 2),
      ∃ (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2),
        ∀ x, runFold tap bias x = g x + v) :
    2 * (b + 1) - 1 ≤ L := by
  by_contra hlt
  have hLle : L ≤ 2 * b := by omega
  by_cases hb0 : b = 0
  · subst hb0
    have hL0 : L = 0 := by omega
    subst hL0
    obtain ⟨tap, bias, hspec⟩ := hall (LinearEquiv.refl (ZMod 2) _) (fun _ => 1)
    have h0 := congrFun (hspec 0) 0
    simp [runFold] at h0
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    by_cases hLw : L < b + 1
    · by_cases hL0 : L = 0
      · subst hL0
        let sw : Equiv.Perm (Fin (b + 1)) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
        let g : (Fin (b + 1) → ZMod 2) ≃ₗ[ZMod 2] (Fin (b + 1) → ZMod 2) :=
          LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) sw
        obtain ⟨tap, bias, hspec⟩ := hall g 0
        have hlin : ∀ x, runFold tap 0 x = g x := by
          intro x
          have h0 := hspec 0
          have hx := hspec x
          rw [map_zero, add_zero] at h0
          rw [runFold_split_bias, h0, add_zero, add_zero] at hx
          exact hx
        have hbad := congrFun (hlin (Pi.single ⟨1, by omega⟩ 1)) ⟨0, by omega⟩
        have hne : (⟨0, by omega⟩ : Fin (b + 1)) ≠ ⟨1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this
        simp [runFold, g, sw, hne] at hbad
      · obtain ⟨tap, bias, hspec⟩ := hall (LinearEquiv.refl (ZMod 2) _) 0
        have hlin : ∀ x, runFold tap 0 x = x := by
          intro x
          have h0 := hspec 0
          have hx := hspec x
          simp only [LinearEquiv.refl_apply, add_zero] at h0 hx
          rw [runFold_split_bias, h0, add_zero] at hx
          exact hx
        have hbad := congrFun (hlin (Pi.single (0 : Fin (b + 1)) 1)) 0
        rw [runFold_eq_stepAt] at hbad
        have hu := stepAt_untouched tap (Pi.single (0 : Fin (b + 1)) 1) L le_rfl 0 (by omega)
        have h0eq : (⟨0, by omega⟩ : Fin (b + 1)) = 0 := rfl
        rw [h0eq] at hu
        rw [hu] at hbad
        have hne : (⟨L + 0, by omega⟩ : Fin (b + 1)) ≠ 0 := by
          intro h; have := congrArg Fin.val h; dsimp at this; omega
        rw [Pi.single_eq_of_ne hne, Pi.single_eq_same] at hbad
        exact zero_ne_one hbad
    · let k := L - (b + 1)
      have hk_lt : k < b := by omega
      have hL_eq : L = k + (b + 1) := by omega
      let sw : Equiv.Perm (Fin (b + 1)) := Equiv.swap 0 ⟨k + 1, by omega⟩
      let g : (Fin (b + 1) → ZMod 2) ≃ₗ[ZMod 2] (Fin (b + 1) → ZMod 2) :=
        LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) sw
      obtain ⟨tap, bias, hspec⟩ := hall g 0
      have hlin : ∀ x, runFold tap 0 x = g x := by
        intro x
        have h0 := hspec 0
        have hx := hspec x
        rw [map_zero, add_zero] at h0
        rw [runFold_split_bias, h0, add_zero, add_zero] at hx
        exact hx
      obtain ⟨x, hx⟩ := (stepAt_zero_bijective tap k (by omega)).2 (Pi.single (0 : Fin (b + 1)) 1)
      dsimp only at hx
      have hxk1 : x ⟨k + 1, by omega⟩ = 0 := by
        have hu := stepAt_untouched tap x k (by omega) 1 (by omega)
        rw [hx] at hu
        have hne : (⟨1, by omega⟩ : Fin (b + 1)) ≠ 0 := by
          intro h; have := congrArg Fin.val h; simp at this
        rw [Pi.single_eq_of_ne hne] at hu
        exact hu.symm
      have hsL0 : stepAt tap 0 x L 0 = 1 := by
        have hshift := stepAt_shift_left tap x (k + 1) (by omega) b (by omega) 0 (by omega)
        have hadd : k + 1 + b = L := by omega
        rw [hadd] at hshift
        have h0eq : (⟨0, by omega⟩ : Fin (b + 1)) = 0 := rfl
        rw [h0eq] at hshift
        rw [hshift]
        have hklt : k < L := by omega
        simp only [stepAt, hklt, ↓reduceDIte]
        have hlast : (⟨b + 0, by omega⟩ : Fin (b + 1)) = Fin.last b := Fin.ext (by simp)
        rw [hlast]
        simp only [step, Fin.snoc_last, hx, Pi.zero_apply, add_zero]
        have hsum0 : ∑ j : Fin b, tap ⟨k, hklt⟩ j * (Pi.single (0 : Fin (b + 1)) (1 : ZMod 2) : Fin (b + 1) → ZMod 2) j.succ = 0 := by
          refine Finset.sum_eq_zero (fun j _ => ?_)
          have hne : j.succ ≠ 0 := Fin.succ_ne_zero j
          rw [Pi.single_eq_of_ne hne, mul_zero]
        rw [hsum0, add_zero, Pi.single_eq_same]
      have hbad := congrFun (hlin x) 0
      rw [runFold_eq_stepAt, hsL0] at hbad
      dsimp [g, sw] at hbad
      rw [Equiv.swap_apply_left, hxk1] at hbad
      exact one_ne_zero hbad

lemma exists_bias_for_target {b L : ℕ} (hL : b + 1 ≤ L)
    (tap : Fin L → Fin b → ZMod 2) (v : Fin (b + 1) → ZMod 2) :
    ∃ bias : Fin L → ZMod 2, runFold tap bias 0 = v := by
  let w := b + 1
  let d := L - w
  have hd_add : d + w = L := Nat.sub_add_cancel hL
  have hbuild : ∀ (t : ℕ) (ht : t ≤ w),
      ∃ (bias : Fin L → ZMod 2),
        (∀ i : Fin L, i.val < d → bias i = 0) ∧
        ∀ (r : ℕ) (hr : r < t),
          stepAt tap bias 0 (d + t) ⟨w - t + r, by omega⟩ = v ⟨r, by omega⟩ := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨0, fun _ _ => rfl, fun r hr => by omega⟩
    | succ t ih =>
      intro ht
      obtain ⟨bias0, hzero, hinv⟩ := ih (Nat.le_of_succ_le ht)
      let idx : Fin L := ⟨d + t, by omega⟩
      let sPrev := stepAt tap bias0 0 (d + t)
      let val : ZMod 2 := v ⟨t, by omega⟩ + sPrev 0 + ∑ j : Fin b, tap idx j * sPrev j.succ
      let bias1 : Fin L → ZMod 2 := fun i => if i = idx then val else bias0 i
      have hsame : ∀ k ≤ d + t, stepAt tap bias1 0 k = stepAt tap bias0 0 k := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ k ihk =>
          intro hk
          have hlt : k < L := by omega
          simp only [stepAt, hlt, ↓reduceDIte]
          have hne : (⟨k, hlt⟩ : Fin L) ≠ idx := by
            intro h; have := congrArg Fin.val h; dsimp [idx] at this; omega
          simp only [bias1, hne, ↓reduceIte, ihk (Nat.le_of_lt hk)]
      refine ⟨bias1, ?_, ?_⟩
      · intro i hi
        have hne : i ≠ idx := by intro h; rw [h] at hi; dsimp [idx] at hi; omega
        simp only [bias1, hne, ↓reduceIte]
        exact hzero i hi
      · intro r hr
        have heq : d + (t + 1) = (d + t) + 1 := by omega
        have hlt : d + t < L := by omega
        rw [heq]
        simp only [stepAt, hlt, ↓reduceDIte]
        rw [hsame (d + t) le_rfl]
        have hbi : bias1 ⟨d + t, hlt⟩ = val := by simp [bias1, idx]
        rw [hbi]
        by_cases hrt : r = t
        · subst hrt
          have hlast : (⟨w - (r + 1) + r, by omega⟩ : Fin (b + 1)) = Fin.last b :=
            Fin.ext (by dsimp [w]; omega)
          rw [hlast]
          simp only [step, Fin.snoc_last]
          change sPrev 0 + (v ⟨r, by omega⟩ + sPrev 0 + ∑ j : Fin b, tap idx j * sPrev j.succ) +
            ∑ j : Fin b, tap idx j * sPrev j.succ = v ⟨r, by omega⟩
          have h1 : sPrev 0 + sPrev 0 = 0 := by
            have := congrFun (z2_add_self (fun _ : Fin 1 => sPrev 0)) 0; exact this
          have h2 : (∑ j : Fin b, tap idx j * sPrev j.succ) + (∑ j : Fin b, tap idx j * sPrev j.succ) = 0 := by
            have := congrFun (z2_add_self (fun _ : Fin 1 => ∑ j : Fin b, tap idx j * sPrev j.succ)) 0; exact this
          calc sPrev 0 + (v ⟨r, by omega⟩ + sPrev 0 + ∑ j : Fin b, tap idx j * sPrev j.succ) +
                ∑ j : Fin b, tap idx j * sPrev j.succ
              = v ⟨r, by omega⟩ + (sPrev 0 + sPrev 0) +
                ((∑ j : Fin b, tap idx j * sPrev j.succ) + (∑ j : Fin b, tap idx j * sPrev j.succ)) := by ring
            _ = v ⟨r, by omega⟩ := by rw [h1, h2, add_zero, add_zero]
        · have hrb : w - (t + 1) + r < b := by omega
          have hcast : (⟨w - (t + 1) + r, by omega⟩ : Fin (b + 1)) = (⟨w - (t + 1) + r, hrb⟩ : Fin b).castSucc := rfl
          rw [hcast]
          simp only [step, Fin.snoc_castSucc]
          have hsucc : (⟨w - (t + 1) + r, hrb⟩ : Fin b).succ = ⟨w - t + r, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hsucc]
          exact hinv r (by omega)
  obtain ⟨bias, _, hfin⟩ := hbuild w le_rfl
  refine ⟨bias, ?_⟩
  rw [runFold_eq_stepAt]
  have hL_step : stepAt tap bias 0 L = stepAt tap bias 0 (d + w) :=
    congrArg (stepAt tap bias 0) hd_add.symm
  rw [hL_step]
  funext r
  have hr := hfin r.val r.isLt
  have hidx : (⟨w - w + r.val, by omega⟩ : Fin (b + 1)) = r := Fin.ext (by dsimp; omega)
  rw [hidx] at hr
  exact hr

lemma exists_notMem_two_subspaces {w : ℕ} (H1 H2 : Submodule (ZMod 2) (Fin w → ZMod 2))
    (h1 : Module.finrank (ZMod 2) H1 < w) (h2 : Module.finrank (ZMod 2) H2 < w) :
    ∃ y : Fin w → ZMod 2, y ∉ H1 ∧ y ∉ H2 := by
  classical
  have hw : 1 ≤ w := by omega
  let S1 : Finset (Fin w → ZMod 2) := Finset.univ.filter (fun x => x ∈ H1)
  let S2 : Finset (Fin w → ZMod 2) := Finset.univ.filter (fun x => x ∈ H2)
  have hc1 : S1.card ≤ 2 ^ (w - 1) := by
    have heq : S1.card = Fintype.card H1 := (Fintype.card_subtype (fun x => x ∈ H1)).symm
    rw [heq, Module.card_eq_pow_finrank (K := ZMod 2) (V := H1)]
    have hfz : Fintype.card (ZMod 2) = 2 := ZMod.card 2
    rw [hfz]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc2 : S2.card ≤ 2 ^ (w - 1) := by
    have heq : S2.card = Fintype.card H2 := (Fintype.card_subtype (fun x => x ∈ H2)).symm
    rw [heq, Module.card_eq_pow_finrank (K := ZMod 2) (V := H2)]
    have hfz : Fintype.card (ZMod 2) = 2 := ZMod.card 2
    rw [hfz]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 : (0 : Fin w → ZMod 2) ∈ S1 ∩ S2 := by
    simp [S1, S2]
  have hinter : 1 ≤ (S1 ∩ S2).card := Finset.one_le_card.2 ⟨0, h0⟩
  have hunion : (S1 ∪ S2).card + (S1 ∩ S2).card = S1.card + S2.card :=
    Finset.card_union_add_card_inter S1 S2
  have hpow : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    conv_rhs => rw [← Nat.sub_add_cancel hw]
    ring
  have hlt : (S1 ∪ S2).card < (Finset.univ : Finset (Fin w → ZMod 2)).card := by
    have huniv : (Finset.univ : Finset (Fin w → ZMod 2)).card = 2 ^ w := by
      simp [ZMod.card]
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_union, S1, S2, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hy
  exact ⟨y, hy.1, hy.2⟩

lemma mem_hyperplane_add {w : ℕ} (H : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hH : Module.finrank (ZMod 2) H + 1 = w) {a c : Fin w → ZMod 2}
    (ha : a ∉ H) (hc : c ∉ H) : a + c ∈ H := by
  have hdisj : Disjoint H (Submodule.span (ZMod 2) {a}) := by
    rw [Submodule.disjoint_def]
    intro x hxH hxS
    rw [Submodule.mem_span_singleton] at hxS
    obtain ⟨r, rfl⟩ := hxS
    rcases z2_cases r with rfl | rfl
    · simp
    · simp at hxH; exact absurd hxH ha
  have ha0 : a ≠ 0 := fun h => ha (h ▸ H.zero_mem)
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a}) = 1 :=
    finrank_span_singleton ha0
  have hsup_rank : Module.finrank (ZMod 2) ↥(H ⊔ Submodule.span (ZMod 2) {a}) = w := by
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span (ZMod 2) {a})
    rw [hdisj.eq_bot, finrank_bot, add_zero, hspan] at hadd
    omega
  have htop : H ⊔ Submodule.span (ZMod 2) {a} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hsup_rank, Module.finrank_fin_fun]
  have hmem : c ∈ H ⊔ Submodule.span (ZMod 2) {a} := by rw [htop]; trivial
  rw [Submodule.mem_sup] at hmem
  obtain ⟨h, hh, s, hs, hcs⟩ := hmem
  rw [Submodule.mem_span_singleton] at hs
  obtain ⟨r, rfl⟩ := hs
  rcases z2_cases r with rfl | rfl
  · simp at hcs
    rw [← hcs] at hc
    exact absurd hh hc
  · simp only [one_smul] at hcs
    have heq : a + c = h := by
      rw [← hcs]
      have := z2_add_self a
      calc a + (h + a) = h + (a + a) := by abel
        _ = h := by rw [this, add_zero]
    rw [heq]
    exact hh

lemma finrank_sup_span_singleton_of_notMem {w : ℕ}
    (H : Submodule (ZMod 2) (Fin w → ZMod 2)) {y : Fin w → ZMod 2} (hy : y ∉ H) :
    Module.finrank (ZMod 2) ↥(H ⊔ Submodule.span (ZMod 2) {y}) =
      Module.finrank (ZMod 2) H + 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ H.zero_mem)
  have hdisj : Disjoint H (Submodule.span (ZMod 2) {y}) := by
    rw [Submodule.disjoint_def]
    intro x hxH hxS
    rw [Submodule.mem_span_singleton] at hxS
    obtain ⟨r, rfl⟩ := hxS
    rcases z2_cases r with rfl | rfl
    · simp
    · simp at hxH; exact absurd hxH hy
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span (ZMod 2) {y})
  rw [hdisj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hy0] at hadd
  exact hadd

lemma build_flag {b : ℕ} (t : Fin (b + 1) → (Fin (b + 1) → ZMod 2))
    (ht_li : LinearIndependent (ZMod 2) t) :
    let w := b + 1
    let V := Fin w → ZMod 2
    let eLast : V := Pi.single (Fin.last b) 1
    let T : ℕ → Submodule (ZMod 2) V := fun m =>
      Submodule.span (ZMod 2) (Set.image t {i : Fin w | i.val < m})
    ∃ Z : Fin (b + 1) → Submodule (ZMod 2) V,
      Z (Fin.last b) = ⊥ ∧
      (∀ i : Fin b, Z i.succ ≤ Z i.castSucc) ∧
      (∀ m : Fin (b + 1), Module.finrank (ZMod 2) (Z m) = b - m.val) ∧
      (∀ m : Fin (b + 1), eLast ∉ Z m) ∧
      (∀ m : Fin (b + 1), Disjoint (Z m) (T (m.val + 1))) := by
  intro w V eLast T
  have hT_rank : ∀ m ≤ w, Module.finrank (ZMod 2) (T m) = m := by
    intro m hm
    let S : Finset (Fin w) := Finset.univ.filter (fun i : Fin w => i.val < m)
    have hset : Set.image t {i : Fin w | i.val < m} = t '' (↑S : Set (Fin w)) := by
      ext v; simp [S]
    have hcard : S.card = m := by
      let e : Fin m ≃ {i : Fin w // i ∈ S} :=
        { toFun := fun j => ⟨⟨j.val, by omega⟩, by simp [S, j.isLt]⟩
          invFun := fun i => ⟨i.1.val, (Finset.mem_filter.1 i.2).2⟩
          left_inv := fun j => Fin.ext rfl
          right_inv := fun i => Subtype.ext (Fin.ext rfl) }
      rw [← Fintype.card_coe, ← Fintype.card_congr e, Fintype.card_fin]
    have hT_eq : T m = Submodule.span (ZMod 2) (Set.range (t ∘ (Subtype.val : {x : Fin w // x ∈ S} → Fin w))) := by
      dsimp only [T]
      congr 1
      ext v
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, Function.comp_apply,
        Subtype.exists, Finset.mem_filter, Finset.mem_univ, true_and, S]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    rw [hT_eq, finrank_span_eq_card (ht_li.comp Subtype.val Subtype.val_injective), Fintype.card_coe, hcard]
  have hbuild : ∀ (k : ℕ) (hk : k ≤ b),
      ∃ Z : (m : ℕ) → m ≤ k → Submodule (ZMod 2) V,
        Z 0 (Nat.zero_le k) = ⊥ ∧
        (∀ m (hm : m < k), Z m (Nat.le_of_lt hm) ≤ Z (m + 1) hm) ∧
        (∀ m (hm : m ≤ k), Module.finrank (ZMod 2) (Z m hm) = m) ∧
        (∀ m (hm : m ≤ k), eLast ∉ Z m hm) ∧
        (∀ m (hm : m ≤ k), Disjoint (Z m hm) (T (b - m + 1))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ _ => ⊥, rfl, fun _ hm => by omega, ?_, ?_, ?_⟩
      · intro m hm; dsimp only; rw [finrank_bot]; omega
      · intro m _ hmem
        dsimp only at hmem
        rw [Submodule.mem_bot] at hmem
        have h0 : eLast (Fin.last b) = 0 := congrFun hmem (Fin.last b)
        simp [eLast] at h0
      · intro _ _; exact disjoint_bot_left
    | succ k ih =>
      intro hk
      obtain ⟨Z0, hbot, hmono, hrank, hnotE, hdisj⟩ := ih (Nat.le_of_succ_le hk)
      let Zm := Z0 k le_rfl
      let H1 := Zm ⊔ Submodule.span (ZMod 2) {eLast}
      let H2 := Zm ⊔ T (b - k)
      have hH1_rank : Module.finrank (ZMod 2) H1 < w := by
        dsimp only [H1]
        rw [finrank_sup_span_singleton_of_notMem Zm (hnotE k le_rfl), hrank k le_rfl]
        dsimp only [w]; omega
      have hTsub : T (b - k) ≤ T (b - k + 1) := by
        apply Submodule.span_mono
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
      have hdisj_k : Disjoint Zm (T (b - k)) := (hdisj k le_rfl).mono_right hTsub
      have hH2_rank : Module.finrank (ZMod 2) H2 < w := by
        dsimp only [H2]
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq Zm (T (b - k))
        rw [hdisj_k.eq_bot, finrank_bot, add_zero, hrank k le_rfl, hT_rank (b - k) (by dsimp [w]; omega)] at hadd
        dsimp only [w]; omega
      obtain ⟨y, hy1, hy2⟩ := exists_notMem_two_subspaces H1 H2 hH1_rank hH2_rank
      have hyZ : y ∉ Zm := fun h => hy1 (Submodule.mem_sup_left h)
      let Znew := Zm ⊔ Submodule.span (ZMod 2) {y}
      let Z : (m : ℕ) → m ≤ k + 1 → Submodule (ZMod 2) V := fun m hm =>
        if h : m ≤ k then Z0 m h else Znew
      refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Z, hbot]
      · intro m hm
        by_cases hmk : m < k
        · have h1 : m ≤ k := Nat.le_of_lt hmk
          have h2 : m + 1 ≤ k := hmk
          simp only [Z, h1, h2, ↓reduceDIte]
          exact hmono m hmk
        · have hmeq : m = k := by omega
          subst hmeq
          have h1 : ¬ m + 1 ≤ m := by omega
          dsimp only [Z, Znew]
          simp only [le_rfl, h1, ↓reduceDIte]
          exact le_sup_left
      · intro m hm
        by_cases hmk : m ≤ k
        · have hZeq : Z m hm = Z0 m hmk := by dsimp only [Z]; simp only [hmk, ↓reduceDIte]
          rw [hZeq]
          exact hrank m hmk
        · have hmeq : m = k + 1 := by omega
          subst hmeq
          have h1 : ¬ k + 1 ≤ k := by omega
          have hZeq : Z (k + 1) hm = Znew := by dsimp only [Z]; simp only [h1, ↓reduceDIte]
          rw [hZeq]
          dsimp only [Znew]
          rw [finrank_sup_span_singleton_of_notMem Zm hyZ, hrank k le_rfl]
      · intro m hm
        by_cases hmk : m ≤ k
        · simp only [Z, hmk, ↓reduceDIte]
          exact hnotE m hmk
        · have hmeq : m = k + 1 := by omega
          subst hmeq
          have h1 : ¬ k + 1 ≤ k := by omega
          dsimp only [Z, Znew]
          simp only [h1, ↓reduceDIte]
          intro hmem
          rw [Submodule.mem_sup] at hmem
          obtain ⟨z, hz, s, hs, hsum⟩ := hmem
          rw [Submodule.mem_span_singleton] at hs
          obtain ⟨r, rfl⟩ := hs
          rcases z2_cases r with rfl | rfl
          · simp only [zero_smul, add_zero] at hsum; rw [hsum] at hz; exact hnotE k le_rfl hz
          · simp only [one_smul] at hsum
            have hy_eq : y = z + eLast := by
              rw [← hsum]
              have := z2_add_self z
              calc y = 0 + y := (zero_add y).symm
                _ = (z + z) + y := by rw [this]
                _ = z + (z + y) := by abel
            apply hy1
            rw [hy_eq]
            exact Submodule.add_mem_sup hz (Submodule.mem_span_singleton_self eLast)
      · intro m hm
        by_cases hmk : m ≤ k
        · simp only [Z, hmk, ↓reduceDIte]
          exact hdisj m hmk
        · have hmeq : m = k + 1 := by omega
          subst hmeq
          have h1 : ¬ k + 1 ≤ k := by omega
          dsimp only [Z, Znew]
          simp only [h1, ↓reduceDIte]
          have heqb : b - (k + 1) + 1 = b - k := by omega
          rw [heqb]
          rw [Submodule.disjoint_def]
          intro x hxZ hxT
          rw [Submodule.mem_sup] at hxZ
          obtain ⟨z, hz, s, hs, hsum⟩ := hxZ
          rw [Submodule.mem_span_singleton] at hs
          obtain ⟨r, rfl⟩ := hs
          rcases z2_cases r with rfl | rfl
          · simp only [zero_smul, add_zero] at hsum; rw [hsum] at hz
            exact Submodule.disjoint_def.1 hdisj_k x hz hxT
          · simp only [one_smul] at hsum
            exfalso
            apply hy2
            have hy_eq : y = z + x := by
              rw [← hsum]
              have := z2_add_self z
              calc y = 0 + y := (zero_add y).symm
                _ = (z + z) + y := by rw [this]
                _ = z + (z + y) := by abel
            rw [hy_eq]
            exact Submodule.add_mem_sup hz hxT
  obtain ⟨Zr, hbot, hmono, hrank, hnotE, hdisj⟩ := hbuild b le_rfl
  let Z : Fin (b + 1) → Submodule (ZMod 2) V := fun m => Zr (b - m.val) (by omega)
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Z, Fin.last]
    have h0 : b - b = 0 := Nat.sub_self b
    simp only [h0, hbot]
  · intro i
    dsimp only [Z]
    have heq : b - i.castSucc.val = (b - i.succ.val) + 1 := by simp [Fin.castSucc, Fin.succ]; omega
    have hlt : b - i.succ.val < b := by simp [Fin.succ]; omega
    have hm := hmono (b - i.succ.val) hlt
    convert hm using 2
  · intro m
    exact hrank (b - m.val) (by omega)
  · intro m
    exact hnotE (b - m.val) (by omega)
  · intro m
    have hd := hdisj (b - m.val) (by omega)
    have heq : b - (b - m.val) + 1 = m.val + 1 := by omega
    rwa [heq] at hd

lemma linear_route_exact (b : ℕ) (g : (Fin (b + 1) → ZMod 2) ≃ₗ[ZMod 2] (Fin (b + 1) → ZMod 2)) :
    ∃ tap : Fin (2 * b + 1) → Fin b → ZMod 2,
      ∀ x, runFold tap 0 x = g x := by
  classical
  let w := b + 1
  let V := Fin w → ZMod 2
  let t : Fin w → V := fun k i => (g (Pi.single i 1)) k
  have hgx : ∀ (x : V) (k : Fin w), g x k = ∑ i : Fin w, t k i * x i := by
    intro x k
    have hx : x = ∑ i : Fin w, x i • (Pi.single i (1 : ZMod 2) : V) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp [t]; ring
  have ht_li : LinearIndependent (ZMod 2) t := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hzero : ∀ x : V, ∑ j : Fin w, c j * g x j = 0 := by
      intro x
      have hx : ∀ j, g x j = ∑ i : Fin w, t j i * x i := hgx x
      calc ∑ j : Fin w, c j * g x j
          = ∑ j : Fin w, c j * ∑ i : Fin w, t j i * x i := by
              refine Finset.sum_congr rfl (fun j _ => by rw [hx j])
        _ = ∑ i : Fin w, (∑ j : Fin w, c j * t j i) * x i := by
              simp_rw [Finset.mul_sum, Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
        _ = ∑ i : Fin w, 0 * x i := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              have hi : (∑ j : Fin w, c j • (t j : Fin w → ZMod 2)) i = 0 := congrFun hc i
              rw [vec_smul_sum_apply] at hi
              rw [hi]
        _ = 0 := by simp
    have hk := hzero (g.symm (Pi.single k 1))
    simp only [LinearEquiv.apply_symm_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hk
    exact hk
  obtain ⟨Z, hZlast, hZmono, hZrank, hZnotE, hZdisj⟩ := build_flag t ht_li
  let e : Fin w → V := fun i => Pi.single i 1
  have he_li : LinearIndependent (ZMod 2) e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi : (∑ j : Fin w, c j • (e j : Fin w → ZMod 2)) i = 0 := congrFun hc i
    rw [vec_smul_sum_apply] at hi
    simpa [e, Pi.single_apply] using hi
  have hfirst : ∀ (m : ℕ) (hm : m ≤ b),
      ∃ (z : Fin m → V) (tp : Fin m → Fin b → ZMod 2),
        let u : ℕ → V := fun r =>
          if h1 : r < w then e ⟨r, h1⟩
          else if h2 : r - w < m then z ⟨r - w, h2⟩
          else 0
        (∀ r : Fin m, z r ∈ Z ⟨r.val, by omega⟩ ∧ z r ∉ Z ⟨r.val + 1, by omega⟩) ∧
        (∀ r : Fin m, u (w + r.val) = u r.val + ∑ j : Fin b, tp r j • u (r.val + 1 + j.val)) ∧
        LinearIndependent (ZMod 2) (fun j : Fin w => u (m + j.val)) ∧
        Z ⟨0, by omega⟩ = Submodule.span (ZMod 2) (Set.range z) ⊔ Z ⟨m, by omega⟩ := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨Fin.elim0, Fin.elim0, fun r => r.elim0, fun r => r.elim0, ?_, ?_⟩
      · have hfun : (fun j : Fin w => (if h1 : 0 + j.val < w then e ⟨0 + j.val, h1⟩
            else if h2 : 0 + j.val - w < 0 then Fin.elim0 ⟨0 + j.val - w, h2⟩ else 0)) = e := by
          funext j
          have hj : 0 + j.val < w := by simp [j.isLt]
          simp only [hj, ↓reduceDIte]
          congr 1; exact Fin.ext (by simp)
        rw [hfun]
        exact he_li
      · simp
    | succ m ih =>
      intro hm
      obtain ⟨z0, tp0, hz0_mem, hstep0, hli0, hZ0_eq⟩ := ih (Nat.le_of_succ_le hm)
      let u0 : ℕ → V := fun r =>
        if h1 : r < w then e ⟨r, h1⟩
        else if h2 : r - w < m then z0 ⟨r - w, h2⟩
        else 0
      let K : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range (fun j : Fin b => u0 (m + 1 + j.val)))
      have hK_li : LinearIndependent (ZMod 2) (fun j : Fin b => u0 (m + 1 + j.val)) := by
        have hcomp : (fun j : Fin b => u0 (m + 1 + j.val)) =
            (fun j : Fin w => u0 (m + j.val)) ∘ Fin.succ := by
          funext j
          have heq : m + 1 + j.val = m + j.succ.val := by simp [Fin.succ]; omega
          simp [heq]
        rw [hcomp]
        exact hli0.comp Fin.succ (Fin.succ_injective b)
      have hK_rank : Module.finrank (ZMod 2) K = b := by
        rw [finrank_span_eq_card hK_li, Fintype.card_fin]
      have hum_notK : u0 m ∉ K := by
        intro hmem
        rw [Submodule.mem_span_range_iff_exists_fun] at hmem
        obtain ⟨c, hc⟩ := hmem
        let f : Fin w → ZMod 2 := Fin.cons 1 c
        have hsum0 : ∑ k : Fin w, f k • u0 (m + k.val) = 0 := by
          rw [Fin.sum_univ_succ]
          simp only [f, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, add_zero, one_smul]
          have htail : ∑ j : Fin b, c j • u0 (m + j.succ.val) = u0 m := by
            rw [← hc]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            congr 2; simp [Fin.succ]; omega
          rw [htail]
          exact z2_add_self (u0 m)
        have h0 := (Fintype.linearIndependent_iff.1 hli0) f hsum0 0
        simp [f] at h0
      have hex_z : ∃ v ∈ Z ⟨m, by omega⟩, v ∉ Z ⟨m + 1, by omega⟩ ∧ v ∉ K := by
        by_contra hnone
        have hsub_diff : ∀ v ∈ Z ⟨m, by omega⟩, v ∉ Z ⟨m + 1, by omega⟩ → v ∈ K := by
          intro v hv1 hv2
          by_contra hvK
          exact hnone ⟨v, hv1, hv2, hvK⟩
        have hlt_rank : Module.finrank (ZMod 2) (Z ⟨m + 1, by omega⟩) <
            Module.finrank (ZMod 2) (Z ⟨m, by omega⟩) := by
          rw [hZrank, hZrank]; dsimp; omega
        have hne_sub : Z ⟨m + 1, by omega⟩ ≠ Z ⟨m, by omega⟩ := by
          intro heq; rw [heq] at hlt_rank; exact Nat.lt_irrefl _ hlt_rank
        have hle_sub : Z ⟨m + 1, by omega⟩ ≤ Z ⟨m, by omega⟩ := hZmono ⟨m, by omega⟩
        obtain ⟨v0, hv0m, hv0not⟩ : ∃ v0 ∈ Z ⟨m, by omega⟩, v0 ∉ Z ⟨m + 1, by omega⟩ := by
          by_contra hall
          apply hne_sub
          apply le_antisymm hle_sub
          intro x hx; by_contra hxn; exact hall ⟨x, hx, hxn⟩
        have hZm_sub_K : Z ⟨m, by omega⟩ ≤ K := by
          intro x hx
          by_cases hx1 : x ∈ Z ⟨m + 1, by omega⟩
          · have hvx_m : v0 + x ∈ Z ⟨m, by omega⟩ := (Z ⟨m, by omega⟩).add_mem hv0m hx
            have hvx_not : v0 + x ∉ Z ⟨m + 1, by omega⟩ := by
              intro hmem
              apply hv0not
              have : v0 = (v0 + x) + x := by
                have := z2_add_self x
                calc v0 = v0 + 0 := (add_zero v0).symm
                  _ = v0 + (x + x) := by rw [this]
                  _ = (v0 + x) + x := by abel
              rw [this]
              exact (Z ⟨m + 1, by omega⟩).add_mem hmem hx1
            have hv0K : v0 ∈ K := hsub_diff v0 hv0m hv0not
            have hvxK : v0 + x ∈ K := hsub_diff (v0 + x) hvx_m hvx_not
            have : x = v0 + (v0 + x) := by
              have := z2_add_self v0
              calc x = 0 + x := (zero_add x).symm
                _ = (v0 + v0) + x := by rw [this]
                _ = v0 + (v0 + x) := by abel
            rw [this]
            exact K.add_mem hv0K hvxK
          · exact hsub_diff x hx hx1
        have hz0_sub_K : Submodule.span (ZMod 2) (Set.range z0) ≤ K := by
          rw [Submodule.span_le]
          rintro _ ⟨r, rfl⟩
          apply Submodule.subset_span
          refine ⟨⟨b - m + r.val, by omega⟩, ?_⟩
          dsimp only
          have hidx : m + 1 + (b - m + r.val) = w + r.val := by dsimp [w]; omega
          rw [hidx]
          have hge : ¬ w + r.val < w := by omega
          have hsub : w + r.val - w = r.val := by omega
          simp only [u0, hge, ↓reduceDIte]
          have hlt : w + r.val - w < m := by omega
          simp only [hlt, ↓reduceDIte]
          congr 1; exact Fin.ext hsub
        have hZ0_le_K : Z ⟨0, by omega⟩ ≤ K := by
          rw [hZ0_eq]
          exact sup_le hz0_sub_K hZm_sub_K
        have hZ0_eq_K : Z ⟨0, by omega⟩ = K := by
          apply Submodule.eq_of_le_of_finrank_eq hZ0_le_K
          rw [hZrank, hK_rank]; simp
        have heLast_K : Pi.single (Fin.last b) (1 : ZMod 2) ∈ K := by
          apply Submodule.subset_span
          refine ⟨⟨b - 1 - m, by omega⟩, ?_⟩
          dsimp only
          have hidx : m + 1 + (b - 1 - m) = b := by omega
          rw [hidx]
          have hlt : b < w := by dsimp [w]; omega
          simp only [u0, hlt, ↓reduceDIte, e]
          rfl
        rw [← hZ0_eq_K] at heLast_K
        exact hZnotE ⟨0, by omega⟩ heLast_K
      obtain ⟨zm, hzm_in, hzm_not1, hzm_notK⟩ := hex_z
      have haddK : u0 m + zm ∈ K := mem_hyperplane_add K (by rw [hK_rank]) hum_notK hzm_notK
      rw [Submodule.mem_span_range_iff_exists_fun] at haddK
      obtain ⟨c, hc⟩ := haddK
      let z : Fin (m + 1) → V := fun r =>
        if h : r.val < m then z0 ⟨r.val, h⟩ else zm
      let tp : Fin (m + 1) → Fin b → ZMod 2 := fun r =>
        if h : r.val < m then tp0 ⟨r.val, h⟩ else c
      let u : ℕ → V := fun r =>
        if h1 : r < w then e ⟨r, h1⟩
        else if h2 : r - w < m + 1 then z ⟨r - w, h2⟩
        else 0
      have hu_eq_u0 : ∀ r < w + m, u r = u0 r := by
        intro r hr
        by_cases h1 : r < w
        · simp only [u, u0, h1, ↓reduceDIte]
        · have h2 : r - w < m := by omega
          have h3 : r - w < m + 1 := by omega
          simp only [u, u0, h1, h2, h3, ↓reduceDIte, z]
      have hu_wm : u (w + m) = zm := by
        have h1 : ¬ w + m < w := by omega
        have h2 : w + m - w < m + 1 := by omega
        have h3 : ¬ (w + m - w) < m := by omega
        simp only [u, h1, h2, ↓reduceDIte, z, h3]
      refine ⟨z, tp, ?_, ?_, ?_, ?_⟩
      · intro r
        by_cases hr : r.val < m
        · simp only [z, hr, ↓reduceDIte]
          exact hz0_mem ⟨r.val, hr⟩
        · have hreq : r.val = m := by omega
          have h1 : (⟨r.val, by omega⟩ : Fin (b + 1)) = ⟨m, by omega⟩ := Fin.ext (by dsimp; omega)
          have h2 : (⟨r.val + 1, by omega⟩ : Fin (b + 1)) = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp; omega)
          simp only [z, hr, ↓reduceDIte]
          rw [h1, h2]
          exact ⟨hzm_in, hzm_not1⟩
      · intro r
        change u (w + r.val) = u r.val + ∑ j : Fin b, tp r j • u (r.val + 1 + j.val)
        by_cases hr : r.val < m
        · simp only [tp, hr, ↓reduceDIte]
          rw [hu_eq_u0 (w + r.val) (by omega), hu_eq_u0 r.val (by omega)]
          have hsum : ∑ j : Fin b, tp0 ⟨r.val, hr⟩ j • u (r.val + 1 + j.val) =
              ∑ j : Fin b, tp0 ⟨r.val, hr⟩ j • u0 (r.val + 1 + j.val) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [hu_eq_u0 (r.val + 1 + j.val) (by dsimp [w]; omega)]
          rw [hsum]
          exact hstep0 ⟨r.val, hr⟩
        · have hreq : r.val = m := by omega
          have hnm : ¬ m < m := Nat.lt_irrefl m
          simp only [tp, hreq, hnm, ↓reduceDIte, hu_wm]
          rw [hu_eq_u0 m (by omega)]
          have hsum : ∑ j : Fin b, c j • u (m + 1 + j.val) =
              ∑ j : Fin b, c j • u0 (m + 1 + j.val) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [hu_eq_u0 (m + 1 + j.val) (by dsimp [w]; omega)]
          rw [hsum, hc]
          have := z2_add_self (u0 m)
          calc zm = 0 + zm := (zero_add zm).symm
            _ = (u0 m + u0 m) + zm := by rw [this]
            _ = u0 m + (u0 m + zm) := by abel
      · change LinearIndependent (ZMod 2) (fun j : Fin w => u (m + 1 + j.val))
        rw [linearIndependent_iff']
        intro s f hf j hj
        let g' : Fin w → V := fun k => u (m + 1 + k.val)
        have hlast_eq : g' (Fin.last b) = zm := by
          dsimp [g', Fin.last]
          have : m + 1 + b = w + m := by dsimp [w]; omega
          rw [this, hu_wm]
        have hcast_eq : ∀ k : Fin b, g' k.castSucc = u0 (m + 1 + k.val) := by
          intro k
          dsimp [g', Fin.castSucc]
          exact hu_eq_u0 (m + 1 + k.val) (by dsimp [w]; omega)
        have hflast : f (Fin.last b) = 0 ∨ Fin.last b ∉ s := by
          by_contra hboth
          rw [not_or, not_not] at hboth
          have hmem_s : Fin.last b ∈ s := hboth.2
          have hfl1 : f (Fin.last b) = 1 := by
            rcases z2_cases (f (Fin.last b)) with hval | hval
            · exact absurd hval hboth.1
            · exact hval
          have hsplit := Finset.add_sum_erase s (fun k => f k • g' k) hmem_s
          rw [hf, hfl1, one_smul, hlast_eq] at hsplit
          have hsum_in_K : ∑ k ∈ s.erase (Fin.last b), f k • g' k ∈ K := by
            refine K.sum_mem (fun k hk => K.smul_mem (f k) ?_)
            have hne : k ≠ Fin.last b := (Finset.mem_erase.1 hk).1
            obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.2 hne
            rw [hcast_eq k']
            exact Submodule.subset_span ⟨k', rfl⟩
          have hzm_K : zm ∈ K := by
            have heq : zm = ∑ k ∈ s.erase (Fin.last b), f k • g' k := by
              have hself := z2_add_self zm
              calc zm = zm + 0 := (add_zero zm).symm
                _ = zm + (zm + ∑ k ∈ s.erase (Fin.last b), f k • g' k) := by rw [← hsplit]
                _ = (zm + zm) + ∑ k ∈ s.erase (Fin.last b), f k • g' k := by abel
                _ = ∑ k ∈ s.erase (Fin.last b), f k • g' k := by rw [hself, zero_add]
            rw [heq]; exact hsum_in_K
          exact hzm_notK hzm_K
        have hsum_b : ∑ k ∈ (Finset.univ : Finset (Fin b)).filter (fun k => k.castSucc ∈ s),
            f k.castSucc • u0 (m + 1 + k.val) = 0 := by
          have h1 : ∑ k ∈ s.erase (Fin.last b), f k • g' k = 0 := by
            rcases hflast with hf0 | hnot
            · by_cases hmem : Fin.last b ∈ s
              · have := Finset.add_sum_erase s (fun k => f k • g' k) hmem
                rw [hf, hf0, zero_smul, zero_add] at this
                exact this
              · rw [Finset.erase_eq_of_notMem hmem]; exact hf
            · rw [Finset.erase_eq_of_notMem hnot]; exact hf
          rw [← h1]
          refine Finset.sum_nbij (fun k : Fin b => k.castSucc) ?_ ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact Finset.mem_erase.2 ⟨Fin.castSucc_ne_last k, hk⟩
          · intro k1 _ k2 _ heq; exact Fin.castSucc_injective b heq
          · intro k hk
            obtain ⟨hne, hks⟩ := Finset.mem_erase.1 hk
            obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.2 hne
            exact ⟨k', Finset.mem_filter.2 ⟨Finset.mem_univ _, hks⟩, rfl⟩
          · intro k _; rw [hcast_eq k]
        by_cases hjlast : j = Fin.last b
        · subst hjlast
          rcases hflast with hf0 | hnot
          · exact hf0
          · exact absurd hj hnot
        · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hjlast
          exact (linearIndependent_iff'.1 hK_li) _ _ hsum_b j'
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
      · have hZm_eq : Z ⟨m, by omega⟩ =
            Submodule.span (ZMod 2) {zm} ⊔ Z ⟨m + 1, by omega⟩ := by
          apply Eq.symm
          apply Submodule.eq_of_le_of_finrank_eq
          · exact sup_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hzm_in)) (hZmono ⟨m, by omega⟩)
          · rw [sup_comm, finrank_sup_span_singleton_of_notMem (Z ⟨m + 1, by omega⟩) hzm_not1,
              hZrank, hZrank]
            dsimp; omega
        rw [hZ0_eq, hZm_eq, ← sup_assoc]
        congr 1
        have hrange : Set.range z = Set.range z0 ∪ {zm} := by
          ext v
          simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · rintro ⟨r, rfl⟩
            by_cases hr : r.val < m
            · left; exact ⟨⟨r.val, hr⟩, by simp [z, hr]⟩
            · right; simp [z, hr]
          · rintro (⟨r, rfl⟩ | rfl)
            · exact ⟨⟨r.val, by omega⟩, by simp [z, r.isLt]⟩
            · exact ⟨⟨m, by omega⟩, by simp [z]⟩
        rw [hrange, Submodule.span_union]
  obtain ⟨z, tp1, hz_mem, hstep1, _, hZ0_eq⟩ := hfirst b le_rfl
  have hZ_span : ∀ (m : ℕ) (hm : m ≤ b),
      Z ⟨m, by omega⟩ = Submodule.span (ZMod 2) (Set.image z {r : Fin b | m ≤ r.val}) := by
    intro m hm
    have hdesc : ∀ (d : ℕ) (hd : d ≤ b),
        Z ⟨b - d, by omega⟩ = Submodule.span (ZMod 2) (Set.image z {r : Fin b | b - d ≤ r.val}) := by
      intro d
      induction d with
      | zero =>
        intro _
        have h0 : (⟨b - 0, by omega⟩ : Fin (b + 1)) = Fin.last b := Fin.ext (by simp [Fin.last])
        rw [h0, hZlast]
        have hemp : Set.image z {r : Fin b | b - 0 ≤ r.val} = ∅ := by
          ext v; simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
          intro r hr; omega
        rw [hemp, Submodule.span_empty]
      | succ d ih =>
        intro hd
        have hprev := ih (Nat.le_of_succ_le hd)
        let idx : Fin b := ⟨b - (d + 1), by omega⟩
        have hsucc_eq : (⟨b - d, by omega⟩ : Fin (b + 1)) = ⟨idx.val + 1, by omega⟩ :=
          Fin.ext (by dsimp [idx]; omega)
        have hZm_eq : Z ⟨idx.val, by omega⟩ =
            Submodule.span (ZMod 2) {z idx} ⊔ Z ⟨idx.val + 1, by omega⟩ := by
          apply Eq.symm
          apply Submodule.eq_of_le_of_finrank_eq
          · exact sup_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 (hz_mem idx).1)) (hZmono idx)
          · rw [sup_comm, finrank_sup_span_singleton_of_notMem (Z ⟨idx.val + 1, by omega⟩) (hz_mem idx).2,
              hZrank, hZrank]
            dsimp [idx]; omega
        rw [hZm_eq, ← hsucc_eq, hprev]
        have hset : Set.image z {r : Fin b | b - (d + 1) ≤ r.val} =
            {z idx} ∪ Set.image z {r : Fin b | b - d ≤ r.val} := by
          ext v
          simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · rintro ⟨r, hr, rfl⟩
            by_cases hreq : r.val = b - (d + 1)
            · left; congr 1; exact Fin.ext (by dsimp [idx]; omega)
            · right; exact ⟨r, by omega, rfl⟩
          · rintro (rfl | ⟨r, hr, rfl⟩)
            · exact ⟨idx, by dsimp [idx]; omega, rfl⟩
            · exact ⟨r, by omega, rfl⟩
        rw [hset, Submodule.span_union]
    have hd := hdesc (b - m) (by omega)
    have hbm : b - (b - m) = m := by omega
    have hfin : (⟨b - (b - m), by omega⟩ : Fin (b + 1)) = ⟨m, by omega⟩ := Fin.ext hbm
    rw [hfin] at hd
    simpa only [hbm] using hd
  let uFull : ℕ → V := fun r =>
    if h1 : r < w then e ⟨r, h1⟩
    else if h2 : r - w < b then z ⟨r - w, h2⟩
    else if h3 : r - (w + b) < w then t ⟨r - (w + b), h3⟩
    else 0
  have hsecond : ∀ m : Fin w,
      ∃ c : Fin b → ZMod 2,
        uFull (w + b + m.val) = uFull (b + m.val) + ∑ j : Fin b, c j • uFull (b + m.val + 1 + j.val) := by
    intro m
    let T : ℕ → Submodule (ZMod 2) V := fun k =>
      Submodule.span (ZMod 2) (Set.image t {i : Fin w | i.val < k})
    have hT_rank : ∀ k ≤ w, Module.finrank (ZMod 2) (T k) = k := by
      intro k hk
      let S : Finset (Fin w) := Finset.univ.filter (fun i : Fin w => i.val < k)
      have hcard : S.card = k := by
        let eqv : Fin k ≃ {i : Fin w // i ∈ S} :=
          { toFun := fun j => ⟨⟨j.val, by omega⟩, by simp [S, j.isLt]⟩
            invFun := fun i => ⟨i.1.val, (Finset.mem_filter.1 i.2).2⟩
            left_inv := fun j => Fin.ext rfl
            right_inv := fun i => Subtype.ext (Fin.ext rfl) }
        rw [← Fintype.card_coe, ← Fintype.card_congr eqv, Fintype.card_fin]
      have hT_eq : T k = Submodule.span (ZMod 2) (Set.range (t ∘ (Subtype.val : {x : Fin w // x ∈ S} → Fin w))) := by
        dsimp only [T]; congr 1; ext v
        simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, Function.comp_apply,
          Subtype.exists, Finset.mem_filter, Finset.mem_univ, true_and, S]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      rw [hT_eq, finrank_span_eq_card (ht_li.comp Subtype.val Subtype.val_injective), Fintype.card_coe, hcard]
    let H := Z m ⊔ T m.val
    have hTsub : T m.val ≤ T (m.val + 1) := by
      apply Submodule.span_mono
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
    have hdisj_m : Disjoint (Z m) (T m.val) := (hZdisj m).mono_right hTsub
    have hH_rank : Module.finrank (ZMod 2) H = b := by
      dsimp only [H]
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq (Z m) (T m.val)
      rw [hdisj_m.eq_bot, finrank_bot, add_zero, hZrank m, hT_rank m.val (by omega)] at hadd
      omega
    have htm_notH : t m ∉ H := by
      intro hmem
      rw [Submodule.mem_sup] at hmem
      obtain ⟨zv, hzv, tv, htv, hsum⟩ := hmem
      have hzv_T : zv ∈ T (m.val + 1) := by
        have htm_in : t m ∈ T (m.val + 1) := Submodule.subset_span ⟨m, Nat.lt_succ_self _, rfl⟩
        have htv_in : tv ∈ T (m.val + 1) := hTsub htv
        have heq : zv = t m + tv := by
          rw [← hsum]
          have := z2_add_self tv
          calc zv = zv + 0 := (add_zero zv).symm
            _ = zv + (tv + tv) := by rw [this]
            _ = (zv + tv) + tv := by abel
        rw [heq]
        exact (T (m.val + 1)).add_mem htm_in htv_in
      have hzv0 : zv = 0 := Submodule.disjoint_def.1 (hZdisj m) zv hzv hzv_T
      rw [hzv0, zero_add] at hsum
      rw [hsum] at htv
      exact (LinearIndependent.notMem_span_image ht_li (by simp : m ∉ {i : Fin w | i.val < m.val})) htv
    have hub_notH : uFull (b + m.val) ∉ H := by
      by_cases hm0 : m.val = 0
      · have hm_eq : m = ⟨0, by omega⟩ := Fin.ext hm0
        dsimp only [H]
        rw [hm_eq]
        have hT0 : T 0 = ⊥ := by
          dsimp only [T]
          have : Set.image t {i : Fin w | i.val < 0} = ∅ := by ext v; simp
          rw [this, Submodule.span_empty]
        simp only [hT0, sup_bot_eq]
        have hu_eq : uFull (b + 0) = Pi.single (Fin.last b) 1 := by
          have hlt : b + 0 < w := by dsimp [w]; omega
          simp only [uFull, hlt, ↓reduceDIte, e]
          rfl
        rw [hu_eq]
        exact hZnotE ⟨0, by omega⟩
      · have hprev_lt : m.val - 1 < b := by omega
        have hu_eq : uFull (b + m.val) = z ⟨m.val - 1, hprev_lt⟩ := by
          have h1 : ¬ b + m.val < w := by dsimp [w]; omega
          have h2 : b + m.val - w < b := by dsimp [w]; omega
          simp only [uFull, h1, h2, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp [w]; omega)
        rw [hu_eq]
        intro hmem
        rw [Submodule.mem_sup] at hmem
        obtain ⟨zv, hzv, tv, htv, hsum⟩ := hmem
        have hz_prev : z ⟨m.val - 1, hprev_lt⟩ ∈ Z ⟨m.val - 1, by omega⟩ :=
          (hz_mem ⟨m.val - 1, hprev_lt⟩).1
        have hzv_prev : zv ∈ Z ⟨m.val - 1, by omega⟩ := by
          have hle : Z m ≤ Z ⟨m.val - 1, by omega⟩ := by
            have hm1 := hZmono ⟨m.val - 1, hprev_lt⟩
            have hs1 : (⟨m.val - 1, hprev_lt⟩ : Fin b).succ = m := Fin.ext (by dsimp; omega)
            have hs2 : (⟨m.val - 1, hprev_lt⟩ : Fin b).castSucc = ⟨m.val - 1, by omega⟩ := Fin.ext rfl
            rw [hs1, hs2] at hm1
            exact hm1
          exact hle hzv
        have htv_inZ : tv ∈ Z ⟨m.val - 1, by omega⟩ := by
          have heq : tv = z ⟨m.val - 1, hprev_lt⟩ + zv := by
            rw [← hsum]
            have := z2_add_self zv
            calc tv = 0 + tv := (zero_add tv).symm
              _ = (zv + zv) + tv := by rw [this]
              _ = (zv + tv) + zv := by abel
          rw [heq]
          exact (Z ⟨m.val - 1, by omega⟩).add_mem hz_prev hzv_prev
        have hdisj_prev := hZdisj ⟨m.val - 1, by omega⟩
        have hteq : m.val - 1 + 1 = m.val := by omega
        rw [hteq] at hdisj_prev
        have htv0 : tv = 0 := Submodule.disjoint_def.1 hdisj_prev tv htv_inZ htv
        rw [htv0, add_zero] at hsum
        rw [hsum] at hzv
        have hnot := (hz_mem ⟨m.val - 1, hprev_lt⟩).2
        have hm_eq : (⟨m.val - 1 + 1, by omega⟩ : Fin (b + 1)) = m := Fin.ext (by omega)
        rw [hm_eq] at hnot
        exact hnot hzv
    have haddH : uFull (b + m.val) + t m ∈ H :=
      mem_hyperplane_add H (by rw [hH_rank]) hub_notH htm_notH
    have hH_eq_range : H = Submodule.span (ZMod 2) (Set.range (fun j : Fin b => uFull (b + m.val + 1 + j.val))) := by
      have hZm : Z m = Submodule.span (ZMod 2) (Set.image z {r : Fin b | m.val ≤ r.val}) :=
        hZ_span m.val (by omega)
      dsimp only [H, T]
      rw [hZm, ← Submodule.span_union]
      congr 1
      ext v
      simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
      constructor
      · rintro (⟨r, hr, rfl⟩ | ⟨i, hi, rfl⟩)
        · refine ⟨⟨r.val - m.val, by omega⟩, ?_⟩
          have h1 : ¬ b + m.val + 1 + (r.val - m.val) < w := by dsimp [w]; omega
          have h2 : b + m.val + 1 + (r.val - m.val) - w < b := by dsimp [w]; omega
          simp only [uFull, h1, h2, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp [w]; omega)
        · refine ⟨⟨b - m.val + i.val, by omega⟩, ?_⟩
          have h1 : ¬ b + m.val + 1 + (b - m.val + i.val) < w := by dsimp [w]; omega
          have h2 : ¬ b + m.val + 1 + (b - m.val + i.val) - w < b := by dsimp [w]; omega
          have h3 : b + m.val + 1 + (b - m.val + i.val) - (w + b) < w := by dsimp [w]; omega
          simp only [uFull, h1, h2, h3, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp [w]; omega)
      · rintro ⟨j, rfl⟩
        by_cases hj : m.val + j.val < b
        · left
          refine ⟨⟨m.val + j.val, hj⟩, by dsimp; omega, ?_⟩
          have h1 : ¬ b + m.val + 1 + j.val < w := by dsimp [w]; omega
          have h2 : b + m.val + 1 + j.val - w < b := by dsimp [w]; omega
          simp only [uFull, h1, h2, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp [w]; omega)
        · right
          refine ⟨⟨m.val + j.val - b, by dsimp [w]; omega⟩, by dsimp; omega, ?_⟩
          have h1 : ¬ b + m.val + 1 + j.val < w := by dsimp [w]; omega
          have h2 : ¬ b + m.val + 1 + j.val - w < b := by dsimp [w]; omega
          have h3 : b + m.val + 1 + j.val - (w + b) < w := by dsimp [w]; omega
          simp only [uFull, h1, h2, h3, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp [w]; omega)
    rw [hH_eq_range, Submodule.mem_span_range_iff_exists_fun] at haddH
    obtain ⟨c, hc⟩ := haddH
    refine ⟨c, ?_⟩
    have htm_eq : uFull (w + b + m.val) = t m := by
      have h1 : ¬ w + b + m.val < w := by omega
      have h2 : ¬ w + b + m.val - w < b := by omega
      have h3 : w + b + m.val - (w + b) < w := by omega
      simp only [uFull, h1, h2, h3, ↓reduceDIte]
      congr 1; exact Fin.ext (by dsimp; omega)
    rw [htm_eq, hc]
    have := z2_add_self (uFull (b + m.val))
    calc t m = 0 + t m := (zero_add (t m)).symm
      _ = (uFull (b + m.val) + uFull (b + m.val)) + t m := by rw [this]
      _ = uFull (b + m.val) + (uFull (b + m.val) + t m) := by abel
  choose tp2 htp2 using hsecond
  let tap : Fin (2 * b + 1) → Fin b → ZMod 2 := fun i =>
    if h : i.val < b then tp1 ⟨i.val, h⟩ else tp2 ⟨i.val - b, by omega⟩
  refine ⟨tap, ?_⟩
  have hstep_all : ∀ (i : Fin (2 * b + 1)),
      uFull (w + i.val) = uFull i.val + ∑ j : Fin b, tap i j • uFull (i.val + 1 + j.val) := by
    intro i
    by_cases hi : i.val < b
    · simp only [tap, hi, ↓reduceDIte]
      have h1 := hstep1 ⟨i.val, hi⟩
      have heq_u : ∀ r < w + b, uFull r =
          (if h1 : r < w then e ⟨r, h1⟩ else if h2 : r - w < b then z ⟨r - w, h2⟩ else 0) := by
        intro r hr
        by_cases ha : r < w
        · simp [uFull, ha]
        · have hb' : r - w < b := by omega
          simp [uFull, ha, hb']
      rw [heq_u (w + i.val) (by omega), heq_u i.val (by omega)]
      have hsum : ∑ j : Fin b, tp1 ⟨i.val, hi⟩ j • uFull (i.val + 1 + j.val) =
          ∑ j : Fin b, tp1 ⟨i.val, hi⟩ j •
            (if h1 : i.val + 1 + j.val < w then e ⟨i.val + 1 + j.val, h1⟩
             else if h2 : i.val + 1 + j.val - w < b then z ⟨i.val + 1 + j.val - w, h2⟩ else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [heq_u (i.val + 1 + j.val) (by dsimp [w]; omega)]
      rw [hsum]
      exact h1
    · simp only [tap, hi, ↓reduceDIte]
      have h2 := htp2 ⟨i.val - b, by omega⟩
      have heq1 : w + b + (i.val - b) = w + i.val := by omega
      have heq2 : b + (i.val - b) = i.val := by omega
      simpa only [heq1, heq2] using h2
  have hdot : ∀ (x : V) (s : ℕ) (hs : s ≤ 2 * b + 1) (k : Fin w),
      stepAt tap 0 x s k = ∑ p : Fin w, uFull (s + k.val) p * x p := by
    intro x s
    induction s with
    | zero =>
      intro _ k
      simp only [stepAt, zero_add]
      have hlt : k.val < w := k.isLt
      have hk_eq : (⟨k.val, hlt⟩ : Fin w) = k := Fin.ext rfl
      simp only [uFull, hlt, ↓reduceDIte, hk_eq, e, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    | succ s ih =>
      intro hs k
      have hlt : s < 2 * b + 1 := Nat.lt_of_succ_le hs
      simp only [stepAt, hlt, ↓reduceDIte]
      refine Fin.lastCases ?_ ?_ k
      · simp only [step, Fin.snoc_last, Pi.zero_apply, add_zero]
        rw [ih (Nat.le_of_lt hs) 0]
        have hst := hstep_all ⟨s, hlt⟩
        have hidx : s + 1 + (Fin.last b).val = w + s := by dsimp [w, Fin.last]; omega
        rw [hidx, hst]
        have hsum_step : ∑ j : Fin b, tap ⟨s, hlt⟩ j * stepAt tap 0 x s j.succ =
            ∑ p : Fin w, (∑ j : Fin b, tap ⟨s, hlt⟩ j • uFull (s + 1 + j.val)) p * x p := by
          have h1 : ∀ j : Fin b, stepAt tap 0 x s j.succ =
              ∑ p : Fin w, uFull (s + 1 + j.val) p * x p := fun j => by
            have := ih (Nat.le_of_lt hs) j.succ
            have heq : s + j.succ.val = s + 1 + j.val := by simp [Fin.succ]; omega
            rwa [heq] at this
          have h2 : ∀ p : Fin w, (∑ j : Fin b, tap ⟨s, hlt⟩ j • uFull (s + 1 + j.val)) p =
              ∑ j : Fin b, tap ⟨s, hlt⟩ j * uFull (s + 1 + j.val) p := fun p =>
            vec_smul_sum_apply Finset.univ (tap ⟨s, hlt⟩) (fun j => uFull (s + 1 + j.val)) p
          simp_rw [h1, h2, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun j _ => by ring))
        rw [hsum_step, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        change uFull (s + 0) p * x p + (∑ j : Fin b, tap ⟨s, hlt⟩ j • uFull (s + 1 + j.val)) p * x p =
          (uFull s p + (∑ j : Fin b, tap ⟨s, hlt⟩ j • uFull (s + 1 + j.val)) p) * x p
        rw [add_zero, add_mul]
      · intro j
        simp only [step, Fin.snoc_castSucc]
        rw [ih (Nat.le_of_lt hs) j.succ]
        have heq : s + j.succ.val = s + 1 + j.castSucc.val := by simp [Fin.succ, Fin.castSucc]; omega
        rw [heq]
  intro x
  rw [runFold_eq_stepAt]
  funext k
  rw [hdot x (2 * b + 1) le_rfl k, hgx x k]
  have h1 : ¬ 2 * b + 1 + k.val < w := by dsimp [w]; omega
  have h2 : ¬ 2 * b + 1 + k.val - w < b := by dsimp [w]; omega
  have h3 : 2 * b + 1 + k.val - (w + b) < w := by dsimp [w]; omega
  simp only [uFull, h1, h2, h3, ↓reduceDIte]
  have heq : (⟨2 * b + 1 + k.val - (w + b), h3⟩ : Fin w) = k := Fin.ext (by dsimp [w]; omega)
  rw [heq]

lemma main_proof (b L : ℕ) :
    let w := b + 1
    let V := Fin w → ZMod 2
    (∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      ∃ (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2),
        ∀ x : V, runFold tap bias x = g x + v) ↔
      2 * w - 1 ≤ L := by
  intro w V
  constructor
  · intro hall
    exact only_if_dir b L hall
  · intro hL g v
    have hL' : 2 * b + 1 ≤ L := by dsimp [w] at hL; omega
    let d := L - (2 * b + 1)
    have hd_add : d + (2 * b + 1) = L := Nat.sub_add_cancel hL'
    let R : V ≃ₗ[ZMod 2] V :=
      { toFun := step 0 0
        map_add' := fun x y => by have h := step_add (0 : Fin b → ZMod 2) 0 0 x y; simpa using h
        map_smul' := fun r x => by
          rcases z2_cases r with rfl | rfl
          · funext k; refine Fin.lastCases ?_ ?_ k
            · simp [step]; rfl
            · intro i; simp [step]; rfl
          · funext k; refine Fin.lastCases ?_ ?_ k
            · simp [step]
            · intro i; simp [step]
        invFun := fun y => Fin.cons (y (Fin.last b)) (fun j : Fin b => y j.castSucc)
        left_inv := fun x => by
          funext k
          refine Fin.cases ?_ ?_ k
          · simp [step]
          · intro j; simp [step]
        right_inv := fun y => by
          funext k
          refine Fin.lastCases ?_ ?_ k
          · simp [step]
          · intro j; simp [step] }
    let Rd : V ≃ₗ[ZMod 2] V := R ^ d
    let g' : V ≃ₗ[ZMod 2] V := Rd.symm.trans g
    obtain ⟨tap0, htap0⟩ := linear_route_exact b g'
    let tap : Fin L → Fin b → ZMod 2 := fun i =>
      if h : i.val < d then 0 else tap0 ⟨i.val - d, by omega⟩
    have hpad : ∀ (x : V) (m : ℕ) (hm : m ≤ d), stepAt tap 0 x m = (R ^ m) x := by
      intro x m
      induction m with
      | zero => intro _; simp [stepAt]
      | succ m ih =>
        intro hm
        have hlt : m < L := by omega
        have hmd : m < d := Nat.lt_of_succ_le hm
        simp only [stepAt, hlt, ↓reduceDIte, tap, hmd]
        rw [ih (Nat.le_of_lt hm), pow_succ']
        rfl
    have htail : ∀ (x : V) (m : ℕ) (hm : m ≤ 2 * b + 1),
        stepAt tap 0 x (d + m) = stepAt tap0 0 (Rd x) m := by
      intro x m
      induction m with
      | zero =>
        intro _
        simp only [add_zero, stepAt]
        exact hpad x d le_rfl
      | succ m ih =>
        intro hm
        have hlt : d + m < L := by omega
        have hmlt : m < 2 * b + 1 := Nat.lt_of_succ_le hm
        have heq : d + (m + 1) = (d + m) + 1 := by omega
        rw [heq]
        simp only [stepAt, hlt, hmlt, ↓reduceDIte]
        have hnd : ¬ d + m < d := by omega
        simp only [tap, hnd, ↓reduceDIte, ih (Nat.le_of_lt hm)]
        have hsub : (⟨d + m - d, by omega⟩ : Fin (2 * b + 1)) = ⟨m, hmlt⟩ := Fin.ext (by dsimp; omega)
        rw [hsub]
        rfl
    have hlin : ∀ x : V, runFold tap 0 x = g x := by
      intro x
      rw [runFold_eq_stepAt]
      have hL_step : stepAt tap 0 x L = stepAt tap 0 x (d + (2 * b + 1)) :=
        congrArg (stepAt tap 0 x) hd_add.symm
      rw [hL_step, htail x (2 * b + 1) le_rfl, ← runFold_eq_stepAt, htap0 (Rd x)]
      simp [g']
    obtain ⟨bias, hbias⟩ := exists_bias_for_target (by omega) tap v
    refine ⟨tap, bias, fun x => ?_⟩
    rw [runFold_split_bias, hlin x, hbias]

end PEqualNP.Outside.L_lib_614_aux

theorem PEqualNP.Outside.L_lib_614 :
∀ (b L : ℕ),
  let w := b + 1
  let V := Fin w → ZMod 2
  (∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
    ∃ (tap : Fin L → Fin b → ZMod 2) (bias : Fin L → ZMod 2),
      ∀ x : V, (List.finRange L).foldl (fun (s : V) i =>
        let tail := fun j : Fin b => s j.succ
        Fin.snoc (α := fun _ : Fin w => ZMod 2) tail
          (s 0 + bias i + ∑ j : Fin b, tap i j * tail j)) x = g x + v) ↔
    2 * w - 1 ≤ L := by
  intro b L
  exact PEqualNP.Outside.L_lib_614_aux.main_proof b L

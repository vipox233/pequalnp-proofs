import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1155_aux

open scoped BigOperators

/-! ### Part A: Single-block (Fin 16) definitions and decidable identities -/

def localPass (opp : Bool) (z x : Fin 16) : Bool :=
  let w := z.val ^^^ x.val
  (w &&& 3) != 0 && (w &&& 13) != (if opp then 1 else 0)

def xor16 (a b : Fin 16) : Fin 16 :=
  ⟨(a.val ^^^ b.val) % 16, Nat.mod_lt _ (by omega)⟩

def chi16 (a b : Fin 16) : ℤ :=
  (-1 : ℤ) ^ ((Finset.univ : Finset (Fin 4)).filter
    (fun k => a.val.testBit k.val && b.val.testBit k.val)).card

def c165 : Fin 16 → ℤ :=
  ![(-8), 3, (-118), 3, (-8), 3, 47, 3, (-8), 3, 47, 3, (-8), 3, 47, 3]

def c0_exact : Fin 16 → ℤ :=
  ![(-2270), (-195), (-1444), (-195), (-286), (-195), 541, (-195),
    (-286), (-195), 541, (-195), (-286), (-195), 541, (-195)]

def c1_exact : Fin 16 → ℤ :=
  ![(-1023), 837, 2077, 837, 1457, (-155), (-403), (-155),
    1457, (-155), (-403), (-155), 1457, (-155), (-403), (-155)]

lemma localPass_symm : ∀ (opp : Bool) (z x : Fin 16), localPass opp z x = localPass opp x z := by
  decide

lemma local_synth_165 : ∀ (y x : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun z =>
      if localPass false z x = true then c165 (xor16 z y) else 0) =
    if x = y then 165 else 0 := by
  decide

lemma local_synth_1 : ∀ (y x : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun z =>
      if localPass false z x = true then c0_exact (xor16 z y) else 0) +
    (Finset.univ : Finset (Fin 16)).sum (fun z =>
      if localPass true z x = true then c1_exact (xor16 z y) else 0) =
    if x = y then 1 else 0 := by
  decide

lemma local_walsh_0 : ∀ (opp : Bool) (z : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun x =>
      if localPass opp z x = true then chi16 x 0 else 0) =
    (if opp then 10 else 11) * chi16 z 0 := by
  decide

lemma local_walsh_1 : ∀ (z : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun x =>
      if localPass false z x = true then chi16 x 1 else 0) =
    (-5) * chi16 z 1 := by
  decide

lemma local_walsh_2 : ∀ (z : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun x =>
      if localPass false z x = true then chi16 x 2 else 0) =
    (-3) * chi16 z 2 := by
  decide

lemma local_walsh_6 : ∀ (opp : Bool) (z : Fin 16),
    (Finset.univ : Finset (Fin 16)).sum (fun x =>
      if localPass opp z x = true then chi16 x 6 else 0) =
    (if opp then 0 else 1) * chi16 z 6 := by
  decide

lemma chi16_sq : ∀ (x t : Fin 16), chi16 x t * chi16 x t = 1 := by
  decide

lemma chi16_zero_left : ∀ (t : Fin 16), chi16 0 t = 1 := by
  decide

/-! ### Part B: Multi-block pass and tensoring -/

noncomputable def passOf {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))

lemma passOf_iff {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    passOf e z x = true ↔ ∀ j : Fin r, localPass (decide (j ∈ e)) (z j) (x j) = true := by
  simp only [passOf, List.all_eq_true, Finset.mem_toList, Finset.mem_univ, forall_true_left]
  refine forall_congr' fun j => ?_
  dsimp only [localPass]
  by_cases hj : j ∈ e <;> simp [hj]

lemma passOf_indicator {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    (if passOf e z x = true then (1 : ℤ) else 0) =
    ∏ j : Fin r, if localPass (decide (j ∈ e)) (z j) (x j) = true then (1 : ℤ) else 0 := by
  by_cases hp : passOf e z x = true
  · rw [if_pos hp]
    exact (Finset.prod_eq_one fun j _ => if_pos ((passOf_iff e z x).mp hp j)).symm
  · rw [if_neg hp]
    have hex : ∃ j : Fin r, localPass (decide (j ∈ e)) (z j) (x j) ≠ true := by
      by_contra hall; push Not at hall
      exact hp ((passOf_iff e z x).mpr hall)
    rcases hex with ⟨j, hj⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)).symm

def synthOf {r : ℕ} (menu : Finset (Finset (Fin r))) (u : ℕ) : Prop :=
  ∀ y : Fin r → Fin 16, ∃ c : Finset (Fin r) → (Fin r → Fin 16) → ℤ, ∀ x : Fin r → Fin 16,
    menu.sum (fun e => ((Finset.univ : Finset (Fin r → Fin 16)).filter
      (fun z => passOf e z x = true)).sum (c e)) =
    if x = y then (u : ℤ) else 0

def separatesOf {r : ℕ} (qs : Finset (Finset (Fin r) × (Fin r → Fin 16))) : Prop :=
  ∀ d : (Fin r → Fin 16) → Fin 11,
    (∀ q ∈ qs, (((Finset.univ : Finset (Fin r → Fin 16)).filter
      (fun x => passOf q.1 q.2 x = true)).sum (fun x => (d x).val)) % 11 = 0) →
    ∀ x, (d x).val = 0

lemma synth_all_one (r : ℕ) : synthOf (Finset.univ : Finset (Finset (Fin r))) 1 := by
  intro y
  let c : Finset (Fin r) → (Fin r → Fin 16) → ℤ := fun e z =>
    ∏ j : Fin r, if j ∈ e then c1_exact (xor16 (z j) (y j)) else c0_exact (xor16 (z j) (y j))
  refine ⟨c, fun x => ?_⟩
  have hinner : ∀ e : Finset (Fin r),
      ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun z => passOf e z x = true)).sum (c e) =
      ∏ j : Fin r, (Finset.univ : Finset (Fin 16)).sum (fun a =>
        if localPass (decide (j ∈ e)) a (x j) = true then
          (if j ∈ e then c1_exact (xor16 a (y j)) else c0_exact (xor16 a (y j)))
        else 0) := by
    intro e
    rw [Finset.sum_filter]
    have hprod : ∀ z : Fin r → Fin 16,
        (if passOf e z x = true then c e z else 0) =
        ∏ j : Fin r, (if localPass (decide (j ∈ e)) (z j) (x j) = true then
          (if j ∈ e then c1_exact (xor16 (z j) (y j)) else c0_exact (xor16 (z j) (y j)))
        else 0) := by
      intro z
      have h1 : (if passOf e z x = true then c e z else 0) =
          (if passOf e z x = true then (1 : ℤ) else 0) * c e z := by split_ifs <;> ring
      rw [h1, passOf_indicator]
      dsimp only [c]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => by split_ifs <;> ring
    calc (Finset.univ : Finset (Fin r → Fin 16)).sum
          (fun z => if passOf e z x = true then c e z else 0)
        = (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
            ∏ j : Fin r, (if localPass (decide (j ∈ e)) (z j) (x j) = true then
              (if j ∈ e then c1_exact (xor16 (z j) (y j)) else c0_exact (xor16 (z j) (y j)))
            else 0)) := Finset.sum_congr rfl fun z _ => hprod z
      _ = _ := (Fintype.prod_sum (fun j a =>
            if localPass (decide (j ∈ e)) a (x j) = true then
              (if j ∈ e then c1_exact (xor16 a (y j)) else c0_exact (xor16 a (y j)))
            else 0)).symm
  simp_rw [hinner]
  -- Biject Finset (Fin r) with (Fin r -> Bool) and apply Fintype.prod_sum
  let g : Fin r → Bool → ℤ := fun j b =>
    (Finset.univ : Finset (Fin 16)).sum (fun a =>
      if localPass b a (x j) = true then
        (if b then c1_exact (xor16 a (y j)) else c0_exact (xor16 a (y j)))
      else 0)
  have hsum_eq : (Finset.univ : Finset (Finset (Fin r))).sum (fun e =>
      ∏ j : Fin r, (Finset.univ : Finset (Fin 16)).sum (fun a =>
        if localPass (decide (j ∈ e)) a (x j) = true then
          (if j ∈ e then c1_exact (xor16 a (y j)) else c0_exact (xor16 a (y j)))
        else 0)) =
      (Finset.univ : Finset (Fin r → Bool)).sum (fun f => ∏ j : Fin r, g j (f j)) := by
    refine Finset.sum_bij (fun e _ j => decide (j ∈ e)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro e₁ _ e₂ _ h; ext j; simpa [decide_eq_decide] using congrFun h j
    · intro f _
      refine ⟨Finset.univ.filter (fun j => f j = true), Finset.mem_univ _, ?_⟩
      funext j; cases hv : f j <;> simp [hv]
    · intro e _
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only [g]
      by_cases hj : j ∈ e <;> simp [hj]
  rw [hsum_eq, ← Fintype.prod_sum g]
  have hlocal : ∀ j : Fin r, (Finset.univ : Finset Bool).sum (fun b => g j b) =
      if x j = y j then (1 : ℤ) else 0 := by
    intro j
    rw [Fintype.sum_bool]
    dsimp only [g]
    have h := local_synth_1 (y j) (x j)
    simpa [add_comm] using h
  simp_rw [hlocal]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun j _ => if_pos rfl
  · rw [if_neg hxy]
    have hex : ∃ j : Fin r, x j ≠ y j := by
      by_contra hall; push Not at hall; exact hxy (funext hall)
    rcases hex with ⟨j, hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

lemma synth_empty_of_dvd (r u : ℕ) (hdvd : 165 ^ r ∣ u) :
    synthOf ({(∅ : Finset (Fin r))} : Finset (Finset (Fin r))) u := by
  rcases hdvd with ⟨q, rfl⟩
  intro y
  let c : Finset (Fin r) → (Fin r → Fin 16) → ℤ := fun _ z =>
    (q : ℤ) * ∏ j : Fin r, c165 (xor16 (z j) (y j))
  refine ⟨c, fun x => ?_⟩
  rw [Finset.sum_singleton, Finset.sum_filter]
  have hpull : (Finset.univ : Finset (Fin r → Fin 16)).sum
      (fun z => if passOf (∅ : Finset (Fin r)) z x = true then c ∅ z else 0) =
      (q : ℤ) * (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
        ∏ j : Fin r, if localPass false (z j) (x j) = true then c165 (xor16 (z j) (y j)) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h1 : (if passOf (∅ : Finset (Fin r)) z x = true then c ∅ z else 0) =
        (q : ℤ) * ((if passOf (∅ : Finset (Fin r)) z x = true then (1 : ℤ) else 0) *
          ∏ j : Fin r, c165 (xor16 (z j) (y j))) := by
      dsimp only [c]; split_ifs <;> ring
    rw [h1, passOf_indicator, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun j _ => by simp
  rw [hpull, ← Fintype.prod_sum (fun j a =>
    if localPass false a (x j) = true then c165 (xor16 a (y j)) else 0)]
  simp_rw [local_synth_165]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hp : (∏ _j : Fin r, (165 : ℤ)) = (165 : ℤ) ^ r := by simp
    have h1 : (∏ j : Fin r, if x j = x j then (165 : ℤ) else 0) = (165 : ℤ) ^ r := by
      simp
    rw [h1]
    push_cast; ring
  · rw [if_neg hxy]
    have hex : ∃ j : Fin r, x j ≠ y j := by
      by_contra hall; push Not at hall; exact hxy (funext hall)
    rcases hex with ⟨j, hj⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj), mul_zero]

/-! ### Part C: Walsh character evaluations and lower bounds -/

lemma sum_pass_prod_chi {r : ℕ} (e : Finset (Fin r)) (z : Fin r → Fin 16) (t : Fin r → Fin 16) :
    ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf e z x = true)).sum
      (fun x => ∏ j : Fin r, chi16 (x j) (t j)) =
    ∏ j : Fin r, (Finset.univ : Finset (Fin 16)).sum (fun a =>
      if localPass (decide (j ∈ e)) (z j) a = true then chi16 a (t j) else 0) := by
  rw [Finset.sum_filter]
  have hprod : ∀ x : Fin r → Fin 16,
      (if passOf e z x = true then ∏ j : Fin r, chi16 (x j) (t j) else 0) =
      ∏ j : Fin r, if localPass (decide (j ∈ e)) (z j) (x j) = true then chi16 (x j) (t j) else 0 := by
    intro x
    have h1 : (if passOf e z x = true then ∏ j : Fin r, chi16 (x j) (t j) else 0) =
        (if passOf e z x = true then (1 : ℤ) else 0) * ∏ j : Fin r, chi16 (x j) (t j) := by
      split_ifs <;> ring
    rw [h1, passOf_indicator, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => by split_ifs <;> ring
  simp_rw [hprod]
  exact (Fintype.prod_sum (fun j a =>
    if localPass (decide (j ∈ e)) (z j) a = true then chi16 a (t j) else 0)).symm

lemma private_char_dvd_eleven {r : ℕ} (e₀ e : Finset (Fin r)) (hne : e ≠ e₀) (z : Fin r → Fin 16) :
    (11 : ℤ) ∣ ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf e z x = true)).sum
      (fun x => ∏ j : Fin r, chi16 (x j) (if j ∈ e₀ then 0 else 6)) := by
  rw [sum_pass_prod_chi]
  have hex : (∃ j : Fin r, j ∈ e₀ ∧ j ∉ e) ∨ (∃ j : Fin r, j ∈ e ∧ j ∉ e₀) := by
    by_contra hno
    push Not at hno
    apply hne
    ext j
    exact ⟨fun hje => hno.2 j hje, fun hj0 => hno.1 j hj0⟩
  rcases hex with ⟨j, hj0, hje⟩ | ⟨j, hje, hj0⟩
  · have hfac : (Finset.univ : Finset (Fin 16)).sum (fun a =>
        if localPass (decide (j ∈ e)) (z j) a = true then chi16 a (if j ∈ e₀ then 0 else 6) else 0) =
        11 * chi16 (z j) 0 := by
      simp only [hj0, ite_true, hje, decide_false]
      simpa using local_walsh_0 false (z j)
    have hdvd : (11 : ℤ) ∣ (Finset.univ : Finset (Fin 16)).sum (fun a =>
        if localPass (decide (j ∈ e)) (z j) a = true then chi16 a (if j ∈ e₀ then 0 else 6) else 0) := by
      rw [hfac]; exact dvd_mul_right 11 _
    exact dvd_trans hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  · have hfac : (Finset.univ : Finset (Fin 16)).sum (fun a =>
        if localPass (decide (j ∈ e)) (z j) a = true then chi16 a (if j ∈ e₀ then 0 else 6) else 0) = 0 := by
      simp only [hj0, ite_false, hje, decide_true]
      simpa using local_walsh_6 true (z j)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hfac]
    exact dvd_zero _

lemma synth_one_implies_univ {r : ℕ} (menu : Finset (Finset (Fin r))) (hs : synthOf menu 1) :
    menu = Finset.univ := by
  by_contra hne
  have hex : ∃ e₀ : Finset (Fin r), e₀ ∉ menu := by
    by_contra hall; push Not at hall
    apply hne; ext e; simp [hall e]
  rcases hex with ⟨e₀, he₀⟩
  let y0 : Fin r → Fin 16 := fun _ => 0
  obtain ⟨c, hc⟩ := hs y0
  let t : Fin r → Fin 16 := fun j => if j ∈ e₀ then 0 else 6
  let d : (Fin r → Fin 16) → ℤ := fun x => ∏ j : Fin r, chi16 (x j) (t j)
  have hdy0 : d y0 = 1 := Finset.prod_eq_one fun j _ => chi16_zero_left (t j)
  have hsum : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * (if x = y0 then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single y0]
    · simp [hdy0]
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (Finset.mem_univ y0) h
  have hrew : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * (if x = y0 then (1 : ℤ) else 0)) =
      menu.sum (fun e => (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
        c e z * ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf e z x = true)).sum d)) := by
    have h1 : ∀ x : Fin r → Fin 16, d x * (if x = y0 then (1 : ℤ) else 0) =
        menu.sum (fun e => (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
          if passOf e z x = true then d x * c e z else 0)) := by
      intro x
      have hx := hc x
      simp only [Nat.cast_one] at hx
      rw [← hx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
  have hdvd : (11 : ℤ) ∣ 1 := by
    rw [← hsum, hrew]
    apply Finset.dvd_sum
    intro e he
    apply Finset.dvd_sum
    intro z _
    have hene : e ≠ e₀ := fun h => he₀ (h ▸ he)
    exact dvd_mul_of_dvd_right (private_char_dvd_eleven e₀ e hene z) _
  omega

lemma synth_empty_implies_dvd (r u : ℕ) (hs : synthOf ({(∅ : Finset (Fin r))} : Finset (Finset (Fin r))) u) :
    165 ^ r ∣ u := by
  let y0 : Fin r → Fin 16 := fun _ => 0
  obtain ⟨c, hc⟩ := hs y0
  have hdvd_ev : ∀ (t0 : Fin 16) (ev : ℤ),
      (∀ z : Fin 16, (Finset.univ : Finset (Fin 16)).sum (fun x =>
        if localPass false z x = true then chi16 x t0 else 0) = ev * chi16 z t0) →
      ev.natAbs ^ r ∣ u := by
    intro t0 ev hev
    let d : (Fin r → Fin 16) → ℤ := fun x => ∏ j : Fin r, chi16 (x j) t0
    have hdy0 : d y0 = 1 := Finset.prod_eq_one fun j _ => chi16_zero_left t0
    have hsum : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * (if x = y0 then (u : ℤ) else 0)) = (u : ℤ) := by
      rw [Finset.sum_eq_single y0]
      · simp [hdy0]
      · intro x _ hx; simp [hx]
      · intro h; exact absurd (Finset.mem_univ y0) h
    have hrew : (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => d x * (if x = y0 then (u : ℤ) else 0)) =
        (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
          c ∅ z * ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf (∅ : Finset (Fin r)) z x = true)).sum d) := by
      have h1 : ∀ x : Fin r → Fin 16, d x * (if x = y0 then (u : ℤ) else 0) =
          (Finset.univ : Finset (Fin r → Fin 16)).sum (fun z =>
            if passOf (∅ : Finset (Fin r)) z x = true then d x * c ∅ z else 0) := by
        intro x
        have hx := hc x
        rw [Finset.sum_singleton, Finset.sum_filter] at hx
        rw [← hx, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
    have hdvdZ : ev ^ r ∣ (u : ℤ) := by
      rw [← hsum, hrew]
      apply Finset.dvd_sum
      intro z _
      have heval : ((Finset.univ : Finset (Fin r → Fin 16)).filter
          (fun x => passOf (∅ : Finset (Fin r)) z x = true)).sum d =
          ev ^ r * ∏ j : Fin r, chi16 (z j) t0 := by
        dsimp only [d]
        rw [sum_pass_prod_chi]
        have hterm : ∀ j : Fin r, (Finset.univ : Finset (Fin 16)).sum (fun a =>
            if localPass (decide (j ∈ (∅ : Finset (Fin r)))) (z j) a = true then chi16 a t0 else 0) =
            ev * chi16 (z j) t0 := fun j => by simpa using hev (z j)
        simp_rw [hterm, Finset.prod_mul_distrib]
        simp
      rw [heval]
      exact ⟨c ∅ z * ∏ j : Fin r, chi16 (z j) t0, by ring⟩
    rcases hdvdZ with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    have hnat : ((u : ℤ)).natAbs = (ev ^ r * k).natAbs := congrArg Int.natAbs hk
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hnat
  have h11 : 11 ^ r ∣ u := hdvd_ev 0 11 (fun z => by simpa using local_walsh_0 false z)
  have h5 : 5 ^ r ∣ u := hdvd_ev 1 (-5) local_walsh_1
  have h3 : 3 ^ r ∣ u := hdvd_ev 2 (-3) local_walsh_2
  have hcop11_5 : Nat.Coprime (11 ^ r) (5 ^ r) :=
    (Nat.Coprime.pow_left r (Nat.Coprime.pow_right r (by decide)))
  have h55 : 11 ^ r * 5 ^ r ∣ u := hcop11_5.mul_dvd_of_dvd_of_dvd h11 h5
  have hcop55_3 : Nat.Coprime (11 ^ r * 5 ^ r) (3 ^ r) :=
    Nat.Coprime.mul_left
      (Nat.Coprime.pow_left r (Nat.Coprime.pow_right r (by decide)))
      (Nat.Coprime.pow_left r (Nat.Coprime.pow_right r (by decide)))
  have h165 : (11 ^ r * 5 ^ r) * 3 ^ r ∣ u := hcop55_3.mul_dvd_of_dvd_of_dvd h55 h3
  have heq165 : (11 ^ r * 5 ^ r) * 3 ^ r = 165 ^ r := by
    rw [← mul_pow, ← mul_pow]
    rfl
  rwa [heq165] at h165

/-! ### Part D: Part 3 (mod-11 separating query sets and dimension 16^r) -/

lemma separates_zmod_iff {r : ℕ} (qs : Finset (Finset (Fin r) × (Fin r → Fin 16))) :
    separatesOf qs ↔
    ∀ d : (Fin r → Fin 16) → ZMod 11,
      (∀ q ∈ qs, ((Finset.univ : Finset (Fin r → Fin 16)).filter
        (fun x => passOf q.1 q.2 x = true)).sum d = 0) →
      d = 0 := by
  constructor
  · intro hsep d hd
    let dFin : (Fin r → Fin 16) → Fin 11 := fun x => ⟨(d x).val, ZMod.val_lt (d x)⟩
    have h0 := hsep dFin (fun q hq => by
      have hq0 := hd q hq
      have hcast : ((((Finset.univ : Finset (Fin r → Fin 16)).filter
          (fun x => passOf q.1 q.2 x = true)).sum (fun x => (dFin x).val) : ℕ) : ZMod 11) = 0 := by
        rw [Nat.cast_sum]
        simpa [dFin, ZMod.natCast_zmod_val] using hq0
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hcast))
    funext x
    have hx := h0 x
    dsimp only [dFin] at hx
    exact (ZMod.val_eq_zero (d x)).mp hx
  · intro hsep d hd x
    let dZ : (Fin r → Fin 16) → ZMod 11 := fun y => ((d y).val : ZMod 11)
    have h0 := hsep dZ (fun q hq => by
      have hmod := hd q hq
      dsimp only [dZ]
      rw [← Nat.cast_sum, ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero hmod)
    have hx := congrFun h0 x
    dsimp only [dZ] at hx
    have hlt := (d x).isLt
    have hval := ZMod.val_natCast_of_lt (n := 11) hlt
    rw [hx, Pi.zero_apply, ZMod.val_zero] at hval
    exact hval.symm

lemma part3_equiv (r : ℕ) (menu : Finset (Finset (Fin r))) (b : ℕ) :
    (∃ qs : Finset (Finset (Fin r) × (Fin r → Fin 16)),
      (∀ q ∈ qs, q.1 ∈ menu) ∧ qs.card ≤ b ∧ separatesOf qs) ↔
    menu = Finset.univ ∧ 16 ^ r ≤ b := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  constructor
  · rintro ⟨qs, hqmenu, hqb, hsep⟩
    have hsepZ := (separates_zmod_iff qs).mp hsep
    have hmenu : menu = Finset.univ := by
      by_contra hne
      have hex : ∃ e₀ : Finset (Fin r), e₀ ∉ menu := by
        by_contra hall; push Not at hall
        apply hne; ext e; simp [hall e]
      rcases hex with ⟨e₀, he₀⟩
      let d : (Fin r → Fin 16) → ZMod 11 := fun x =>
        ((∏ j : Fin r, chi16 (x j) (if j ∈ e₀ then 0 else 6) : ℤ) : ZMod 11)
      have hker : ∀ q ∈ qs, ((Finset.univ : Finset (Fin r → Fin 16)).filter
          (fun x => passOf q.1 q.2 x = true)).sum d = 0 := by
        intro q hq
        have hne_q : q.1 ≠ e₀ := fun h => he₀ (h ▸ hqmenu q hq)
        have hdvd := private_char_dvd_eleven e₀ q.1 hne_q q.2
        dsimp only [d]
        rw [← Int.cast_sum]
        rcases hdvd with ⟨k, hk⟩
        rw [hk]
        push_cast
        have h11 : (11 : ZMod 11) = 0 := by simpa using (ZMod.natCast_self 11)
        rw [h11, zero_mul]
      have hd0 := hsepZ d hker
      have hy0 := congrFun hd0 (fun _ => 0)
      dsimp only [d] at hy0
      have hprod1 : (∏ j : Fin r, chi16 (0 : Fin 16) (if j ∈ e₀ then 0 else 6)) = 1 :=
        Finset.prod_eq_one fun j _ => chi16_zero_left _
      rw [hprod1, Int.cast_one] at hy0
      exact one_ne_zero hy0
    refine ⟨hmenu, ?_⟩
    -- Injectivity of evaluation map gives 11^(16^r) <= 11^qs.card -> 16^r <= qs.card <= b
    let evalMap : ((Fin r → Fin 16) → ZMod 11) → ({q // q ∈ qs} → ZMod 11) := fun d q =>
      ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passOf q.1.1 q.1.2 x = true)).sum d
    have hinj : Function.Injective evalMap := by
      intro d₁ d₂ hEq
      have hdiff : d₁ - d₂ = 0 := hsepZ (d₁ - d₂) fun q hq => by
        have h := congrFun hEq ⟨q, hq⟩
        dsimp only [evalMap] at h
        simp [Pi.sub_apply, Finset.sum_sub_distrib, h]
      exact sub_eq_zero.mp hdiff
    have hcard_le := Fintype.card_le_of_injective evalMap hinj
    have hcard_dom : Fintype.card ((Fin r → Fin 16) → ZMod 11) = 11 ^ (16 ^ r) := by
      simp [Fintype.card_fun, Fintype.card_fin]
    have hcard_cod : Fintype.card ({q // q ∈ qs} → ZMod 11) = 11 ^ qs.card := by
      simp [Fintype.card_fun]
    rw [hcard_dom, hcard_cod] at hcard_le
    have hle : 16 ^ r ≤ qs.card := (Nat.pow_le_pow_iff_right (by omega : 1 < 11)).mp hcard_le
    omega
  · rintro ⟨rfl, hb⟩
    -- Rows of Kind x Word span all of (Word -> ZMod 11) because synth_all_one holds
    let row : (Finset (Fin r) × (Fin r → Fin 16)) → ((Fin r → Fin 16) → ZMod 11) := fun q x =>
      if passOf q.1 q.2 x = true then 1 else 0
    have hspan_all : Submodule.span (ZMod 11) (row '' ((Finset.univ : Finset (Finset (Fin r) × (Fin r → Fin 16))) : Set _)) = ⊤ := by
      rw [eq_top_iff]
      intro f _
      have hf_eq : f = (Finset.univ : Finset (Fin r → Fin 16)).sum (fun y => f y • Pi.single y (1 : ZMod 11)) := by
        funext x
        rw [Finset.sum_apply, Finset.sum_eq_single x]
        · simp
        · intro y _ hy; simp [Pi.single_eq_of_ne (Ne.symm hy)]
        · intro h; exact absurd (Finset.mem_univ x) h
      rw [hf_eq]
      apply Submodule.sum_mem
      intro y _
      apply Submodule.smul_mem
      obtain ⟨c, hc⟩ := synth_all_one r y
      have hsingle : Pi.single y (1 : ZMod 11) =
          (Finset.univ : Finset (Finset (Fin r) × (Fin r → Fin 16))).sum
            (fun q => (c q.1 q.2 : ZMod 11) • row q) := by
        funext x
        rw [Finset.sum_apply]
        have hx := hc x
        have hcast : (((Finset.univ : Finset (Finset (Fin r))).sum (fun e =>
            ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun z => passOf e z x = true)).sum (c e)) : ℤ) : ZMod 11) =
            if x = y then 1 else 0 := by
          rw [hx]; split_ifs <;> simp
        have hsum_prod : (Finset.univ : Finset (Finset (Fin r) × (Fin r → Fin 16))).sum
            (fun q => ((c q.1 q.2 : ZMod 11) • row q) x) =
            (((Finset.univ : Finset (Finset (Fin r))).sum (fun e =>
              ((Finset.univ : Finset (Fin r → Fin 16)).filter (fun z => passOf e z x = true)).sum (c e)) : ℤ) : ZMod 11) := by
          rw [Int.cast_sum, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_filter, Int.cast_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          dsimp only [row, Pi.smul_apply, smul_eq_mul]
          split_ifs <;> simp
        rw [hsum_prod, hcast]
        by_cases hxy : x = y
        · subst hxy; simp
        · simp [Pi.single_eq_of_ne hxy, hxy]
      rw [hsingle]
      apply Submodule.sum_mem
      intro q _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨q, Finset.mem_univ q, rfl⟩
    -- Pick a minimum-cardinality spanning subset qs via Nat.find
    let P : ℕ → Prop := fun n =>
      ∃ qs : Finset (Finset (Fin r) × (Fin r → Fin 16)),
        qs.card = n ∧
        Submodule.span (ZMod 11) (row '' (qs : Set (Finset (Fin r) × (Fin r → Fin 16)))) = ⊤
    have hexP : ∃ n, P n :=
      ⟨(Finset.univ : Finset (Finset (Fin r) × (Fin r → Fin 16))).card, Finset.univ, rfl, hspan_all⟩
    obtain ⟨qs, hqs_card, hqs_span⟩ := Nat.find_spec hexP
    -- Prove linear map (qs -> ZMod 11) -> (Word -> ZMod 11) is injective by minimality
    let linComb : ({q // q ∈ qs} → ZMod 11) → ((Fin r → Fin 16) → ZMod 11) := fun a =>
      (Finset.univ : Finset {q // q ∈ qs}).sum (fun q => a q • row q.1)
    have hlin_inj : Function.Injective linComb := by
      intro a₁ a₂ hEq
      have hzero : linComb (a₁ - a₂) = 0 := by
        dsimp only [linComb] at hEq ⊢
        have : (Finset.univ : Finset {q // q ∈ qs}).sum (fun q => (a₁ - a₂) q • row q.1) =
            (Finset.univ : Finset {q // q ∈ qs}).sum (fun q => a₁ q • row q.1) -
            (Finset.univ : Finset {q // q ∈ qs}).sum (fun q => a₂ q • row q.1) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun q _ => by rw [Pi.sub_apply, sub_smul]
        rw [this, hEq, sub_self]
      by_contra hne
      have hex : ∃ q₀ : {q // q ∈ qs}, (a₁ - a₂) q₀ ≠ 0 := by
        by_contra hall; push Not at hall
        apply hne; funext q; exact sub_eq_zero.mp (hall q)
      rcases hex with ⟨q₀, hq₀_nz⟩
      -- row q₀.1 is in span of qs.erase q₀.1, contradicting minimality!
      have hrow_in : row q₀.1 ∈ Submodule.span (ZMod 11) (row '' ((qs.erase q₀.1 : Finset _) : Set _)) := by
        let a := a₁ - a₂
        have hsplit : a q₀ • row q₀.1 +
            ((Finset.univ : Finset {q // q ∈ qs}).erase q₀).sum (fun q => a q • row q.1) = 0 :=
          (Finset.add_sum_erase (Finset.univ : Finset {q // q ∈ qs}) (fun q => a q • row q.1) (Finset.mem_univ q₀)).trans hzero
        have hrow_eq : row q₀.1 =
            (-(a q₀)⁻¹) • ((Finset.univ : Finset {q // q ∈ qs}).erase q₀).sum (fun q => a q • row q.1) := by
          have h1 : a q₀ • row q₀.1 = -((Finset.univ : Finset {q // q ∈ qs}).erase q₀).sum (fun q => a q • row q.1) :=
            eq_neg_of_add_eq_zero_left hsplit
          calc row q₀.1 = (a q₀)⁻¹ • (a q₀ • row q₀.1) := by rw [smul_smul, inv_mul_cancel₀ hq₀_nz, one_smul]
            _ = (a q₀)⁻¹ • (-((Finset.univ : Finset {q // q ∈ qs}).erase q₀).sum (fun q => a q • row q.1)) := by rw [h1]
            _ = (-(a q₀)⁻¹) • _ := by rw [smul_neg, neg_smul]
        rw [hrow_eq]
        apply Submodule.smul_mem
        apply Submodule.sum_mem
        intro q hq
        apply Submodule.smul_mem
        have hqne : q.1 ≠ q₀.1 := fun h => (Finset.mem_erase.mp hq).1 (Subtype.ext h)
        exact Submodule.subset_span ⟨q.1, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hqne, q.2⟩), rfl⟩
      have hspan_er : Submodule.span (ZMod 11) (row '' ((qs.erase q₀.1 : Finset _) : Set _)) = ⊤ := by
        rw [← hqs_span]
        apply le_antisymm
        · apply Submodule.span_mono
          rintro _ ⟨q, hq, rfl⟩
          exact ⟨q, Finset.mem_coe.mpr (Finset.erase_subset _ _ (Finset.mem_coe.mp hq)), rfl⟩
        · rw [Submodule.span_le]
          rintro _ ⟨q, hq, rfl⟩
          by_cases hqq : q = q₀.1
          · subst hqq; exact hrow_in
          · exact Submodule.subset_span ⟨q, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hqq, Finset.mem_coe.mp hq⟩), rfl⟩
      have hcard_er : (qs.erase q₀.1).card = qs.card - 1 := Finset.card_erase_of_mem q₀.2
      have hpos : 0 < qs.card := Finset.card_pos.mpr ⟨q₀.1, q₀.2⟩
      have hlt : qs.card - 1 < Nat.find hexP := by omega
      exact Nat.find_min hexP hlt ⟨qs.erase q₀.1, hcard_er, hspan_er⟩
    have hcard_le := Fintype.card_le_of_injective linComb hlin_inj
    have hcard_dom : Fintype.card ({q // q ∈ qs} → ZMod 11) = 11 ^ qs.card := by
      simp [Fintype.card_fun]
    have hcard_cod : Fintype.card ((Fin r → Fin 16) → ZMod 11) = 11 ^ (16 ^ r) := by
      simp [Fintype.card_fun, Fintype.card_fin]
    rw [hcard_dom, hcard_cod] at hcard_le
    have hqs_le : qs.card ≤ 16 ^ r := (Nat.pow_le_pow_iff_right (by omega : 1 < 11)).mp hcard_le
    refine ⟨qs, fun _ _ => Finset.mem_univ _, le_trans hqs_le hb, ?_⟩
    rw [separates_zmod_iff]
    intro d hd
    -- Define the orthogonal subspace {f | sum_x f x * d x = 0}, show it contains row '' qs, hence = ⊤
    let orth : Submodule (ZMod 11) ((Fin r → Fin 16) → ZMod 11) :=
      { carrier := {f | (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => f x * d x) = 0}, add_mem' := fun {f g} hf hg => by
          change (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => (f x + g x) * d x) = 0
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, hf, hg, add_zero]
        zero_mem' := by change (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => 0 * d x) = 0; simp
        smul_mem' := fun c {f} hf => by
          change (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => (c * f x) * d x) = 0
          simp_rw [mul_assoc, ← Finset.mul_sum]
          rw [hf, mul_zero] }
    have horth_top : (⊤ : Submodule (ZMod 11) ((Fin r → Fin 16) → ZMod 11)) ≤ orth := by
      rw [← hqs_span, Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      change (Finset.univ : Finset (Fin r → Fin 16)).sum (fun x => row q x * d x) = 0
      have hq' := hd q (Finset.mem_coe.mp hq)
      rw [Finset.sum_filter] at hq'
      convert hq' using 1
      refine Finset.sum_congr rfl fun x _ => by dsimp only [row]; split_ifs <;> simp
    funext y
    have hmem : (Pi.single y (1 : ZMod 11) : (Fin r → Fin 16) → ZMod 11) ∈ orth := horth_top trivial
    change (Finset.univ : Finset (Fin r → Fin 16)).sum
      (fun x => (Pi.single y (1 : ZMod 11) : (Fin r → Fin 16) → ZMod 11) x * d x) = 0 at hmem
    rw [Finset.sum_eq_single y] at hmem
    · simpa using hmem
    · intro x _ hxy; simp [Pi.single_eq_of_ne hxy]
    · intro h; exact absurd (Finset.mem_univ y) h

theorem main :
    ∀ r : Nat,
      let Kind := Finset (Fin r)
      let Word := Fin r → Fin 16
      let kinds := (Finset.univ : Finset Kind)
      let cube := (Finset.univ : Finset Word)
      let sites := (Finset.univ : Finset (Fin r))
      let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
        let w := (z j).val ^^^ (x j).val
        (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
      let synth := fun (menu : Finset Kind) (u : Nat) =>
        ∀ y : Word, ∃ c : Kind → Word → Int, ∀ x : Word,
          menu.sum (fun e => (cube.filter (fun z => pass e z x)).sum (c e)) =
            if x = y then (u : Int) else 0
      let separates := fun (qs : Finset (Kind × Word)) =>
        ∀ d : Word → Fin 11, (∀ q ∈ qs, ((cube.filter (fun x => pass q.1 q.2 x)).sum
          (fun x => (d x).val)) % 11 = 0) → ∀ x, (d x).val = 0
      (∀ menu : Finset Kind, synth menu 1 ↔ menu = kinds) ∧
      (∀ u : Nat, synth ({(∅ : Kind)} : Finset Kind) u ↔ 165 ^ r ∣ u) ∧
      (∀ (menu : Finset Kind) (b : Nat),
        (∃ qs : Finset (Kind × Word), (∀ q ∈ qs, q.1 ∈ menu) ∧ qs.card ≤ b ∧ separates qs) ↔
          menu = kinds ∧ 16 ^ r ≤ b) := by
  intro r
  dsimp only
  refine ⟨fun menu => ⟨synth_one_implies_univ menu, fun h => h ▸ synth_all_one r⟩,
          fun u => ⟨synth_empty_implies_dvd r u, synth_empty_of_dvd r u⟩,
          fun menu b => part3_equiv r menu b⟩

end PEqualNP.Outside.L_lib_1155_aux

theorem PEqualNP.Outside.L_lib_1155 :
∀ r : Nat,
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let synth := fun (menu : Finset Kind) (u : Nat) =>
    ∀ y : Word, ∃ c : Kind → Word → Int, ∀ x : Word,
      menu.sum (fun e => (cube.filter (fun z => pass e z x)).sum (c e)) =
        if x = y then (u : Int) else 0
  let separates := fun (qs : Finset (Kind × Word)) =>
    ∀ d : Word → Fin 11, (∀ q ∈ qs, ((cube.filter (fun x => pass q.1 q.2 x)).sum
      (fun x => (d x).val)) % 11 = 0) → ∀ x, (d x).val = 0
  (∀ menu : Finset Kind, synth menu 1 ↔ menu = kinds) ∧
  (∀ u : Nat, synth ({(∅ : Kind)} : Finset Kind) u ↔ 165 ^ r ∣ u) ∧
  (∀ (menu : Finset Kind) (b : Nat),
    (∃ qs : Finset (Kind × Word), (∀ q ∈ qs, q.1 ∈ menu) ∧ qs.card ≤ b ∧ separates qs) ↔
      menu = kinds ∧ 16 ^ r ≤ b) :=
  PEqualNP.Outside.L_lib_1155_aux.main
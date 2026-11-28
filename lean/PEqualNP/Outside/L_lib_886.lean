import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_886

open scoped BigOperators

abbrev F2 := ZMod 2

lemma zmod2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma zmod2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_ne_zero_iff (x : F2) : x ≠ 0 ↔ x = 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · simp
  · simp

lemma fin4_cases (b : Fin 4) : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
  fin_cases b <;> simp

-- Cyclic shift on Fin (6 * t)
def nextIdx (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) : Fin (6 * t) :=
  ⟨(i.val + 1) % (6 * t), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 5) hpos)⟩

def shiftIdx (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (d : ℕ) : Fin (6 * t) :=
  ⟨(i.val + d) % (6 * t), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 5) hpos)⟩

def prevIdx (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) : Fin (6 * t) :=
  ⟨(i.val + (6 * t - 1)) % (6 * t), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 5) hpos)⟩

lemma shiftIdx_zero (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    shiftIdx t hpos i 0 = i := by
  apply Fin.ext
  simp [shiftIdx, Nat.mod_eq_of_lt i.isLt]

lemma shiftIdx_one (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    shiftIdx t hpos i 1 = nextIdx t hpos i := rfl

lemma shiftIdx_add (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (a b : ℕ) :
    shiftIdx t hpos (shiftIdx t hpos i a) b = shiftIdx t hpos i (a + b) := by
  apply Fin.ext
  dsimp [shiftIdx]
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma nextIdx_prevIdx (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    nextIdx t hpos (prevIdx t hpos i) = i := by
  apply Fin.ext
  dsimp [nextIdx, prevIdx]
  rw [Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ 6 * t)]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma prevIdx_nextIdx (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    prevIdx t hpos (nextIdx t hpos i) = i := by
  apply Fin.ext
  dsimp [nextIdx, prevIdx]
  rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_sub_cancel' (by omega : 1 ≤ 6 * t)]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma nextIdx_inj (t : ℕ) (hpos : 0 < t) : Function.Injective (nextIdx t hpos) := by
  intro a b hab
  have := congrArg (prevIdx t hpos) hab
  rwa [prevIdx_nextIdx, prevIdx_nextIdx] at this

def nextEquiv (t : ℕ) (hpos : 0 < t) : Fin (6 * t) ≃ Fin (6 * t) :=
  { toFun := nextIdx t hpos
    invFun := prevIdx t hpos
    left_inv := prevIdx_nextIdx t hpos
    right_inv := nextIdx_prevIdx t hpos }

lemma shiftIdx_inj_range (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t))
    {a b : ℕ} (ha : a < 6 * t) (hb : b < 6 * t)
    (heq : shiftIdx t hpos u a = shiftIdx t hpos u b) : a = b := by
  have hv : (u.val + a) % (6 * t) = (u.val + b) % (6 * t) := congrArg Fin.val heq
  have hu : u.val < 6 * t := u.isLt
  have hmod : ∀ x < 6 * t, (u.val + x) % (6 * t) =
      if u.val + x < 6 * t then u.val + x else u.val + x - 6 * t := by
    intro x hx
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod a ha, hmod b hb] at hv
  split_ifs at hv <;> omega

lemma nextIdx_mod2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    (nextIdx t hpos i).val % 2 = 1 - i.val % 2 := by
  dsimp [nextIdx]
  have hi := i.isLt
  by_cases hlt : i.val + 1 < 6 * t
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · have heq : i.val + 1 = 6 * t := by omega
    rw [heq, Nat.mod_self]; omega

lemma shiftIdx_mod2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (d : ℕ) :
    (shiftIdx t hpos i d).val % 2 = (i.val + d) % 2 := by
  dsimp [shiftIdx]
  have h2 : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
  exact Nat.mod_mod_of_dvd (i.val + d) h2

lemma shiftIdx_two_div2_mod3 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    (shiftIdx t hpos i 2).val / 2 % 3 = (i.val / 2 + 1) % 3 := by
  dsimp [shiftIdx]
  have hi := i.isLt
  by_cases hlt : i.val + 2 < 6 * t
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · have hmod : (i.val + 2) % (6 * t) = i.val + 2 - 6 * t := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have hdiv : (i.val + 2 - 6 * t) / 2 = i.val / 2 + 1 - 3 * t := by omega
    rw [hdiv]
    have : 3 * t ≤ i.val / 2 + 1 := by omega
    omega

-- Parity-check function h
def hFn (t : ℕ) (i : Fin (6 * t)) (b : Fin 4) : F2 :=
  if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
  then (1 : F2) else 0

def Hmap (t : ℕ) : (Fin (6 * t) → F2) →ₗ[F2] (Fin 4 → F2) :=
  { toFun := fun x b => ∑ i : Fin (6 * t), hFn t i b * x i
    map_add' := fun x y => by
      ext b; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := fun c x => by
      ext b
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring) }

lemma Hmap_single (t : ℕ) (i : Fin (6 * t)) (b : Fin 4) :
    Hmap t (Pi.single i (1 : F2)) b = hFn t i b := by
  change ∑ j : Fin (6 * t), hFn t j b * (Pi.single i (1 : F2) : Fin (6 * t) → F2) j = hFn t i b
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Pi.single_eq_of_ne hji]
  · intro hi; exact False.elim (hi (Finset.mem_univ i))

lemma hFn_sum_triple (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (b : Fin 4) :
    hFn t i b + hFn t (shiftIdx t hpos i 2) b + hFn t (shiftIdx t hpos i 4) b = 0 := by
  have hm2_2 : (shiftIdx t hpos i 2).val % 2 = i.val % 2 := by
    rw [shiftIdx_mod2]; omega
  have hm2_4 : (shiftIdx t hpos i 4).val % 2 = i.val % 2 := by
    rw [shiftIdx_mod2]; omega
  have hd2 : (shiftIdx t hpos i 2).val / 2 % 3 = (i.val / 2 + 1) % 3 :=
    shiftIdx_two_div2_mod3 t hpos i
  have hd4 : (shiftIdx t hpos i 4).val / 2 % 3 = (i.val / 2 + 2) % 3 := by
    have h4 : shiftIdx t hpos i 4 = shiftIdx t hpos (shiftIdx t hpos i 2) 2 := by
      rw [shiftIdx_add]
    rw [h4, shiftIdx_two_div2_mod3, Nat.add_mod, hd2]
    omega
  unfold hFn
  rw [hm2_2, hm2_4, hd2, hd4]
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  have hp : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  fin_cases b <;> rcases hp with hp | hp <;> rcases hr with hr | hr | hr <;>
    simp [hp, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3),
      (by omega : (i.val / 2 + 2) % 3 = (i.val / 2 % 3 + 2) % 3)] <;>
    exact zmod2_add_self 1

lemma hFn_other_lane (t : ℕ) (i : Fin (6 * t)) (b : Fin 4)
    (hne : i.val % 2 ≠ b.val / 2) : hFn t i b = 0 := by
  simp [hFn, hne]

-- Even-lane / odd-lane 2-bit syndromes are nonzero and consecutive ones are linearly independent
lemma hFn_single_ne_zero (t : ℕ) (i : Fin (6 * t)) :
    (i.val % 2 = 0 → hFn t i 0 ≠ 0 ∨ hFn t i 1 ≠ 0) ∧
    (i.val % 2 = 1 → hFn t i 2 ≠ 0 ∨ hFn t i 3 ≠ 0) := by
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  constructor
  · intro hp
    rcases hr with hr | hr | hr
    · left; simp [hFn, hp, hr]
    · right; simp [hFn, hp, hr]
    · left; simp [hFn, hp, hr]
  · intro hp
    rcases hr with hr | hr | hr
    · left; simp [hFn, hp, hr]
    · right; simp [hFn, hp, hr]
    · left; simp [hFn, hp, hr]

lemma hFn_pair_indep_even (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (hi : i.val % 2 = 0)
    (c0 c1 : F2)
    (h0 : hFn t i 0 * c0 + hFn t (shiftIdx t hpos i 2) 0 * c1 = 0)
    (h1 : hFn t i 1 * c0 + hFn t (shiftIdx t hpos i 2) 1 * c1 = 0) :
    c0 = 0 ∧ c1 = 0 := by
  have hi2 : (shiftIdx t hpos i 2).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  have hd2 : (shiftIdx t hpos i 2).val / 2 % 3 = (i.val / 2 + 1) % 3 :=
    shiftIdx_two_div2_mod3 t hpos i
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rcases zmod2_eq_zero_or_one c0 with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one c1 with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso; rcases hr with hr | hr | hr <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)] at h0 h1
  · exfalso; rcases hr with hr | hr | hr <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)] at h0 h1
  · exfalso; rcases hr with hr | hr | hr <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3),
        zmod2_add_self] at h0 h1

lemma hFn_pair_indep_odd (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (hi : i.val % 2 = 1)
    (c0 c1 : F2)
    (h2 : hFn t i 2 * c0 + hFn t (shiftIdx t hpos i 2) 2 * c1 = 0)
    (h3 : hFn t i 3 * c0 + hFn t (shiftIdx t hpos i 2) 3 * c1 = 0) :
    c0 = 0 ∧ c1 = 0 := by
  have hi2 : (shiftIdx t hpos i 2).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  have hd2 : (shiftIdx t hpos i 2).val / 2 % 3 = (i.val / 2 + 1) % 3 :=
    shiftIdx_two_div2_mod3 t hpos i
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rcases zmod2_eq_zero_or_one c0 with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one c1 with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso; rcases hr with hr | hr | hr <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)] at h2 h3
  · exfalso; rcases hr with hr | hr | hr <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)] at h2 h3
  · exfalso; rcases hr with hr | hr | hr <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3),
        zmod2_add_self] at h2 h3

lemma hFn_pair_span_even (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (hi : i.val % 2 = 0)
    (y0 y1 : F2) :
    ∃ c0 c1 : F2,
      hFn t i 0 * c0 + hFn t (shiftIdx t hpos i 2) 0 * c1 = y0 ∧
      hFn t i 1 * c0 + hFn t (shiftIdx t hpos i 2) 1 * c1 = y1 := by
  have hi2 : (shiftIdx t hpos i 2).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  have hd2 : (shiftIdx t hpos i 2).val / 2 % 3 = (i.val / 2 + 1) % 3 :=
    shiftIdx_two_div2_mod3 t hpos i
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · refine ⟨y0, y1, ?_, ?_⟩ <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)]
  · refine ⟨y0 + y1, y0, ?_, ?_⟩ <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)]
    calc y0 + y1 + y0 = y1 + (y0 + y0) := by ring
      _ = y1 := by rw [zmod2_add_self, add_zero]
  · refine ⟨y1, y0 + y1, ?_, ?_⟩ <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)]
    calc y1 + (y0 + y1) = y0 + (y1 + y1) := by ring
      _ = y0 := by rw [zmod2_add_self, add_zero]

lemma hFn_pair_span_odd (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) (hi : i.val % 2 = 1)
    (y2 y3 : F2) :
    ∃ c0 c1 : F2,
      hFn t i 2 * c0 + hFn t (shiftIdx t hpos i 2) 2 * c1 = y2 ∧
      hFn t i 3 * c0 + hFn t (shiftIdx t hpos i 2) 3 * c1 = y3 := by
  have hi2 : (shiftIdx t hpos i 2).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  have hd2 : (shiftIdx t hpos i 2).val / 2 % 3 = (i.val / 2 + 1) % 3 :=
    shiftIdx_two_div2_mod3 t hpos i
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · refine ⟨y2, y3, ?_, ?_⟩ <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)]
  · refine ⟨y2 + y3, y2, ?_, ?_⟩ <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)]
    calc y2 + y3 + y2 = y3 + (y2 + y2) := by ring
      _ = y3 := by rw [zmod2_add_self, add_zero]
  · refine ⟨y3, y2 + y3, ?_, ?_⟩ <;>
      simp [hFn, hi, hi2, hd2, hr, (by omega : (i.val / 2 + 1) % 3 = (i.val / 2 % 3 + 1) % 3)]
    calc y3 + (y2 + y3) = y2 + (y3 + y3) := by ring
      _ = y2 := by rw [zmod2_add_self, add_zero]

-- Stage 1: Vset S and GoodMax S
def goodP (t : ℕ) (hpos : 0 < t) (U : Submodule F2 (Fin (6 * t) → F2)) : Prop :=
  (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hFn t i b * x i) = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextIdx t hpos i) = x (nextIdx t hpos i) * y i)

open Classical in
noncomputable def suppU (t : ℕ) (U : Submodule F2 (Fin (6 * t) → F2)) : Finset (Fin (6 * t)) :=
  Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

def sitesS (t : ℕ) (S : Finset (Fin (6 * t))) (p : ℕ) : ℕ :=
  (S.filter (fun i => i.val % 2 = p)).card

def runsS (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) : ℕ :=
  (S.filter (fun i => nextIdx t hpos i ∉ S)).card

def Vset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) : Submodule F2 (Fin (6 * t) → F2) :=
  { carrier := {x | (∀ i, i ∉ S → x i = 0) ∧
      (∀ i, i ∈ S → nextIdx t hpos i ∈ S → x i = x (nextIdx t hpos i))}
    zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, add_mem' := fun hx hy =>
      ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
       fun i hi hni => by simp [hx.2 i hi hni, hy.2 i hi hni]⟩
    smul_mem' := fun c _ hx =>
      ⟨fun i hi => by simp [hx.1 i hi],
       fun i hi hni => by simp [hx.2 i hi hni]⟩ }

def GoodMax (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    Submodule F2 (Fin (6 * t) → F2) :=
  Vset t hpos S ⊓ LinearMap.ker (Hmap t)

lemma good_le_GoodMax (t : ℕ) (hpos : 0 < t) {U : Submodule F2 (Fin (6 * t) → F2)}
    (hg : goodP t hpos U) :
    U ≤ GoodMax t hpos (suppU t U) := by
  intro x hx
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    by_contra hne
    apply hi
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, hne⟩
  · intro i hi hni
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at hi hni
    rcases hi with ⟨y, hy, hyi⟩
    rcases hni with ⟨z, hz, hzni⟩
    have hy1 : y i = 1 := (zmod2_ne_zero_iff _).mp hyi
    have hz1 : z (nextIdx t hpos i) = 1 := (zmod2_ne_zero_iff _).mp hzni
    rcases zmod2_eq_zero_or_one (x i) with hxi | hxi <;>
    rcases zmod2_eq_zero_or_one (x (nextIdx t hpos i)) with hxni | hxni
    · rw [hxi, hxni]
    · have h := hg.2 x hx y hy i
      rw [hxi, hxni, hy1] at h
      simp at h
    · have h := hg.2 x hx z hz i
      rw [hxi, hxni, hz1] at h
      simp at h
    · rw [hxi, hxni]
  · ext b
    exact hg.1 x hx b

lemma GoodMax_good (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    goodP t hpos (GoodMax t hpos S) := by
  refine ⟨fun x hx b => congrFun hx.2 b, fun x hx y hy i => ?_⟩
  by_cases hi : i ∈ S
  · by_cases hni : nextIdx t hpos i ∈ S
    · rw [hx.1.2 i hi hni, hy.1.2 i hi hni, mul_comm]
    · rw [hx.1.1 _ hni, hy.1.1 _ hni, mul_zero, zero_mul]
  · rw [hx.1.1 _ hi, hy.1.1 _ hi, zero_mul, mul_zero]

lemma suppU_GoodMax_subset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    suppU t (GoodMax t hpos S) ⊆ S := by
  intro i hi
  simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨x, hx, hxi⟩
  by_contra hnot
  exact hxi (hx.1.1 i hnot)

lemma suppU_mono (t : ℕ) {U V : Submodule F2 (Fin (6 * t) → F2)} (hUV : U ≤ V) :
    suppU t U ⊆ suppU t V := by
  intro i hi
  simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with ⟨x, hx, hxi⟩
  exact ⟨x, hUV hx, hxi⟩

lemma exists_good_supp_iff (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    (∃ U, goodP t hpos U ∧ suppU t U = S) ↔ suppU t (GoodMax t hpos S) = S := by
  constructor
  · rintro ⟨U, hg, rfl⟩
    apply Finset.Subset.antisymm (suppU_GoodMax_subset t hpos (suppU t U))
    exact suppU_mono t (good_le_GoodMax t hpos hg)
  · intro hsupp
    exact ⟨GoodMax t hpos S, GoodMax_good t hpos S, hsupp⟩

-- Finrank of Vset S equals runsS S when runsS S > 0 (i.e. S != univ)
lemma finrank_Vset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (hruns : 0 < runsS t hpos S) :
    Module.finrank F2 (Vset t hpos S) = runsS t hpos S := by
  let ends := S.filter (fun i => nextIdx t hpos i ∉ S)
  let evalEnds : Vset t hpos S →ₗ[F2] (ends → F2) :=
    { toFun := fun x e => x.1 e.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Every i ∈ S reaches a unique end in ≤ 6*t steps going forward
  have hS_ne_univ : ∃ z : Fin (6 * t), z ∉ S := by
    rcases Finset.card_pos.mp hruns with ⟨e, he⟩
    exact ⟨nextIdx t hpos e, (Finset.mem_filter.mp he).2⟩
  have hreach : ∀ i ∈ S, ∃ d < 6 * t,
      (∀ k ≤ d, shiftIdx t hpos i k ∈ S) ∧ nextIdx t hpos (shiftIdx t hpos i d) ∉ S := by
    intro i hi
    rcases hS_ne_univ with ⟨z, hz⟩
    let d0 : ℕ := (z.val + 6 * t - i.val) % (6 * t)
    have hd0_lt : d0 < 6 * t := Nat.mod_lt _ (by omega)
    have hsh_z : shiftIdx t hpos i d0 = z := by
      apply Fin.ext
      dsimp [shiftIdx, d0]
      have hi_lt := i.isLt
      have hz_lt := z.isLt
      by_cases hle : i.val ≤ z.val
      · have : (z.val + 6 * t - i.val) % (6 * t) = z.val - i.val := by
          rw [show z.val + 6 * t - i.val = (z.val - i.val) + 6 * t by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [this, show i.val + (z.val - i.val) = z.val by omega, Nat.mod_eq_of_lt hz_lt]
      · have : (z.val + 6 * t - i.val) % (6 * t) = z.val + 6 * t - i.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [this, show i.val + (z.val + 6 * t - i.val) = z.val + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hz_lt]
    have hex_out : ∃ k ≤ d0, shiftIdx t hpos i k ∉ S := ⟨d0, le_rfl, hsh_z.symm ▸ hz⟩
    classical
    let m0 := Nat.find hex_out
    have hm0_spec : m0 ≤ d0 ∧ shiftIdx t hpos i m0 ∉ S := Nat.find_spec hex_out
    have hm0_pos : 0 < m0 := by
      by_contra h0
      have hm0 : m0 = 0 := by omega
      have := hm0_spec.2
      rw [hm0, shiftIdx_zero] at this
      exact this hi
    refine ⟨m0 - 1, by omega, ?_, ?_⟩
    · intro k hk
      by_contra hnot
      have := Nat.find_min hex_out (show k < m0 by omega)
      exact this ⟨by omega, hnot⟩
    · have hnext : nextIdx t hpos (shiftIdx t hpos i (m0 - 1)) = shiftIdx t hpos i m0 := by
        rw [← shiftIdx_one, shiftIdx_add, Nat.sub_add_cancel hm0_pos]
      rw [hnext]
      exact hm0_spec.2
  -- First prove evalEnds is injective
  have hinj : Function.Injective evalEnds := by
    intro x y hxy
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · rcases hreach i hi with ⟨d, _, hall, hout⟩
      have he_mem : shiftIdx t hpos i d ∈ ends :=
        Finset.mem_filter.mpr ⟨hall d le_rfl, hout⟩
      have hconst : ∀ (v : Vset t hpos S) (k : ℕ), k ≤ d → v.1 (shiftIdx t hpos i k) = v.1 i := by
        intro v k
        induction k with
        | zero => intro _; rw [shiftIdx_zero]
        | succ k ih =>
          intro hk
          have hk1 : shiftIdx t hpos i (k + 1) = nextIdx t hpos (shiftIdx t hpos i k) := by
            rw [← shiftIdx_one, shiftIdx_add]
          rw [hk1, ← v.2.2 (shiftIdx t hpos i k) (hall k (by omega)) (hk1 ▸ hall (k + 1) hk)]
          exact ih (by omega)
      have hxd : x.1 (shiftIdx t hpos i d) = x.1 i := hconst x d le_rfl
      have hyd : y.1 (shiftIdx t hpos i d) = y.1 i := hconst y d le_rfl
      have heq : x.1 (shiftIdx t hpos i d) = y.1 (shiftIdx t hpos i d) :=
        congrFun hxy ⟨shiftIdx t hpos i d, he_mem⟩
      rw [← hxd, ← hyd, heq]
    · rw [x.2.1 i hi, y.2.1 i hi]
  -- Next prove evalEnds is surjective
  have hsurj : Function.Surjective evalEnds := by
    classical
    intro g
    -- Define x i = if hi : i ∈ S then g (unique forward end of i) else 0
    have hex_end : ∀ i ∈ S, ∃ e ∈ ends, ∃ d < 6 * t,
        (∀ k ≤ d, shiftIdx t hpos i k ∈ S) ∧ shiftIdx t hpos i d = e := by
      intro i hi
      rcases hreach i hi with ⟨d, hd, hall, hout⟩
      exact ⟨shiftIdx t hpos i d, Finset.mem_filter.mpr ⟨hall d le_rfl, hout⟩, d, hd, hall, rfl⟩
    let endOf : Fin (6 * t) → F2 := fun i =>
      if hi : i ∈ S then g ⟨Classical.choose (hex_end i hi),
        (Classical.choose_spec (hex_end i hi)).1⟩ else 0
    have hend_unique : ∀ (i : Fin (6 * t)) (hi : i ∈ S) (e : Fin (6 * t)) (he : e ∈ ends)
        (d : ℕ), d < 6 * t → (∀ k ≤ d, shiftIdx t hpos i k ∈ S) → shiftIdx t hpos i d = e →
        Classical.choose (hex_end i hi) = e := by
      intro i hi e he d hd hall hsh
      rcases Classical.choose_spec (hex_end i hi) with ⟨he', d', hd', hall', hsh'⟩
      have hd_eq : d' = d := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h1 : nextIdx t hpos (shiftIdx t hpos i d') ∈ S := by
            rw [← shiftIdx_one, shiftIdx_add]; exact hall (d' + 1) (by omega)
          rw [hsh'] at h1
          exact (Finset.mem_filter.mp he').2 h1
        · have h1 : nextIdx t hpos (shiftIdx t hpos i d) ∈ S := by
            rw [← shiftIdx_one, shiftIdx_add]; exact hall' (d + 1) (by omega)
          rw [hsh] at h1
          exact (Finset.mem_filter.mp he).2 h1
      rw [← hsh', hd_eq, hsh]
    have hxV : endOf ∈ Vset t hpos S := by
      refine ⟨fun i hi => by simp [endOf, hi], fun i hi hni => ?_⟩
      simp only [endOf, hi, hni, ↓reduceDIte]
      congr 1
      apply Subtype.ext
      rcases Classical.choose_spec (hex_end (nextIdx t hpos i) hni) with ⟨he, d, hd, hall, hsh⟩
      have hd1 : d + 1 < 6 * t := by
        by_contra hge
        have hd_eq : d = 6 * t - 1 := by omega
        -- Then every element of Fin (6*t) is in S, contradicting hS_ne_univ
        rcases hS_ne_univ with ⟨z, hz⟩
        let k0 : ℕ := (z.val + 6 * t - (nextIdx t hpos i).val) % (6 * t)
        have hk0_le : k0 ≤ d := by
          have : k0 < 6 * t := Nat.mod_lt _ (by omega)
          omega
        have hk0_sh : shiftIdx t hpos (nextIdx t hpos i) k0 = z := by
          apply Fin.ext; dsimp [shiftIdx, k0]
          have h1 := (nextIdx t hpos i).isLt
          have h2 := z.isLt
          by_cases hle : (nextIdx t hpos i).val ≤ z.val
          · have : (z.val + 6 * t - (nextIdx t hpos i).val) % (6 * t) =
                z.val - (nextIdx t hpos i).val := by
              rw [show z.val + 6 * t - (nextIdx t hpos i).val =
                (z.val - (nextIdx t hpos i).val) + 6 * t by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [this, show (nextIdx t hpos i).val + (z.val - (nextIdx t hpos i).val) = z.val by omega,
              Nat.mod_eq_of_lt h2]
          · have : (z.val + 6 * t - (nextIdx t hpos i).val) % (6 * t) =
                z.val + 6 * t - (nextIdx t hpos i).val := Nat.mod_eq_of_lt (by omega)
            rw [this, show (nextIdx t hpos i).val + (z.val + 6 * t - (nextIdx t hpos i).val) =
              z.val + 6 * t by omega, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
        exact hz (hk0_sh ▸ hall k0 hk0_le)
      refine hend_unique i hi _ he (d + 1) hd1 ?_ ?_
      · intro k hk
        cases k with
        | zero => rw [shiftIdx_zero]; exact hi
        | succ k =>
          have h1 : shiftIdx t hpos i (k + 1) = shiftIdx t hpos (nextIdx t hpos i) k := by
            rw [← shiftIdx_one, shiftIdx_add, Nat.add_comm]
          rw [h1]; exact hall k (by omega)
      · have hstep : shiftIdx t hpos i (d + 1) = shiftIdx t hpos (nextIdx t hpos i) d := by
          rw [← shiftIdx_one, shiftIdx_add, Nat.add_comm]
        exact hstep.trans hsh
    refine ⟨⟨endOf, hxV⟩, ?_⟩
    ext e
    have heS : e.1 ∈ S := (Finset.mem_filter.mp e.2).1
    simp only [evalEnds, LinearMap.coe_mk, AddHom.coe_mk, endOf, heS, ↓reduceDIte]
    congr 1
    apply Subtype.ext
    exact hend_unique e.1 heS e.1 e.2 0 (by omega) (fun k hk => by
      have : k = 0 := by omega
      rw [this, shiftIdx_zero]; exact heS) (shiftIdx_zero t hpos e.1)
  have heq : Module.finrank F2 (Vset t hpos S) = Module.finrank F2 (ends → F2) :=
    (LinearEquiv.ofBijective evalEnds ⟨hinj, hsurj⟩).finrank_eq
  rw [heq, Module.finrank_pi_fintype]
  simp [ends, runsS]

-- Stage 2: S = symmDiff (cycInt u L) EvenSet characterization
def evenSet (t : ℕ) : Finset (Fin (6 * t)) :=
  Finset.univ.filter (fun i => i.val % 2 = 0)

def cycInt (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) (L : ℕ) : Finset (Fin (6 * t)) :=
  (Finset.range L).image (fun d => shiftIdx t hpos u d)

lemma card_cycInt (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ} (hL : L ≤ 6 * t) :
    (cycInt t hpos u L).card = L := by
  unfold cycInt
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact shiftIdx_inj_range t hpos u (lt_of_lt_of_le (Finset.mem_range.mp ha) hL)
    (lt_of_lt_of_le (Finset.mem_range.mp hb) hL) hab

lemma mem_cycInt_iff (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) (L : ℕ) (i : Fin (6 * t)) :
    i ∈ cycInt t hpos u L ↔ ∃ d < L, shiftIdx t hpos u d = i := by
  simp [cycInt]

lemma card_runs_eq_starts (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    (Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S)).card =
      runsS t hpos S := by
  have h1 : S.card = (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S)).card +
      (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S)).card := by
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S))
        (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2.2
    have hun : Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S) ∪
        Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S) = S := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [← Finset.card_union_of_disjoint hdisj, hun]
  have h2 : S.card = (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S)).card +
      (Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S)).card := by
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S))
        (Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
    have hun : (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S) ∪
        Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S)).card = S.card := by
      have heq : Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∈ S) ∪
          Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S) =
          Finset.univ.filter (fun i : Fin (6 * t) => nextIdx t hpos i ∈ S) := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      rw [heq]
      refine Finset.card_bij (fun i _ => nextIdx t hpos i)
        (fun i hi => (Finset.mem_filter.mp hi).2)
        (fun _ _ _ _ hab => nextIdx_inj t hpos hab)
        (fun j hj => ⟨prevIdx t hpos j, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by rw [nextIdx_prevIdx]; exact hj⟩, nextIdx_prevIdx t hpos j⟩)
    rw [← Finset.card_union_of_disjoint hdisj, hun]
  have h3 : (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S)).card =
      runsS t hpos S := by
    unfold runsS; congr 1; ext i; simp [and_comm]
  omega

-- Key duality: runsS S + runsS (symmDiff S evenSet) = 3 * t
lemma runsS_add_symmDiff_even (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    runsS t hpos S + runsS t hpos (symmDiff S (evenSet t)) = 3 * t := by
  let T := symmDiff S (evenSet t)
  have hmemT : ∀ i : Fin (6 * t), i ∈ T ↔ ((i ∈ S) ↔ i.val % 2 ≠ 0) := by
    intro i
    simp only [T, Finset.mem_symmDiff, evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hiff : ∀ i : Fin (6 * t),
      ((i ∈ S ∧ nextIdx t hpos i ∉ S) ∨ (i ∉ S ∧ nextIdx t hpos i ∈ S)) ↔
      ¬ ((i ∈ T ∧ nextIdx t hpos i ∉ T) ∨ (i ∉ T ∧ nextIdx t hpos i ∈ T)) := by
    intro i
    have h1 := hmemT i
    have h2 := hmemT (nextIdx t hpos i)
    have hmod := nextIdx_mod2 t hpos i
    have hp : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hp with hp | hp <;> rw [hp] at h1 hmod <;> rw [hmod] at h2 <;> norm_num at h1 h2 <;> tauto
  let BS := Finset.univ.filter (fun i : Fin (6 * t) =>
    (i ∈ S ∧ nextIdx t hpos i ∉ S) ∨ (i ∉ S ∧ nextIdx t hpos i ∈ S))
  let BT := Finset.univ.filter (fun i : Fin (6 * t) =>
    (i ∈ T ∧ nextIdx t hpos i ∉ T) ∨ (i ∉ T ∧ nextIdx t hpos i ∈ T))
  have hBS_card : BS.card = 2 * runsS t hpos S := by
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S))
        (Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
    have hun : Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S) ∪
        Finset.univ.filter (fun i : Fin (6 * t) => i ∉ S ∧ nextIdx t hpos i ∈ S) = BS := by
      ext i; simp [BS]
    have h1 : (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ S ∧ nextIdx t hpos i ∉ S)).card =
        runsS t hpos S := by unfold runsS; congr 1; ext i; simp [and_comm]
    rw [← hun, Finset.card_union_of_disjoint hdisj, h1, card_runs_eq_starts]
    ring
  have hBT_card : BT.card = 2 * runsS t hpos T := by
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ T ∧ nextIdx t hpos i ∉ T))
        (Finset.univ.filter (fun i : Fin (6 * t) => i ∉ T ∧ nextIdx t hpos i ∈ T)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
    have hun : Finset.univ.filter (fun i : Fin (6 * t) => i ∈ T ∧ nextIdx t hpos i ∉ T) ∪
        Finset.univ.filter (fun i : Fin (6 * t) => i ∉ T ∧ nextIdx t hpos i ∈ T) = BT := by
      ext i; simp [BT]
    have h1 : (Finset.univ.filter (fun i : Fin (6 * t) => i ∈ T ∧ nextIdx t hpos i ∉ T)).card =
        runsS t hpos T := by unfold runsS; congr 1; ext i; simp [and_comm]
    rw [← hun, Finset.card_union_of_disjoint hdisj, h1, card_runs_eq_starts]
    ring
  have hdisj_all : Disjoint BS BT := by
    rw [Finset.disjoint_left]; intro i h1 h2
    exact (hiff i).mp (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hun_all : BS ∪ BT = Finset.univ := by
    ext i
    simp only [BS, BT, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have := hiff i; tauto
  have htot : BS.card + BT.card = 6 * t := by
    rw [← Finset.card_union_of_disjoint hdisj_all, hun_all, Finset.card_univ, Fintype.card_fin]
  dsimp only [T] at hBT_card
  omega

-- runsS T = 1 iff T = cycInt u L for unique (u, L) with 1 <= L < 6*t
lemma runsS_cycInt (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ}
    (hL1 : 1 ≤ L) (hLn : L < 6 * t) :
    runsS t hpos (cycInt t hpos u L) = 1 := by
  have heq : (cycInt t hpos u L).filter (fun i => nextIdx t hpos i ∉ cycInt t hpos u L) =
      {shiftIdx t hpos u (L - 1)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_cycInt_iff]
    constructor
    · rintro ⟨⟨d, hdL, rfl⟩, hnot⟩
      by_cases hlast : d = L - 1
      · rw [hlast]
      · exfalso; apply hnot
        refine ⟨d + 1, by omega, ?_⟩
        rw [← shiftIdx_one, shiftIdx_add]
    · rintro rfl
      refine ⟨⟨L - 1, by omega, rfl⟩, ?_⟩
      rintro ⟨d, hdL, hd_eq⟩
      rw [← shiftIdx_one, shiftIdx_add, Nat.sub_add_cancel hL1] at hd_eq
      have := shiftIdx_inj_range t hpos u (by omega) hLn hd_eq
      omega
  unfold runsS
  rw [heq, Finset.card_singleton]

lemma runsS_eq_one_iff (t : ℕ) (hpos : 0 < t) (T : Finset (Fin (6 * t))) :
    runsS t hpos T = 1 ↔ ∃ u : Fin (6 * t), ∃ L : ℕ, 1 ≤ L ∧ L < 6 * t ∧ T = cycInt t hpos u L := by
  constructor
  · intro h1
    have hstarts : (Finset.univ.filter (fun i : Fin (6 * t) => i ∉ T ∧ nextIdx t hpos i ∈ T)).card = 1 := by
      rw [card_runs_eq_starts, h1]
    rcases Finset.card_eq_one.mp hstarts with ⟨p, hp⟩
    rcases Finset.card_eq_one.mp h1 with ⟨e, he⟩
    let u := nextIdx t hpos p
    have hp_mem : p ∉ T ∧ u ∈ T := by
      have hpm : p ∈ Finset.univ.filter (fun i : Fin (6 * t) => i ∉ T ∧ nextIdx t hpos i ∈ T) := by
        rw [hp]; exact Finset.mem_singleton_self p
      exact (Finset.mem_filter.mp hpm).2
    have he_mem : e ∈ T ∧ nextIdx t hpos e ∉ T := by
      have hem : e ∈ T.filter (fun i => nextIdx t hpos i ∉ T) := by
        rw [he]; exact Finset.mem_singleton_self e
      exact Finset.mem_filter.mp hem
    let d0 : ℕ := (e.val + 6 * t - u.val) % (6 * t)
    have hd0_lt : d0 < 6 * t := Nat.mod_lt _ (by omega)
    have hsh_e : shiftIdx t hpos u d0 = e := by
      apply Fin.ext; dsimp [shiftIdx, d0]
      have hu := u.isLt; have hev := e.isLt
      by_cases hle : u.val ≤ e.val
      · have : (e.val + 6 * t - u.val) % (6 * t) = e.val - u.val := by
          rw [show e.val + 6 * t - u.val = (e.val - u.val) + 6 * t by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [this, show u.val + (e.val - u.val) = e.val by omega, Nat.mod_eq_of_lt hev]
      · have : (e.val + 6 * t - u.val) % (6 * t) = e.val + 6 * t - u.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [this, show u.val + (e.val + 6 * t - u.val) = e.val + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hev]
    have hd0_lt2 : d0 + 1 < 6 * t := by
      by_contra hge
      have hd_eq : d0 = 6 * t - 1 := by omega
      have : nextIdx t hpos e = u := by
        rw [← hsh_e, ← shiftIdx_one, shiftIdx_add, hd_eq,
          Nat.sub_add_cancel (by omega : 1 ≤ 6 * t)]
        apply Fin.ext; simp [shiftIdx, Nat.mod_eq_of_lt u.isLt]
      exact he_mem.2 (this ▸ hp_mem.2)
    -- Show shift u k ∈ T for k ≤ d0 and shift u k ∉ T for d0 < k < 6*t
    have hin : ∀ k ≤ d0, shiftIdx t hpos u k ∈ T := by
      intro k
      induction k with
      | zero => intro _; rw [shiftIdx_zero]; exact hp_mem.2
      | succ k ih =>
        intro hk
        have hprev : shiftIdx t hpos u k ∈ T := ih (by omega)
        by_contra hnot
        have hk_end : shiftIdx t hpos u k ∈ T.filter (fun i => nextIdx t hpos i ∉ T) := by
          refine Finset.mem_filter.mpr ⟨hprev, ?_⟩
          rw [← shiftIdx_one, shiftIdx_add]; exact hnot
        rw [he, Finset.mem_singleton] at hk_end
        have := shiftIdx_inj_range t hpos u (by omega) hd0_lt (hk_end.trans hsh_e.symm)
        omega
    have hout : ∀ k, d0 < k → k < 6 * t → shiftIdx t hpos u k ∉ T := by
      intro k
      induction k with
      | zero => intro hlt; omega
      | succ k ih =>
        intro hgt hlt
        by_cases hkeq : k = d0
        · subst hkeq
          rw [← shiftIdx_add, shiftIdx_one, hsh_e]
          exact he_mem.2
        · have hprev : shiftIdx t hpos u k ∉ T := ih (by omega) (by omega)
          intro hmem
          have hk_st : shiftIdx t hpos u k ∈
              Finset.univ.filter (fun i : Fin (6 * t) => i ∉ T ∧ nextIdx t hpos i ∈ T) := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprev, ?_⟩
            rw [← shiftIdx_one, shiftIdx_add]; exact hmem
          rw [hp, Finset.mem_singleton] at hk_st
          have hnext : shiftIdx t hpos u (k + 1) = shiftIdx t hpos u 0 := by
            rw [← shiftIdx_add, shiftIdx_one, hk_st, shiftIdx_zero]
          have := shiftIdx_inj_range t hpos u hlt (by omega) hnext
          omega
    refine ⟨u, d0 + 1, by omega, hd0_lt2, ?_⟩
    ext i
    rw [mem_cycInt_iff]
    let k : ℕ := (i.val + 6 * t - u.val) % (6 * t)
    have hk_lt : k < 6 * t := Nat.mod_lt _ (by omega)
    have hsh_i : shiftIdx t hpos u k = i := by
      apply Fin.ext; dsimp [shiftIdx, k]
      have hu := u.isLt; have hiv := i.isLt
      by_cases hle : u.val ≤ i.val
      · have : (i.val + 6 * t - u.val) % (6 * t) = i.val - u.val := by
          rw [show i.val + 6 * t - u.val = (i.val - u.val) + 6 * t by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [this, show u.val + (i.val - u.val) = i.val by omega, Nat.mod_eq_of_lt hiv]
      · have : (i.val + 6 * t - u.val) % (6 * t) = i.val + 6 * t - u.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [this, show u.val + (i.val + 6 * t - u.val) = i.val + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hiv]
    constructor
    · intro hiT
      by_cases hle : k ≤ d0
      · exact ⟨k, by omega, hsh_i⟩
      · exact False.elim (hout k (by omega) hk_lt (hsh_i.symm ▸ hiT))
    · rintro ⟨d, hd, rfl⟩
      exact hin d (by omega)
  · rintro ⟨u, L, hL1, hLn, rfl⟩
    exact runsS_cycInt t hpos u hL1 hLn

lemma cycInt_unique (t : ℕ) (hpos : 0 < t) {u1 u2 : Fin (6 * t)} {L1 L2 : ℕ}
    (h1a : 1 ≤ L1) (h1b : L1 < 6 * t) (h2a : 1 ≤ L2) (h2b : L2 < 6 * t)
    (heq : cycInt t hpos u1 L1 = cycInt t hpos u2 L2) :
    u1 = u2 ∧ L1 = L2 := by
  have hL : L1 = L2 := by
    have := congrArg Finset.card heq
    rwa [card_cycInt t hpos u1 (by omega), card_cycInt t hpos u2 (by omega)] at this
  subst hL
  refine ⟨?_, rfl⟩
  have hu1_in : u1 ∈ cycInt t hpos u2 L1 := by
    rw [← heq, mem_cycInt_iff]; exact ⟨0, by omega, shiftIdx_zero t hpos u1⟩
  have hp1_out : prevIdx t hpos u1 ∉ cycInt t hpos u2 L1 := by
    rw [← heq, mem_cycInt_iff]
    rintro ⟨d, hd, hdeq⟩
    have h1 : shiftIdx t hpos u1 (d + 1) = shiftIdx t hpos u1 0 := by
      rw [← shiftIdx_add, shiftIdx_one, hdeq, nextIdx_prevIdx, shiftIdx_zero]
    have := shiftIdx_inj_range t hpos u1 (by omega) (by omega) h1
    omega
  rcases (mem_cycInt_iff t hpos u2 L1 u1).mp hu1_in with ⟨d, hd, hdeq⟩
  cases d with
  | zero => rw [shiftIdx_zero] at hdeq; exact hdeq.symm
  | succ d =>
    exfalso; apply hp1_out
    rw [mem_cycInt_iff]
    refine ⟨d, by omega, ?_⟩
    apply nextIdx_inj t hpos
    rw [nextIdx_prevIdx, ← hdeq, ← shiftIdx_one, shiftIdx_add]

-- Sites count for S = symmDiff (cycInt u L) (evenSet t)
lemma sites_symmDiff_cycInt (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ}
    (hLn : L < 6 * t) :
    sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 1 = (L + u.val % 2) / 2 ∧
    sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 0 = 3 * t - (L + (1 - u.val % 2)) / 2 := by
  let T := cycInt t hpos u L
  let S := symmDiff T (evenSet t)
  have hT1 : S.filter (fun i => i.val % 2 = 1) = T.filter (fun i => i.val % 2 = 1) := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_symmDiff, evenSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, hp⟩
      refine ⟨?_, hp⟩
      rcases h1 with ⟨hiT, _⟩ | ⟨hiE, _⟩
      · exact hiT
      · omega
    · rintro ⟨hiT, hp⟩
      exact ⟨Or.inl ⟨hiT, by omega⟩, hp⟩
  have hT0 : S.filter (fun i => i.val % 2 = 0) = (evenSet t) \ T := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_sdiff, evenSet,
      Finset.mem_univ, true_and]
    tauto
  have hcard_range_odd : ∀ (p L0 : ℕ), p ≤ 1 →
      ((Finset.range L0).filter (fun d => (p + d) % 2 = 1)).card = (L0 + p) / 2 := by
    intro p L0 hp
    induction L0 with
    | zero => simp; omega
    | succ k ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
      · rw [ih]; omega
  have hcard_range_even : ∀ (p L0 : ℕ), p ≤ 1 →
      ((Finset.range L0).filter (fun d => (p + d) % 2 = 0)).card = (L0 + (1 - p)) / 2 := by
    intro p L0 hp
    induction L0 with
    | zero => simp; omega
    | succ k ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
      · rw [ih]; omega
  have hT1_card : (T.filter (fun i => i.val % 2 = 1)).card = (L + u.val % 2) / 2 := by
    have hbij : (T.filter (fun i => i.val % 2 = 1)).card =
        ((Finset.range L).filter (fun d => (u.val % 2 + d) % 2 = 1)).card := by
      refine (Finset.card_bij (fun d _ => shiftIdx t hpos u d) ?_ ?_ ?_).symm
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdL, hmod⟩
        refine Finset.mem_filter.mpr ⟨(mem_cycInt_iff t hpos u L _).mpr
          ⟨d, Finset.mem_range.mp hdL, rfl⟩, ?_⟩
        rw [shiftIdx_mod2]; omega
      · intro a ha b hb hab
        exact shiftIdx_inj_range t hpos u
          (lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp ha).1) hLn)
          (lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hLn) hab
      · intro i hi
        rcases Finset.mem_filter.mp hi with ⟨hiT, hmod⟩
        rcases (mem_cycInt_iff t hpos u L i).mp hiT with ⟨d, hdL, rfl⟩
        refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdL, ?_⟩, rfl⟩
        rw [shiftIdx_mod2] at hmod; omega
    rw [hbij, hcard_range_odd (u.val % 2) L (by omega)]
  have hT0_inter : ((evenSet t) ∩ T).card = (L + (1 - u.val % 2)) / 2 := by
    have hbij : ((evenSet t) ∩ T).card =
        ((Finset.range L).filter (fun d => (u.val % 2 + d) % 2 = 0)).card := by
      refine (Finset.card_bij (fun d _ => shiftIdx t hpos u d) ?_ ?_ ?_).symm
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdL, hmod⟩
        refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          (mem_cycInt_iff t hpos u L _).mpr ⟨d, Finset.mem_range.mp hdL, rfl⟩⟩
        rw [shiftIdx_mod2]; omega
      · intro a ha b hb hab
        exact shiftIdx_inj_range t hpos u
          (lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp ha).1) hLn)
          (lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hLn) hab
      · intro i hi
        rcases Finset.mem_inter.mp hi with ⟨hiE, hiT⟩
        have hmod : i.val % 2 = 0 := (Finset.mem_filter.mp hiE).2
        rcases (mem_cycInt_iff t hpos u L i).mp hiT with ⟨d, hdL, rfl⟩
        refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdL, ?_⟩, rfl⟩
        rw [shiftIdx_mod2] at hmod; omega
    rw [hbij, hcard_range_even (u.val % 2) L (by omega)]
  have heven_card : (evenSet t).card = 3 * t := by
    unfold evenSet
    have hbij : (Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = 0)).card =
        (Finset.univ : Finset (Fin (3 * t))).card :=
      Finset.card_bij (fun (i : Fin (6 * t)) _ => (⟨i.val / 2, by omega⟩ : Fin (3 * t)))
        (fun _ _ => Finset.mem_univ _)
        (fun a ha b hb hab => by
          have ha0 := (Finset.mem_filter.mp ha).2
          have hb0 := (Finset.mem_filter.mp hb).2
          have hv := congrArg Fin.val hab; dsimp at hv
          exact Fin.ext (by omega))
        (fun q _ => ⟨⟨2 * q.val, by have := q.isLt; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩,
          Fin.ext (by have := q.isLt; dsimp; omega)⟩)
    simpa using hbij
  constructor
  · unfold sitesS; rw [hT1, hT1_card]
  · unfold sitesS
    have hsub : (evenSet t \ T).card = (evenSet t).card - (evenSet t ∩ T).card := by
      have := Finset.card_sdiff_add_card_inter (evenSet t) T; omega
    rw [hT0, hsub, heven_card, hT0_inter]

-- Stage 3: Necessary condition (sites >= 3 on both lanes)
lemma supp_GoodMax_imp_sites_ge3 (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t)
    (u : Fin (6 * t)) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < 6 * t)
    (hs0 : 0 < sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 0)
    (hs1 : 0 < sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 1)
    (hsupp : suppU t (GoodMax t hpos (symmDiff (cycInt t hpos u L) (evenSet t))) =
      symmDiff (cycInt t hpos u L) (evenSet t)) :
    3 ≤ sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 0 ∧
    3 ≤ sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 1 := by
  let T := cycInt t hpos u L
  let S := symmDiff T (evenSet t)
  have hsites := sites_symmDiff_cycInt t hpos u hLn
  -- Express odd sites of S as {shift o0 (2*q) | q < k1}
  let o0 : Fin (6 * t) := if u.val % 2 = 1 then u else nextIdx t hpos u
  have ho0_odd : o0.val % 2 = 1 := by
    dsimp [o0]; split_ifs with h
    · exact h
    · rw [nextIdx_mod2]; omega
  let k1 := sitesS t S 1
  have hO_eq : S.filter (fun i => i.val % 2 = 1) =
      (Finset.range k1).image (fun q => shiftIdx t hpos o0 (2 * q)) := by
    have hsub : (Finset.range k1).image (fun q => shiftIdx t hpos o0 (2 * q)) ⊆
        S.filter (fun i => i.val % 2 = 1) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
      have hqk1 : q < k1 := Finset.mem_range.mp hq
      have hmod : (shiftIdx t hpos o0 (2 * q)).val % 2 = 1 := by
        rw [shiftIdx_mod2]; omega
      refine Finset.mem_filter.mpr ⟨?_, hmod⟩
      have hT : shiftIdx t hpos o0 (2 * q) ∈ T := by
        rw [mem_cycInt_iff]
        dsimp [o0]
        have hk1_eq : k1 = (L + u.val % 2) / 2 := hsites.1
        split_ifs with hu
        · refine ⟨2 * q, ?_, rfl⟩
          omega
        · refine ⟨1 + 2 * q, ?_, ?_⟩
          · omega
          · rw [← shiftIdx_one, shiftIdx_add]
      simp only [S, Finset.mem_symmDiff, evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨hT, by omega⟩
    have hcard : ((Finset.range k1).image (fun q => shiftIdx t hpos o0 (2 * q))).card =
        (S.filter (fun i => i.val % 2 = 1)).card := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      · rfl
      · intro a ha b hb hab
        have h1 : a < k1 := Finset.mem_range.mp ha
        have h2 : b < k1 := Finset.mem_range.mp hb
        have hk1_le : k1 ≤ 3 * t := by
          have := hsites.1; change k1 = (L + u.val % 2) / 2 at this; omega
        have := shiftIdx_inj_range t hpos o0 (by omega) (by omega) hab
        omega
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)).symm
  -- Express even sites of S as {shift e0 (2*q) | q < k0}
  let v := shiftIdx t hpos u L
  let e0 : Fin (6 * t) := if v.val % 2 = 0 then v else nextIdx t hpos v
  have he0_even : e0.val % 2 = 0 := by
    dsimp [e0]; split_ifs with h
    · exact h
    · rw [nextIdx_mod2]; omega
  let k0 := sitesS t S 0
  have hE_eq : S.filter (fun i => i.val % 2 = 0) =
      (Finset.range k0).image (fun q => shiftIdx t hpos e0 (2 * q)) := by
    have hsub : (Finset.range k0).image (fun q => shiftIdx t hpos e0 (2 * q)) ⊆
        S.filter (fun i => i.val % 2 = 0) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
      have hqk0 : q < k0 := Finset.mem_range.mp hq
      have hmod : (shiftIdx t hpos e0 (2 * q)).val % 2 = 0 := by
        rw [shiftIdx_mod2]; omega
      refine Finset.mem_filter.mpr ⟨?_, hmod⟩
      have hnotT : shiftIdx t hpos e0 (2 * q) ∉ T := by
        rw [mem_cycInt_iff]
        rintro ⟨d, hdL, hdeq⟩
        have hv_mod : v.val % 2 = (u.val + L) % 2 := shiftIdx_mod2 t hpos u L
        have hk0_eq : k0 = 3 * t - (L + (1 - u.val % 2)) / 2 := hsites.2
        dsimp [e0, v] at hdeq
        split_ifs at hdeq with hv
        · rw [shiftIdx_add] at hdeq
          have := shiftIdx_inj_range t hpos u (by omega) (by omega) hdeq
          omega
        · rw [← shiftIdx_one, shiftIdx_add, shiftIdx_add] at hdeq
          have := shiftIdx_inj_range t hpos u (by omega) (by omega) hdeq
          omega
      simp only [S, Finset.mem_symmDiff, evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨hmod, hnotT⟩
    have hcard : ((Finset.range k0).image (fun q => shiftIdx t hpos e0 (2 * q))).card =
        (S.filter (fun i => i.val % 2 = 0)).card := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      · rfl
      · intro a ha b hb hab
        have h1 : a < k0 := Finset.mem_range.mp ha
        have h2 : b < k0 := Finset.mem_range.mp hb
        have hk0_le : k0 ≤ 3 * t := by
          have := hsites.2; change k0 = 3 * t - (L + (1 - u.val % 2)) / 2 at this; omega
        have := shiftIdx_inj_range t hpos e0 (by omega) (by omega) hab
        omega
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)).symm
  -- Now prove 3 <= k0 and 3 <= k1 by contradiction
  constructor
  · by_contra hlt
    have hk0_pos : 0 < k0 := hs0
    have hk0_lt : k0 < 3 := by dsimp only [k0, S, T]; omega
    have hk0_cases : k0 = 1 ∨ k0 = 2 := by omega
    have he0_in : e0 ∈ S := by
      have : e0 ∈ S.filter (fun i => i.val % 2 = 0) := by
        rw [hE_eq]; refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), shiftIdx_zero _ _ _⟩
      exact (Finset.mem_filter.mp this).1
    have he0_supp : e0 ∈ suppU t (GoodMax t hpos S) := by rw [hsupp]; exact he0_in
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at he0_supp
    rcases he0_supp with ⟨x, hx, hxe0⟩
    have hsum_even : ∀ b : Fin 4, b.val / 2 = 0 →
        (∑ i ∈ S.filter (fun i => i.val % 2 = 0), hFn t i b * x i) = 0 := by
      intro b hb
      have htot : (∑ i : Fin (6 * t), hFn t i b * x i) = 0 := congrFun hx.2 b
      rw [← htot]
      symm
      rw [← Finset.sum_subset (Finset.subset_univ (S.filter (fun i => i.val % 2 = 0)))]
      intro i _ hnot
      by_cases hiS : i ∈ S
      · have hodd : i.val % 2 ≠ 0 := fun h0 => hnot (Finset.mem_filter.mpr ⟨hiS, h0⟩)
        rw [hFn_other_lane t i b (by omega), zero_mul]
      · rw [hx.1.1 i hiS, mul_zero]
    have h0 := hsum_even 0 (by decide)
    have h1 := hsum_even 1 (by decide)
    rw [hE_eq] at h0 h1
    rcases hk0_cases with hk0_1 | hk0_2
    · rw [hk0_1] at h0 h1
      simp only [Finset.range_one, Finset.image_singleton, Finset.sum_singleton, mul_zero, shiftIdx_zero] at h0 h1
      have hx1 : x e0 = 1 := (zmod2_ne_zero_iff _).mp hxe0
      rw [hx1, mul_one] at h0 h1
      rcases (hFn_single_ne_zero t e0).1 he0_even with hne | hne
      · exact hne h0
      · exact hne h1
    · rw [hk0_2] at h0 h1
      have hne02 : shiftIdx t hpos e0 0 ≠ shiftIdx t hpos e0 2 := fun h => by
        have := shiftIdx_inj_range t hpos e0 (by omega) (by omega) h; omega
      have hpair : (Finset.range 2).image (fun q => shiftIdx t hpos e0 (2 * q)) =
          {e0, shiftIdx t hpos e0 2} := by
        ext i; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨q, hq, rfl⟩
          have : q = 0 ∨ q = 1 := by omega
          rcases this with rfl | rfl
          · left; exact shiftIdx_zero t hpos e0
          · right; rfl
        · rintro (rfl | rfl)
          · exact ⟨0, by omega, shiftIdx_zero t hpos e0⟩
          · exact ⟨1, by omega, rfl⟩
      rw [hpair, Finset.sum_pair (by rwa [shiftIdx_zero] at hne02)] at h0 h1
      exact hxe0 (hFn_pair_indep_even t hpos e0 he0_even (x e0) (x (shiftIdx t hpos e0 2)) h0 h1).1
  · by_contra hlt
    have hk1_pos : 0 < k1 := hs1
    have hk1_lt : k1 < 3 := by dsimp only [k1, S, T]; omega
    have hk1_cases : k1 = 1 ∨ k1 = 2 := by omega
    have ho0_in : o0 ∈ S := by
      have : o0 ∈ S.filter (fun i => i.val % 2 = 1) := by
        rw [hO_eq]; refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), shiftIdx_zero _ _ _⟩
      exact (Finset.mem_filter.mp this).1
    have ho0_supp : o0 ∈ suppU t (GoodMax t hpos S) := by rw [hsupp]; exact ho0_in
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at ho0_supp
    rcases ho0_supp with ⟨x, hx, hxo0⟩
    have hsum_odd : ∀ b : Fin 4, b.val / 2 = 1 →
        (∑ i ∈ S.filter (fun i => i.val % 2 = 1), hFn t i b * x i) = 0 := by
      intro b hb
      have htot : (∑ i : Fin (6 * t), hFn t i b * x i) = 0 := congrFun hx.2 b
      rw [← htot]
      symm
      rw [← Finset.sum_subset (Finset.subset_univ (S.filter (fun i => i.val % 2 = 1)))]
      intro i _ hnot
      by_cases hiS : i ∈ S
      · have hev : i.val % 2 ≠ 1 := fun h1 => hnot (Finset.mem_filter.mpr ⟨hiS, h1⟩)
        rw [hFn_other_lane t i b (by omega), zero_mul]
      · rw [hx.1.1 i hiS, mul_zero]
    have h2 := hsum_odd 2 (by decide)
    have h3 := hsum_odd 3 (by decide)
    rw [hO_eq] at h2 h3
    rcases hk1_cases with hk1_1 | hk1_2
    · rw [hk1_1] at h2 h3
      simp only [Finset.range_one, Finset.image_singleton, Finset.sum_singleton, mul_zero, shiftIdx_zero] at h2 h3
      have hx1 : x o0 = 1 := (zmod2_ne_zero_iff _).mp hxo0
      rw [hx1, mul_one] at h2 h3
      rcases (hFn_single_ne_zero t o0).2 ho0_odd with hne | hne
      · exact hne h2
      · exact hne h3
    · rw [hk1_2] at h2 h3
      have hne02 : shiftIdx t hpos o0 0 ≠ shiftIdx t hpos o0 2 := fun h => by
        have := shiftIdx_inj_range t hpos o0 (by omega) (by omega) h; omega
      have hpair : (Finset.range 2).image (fun q => shiftIdx t hpos o0 (2 * q)) =
          {o0, shiftIdx t hpos o0 2} := by
        ext i; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨q, hq, rfl⟩
          have : q = 0 ∨ q = 1 := by omega
          rcases this with rfl | rfl
          · left; exact shiftIdx_zero t hpos o0
          · right; rfl
        · rintro (rfl | rfl)
          · exact ⟨0, by omega, shiftIdx_zero t hpos o0⟩
          · exact ⟨1, by omega, rfl⟩
      rw [hpair, Finset.sum_pair (by rwa [shiftIdx_zero] at hne02)] at h2 h3
      exact hxo0 (hFn_pair_indep_odd t hpos o0 ho0_odd (x o0) (x (shiftIdx t hpos o0 2)) h2 h3).1

-- Stage 3B: Sufficiency (sites >= 3 on both lanes => supp GoodMax = S and finrank GoodMax = 3*t - 5)
lemma single_mem_Vset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (i : Fin (6 * t))
    (hi : i ∈ S) (hprev : prevIdx t hpos i ∉ S) (hnext : nextIdx t hpos i ∉ S) :
    Pi.single i (1 : F2) ∈ Vset t hpos S := by
  refine ⟨fun j hj => by
    have hne : j ≠ i := fun h => hj (h ▸ hi)
    exact Pi.single_eq_of_ne hne 1,
    fun j hj hnj => ?_⟩
  have h1 : j ≠ i := fun h => hnext (h ▸ hnj)
  have h2 : nextIdx t hpos j ≠ i := fun h => by
    have : j = prevIdx t hpos i := by rw [← h, prevIdx_nextIdx]
    exact hprev (this ▸ hj)
  rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

lemma pair_mem_Vset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (i : Fin (6 * t))
    (hi : i ∈ S) (hni : nextIdx t hpos i ∈ S)
    (hprev : prevIdx t hpos i ∉ S) (hnn : nextIdx t hpos (nextIdx t hpos i) ∉ S) :
    Pi.single i (1 : F2) + Pi.single (nextIdx t hpos i) (1 : F2) ∈ Vset t hpos S := by
  have hne : i ≠ nextIdx t hpos i := fun h => by
    have h1 := nextIdx_mod2 t hpos i
    rw [← h] at h1; omega
  refine ⟨fun j hj => by
    have h1 : j ≠ i := fun h => hj (h ▸ hi)
    have h2 : j ≠ nextIdx t hpos i := fun h => hj (h ▸ hni)
    simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2],
    fun j hj hnj => ?_⟩
  by_cases hji : j = i
  · subst hji
    simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
  · have hjni : j ≠ nextIdx t hpos i := fun h => hnn (h ▸ hnj)
    have hnji : nextIdx t hpos j ≠ i := fun h => by
      have : j = prevIdx t hpos i := by rw [← h, prevIdx_nextIdx]
      exact hprev (this ▸ hj)
    have hnjni : nextIdx t hpos j ≠ nextIdx t hpos i := fun h => hji (nextIdx_inj t hpos h)
    simp [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hjni,
      Pi.single_eq_of_ne hnji, Pi.single_eq_of_ne hnjni]

-- Helper: runVec S i for S = symmDiff (cycInt u L) evenSet with 5 <= L <= 6*t - 5
noncomputable def runVec (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (i : Fin (6 * t)) :
    Fin (6 * t) → F2 :=
  if nextIdx t hpos i ∈ S then Pi.single i 1 + Pi.single (nextIdx t hpos i) 1
  else if prevIdx t hpos i ∈ S then Pi.single (prevIdx t hpos i) 1 + Pi.single i 1
  else Pi.single i 1

lemma mem_S_shift_iff (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ} (hLn : L < 6 * t)
    {d : ℕ} (hd : d < 6 * t) :
    (shiftIdx t hpos u d ∈ symmDiff (cycInt t hpos u L) (evenSet t)) ↔
    ((d < L ∧ (u.val + d) % 2 = 1) ∨ (L ≤ d ∧ (u.val + d) % 2 = 0)) := by
  have hm : (shiftIdx t hpos u d).val % 2 = (u.val + d) % 2 := shiftIdx_mod2 t hpos u d
  have hT : shiftIdx t hpos u d ∈ cycInt t hpos u L ↔ d < L := by
    rw [mem_cycInt_iff]
    constructor
    · rintro ⟨d', hd', heq⟩
      have := shiftIdx_inj_range t hpos u (by omega) hd heq
      omega
    · intro hlt; exact ⟨d, hlt, rfl⟩
  simp only [Finset.mem_symmDiff, evenSet, Finset.mem_filter, Finset.mem_univ, true_and, hm, hT]
  omega

lemma prevIdx_shiftIdx (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {k : ℕ} (hk : k < 6 * t) :
    prevIdx t hpos (shiftIdx t hpos u k) = shiftIdx t hpos u ((k + 6 * t - 1) % (6 * t)) := by
  apply nextIdx_inj t hpos
  rw [nextIdx_prevIdx, ← shiftIdx_one, shiftIdx_add]
  apply Fin.ext; dsimp [shiftIdx]
  rw [Nat.add_mod, Nat.add_mod (u.val) ((k + 6 * t - 1) % (6 * t) + 1)]
  congr 1
  rw [Nat.add_mod ((k + 6 * t - 1) % (6 * t)) 1, Nat.mod_mod, ← Nat.add_mod,
    show k + 6 * t - 1 + 1 = k + 6 * t by omega, Nat.add_mod_right]

lemma nextIdx_shiftIdx (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) (k : ℕ) :
    nextIdx t hpos (shiftIdx t hpos u k) = shiftIdx t hpos u ((k + 1) % (6 * t)) := by
  rw [← shiftIdx_one, shiftIdx_add]
  apply Fin.ext; dsimp [shiftIdx]
  rw [Nat.add_mod, Nat.add_mod u.val ((k + 1) % (6 * t)), Nat.mod_mod]

lemma odd_sing_mem_Vset (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ} (hLn : L < 6 * t)
    {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d + 2 ≤ L) (hm : (u.val + d) % 2 = 1) :
    Pi.single (shiftIdx t hpos u d) (1 : F2) ∈
      Vset t hpos (symmDiff (cycInt t hpos u L) (evenSet t)) := by
  apply single_mem_Vset
  · exact (mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨by omega, hm⟩)
  · rw [prevIdx_shiftIdx t hpos u (by omega)]
    have hmod : (d + 6 * t - 1) % (6 * t) = d - 1 := by
      rw [show d + 6 * t - 1 = (d - 1) + 6 * t by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hmod, mem_S_shift_iff t hpos u hLn (by omega)]; omega
  · rw [nextIdx_shiftIdx t hpos u d, Nat.mod_eq_of_lt (by omega : d + 1 < 6 * t),
      mem_S_shift_iff t hpos u hLn (by omega)]; omega

lemma even_sing_mem_Vset (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ} (hLn : L < 6 * t)
    {d : ℕ} (hd1 : L + 1 ≤ d) (hd2 : d + 2 ≤ 6 * t) (hm : (u.val + d) % 2 = 0) :
    Pi.single (shiftIdx t hpos u d) (1 : F2) ∈
      Vset t hpos (symmDiff (cycInt t hpos u L) (evenSet t)) := by
  apply single_mem_Vset
  · exact (mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inr ⟨by omega, hm⟩)
  · rw [prevIdx_shiftIdx t hpos u (by omega)]
    have hmod : (d + 6 * t - 1) % (6 * t) = d - 1 := by
      rw [show d + 6 * t - 1 = (d - 1) + 6 * t by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hmod, mem_S_shift_iff t hpos u hLn (by omega)]; omega
  · rw [nextIdx_shiftIdx t hpos u d, Nat.mod_eq_of_lt (by omega : d + 1 < 6 * t),
      mem_S_shift_iff t hpos u hLn (by omega)]; omega

lemma runVec_mem_Vset (t : ℕ) (hpos : 0 < t) (u : Fin (6 * t)) {L : ℕ}
    (hL5 : 5 ≤ L) (hLn5 : L ≤ 6 * t - 5) {d : ℕ} (hd : d < 6 * t)
    (hmem : shiftIdx t hpos u d ∈ symmDiff (cycInt t hpos u L) (evenSet t)) :
    runVec t hpos (symmDiff (cycInt t hpos u L) (evenSet t)) (shiftIdx t hpos u d) ∈
      Vset t hpos (symmDiff (cycInt t hpos u L) (evenSet t)) := by
  have hLn : L < 6 * t := by omega
  let S := symmDiff (cycInt t hpos u L) (evenSet t)
  unfold runVec
  split_ifs with h1 h2
  · have hni : shiftIdx t hpos u ((d + 1) % (6 * t)) ∈ S := by
      rwa [← nextIdx_shiftIdx t hpos u d]
    have hd_or : d = L - 1 ∨ d = 6 * t - 1 := by
      have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
      have hB := (mem_S_shift_iff t hpos u hLn (Nat.mod_lt _ (by omega))).mp hni
      by_cases hlast : d + 1 < 6 * t
      · rw [Nat.mod_eq_of_lt hlast] at hB; omega
      · right; omega
    apply pair_mem_Vset t hpos S _ hmem h1
    · rw [prevIdx_shiftIdx t hpos u hd, mem_S_shift_iff t hpos u hLn (Nat.mod_lt _ (by omega))]
      rcases hd_or with hd_eq | hd_eq
      · rw [hd_eq]
        have hm1 : (L - 1 + 6 * t - 1) % (6 * t) = L - 2 := by
          rw [show L - 1 + 6 * t - 1 = (L - 2) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hm1]
        have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
        rw [hd_eq] at hA; omega
      · rw [hd_eq]
        have hm1 : (6 * t - 1 + 6 * t - 1) % (6 * t) = 6 * t - 2 := by
          rw [show 6 * t - 1 + 6 * t - 1 = (6 * t - 2) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hm1]
        have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
        rw [hd_eq] at hA; omega
    · rw [nextIdx_shiftIdx t hpos u d, nextIdx_shiftIdx t hpos u _,
        mem_S_shift_iff t hpos u hLn (Nat.mod_lt _ (by omega))]
      rcases hd_or with hd_eq | hd_eq
      · rw [hd_eq]
        have hm1 : ((L - 1 + 1) % (6 * t) + 1) % (6 * t) = L + 1 := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ L),
            Nat.mod_eq_of_lt (show L < 6 * t by omega),
            Nat.mod_eq_of_lt (show L + 1 < 6 * t by omega)]
        rw [hm1]
        have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
        rw [hd_eq] at hA; omega
      · rw [hd_eq]
        have hm1 : ((6 * t - 1 + 1) % (6 * t) + 1) % (6 * t) = 1 := by
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self, zero_add,
            Nat.mod_eq_of_lt (by omega)]
        rw [hm1]
        have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
        rw [hd_eq] at hA; omega
  · have hpi : shiftIdx t hpos u ((d + 6 * t - 1) % (6 * t)) ∈ S := by
      rwa [← prevIdx_shiftIdx t hpos u hd]
    have hd_or : d = L ∨ d = 0 := by
      have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
      have hB := (mem_S_shift_iff t hpos u hLn (Nat.mod_lt _ (by omega))).mp hpi
      by_cases hz : d = 0
      · right; exact hz
      · have hmod : (d + 6 * t - 1) % (6 * t) = d - 1 := by
          rw [show d + 6 * t - 1 = (d - 1) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod] at hB; left; omega
    have hnp : nextIdx t hpos (prevIdx t hpos (shiftIdx t hpos u d)) = shiftIdx t hpos u d :=
      nextIdx_prevIdx t hpos _
    have hpr := pair_mem_Vset t hpos S (prevIdx t hpos (shiftIdx t hpos u d)) h2 (hnp.symm ▸ hmem)
    rw [hnp] at hpr
    apply hpr
    · rw [prevIdx_shiftIdx t hpos u hd, prevIdx_shiftIdx t hpos u (Nat.mod_lt _ (by omega)),
        mem_S_shift_iff t hpos u hLn (Nat.mod_lt _ (by omega))]
      rcases hd_or with hd_eq | hd_eq
      · rw [hd_eq]
        have hm1 : (L + 6 * t - 1) % (6 * t) = L - 1 := by
          rw [show L + 6 * t - 1 = (L - 1) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        have hm2 : (L - 1 + 6 * t - 1) % (6 * t) = L - 2 := by
          rw [show L - 1 + 6 * t - 1 = (L - 2) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hm1, hm2]
        have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
        rw [hd_eq] at hA; omega
      · rw [hd_eq]
        have hm1 : (0 + 6 * t - 1) % (6 * t) = 6 * t - 1 := by
          rw [zero_add, Nat.mod_eq_of_lt (by omega)]
        have hm2 : (6 * t - 1 + 6 * t - 1) % (6 * t) = 6 * t - 2 := by
          rw [show 6 * t - 1 + 6 * t - 1 = (6 * t - 2) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hm1, hm2]
        have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem
        rw [hd_eq] at hA; omega
    · exact h1
  · exact single_mem_Vset t hpos S _ hmem h2 h1

-- Clean span helpers on even/odd pairs
lemma even_pair_cancel (t : ℕ) (hpos : 0 < t) (se : Fin (6 * t)) (hse : se.val % 2 = 0)
    (target : Fin 4 → F2) (ht2 : target 2 = 0) (ht3 : target 3 = 0) :
    ∃ c0 c1 : F2, Hmap t (c0 • Pi.single se 1 + c1 • Pi.single (shiftIdx t hpos se 2) 1) = target := by
  have hse2 : (shiftIdx t hpos se 2).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  rcases hFn_pair_span_even t hpos se hse (target 0) (target 1) with ⟨c0, c1, hc0, hc1⟩
  refine ⟨c0, c1, ?_⟩
  ext b
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single]
  rcases fin4_cases b with rfl | rfl | rfl | rfl
  · simpa [mul_comm] using hc0
  · simpa [mul_comm] using hc1
  · rw [hFn_other_lane t se 2 (by omega), hFn_other_lane t (shiftIdx t hpos se 2) 2 (by omega), ht2]; ring
  · rw [hFn_other_lane t se 3 (by omega), hFn_other_lane t (shiftIdx t hpos se 2) 3 (by omega), ht3]; ring

lemma odd_pair_cancel (t : ℕ) (hpos : 0 < t) (so : Fin (6 * t)) (hso : so.val % 2 = 1)
    (target : Fin 4 → F2) (ht0 : target 0 = 0) (ht1 : target 1 = 0) :
    ∃ d0 d1 : F2, Hmap t (d0 • Pi.single so 1 + d1 • Pi.single (shiftIdx t hpos so 2) 1) = target := by
  have hso2 : (shiftIdx t hpos so 2).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  rcases hFn_pair_span_odd t hpos so hso (target 2) (target 3) with ⟨d0, d1, hd0, hd1⟩
  refine ⟨d0, d1, ?_⟩
  ext b
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single]
  rcases fin4_cases b with rfl | rfl | rfl | rfl
  · rw [hFn_other_lane t so 0 (by omega), hFn_other_lane t (shiftIdx t hpos so 2) 0 (by omega), ht0]; ring
  · rw [hFn_other_lane t so 1 (by omega), hFn_other_lane t (shiftIdx t hpos so 2) 1 (by omega), ht1]; ring
  · simpa [mul_comm] using hd0
  · simpa [mul_comm] using hd1

lemma both_pairs_cancel (t : ℕ) (hpos : 0 < t) (se so : Fin (6 * t))
    (hse : se.val % 2 = 0) (hso : so.val % 2 = 1) (target : Fin 4 → F2) :
    ∃ c0 c1 d0 d1 : F2,
      Hmap t (c0 • Pi.single se 1 + c1 • Pi.single (shiftIdx t hpos se 2) 1 +
              d0 • Pi.single so 1 + d1 • Pi.single (shiftIdx t hpos so 2) 1) = target := by
  have hse2 : (shiftIdx t hpos se 2).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  have hso2 : (shiftIdx t hpos so 2).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  rcases hFn_pair_span_even t hpos se hse (target 0) (target 1) with ⟨c0, c1, hc0, hc1⟩
  rcases hFn_pair_span_odd t hpos so hso (target 2) (target 3) with ⟨d0, d1, hd0, hd1⟩
  refine ⟨c0, c1, d0, d1, ?_⟩
  ext b
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single]
  rcases fin4_cases b with rfl | rfl | rfl | rfl
  · rw [hFn_other_lane t so 0 (by omega), hFn_other_lane t (shiftIdx t hpos so 2) 0 (by omega)]
    simpa [mul_comm] using hc0
  · rw [hFn_other_lane t so 1 (by omega), hFn_other_lane t (shiftIdx t hpos so 2) 1 (by omega)]
    simpa [mul_comm] using hc1
  · rw [hFn_other_lane t se 2 (by omega), hFn_other_lane t (shiftIdx t hpos se 2) 2 (by omega)]
    simpa [mul_comm] using hd0
  · rw [hFn_other_lane t se 3 (by omega), hFn_other_lane t (shiftIdx t hpos se 2) 3 (by omega)]
    simpa [mul_comm] using hd1

-- Case B: L = 5, u odd
lemma caseB_L5 (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t) (u : Fin (6 * t)) (hu1 : u.val % 2 = 1) :
    let S := symmDiff (cycInt t hpos u 5) (evenSet t)
    Function.Surjective ((Hmap t).comp (Vset t hpos S).subtype) ∧
    ∀ d < 6 * t, shiftIdx t hpos u d ∈ S → ∃ x ∈ GoodMax t hpos S, x (shiftIdx t hpos u d) ≠ 0 := by
  intro S
  have hLn : 5 < 6 * t := by omega
  have he1 : Pi.single (shiftIdx t hpos u 7) (1 : F2) ∈ Vset t hpos S :=
    even_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)
  have he2 : Pi.single (shiftIdx t hpos u 9) (1 : F2) ∈ Vset t hpos S :=
    even_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)
  have ho_mid : Pi.single (shiftIdx t hpos u 2) (1 : F2) ∈ Vset t hpos S :=
    odd_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)
  have hpair0 : Pi.single (shiftIdx t hpos u (6 * t - 1)) (1 : F2) +
      Pi.single (shiftIdx t hpos u 0) (1 : F2) ∈ Vset t hpos S := by
    have hmem := runVec_mem_Vset t hpos u (L := 5) (by omega) (by omega) (d := 0) (by omega)
      ((mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨by omega, by omega⟩))
    have h1 : nextIdx t hpos (shiftIdx t hpos u 0) ∉ S := by
      rw [nextIdx_shiftIdx, Nat.mod_eq_of_lt (by omega : 0 + 1 < 6 * t),
        mem_S_shift_iff t hpos u hLn (by omega)]; omega
    have h2 : prevIdx t hpos (shiftIdx t hpos u 0) = shiftIdx t hpos u (6 * t - 1) := by
      rw [prevIdx_shiftIdx t hpos u (by omega), zero_add, Nat.mod_eq_of_lt (by omega)]
    have h2m : prevIdx t hpos (shiftIdx t hpos u 0) ∈ S := by
      rw [h2, mem_S_shift_iff t hpos u hLn (by omega)]; omega
    have hrv : runVec t hpos S (shiftIdx t hpos u 0) =
        Pi.single (shiftIdx t hpos u (6 * t - 1)) 1 + Pi.single (shiftIdx t hpos u 0) 1 := by
      unfold runVec; rw [if_neg h1, if_pos h2m, h2]
    rwa [hrv] at hmem
  have hpairL : Pi.single (shiftIdx t hpos u 4) (1 : F2) +
      Pi.single (shiftIdx t hpos u 5) (1 : F2) ∈ Vset t hpos S := by
    have hmem := runVec_mem_Vset t hpos u (L := 5) (by omega) (by omega) (d := 4) (by omega)
      ((mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨by omega, by omega⟩))
    have hn : nextIdx t hpos (shiftIdx t hpos u 4) = shiftIdx t hpos u 5 := by
      rw [nextIdx_shiftIdx, Nat.mod_eq_of_lt (by omega : 4 + 1 < 6 * t)]
    have h1 : nextIdx t hpos (shiftIdx t hpos u 4) ∈ S := by
      rw [hn, mem_S_shift_iff t hpos u hLn (by omega)]; omega
    have hrv : runVec t hpos S (shiftIdx t hpos u 4) =
        Pi.single (shiftIdx t hpos u 4) 1 + Pi.single (shiftIdx t hpos u 5) 1 := by
      unfold runVec; rw [if_pos h1, hn]
    rwa [hrv] at hmem
  have h7m : (shiftIdx t hpos u 7).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  have h79 : shiftIdx t hpos (shiftIdx t hpos u 7) 2 = shiftIdx t hpos u 9 := by rw [shiftIdx_add]
  have hm_last : (shiftIdx t hpos u (6 * t - 1)).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  have hm_5 : (shiftIdx t hpos u 5).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
  constructor
  · intro target
    have h0m : (shiftIdx t hpos u 0).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
    have h02 : shiftIdx t hpos (shiftIdx t hpos u 0) 2 = shiftIdx t hpos u 2 := by rw [shiftIdx_add]
    rcases hFn_pair_span_odd t hpos (shiftIdx t hpos u 0) h0m (target 2) (target 3) with ⟨d0, d1, hd0, hd1⟩
    rw [h02] at hd0 hd1
    let yOdd : Fin (6 * t) → F2 :=
      d0 • (Pi.single (shiftIdx t hpos u (6 * t - 1)) 1 + Pi.single (shiftIdx t hpos u 0) 1) +
      d1 • Pi.single (shiftIdx t hpos u 2) 1
    have hyOdd_V : yOdd ∈ Vset t hpos S :=
      Submodule.add_mem _ (Submodule.smul_mem _ d0 hpair0) (Submodule.smul_mem _ d1 ho_mid)
    have hrem2 : (target + Hmap t yOdd) 2 = 0 := by
      have hz := hFn_other_lane t (shiftIdx t hpos u (6 * t - 1)) 2 (by omega)
      simp only [yOdd, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single,
        hz, zero_add]
      calc target 2 + (d0 * hFn t (shiftIdx t hpos u 0) 2 + d1 * hFn t (shiftIdx t hpos u 2) 2)
          = target 2 + (hFn t (shiftIdx t hpos u 0) 2 * d0 + hFn t (shiftIdx t hpos u 2) 2 * d1) := by ring
        _ = target 2 + target 2 := by rw [hd0]
        _ = 0 := zmod2_add_self _
    have hrem3 : (target + Hmap t yOdd) 3 = 0 := by
      have hz := hFn_other_lane t (shiftIdx t hpos u (6 * t - 1)) 3 (by omega)
      simp only [yOdd, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single,
        hz, zero_add]
      calc target 3 + (d0 * hFn t (shiftIdx t hpos u 0) 3 + d1 * hFn t (shiftIdx t hpos u 2) 3)
          = target 3 + (hFn t (shiftIdx t hpos u 0) 3 * d0 + hFn t (shiftIdx t hpos u 2) 3 * d1) := by ring
        _ = target 3 + target 3 := by rw [hd1]
        _ = 0 := zmod2_add_self _
    rcases even_pair_cancel t hpos (shiftIdx t hpos u 7) h7m (target + Hmap t yOdd) hrem2 hrem3 with
      ⟨c0, c1, hc⟩
    rw [h79] at hc
    let xV : Fin (6 * t) → F2 :=
      yOdd + (c0 • Pi.single (shiftIdx t hpos u 7) 1 + c1 • Pi.single (shiftIdx t hpos u 9) 1)
    have hxV : xV ∈ Vset t hpos S :=
      Submodule.add_mem _ hyOdd_V
        (Submodule.add_mem _ (Submodule.smul_mem _ c0 he1) (Submodule.smul_mem _ c1 he2))
    refine ⟨⟨xV, hxV⟩, ?_⟩
    change Hmap t xV = target
    have hx1 : Hmap t xV = Hmap t yOdd + (target + Hmap t yOdd) := by
      simp only [xV, map_add, hc]
    rw [hx1]; ext b; simp only [Pi.add_apply]
    calc Hmap t yOdd b + (target b + Hmap t yOdd b)
        = target b + (Hmap t yOdd b + Hmap t yOdd b) := by ring
      _ = target b := by rw [zmod2_add_self, add_zero]
  · let wOdd : Fin (6 * t) → F2 :=
      (Pi.single (shiftIdx t hpos u (6 * t - 1)) 1 + Pi.single (shiftIdx t hpos u 0) 1) +
      Pi.single (shiftIdx t hpos u 2) 1 +
      (Pi.single (shiftIdx t hpos u 4) 1 + Pi.single (shiftIdx t hpos u 5) 1)
    have hwOdd_V : wOdd ∈ Vset t hpos S :=
      Submodule.add_mem _ (Submodule.add_mem _ hpair0 ho_mid) hpairL
    have hwOdd_2 : Hmap t wOdd 2 = 0 := by
      have hz1 := hFn_other_lane t (shiftIdx t hpos u (6 * t - 1)) 2 (by omega)
      have hz5 := hFn_other_lane t (shiftIdx t hpos u 5) 2 (by omega)
      have hs2 : shiftIdx t hpos (shiftIdx t hpos u 0) 2 = shiftIdx t hpos u 2 := by rw [shiftIdx_add]
      have hs4 : shiftIdx t hpos (shiftIdx t hpos u 0) 4 = shiftIdx t hpos u 4 := by rw [shiftIdx_add]
      simp only [wOdd, map_add, Pi.add_apply, Hmap_single, hz1, hz5, zero_add, add_zero]
      rw [← hs2, ← hs4]; exact hFn_sum_triple t hpos (shiftIdx t hpos u 0) 2
    have hwOdd_3 : Hmap t wOdd 3 = 0 := by
      have hz1 := hFn_other_lane t (shiftIdx t hpos u (6 * t - 1)) 3 (by omega)
      have hz5 := hFn_other_lane t (shiftIdx t hpos u 5) 3 (by omega)
      have hs2 : shiftIdx t hpos (shiftIdx t hpos u 0) 2 = shiftIdx t hpos u 2 := by rw [shiftIdx_add]
      have hs4 : shiftIdx t hpos (shiftIdx t hpos u 0) 4 = shiftIdx t hpos u 4 := by rw [shiftIdx_add]
      simp only [wOdd, map_add, Pi.add_apply, Hmap_single, hz1, hz5, zero_add, add_zero]
      rw [← hs2, ← hs4]; exact hFn_sum_triple t hpos (shiftIdx t hpos u 0) 3
    rcases even_pair_cancel t hpos (shiftIdx t hpos u 7) h7m (Hmap t wOdd) hwOdd_2 hwOdd_3 with
      ⟨c0, c1, hc⟩
    rw [h79] at hc
    let xOdd : Fin (6 * t) → F2 :=
      wOdd + (c0 • Pi.single (shiftIdx t hpos u 7) 1 + c1 • Pi.single (shiftIdx t hpos u 9) 1)
    have hxOdd_G : xOdd ∈ GoodMax t hpos S := by
      refine ⟨Submodule.add_mem _ hwOdd_V
        (Submodule.add_mem _ (Submodule.smul_mem _ c0 he1) (Submodule.smul_mem _ c1 he2)), ?_⟩
      change Hmap t xOdd = 0
      rw [show Hmap t xOdd = Hmap t wOdd + Hmap t wOdd by simp only [xOdd, map_add, hc]]
      ext b; exact zmod2_add_self _
    intro d hd hmem
    have hd_cases : d = 0 ∨ d = 2 ∨ d = 4 ∨ d = 5 ∨ d = 6 * t - 1 ∨
        (7 ≤ d ∧ d + 2 ≤ 6 * t ∧ (u.val + d) % 2 = 0) := by
      have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem; omega
    have hne : ∀ a b, a < 6 * t → b < 6 * t → a ≠ b → shiftIdx t hpos u a ≠ shiftIdx t hpos u b :=
      fun a b ha hb hab h => hab (shiftIdx_inj_range t hpos u ha hb h)
    rcases hd_cases with rfl | rfl | rfl | rfl | rfl | ⟨hd7, hdend, hdm⟩
    · refine ⟨xOdd, hxOdd_G, ?_⟩
      simp [xOdd, wOdd, Pi.single_eq_of_ne (hne 0 (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 4 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 5 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 7 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 9 (by omega) (by omega) (by omega))]
    · refine ⟨xOdd, hxOdd_G, ?_⟩
      simp [xOdd, wOdd, Pi.single_eq_of_ne (hne 2 (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 2 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 2 4 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 2 5 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 2 7 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 2 9 (by omega) (by omega) (by omega))]
    · refine ⟨xOdd, hxOdd_G, ?_⟩
      simp [xOdd, wOdd, Pi.single_eq_of_ne (hne 4 (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 4 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 4 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 4 5 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 4 7 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 4 9 (by omega) (by omega) (by omega))]
    · refine ⟨xOdd, hxOdd_G, ?_⟩
      simp [xOdd, wOdd, Pi.single_eq_of_ne (hne 5 (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 5 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 5 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 5 4 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 5 7 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 5 9 (by omega) (by omega) (by omega))]
    · refine ⟨xOdd, hxOdd_G, ?_⟩
      simp [xOdd, wOdd, Pi.single_eq_of_ne (hne (6 * t - 1) 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 4 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 5 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 7 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 9 (by omega) (by omega) (by omega))]
    · let baseD : ℕ := if d + 4 ≤ 6 * t - 2 then d else d - 4
      have hbd_lo : 7 ≤ baseD := by dsimp [baseD]; split_ifs <;> omega
      have hbd_hi : baseD + 6 ≤ 6 * t := by dsimp [baseD]; split_ifs <;> omega
      have hbd_m : (u.val + baseD) % 2 = 0 := by dsimp [baseD]; split_ifs <;> omega
      let xTri : Fin (6 * t) → F2 :=
        Pi.single (shiftIdx t hpos u baseD) 1 +
        Pi.single (shiftIdx t hpos u (baseD + 2)) 1 +
        Pi.single (shiftIdx t hpos u (baseD + 4)) 1
      have hxTri_G : xTri ∈ GoodMax t hpos S := by
        refine ⟨Submodule.add_mem _ (Submodule.add_mem _
          (even_sing_mem_Vset t hpos u hLn (by omega) (by omega) hbd_m)
          (even_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)))
          (even_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)), ?_⟩
        ext b
        simp only [xTri, map_add, Pi.add_apply, Hmap_single, LinearMap.zero_apply]
        have h2 : shiftIdx t hpos (shiftIdx t hpos u baseD) 2 = shiftIdx t hpos u (baseD + 2) := by
          rw [shiftIdx_add]
        have h4 : shiftIdx t hpos (shiftIdx t hpos u baseD) 4 = shiftIdx t hpos u (baseD + 4) := by
          rw [shiftIdx_add]
        rw [← h2, ← h4]; exact hFn_sum_triple t hpos (shiftIdx t hpos u baseD) b
      refine ⟨xTri, hxTri_G, ?_⟩
      have hd_eq : d = baseD ∨ d = baseD + 4 := by dsimp [baseD]; split_ifs <;> omega
      rcases hd_eq with hd_eq | hd_eq
      · rw [hd_eq]
        simp [xTri, Pi.single_eq_of_ne (hne baseD (baseD + 2) (by omega) (by omega) (by omega)),
          Pi.single_eq_of_ne (hne baseD (baseD + 4) (by omega) (by omega) (by omega))]
      · rw [hd_eq]
        simp [xTri, Pi.single_eq_of_ne (hne (baseD + 4) baseD (by omega) (by omega) (by omega)),
          Pi.single_eq_of_ne (hne (baseD + 4) (baseD + 2) (by omega) (by omega) (by omega))]

-- Case C: L = 6*t - 5, u odd
lemma caseC_L6t5 (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t) (u : Fin (6 * t)) (hu1 : u.val % 2 = 1) :
    let S := symmDiff (cycInt t hpos u (6 * t - 5)) (evenSet t)
    Function.Surjective ((Hmap t).comp (Vset t hpos S).subtype) ∧
    ∀ d < 6 * t, shiftIdx t hpos u d ∈ S → ∃ x ∈ GoodMax t hpos S, x (shiftIdx t hpos u d) ≠ 0 := by
  intro S
  have hLn : 6 * t - 5 < 6 * t := by omega
  have ho1 : Pi.single (shiftIdx t hpos u 2) (1 : F2) ∈ Vset t hpos S :=
    odd_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)
  have ho2 : Pi.single (shiftIdx t hpos u 4) (1 : F2) ∈ Vset t hpos S :=
    odd_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)
  have he_mid : Pi.single (shiftIdx t hpos u (6 * t - 3)) (1 : F2) ∈ Vset t hpos S :=
    even_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)
  have hpair0 : Pi.single (shiftIdx t hpos u (6 * t - 1)) (1 : F2) +
      Pi.single (shiftIdx t hpos u 0) (1 : F2) ∈ Vset t hpos S := by
    have hmem := runVec_mem_Vset t hpos u (L := 6 * t - 5) (by omega) (by omega) (d := 0) (by omega)
      ((mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨by omega, by omega⟩))
    have h1 : nextIdx t hpos (shiftIdx t hpos u 0) ∉ S := by
      rw [nextIdx_shiftIdx, Nat.mod_eq_of_lt (by omega : 0 + 1 < 6 * t),
        mem_S_shift_iff t hpos u hLn (by omega)]; omega
    have h2 : prevIdx t hpos (shiftIdx t hpos u 0) = shiftIdx t hpos u (6 * t - 1) := by
      rw [prevIdx_shiftIdx t hpos u (by omega), zero_add, Nat.mod_eq_of_lt (by omega)]
    have h2m : prevIdx t hpos (shiftIdx t hpos u 0) ∈ S := by
      rw [h2, mem_S_shift_iff t hpos u hLn (by omega)]; omega
    have hrv : runVec t hpos S (shiftIdx t hpos u 0) =
        Pi.single (shiftIdx t hpos u (6 * t - 1)) 1 + Pi.single (shiftIdx t hpos u 0) 1 := by
      unfold runVec; rw [if_neg h1, if_pos h2m, h2]
    rwa [hrv] at hmem
  have hpairL : Pi.single (shiftIdx t hpos u (6 * t - 6)) (1 : F2) +
      Pi.single (shiftIdx t hpos u (6 * t - 5)) (1 : F2) ∈ Vset t hpos S := by
    have hmem := runVec_mem_Vset t hpos u (L := 6 * t - 5) (by omega) (by omega)
      (d := 6 * t - 6) (by omega)
      ((mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨by omega, by omega⟩))
    have hn : nextIdx t hpos (shiftIdx t hpos u (6 * t - 6)) = shiftIdx t hpos u (6 * t - 5) := by
      rw [nextIdx_shiftIdx, show 6 * t - 6 + 1 = 6 * t - 5 by omega, Nat.mod_eq_of_lt (by omega)]
    have h1 : nextIdx t hpos (shiftIdx t hpos u (6 * t - 6)) ∈ S := by
      rw [hn, mem_S_shift_iff t hpos u hLn (by omega)]; omega
    have hrv : runVec t hpos S (shiftIdx t hpos u (6 * t - 6)) =
        Pi.single (shiftIdx t hpos u (6 * t - 6)) 1 + Pi.single (shiftIdx t hpos u (6 * t - 5)) 1 := by
      unfold runVec; rw [if_pos h1, hn]
    rwa [hrv] at hmem
  have h2m : (shiftIdx t hpos u 2).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  have h24 : shiftIdx t hpos (shiftIdx t hpos u 2) 2 = shiftIdx t hpos u 4 := by rw [shiftIdx_add]
  have hm6 : (shiftIdx t hpos u (6 * t - 6)).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  have hm0 : (shiftIdx t hpos u 0).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
  constructor
  · intro target
    have he0m : (shiftIdx t hpos u (6 * t - 5)).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
    have he2eq : shiftIdx t hpos (shiftIdx t hpos u (6 * t - 5)) 2 =
        shiftIdx t hpos u (6 * t - 3) := by rw [shiftIdx_add]; congr 1; omega
    rcases hFn_pair_span_even t hpos (shiftIdx t hpos u (6 * t - 5)) he0m (target 0) (target 1) with
      ⟨c0, c1, hc0, hc1⟩
    rw [he2eq] at hc0 hc1
    let yEv : Fin (6 * t) → F2 :=
      c0 • (Pi.single (shiftIdx t hpos u (6 * t - 6)) 1 +
            Pi.single (shiftIdx t hpos u (6 * t - 5)) 1) +
      c1 • Pi.single (shiftIdx t hpos u (6 * t - 3)) 1
    have hyEv_V : yEv ∈ Vset t hpos S :=
      Submodule.add_mem _ (Submodule.smul_mem _ c0 hpairL) (Submodule.smul_mem _ c1 he_mid)
    have hrem0 : (target + Hmap t yEv) 0 = 0 := by
      have hz := hFn_other_lane t (shiftIdx t hpos u (6 * t - 6)) 0 (by omega)
      simp only [yEv, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single,
        hz, zero_add]
      calc target 0 + (c0 * hFn t (shiftIdx t hpos u (6 * t - 5)) 0 +
            c1 * hFn t (shiftIdx t hpos u (6 * t - 3)) 0)
          = target 0 + (hFn t (shiftIdx t hpos u (6 * t - 5)) 0 * c0 +
            hFn t (shiftIdx t hpos u (6 * t - 3)) 0 * c1) := by ring
        _ = target 0 + target 0 := by rw [hc0]
        _ = 0 := zmod2_add_self _
    have hrem1 : (target + Hmap t yEv) 1 = 0 := by
      have hz := hFn_other_lane t (shiftIdx t hpos u (6 * t - 6)) 1 (by omega)
      simp only [yEv, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Hmap_single,
        hz, zero_add]
      calc target 1 + (c0 * hFn t (shiftIdx t hpos u (6 * t - 5)) 1 +
            c1 * hFn t (shiftIdx t hpos u (6 * t - 3)) 1)
          = target 1 + (hFn t (shiftIdx t hpos u (6 * t - 5)) 1 * c0 +
            hFn t (shiftIdx t hpos u (6 * t - 3)) 1 * c1) := by ring
        _ = target 1 + target 1 := by rw [hc1]
        _ = 0 := zmod2_add_self _
    rcases odd_pair_cancel t hpos (shiftIdx t hpos u 2) h2m (target + Hmap t yEv) hrem0 hrem1 with
      ⟨d0, d1, hd⟩
    rw [h24] at hd
    let xV : Fin (6 * t) → F2 :=
      yEv + (d0 • Pi.single (shiftIdx t hpos u 2) 1 + d1 • Pi.single (shiftIdx t hpos u 4) 1)
    have hxV : xV ∈ Vset t hpos S :=
      Submodule.add_mem _ hyEv_V
        (Submodule.add_mem _ (Submodule.smul_mem _ d0 ho1) (Submodule.smul_mem _ d1 ho2))
    refine ⟨⟨xV, hxV⟩, ?_⟩
    change Hmap t xV = target
    rw [show Hmap t xV = Hmap t yEv + (target + Hmap t yEv) by simp only [xV, map_add, hd]]
    ext b; simp only [Pi.add_apply]
    calc Hmap t yEv b + (target b + Hmap t yEv b)
        = target b + (Hmap t yEv b + Hmap t yEv b) := by ring
      _ = target b := by rw [zmod2_add_self, add_zero]
  · let wEv : Fin (6 * t) → F2 :=
      (Pi.single (shiftIdx t hpos u (6 * t - 6)) 1 +
       Pi.single (shiftIdx t hpos u (6 * t - 5)) 1) +
      Pi.single (shiftIdx t hpos u (6 * t - 3)) 1 +
      (Pi.single (shiftIdx t hpos u (6 * t - 1)) 1 + Pi.single (shiftIdx t hpos u 0) 1)
    have hwEv_V : wEv ∈ Vset t hpos S :=
      Submodule.add_mem _ (Submodule.add_mem _ hpairL he_mid) hpair0
    have hwEv_0 : Hmap t wEv 0 = 0 := by
      have hz6 := hFn_other_lane t (shiftIdx t hpos u (6 * t - 6)) 0 (by omega)
      have hz0 := hFn_other_lane t (shiftIdx t hpos u 0) 0 (by omega)
      have hs2 : shiftIdx t hpos (shiftIdx t hpos u (6 * t - 5)) 2 =
          shiftIdx t hpos u (6 * t - 3) := by rw [shiftIdx_add]; congr 1; omega
      have hs4 : shiftIdx t hpos (shiftIdx t hpos u (6 * t - 5)) 4 =
          shiftIdx t hpos u (6 * t - 1) := by rw [shiftIdx_add]; congr 1; omega
      simp only [wEv, map_add, Pi.add_apply, Hmap_single, hz6, hz0, zero_add, add_zero]
      rw [← hs2, ← hs4]; exact hFn_sum_triple t hpos (shiftIdx t hpos u (6 * t - 5)) 0
    have hwEv_1 : Hmap t wEv 1 = 0 := by
      have hz6 := hFn_other_lane t (shiftIdx t hpos u (6 * t - 6)) 1 (by omega)
      have hz0 := hFn_other_lane t (shiftIdx t hpos u 0) 1 (by omega)
      have hs2 : shiftIdx t hpos (shiftIdx t hpos u (6 * t - 5)) 2 =
          shiftIdx t hpos u (6 * t - 3) := by rw [shiftIdx_add]; congr 1; omega
      have hs4 : shiftIdx t hpos (shiftIdx t hpos u (6 * t - 5)) 4 =
          shiftIdx t hpos u (6 * t - 1) := by rw [shiftIdx_add]; congr 1; omega
      simp only [wEv, map_add, Pi.add_apply, Hmap_single, hz6, hz0, zero_add, add_zero]
      rw [← hs2, ← hs4]; exact hFn_sum_triple t hpos (shiftIdx t hpos u (6 * t - 5)) 1
    rcases odd_pair_cancel t hpos (shiftIdx t hpos u 2) h2m (Hmap t wEv) hwEv_0 hwEv_1 with
      ⟨d0, d1, hd⟩
    rw [h24] at hd
    let xEv : Fin (6 * t) → F2 :=
      wEv + (d0 • Pi.single (shiftIdx t hpos u 2) 1 + d1 • Pi.single (shiftIdx t hpos u 4) 1)
    have hxEv_G : xEv ∈ GoodMax t hpos S := by
      refine ⟨Submodule.add_mem _ hwEv_V
        (Submodule.add_mem _ (Submodule.smul_mem _ d0 ho1) (Submodule.smul_mem _ d1 ho2)), ?_⟩
      change Hmap t xEv = 0
      rw [show Hmap t xEv = Hmap t wEv + Hmap t wEv by simp only [xEv, map_add, hd]]
      ext b; exact zmod2_add_self _
    intro d hd hmem
    have hd_cases : d = 0 ∨ d = 6 * t - 6 ∨ d = 6 * t - 5 ∨ d = 6 * t - 3 ∨ d = 6 * t - 1 ∨
        (2 ≤ d ∧ d + 2 ≤ 6 * t - 5 ∧ (u.val + d) % 2 = 1) := by
      have hA := (mem_S_shift_iff t hpos u hLn hd).mp hmem; omega
    have hne : ∀ a b, a < 6 * t → b < 6 * t → a ≠ b → shiftIdx t hpos u a ≠ shiftIdx t hpos u b :=
      fun a b ha hb hab h => hab (shiftIdx_inj_range t hpos u ha hb h)
    rcases hd_cases with rfl | rfl | rfl | rfl | rfl | ⟨hd2, hdend, hdm⟩
    · refine ⟨xEv, hxEv_G, ?_⟩
      simp [xEv, wEv, Pi.single_eq_of_ne (hne 0 (6 * t - 6) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 (6 * t - 5) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 (6 * t - 3) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne 0 4 (by omega) (by omega) (by omega))]
    · refine ⟨xEv, hxEv_G, ?_⟩
      simp [xEv, wEv, Pi.single_eq_of_ne (hne (6 * t - 6) 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 6) (6 * t - 5) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 6) (6 * t - 3) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 6) (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 6) 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 6) 4 (by omega) (by omega) (by omega))]
    · refine ⟨xEv, hxEv_G, ?_⟩
      simp [xEv, wEv, Pi.single_eq_of_ne (hne (6 * t - 5) 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 5) (6 * t - 6) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 5) (6 * t - 3) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 5) (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 5) 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 5) 4 (by omega) (by omega) (by omega))]
    · refine ⟨xEv, hxEv_G, ?_⟩
      simp [xEv, wEv, Pi.single_eq_of_ne (hne (6 * t - 3) 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 3) (6 * t - 6) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 3) (6 * t - 5) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 3) (6 * t - 1) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 3) 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 3) 4 (by omega) (by omega) (by omega))]
    · refine ⟨xEv, hxEv_G, ?_⟩
      simp [xEv, wEv, Pi.single_eq_of_ne (hne (6 * t - 1) 0 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) (6 * t - 6) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) (6 * t - 5) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) (6 * t - 3) (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 2 (by omega) (by omega) (by omega)),
        Pi.single_eq_of_ne (hne (6 * t - 1) 4 (by omega) (by omega) (by omega))]
    · let baseD : ℕ := if d + 4 ≤ 6 * t - 7 then d else d - 4
      have hbd_lo : 2 ≤ baseD := by dsimp [baseD]; split_ifs <;> omega
      have hbd_hi : baseD + 6 ≤ 6 * t - 5 := by dsimp [baseD]; split_ifs <;> omega
      have hbd_m : (u.val + baseD) % 2 = 1 := by dsimp [baseD]; split_ifs <;> omega
      let xTri : Fin (6 * t) → F2 :=
        Pi.single (shiftIdx t hpos u baseD) 1 +
        Pi.single (shiftIdx t hpos u (baseD + 2)) 1 +
        Pi.single (shiftIdx t hpos u (baseD + 4)) 1
      have hxTri_G : xTri ∈ GoodMax t hpos S := by
        refine ⟨Submodule.add_mem _ (Submodule.add_mem _
          (odd_sing_mem_Vset t hpos u hLn (by omega) (by omega) hbd_m)
          (odd_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)))
          (odd_sing_mem_Vset t hpos u hLn (by omega) (by omega) (by omega)), ?_⟩
        ext b
        simp only [xTri, map_add, Pi.add_apply, Hmap_single, LinearMap.zero_apply]
        have h2 : shiftIdx t hpos (shiftIdx t hpos u baseD) 2 = shiftIdx t hpos u (baseD + 2) := by
          rw [shiftIdx_add]
        have h4 : shiftIdx t hpos (shiftIdx t hpos u baseD) 4 = shiftIdx t hpos u (baseD + 4) := by
          rw [shiftIdx_add]
        rw [← h2, ← h4]; exact hFn_sum_triple t hpos (shiftIdx t hpos u baseD) b
      refine ⟨xTri, hxTri_G, ?_⟩
      have hd_eq : d = baseD ∨ d = baseD + 4 := by dsimp [baseD]; split_ifs <;> omega
      rcases hd_eq with hd_eq | hd_eq
      · rw [hd_eq]
        simp [xTri, Pi.single_eq_of_ne (hne baseD (baseD + 2) (by omega) (by omega) (by omega)),
          Pi.single_eq_of_ne (hne baseD (baseD + 4) (by omega) (by omega) (by omega))]
      · rw [hd_eq]
        simp [xTri, Pi.single_eq_of_ne (hne (baseD + 4) baseD (by omega) (by omega) (by omega)),
          Pi.single_eq_of_ne (hne (baseD + 4) (baseD + 2) (by omega) (by omega) (by omega))]

-- Case A: neither (L=5 ∧ u odd) nor (L=6*t-5 ∧ u odd), so both lanes have 2 consecutive singletons
lemma caseA_both_pairs (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t) (u : Fin (6 * t)) {L : ℕ}
    (hL5 : 5 ≤ L) (hLn5 : L ≤ 6 * t - 5)
    (hs0 : 3 ≤ sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 0)
    (hs1 : 3 ≤ sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 1)
    (hnotO : ¬ (L = 5 ∧ u.val % 2 = 1))
    (hnotE : ¬ (L = 6 * t - 5 ∧ u.val % 2 = 1)) :
    let S := symmDiff (cycInt t hpos u L) (evenSet t)
    Function.Surjective ((Hmap t).comp (Vset t hpos S).subtype) ∧
    ∀ d < 6 * t, shiftIdx t hpos u d ∈ S → ∃ x ∈ GoodMax t hpos S, x (shiftIdx t hpos u d) ≠ 0 := by
  intro S
  have hLn : L < 6 * t := by omega
  have hsites := sites_symmDiff_cycInt t hpos u hLn
  have hsing_odd : ∀ k < L, (u.val + k) % 2 = 1 →
      (k = 0 → u.val % 2 = 0) → (k = L - 1 → (u.val + L) % 2 = 1) →
      Pi.single (shiftIdx t hpos u k) (1 : F2) ∈ Vset t hpos S := by
    intro k hkL hkm hk0 hkL1
    apply single_mem_Vset
    · exact (mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨hkL, hkm⟩)
    · by_cases h0 : k = 0
      · exfalso; have := hk0 h0; omega
      · rw [prevIdx_shiftIdx t hpos u (by omega)]
        have hmod : (k + 6 * t - 1) % (6 * t) = k - 1 := by
          rw [show k + 6 * t - 1 = (k - 1) + 6 * t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod, mem_S_shift_iff t hpos u hLn (by omega)]; omega
    · rw [nextIdx_shiftIdx t hpos u k, Nat.mod_eq_of_lt (by omega : k + 1 < 6 * t),
        mem_S_shift_iff t hpos u hLn (by omega)]
      by_cases hlast : k = L - 1
      · have := hkL1 hlast; omega
      · omega
  have hsing_even : ∀ k, L ≤ k → k < 6 * t → (u.val + k) % 2 = 0 →
      (k = L → (u.val + L) % 2 = 1) → (k = 6 * t - 1 → u.val % 2 = 0) →
      Pi.single (shiftIdx t hpos u k) (1 : F2) ∈ Vset t hpos S := by
    intro k hkL hkn hkm hkL0 hkEnd
    apply single_mem_Vset
    · exact (mem_S_shift_iff t hpos u hLn hkn).mpr (Or.inr ⟨hkL, hkm⟩)
    · rw [prevIdx_shiftIdx t hpos u hkn]
      have hmod : (k + 6 * t - 1) % (6 * t) = k - 1 := by
        rw [show k + 6 * t - 1 = (k - 1) + 6 * t by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hmod, mem_S_shift_iff t hpos u hLn (by omega)]
      by_cases hfirst : k = L
      · have := hkL0 hfirst; omega
      · omega
    · by_cases hlast : k = 6 * t - 1
      · exfalso; have := hkEnd hlast; omega
      · rw [nextIdx_shiftIdx t hpos u k, Nat.mod_eq_of_lt (by omega : k + 1 < 6 * t),
          mem_S_shift_iff t hpos u hLn (by omega)]; omega
  let dO1 : ℕ := if u.val % 2 = 0 then 1 else 2
  let dE1 : ℕ := if (u.val + L) % 2 = 1 then L + 1 else L + 2
  have hdO1_b : 1 ≤ dO1 ∧ dO1 + 2 < L ∧ (u.val + dO1) % 2 = 1 := by
    dsimp [dO1]; split_ifs <;> omega
  have hdE1_b : L + 1 ≤ dE1 ∧ dE1 + 2 < 6 * t ∧ (u.val + dE1) % 2 = 0 := by
    dsimp [dE1]; split_ifs <;> omega
  have hdO_sing0 : Pi.single (shiftIdx t hpos u dO1) (1 : F2) ∈ Vset t hpos S :=
    hsing_odd dO1 (by omega) hdO1_b.2.2 (by omega) (by omega)
  have hdO_sing2 : Pi.single (shiftIdx t hpos u (dO1 + 2)) (1 : F2) ∈ Vset t hpos S :=
    hsing_odd (dO1 + 2) hdO1_b.2.1 (by omega) (by omega) (fun hlast => by
      dsimp [dO1] at hlast; split_ifs at hlast <;> omega)
  have hdE_sing0 : Pi.single (shiftIdx t hpos u dE1) (1 : F2) ∈ Vset t hpos S :=
    hsing_even dE1 (by omega) (by omega) hdE1_b.2.2 (by omega) (by omega)
  have hdE_sing2 : Pi.single (shiftIdx t hpos u (dE1 + 2)) (1 : F2) ∈ Vset t hpos S :=
    hsing_even (dE1 + 2) (by omega) hdE1_b.2.1 (by omega) (by omega) (fun hlast => by
      dsimp [dE1] at hlast; split_ifs at hlast <;> omega)
  let se := shiftIdx t hpos u dE1
  let so := shiftIdx t hpos u dO1
  have hse_m : se.val % 2 = 0 := by rw [shiftIdx_mod2]; exact hdE1_b.2.2
  have hso_m : so.val % 2 = 1 := by rw [shiftIdx_mod2]; exact hdO1_b.2.2
  have hse2_eq : shiftIdx t hpos se 2 = shiftIdx t hpos u (dE1 + 2) := by rw [shiftIdx_add]
  have hso2_eq : shiftIdx t hpos so 2 = shiftIdx t hpos u (dO1 + 2) := by rw [shiftIdx_add]
  constructor
  · intro target
    rcases both_pairs_cancel t hpos se so hse_m hso_m target with ⟨c0, c1, d0, d1, hc⟩
    refine ⟨⟨c0 • Pi.single se 1 + c1 • Pi.single (shiftIdx t hpos se 2) 1 +
      d0 • Pi.single so 1 + d1 • Pi.single (shiftIdx t hpos so 2) 1,
      Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ c0 hdE_sing0)
        (Submodule.smul_mem _ c1 (hse2_eq ▸ hdE_sing2)))
        (Submodule.smul_mem _ d0 hdO_sing0))
        (Submodule.smul_mem _ d1 (hso2_eq ▸ hdO_sing2))⟩, hc⟩
  · -- Witness xE3 for {se, se+2}
    let dE3 : ℕ := if dE1 + 4 < 6 * t then dE1 + 4 else dE1 - 2
    have hdE3_b : L ≤ dE3 ∧ dE3 < 6 * t ∧ (u.val + dE3) % 2 = 0 := by
      dsimp [dE3, dE1]; split_ifs <;> omega
    have hdE3_S : shiftIdx t hpos u dE3 ∈ S :=
      (mem_S_shift_iff t hpos u hLn hdE3_b.2.1).mpr (Or.inr ⟨hdE3_b.1, hdE3_b.2.2⟩)
    let wE3 : Fin (6 * t) → F2 :=
      Pi.single se 1 + Pi.single (shiftIdx t hpos se 2) 1 + runVec t hpos S (shiftIdx t hpos u dE3)
    have hwE3_V : wE3 ∈ Vset t hpos S :=
      Submodule.add_mem _ (Submodule.add_mem _ hdE_sing0 (hse2_eq ▸ hdE_sing2))
        (runVec_mem_Vset t hpos u hL5 hLn5 hdE3_b.2.1 hdE3_S)
    have hrv_even : ∀ b : Fin 4, b.val / 2 = 0 →
        Hmap t (runVec t hpos S (shiftIdx t hpos u dE3)) b = hFn t (shiftIdx t hpos u dE3) b := by
      intro b hb
      unfold runVec
      have hnm : (nextIdx t hpos (shiftIdx t hpos u dE3)).val % 2 = 1 := by
        rw [nextIdx_mod2, shiftIdx_mod2]; omega
      have hpm : (prevIdx t hpos (shiftIdx t hpos u dE3)).val % 2 = 1 := by
        have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u dE3))
        rw [nextIdx_prevIdx, shiftIdx_mod2] at this; omega
      have h0n := hFn_other_lane t (nextIdx t hpos (shiftIdx t hpos u dE3)) b (by omega)
      have h0p := hFn_other_lane t (prevIdx t hpos (shiftIdx t hpos u dE3)) b (by omega)
      split_ifs
      · simp [map_add, Hmap_single, h0n]
      · simp [map_add, Hmap_single, h0p]
      · simp [Hmap_single]
    have hwE3_01 : ∀ b : Fin 4, b.val / 2 = 0 → Hmap t wE3 b = 0 := by
      intro b hb
      simp only [wE3, map_add, Pi.add_apply, Hmap_single, hrv_even b hb]
      by_cases hlt : dE1 + 4 < 6 * t
      · have hd3 : dE3 = dE1 + 4 := if_pos hlt
        have h4 : shiftIdx t hpos u dE3 = shiftIdx t hpos se 4 := by
          rw [hd3, show se = shiftIdx t hpos u dE1 from rfl, shiftIdx_add]
        rw [h4]; exact hFn_sum_triple t hpos se b
      · have hd3 : dE3 = dE1 - 2 := if_neg hlt
        have h2 : se = shiftIdx t hpos (shiftIdx t hpos u dE3) 2 := by
          rw [hd3, shiftIdx_add]; dsimp only [se]; congr 1; have := hdE1_b.1; omega
        have h4 : shiftIdx t hpos se 2 = shiftIdx t hpos (shiftIdx t hpos u dE3) 4 := by
          rw [h2, shiftIdx_add]
        rw [h4, h2]
        calc hFn t (shiftIdx t hpos (shiftIdx t hpos u dE3) 2) b +
              hFn t (shiftIdx t hpos (shiftIdx t hpos u dE3) 4) b +
              hFn t (shiftIdx t hpos u dE3) b
            = hFn t (shiftIdx t hpos u dE3) b +
              hFn t (shiftIdx t hpos (shiftIdx t hpos u dE3) 2) b +
              hFn t (shiftIdx t hpos (shiftIdx t hpos u dE3) 4) b := by ring
          _ = 0 := hFn_sum_triple t hpos (shiftIdx t hpos u dE3) b
    rcases odd_pair_cancel t hpos so hso_m (Hmap t wE3) (hwE3_01 0 (by decide)) (hwE3_01 1 (by decide)) with
      ⟨d0, d1, hd⟩
    let xE3 : Fin (6 * t) → F2 :=
      wE3 + (d0 • Pi.single so 1 + d1 • Pi.single (shiftIdx t hpos so 2) 1)
    have hxE3_G : xE3 ∈ GoodMax t hpos S := by
      refine ⟨Submodule.add_mem _ hwE3_V
        (Submodule.add_mem _ (Submodule.smul_mem _ d0 hdO_sing0)
          (Submodule.smul_mem _ d1 (hso2_eq ▸ hdO_sing2))), ?_⟩
      change Hmap t xE3 = 0
      rw [show Hmap t xE3 = Hmap t wE3 + Hmap t wE3 by simp only [xE3, map_add, hd]]
      ext b; exact zmod2_add_self _
    -- Witness xO3 for {so, so+2}
    let dO3 : ℕ := if dO1 + 4 < L then dO1 + 4 else dO1 - 2
    have hdO3_b : dO3 < L ∧ (u.val + dO3) % 2 = 1 := by
      dsimp [dO3, dO1]; split_ifs <;> omega
    have hdO3_S : shiftIdx t hpos u dO3 ∈ S :=
      (mem_S_shift_iff t hpos u hLn (by omega)).mpr (Or.inl ⟨hdO3_b.1, hdO3_b.2⟩)
    let wO3 : Fin (6 * t) → F2 :=
      Pi.single so 1 + Pi.single (shiftIdx t hpos so 2) 1 + runVec t hpos S (shiftIdx t hpos u dO3)
    have hwO3_V : wO3 ∈ Vset t hpos S :=
      Submodule.add_mem _ (Submodule.add_mem _ hdO_sing0 (hso2_eq ▸ hdO_sing2))
        (runVec_mem_Vset t hpos u hL5 hLn5 (by omega) hdO3_S)
    have hrv_odd : ∀ b : Fin 4, b.val / 2 = 1 →
        Hmap t (runVec t hpos S (shiftIdx t hpos u dO3)) b = hFn t (shiftIdx t hpos u dO3) b := by
      intro b hb
      unfold runVec
      have hnm : (nextIdx t hpos (shiftIdx t hpos u dO3)).val % 2 = 0 := by
        rw [nextIdx_mod2, shiftIdx_mod2]; omega
      have hpm : (prevIdx t hpos (shiftIdx t hpos u dO3)).val % 2 = 0 := by
        have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u dO3))
        rw [nextIdx_prevIdx, shiftIdx_mod2] at this; omega
      have h0n := hFn_other_lane t (nextIdx t hpos (shiftIdx t hpos u dO3)) b (by omega)
      have h0p := hFn_other_lane t (prevIdx t hpos (shiftIdx t hpos u dO3)) b (by omega)
      split_ifs
      · simp [map_add, Hmap_single, h0n]
      · simp [map_add, Hmap_single, h0p]
      · simp [Hmap_single]
    have hwO3_23 : ∀ b : Fin 4, b.val / 2 = 1 → Hmap t wO3 b = 0 := by
      intro b hb
      simp only [wO3, map_add, Pi.add_apply, Hmap_single, hrv_odd b hb]
      by_cases hlt : dO1 + 4 < L
      · have hd3 : dO3 = dO1 + 4 := if_pos hlt
        have h4 : shiftIdx t hpos u dO3 = shiftIdx t hpos so 4 := by
          rw [hd3, show so = shiftIdx t hpos u dO1 from rfl, shiftIdx_add]
        rw [h4]; exact hFn_sum_triple t hpos so b
      · have hd3 : dO3 = dO1 - 2 := if_neg hlt
        have h2 : so = shiftIdx t hpos (shiftIdx t hpos u dO3) 2 := by
          rw [hd3, shiftIdx_add]; dsimp only [so]; congr 1
          have := hsites.1; dsimp [dO1] at *; split_ifs at * <;> omega
        have h4 : shiftIdx t hpos so 2 = shiftIdx t hpos (shiftIdx t hpos u dO3) 4 := by
          rw [h2, shiftIdx_add]
        rw [h4, h2]
        calc hFn t (shiftIdx t hpos (shiftIdx t hpos u dO3) 2) b +
              hFn t (shiftIdx t hpos (shiftIdx t hpos u dO3) 4) b +
              hFn t (shiftIdx t hpos u dO3) b
            = hFn t (shiftIdx t hpos u dO3) b +
              hFn t (shiftIdx t hpos (shiftIdx t hpos u dO3) 2) b +
              hFn t (shiftIdx t hpos (shiftIdx t hpos u dO3) 4) b := by ring
          _ = 0 := hFn_sum_triple t hpos (shiftIdx t hpos u dO3) b
    rcases even_pair_cancel t hpos se hse_m (Hmap t wO3) (hwO3_23 2 (by decide)) (hwO3_23 3 (by decide)) with
      ⟨c0, c1, hc⟩
    let xO3 : Fin (6 * t) → F2 :=
      wO3 + (c0 • Pi.single se 1 + c1 • Pi.single (shiftIdx t hpos se 2) 1)
    have hxO3_G : xO3 ∈ GoodMax t hpos S := by
      refine ⟨Submodule.add_mem _ hwO3_V
        (Submodule.add_mem _ (Submodule.smul_mem _ c0 hdE_sing0)
          (Submodule.smul_mem _ c1 (hse2_eq ▸ hdE_sing2))), ?_⟩
      change Hmap t xO3 = 0
      rw [show Hmap t xO3 = Hmap t wO3 + Hmap t wO3 by simp only [xO3, map_add, hc]]
      ext b; exact zmod2_add_self _
    intro d hd hmem
    have hrv_val : runVec t hpos S (shiftIdx t hpos u d) (shiftIdx t hpos u d) = 1 := by
      unfold runVec
      have hne1 : shiftIdx t hpos u d ≠ nextIdx t hpos (shiftIdx t hpos u d) := fun h => by
        have := nextIdx_mod2 t hpos (shiftIdx t hpos u d); rw [← h] at this; omega
      have hne2 : shiftIdx t hpos u d ≠ prevIdx t hpos (shiftIdx t hpos u d) := fun h => by
        have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u d))
        rw [nextIdx_prevIdx, ← h] at this; omega
      split_ifs
      · simp [Pi.single_eq_of_ne hne1]
      · simp [Pi.single_eq_of_ne hne2]
      · simp
    by_cases hd_basis : d = dE1 ∨ d = dE1 + 2 ∨ d = dO1 ∨ d = dO1 + 2
    · rcases hd_basis with rfl | rfl | rfl | rfl
      · refine ⟨xE3, hxE3_G, ?_⟩
        have hrv0 : runVec t hpos S (shiftIdx t hpos u dE3) se = 0 := by
          unfold runVec
          have h1 : se ≠ shiftIdx t hpos u dE3 := fun h => by
            have := shiftIdx_inj_range t hpos u (by omega) hdE3_b.2.1 h
            dsimp [dE3] at this; split_ifs at this <;> omega
          have h2 : se ≠ nextIdx t hpos (shiftIdx t hpos u dE3) := fun h => by
            have := nextIdx_mod2 t hpos (shiftIdx t hpos u dE3)
            rw [← h, hse_m, shiftIdx_mod2] at this; omega
          have h3 : se ≠ prevIdx t hpos (shiftIdx t hpos u dE3) := fun h => by
            have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u dE3))
            rw [nextIdx_prevIdx, ← h, hse_m, shiftIdx_mod2] at this; omega
          split_ifs <;> simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h3]
        have hne_se2 : se ≠ shiftIdx t hpos se 2 := fun h => by
          have := shiftIdx_inj_range t hpos se (a := 0) (b := 2) (by omega) (by omega)
            ((shiftIdx_zero t hpos se).trans h); omega
        have hne_so : se ≠ so := fun h => by rw [h] at hse_m; omega
        have hne_so2 : se ≠ shiftIdx t hpos so 2 := fun h => by
          have := shiftIdx_mod2 t hpos so 2; rw [← h, hse_m] at this; omega
        change xE3 se ≠ 0
        simp [xE3, wE3, hrv0, Pi.single_eq_of_ne hne_se2, Pi.single_eq_of_ne hne_so,
          Pi.single_eq_of_ne hne_so2]
      · refine ⟨xE3, hxE3_G, ?_⟩
        rw [← hse2_eq]
        have hse2m : (shiftIdx t hpos se 2).val % 2 = 0 := by rw [shiftIdx_mod2]; omega
        have hrv0 : runVec t hpos S (shiftIdx t hpos u dE3) (shiftIdx t hpos se 2) = 0 := by
          unfold runVec
          have h1 : shiftIdx t hpos se 2 ≠ shiftIdx t hpos u dE3 := fun h => by
            rw [hse2_eq] at h
            have := shiftIdx_inj_range t hpos u (by omega) hdE3_b.2.1 h
            dsimp [dE3] at this; split_ifs at this <;> omega
          have h2 : shiftIdx t hpos se 2 ≠ nextIdx t hpos (shiftIdx t hpos u dE3) := fun h => by
            have := nextIdx_mod2 t hpos (shiftIdx t hpos u dE3)
            rw [← h, hse2m, shiftIdx_mod2] at this; omega
          have h3 : shiftIdx t hpos se 2 ≠ prevIdx t hpos (shiftIdx t hpos u dE3) := fun h => by
            have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u dE3))
            rw [nextIdx_prevIdx, ← h, hse2m, shiftIdx_mod2] at this; omega
          split_ifs <;> simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h3]
        have hne_se : shiftIdx t hpos se 2 ≠ se := fun h => by
          have := shiftIdx_inj_range t hpos se (a := 2) (b := 0) (by omega) (by omega)
            (h.trans (shiftIdx_zero t hpos se).symm); omega
        have hne_so : shiftIdx t hpos se 2 ≠ so := fun h => by rw [h] at hse2m; omega
        have hne_so2 : shiftIdx t hpos se 2 ≠ shiftIdx t hpos so 2 := fun h => by
          have := shiftIdx_mod2 t hpos so 2; rw [← h, hse2m] at this; omega
        simp [xE3, wE3, hrv0, Pi.single_eq_of_ne hne_se, Pi.single_eq_of_ne hne_so,
          Pi.single_eq_of_ne hne_so2]
      · refine ⟨xO3, hxO3_G, ?_⟩
        have hrv0 : runVec t hpos S (shiftIdx t hpos u dO3) so = 0 := by
          unfold runVec
          have h1 : so ≠ shiftIdx t hpos u dO3 := fun h => by
            have := shiftIdx_inj_range t hpos u (by omega) (by omega) h
            dsimp [dO3] at this; split_ifs at this <;> omega
          have h2 : so ≠ nextIdx t hpos (shiftIdx t hpos u dO3) := fun h => by
            have := nextIdx_mod2 t hpos (shiftIdx t hpos u dO3)
            rw [← h, hso_m, shiftIdx_mod2] at this; omega
          have h3 : so ≠ prevIdx t hpos (shiftIdx t hpos u dO3) := fun h => by
            have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u dO3))
            rw [nextIdx_prevIdx, ← h, hso_m, shiftIdx_mod2] at this; omega
          split_ifs <;> simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h3]
        have hne_so2 : so ≠ shiftIdx t hpos so 2 := fun h => by
          have := shiftIdx_inj_range t hpos so (a := 0) (b := 2) (by omega) (by omega)
            ((shiftIdx_zero t hpos so).trans h); omega
        have hne_se : so ≠ se := fun h => by rw [h] at hso_m; omega
        have hne_se2 : so ≠ shiftIdx t hpos se 2 := fun h => by
          have := shiftIdx_mod2 t hpos se 2; rw [← h, hso_m] at this; omega
        change xO3 so ≠ 0
        simp [xO3, wO3, hrv0, Pi.single_eq_of_ne hne_so2, Pi.single_eq_of_ne hne_se,
          Pi.single_eq_of_ne hne_se2]
      · refine ⟨xO3, hxO3_G, ?_⟩
        rw [← hso2_eq]
        have hso2m : (shiftIdx t hpos so 2).val % 2 = 1 := by rw [shiftIdx_mod2]; omega
        have hrv0 : runVec t hpos S (shiftIdx t hpos u dO3) (shiftIdx t hpos so 2) = 0 := by
          unfold runVec
          have h1 : shiftIdx t hpos so 2 ≠ shiftIdx t hpos u dO3 := fun h => by
            rw [hso2_eq] at h
            have := shiftIdx_inj_range t hpos u (by omega) (by omega) h
            dsimp [dO3] at this; split_ifs at this <;> omega
          have h2 : shiftIdx t hpos so 2 ≠ nextIdx t hpos (shiftIdx t hpos u dO3) := fun h => by
            have := nextIdx_mod2 t hpos (shiftIdx t hpos u dO3)
            rw [← h, hso2m, shiftIdx_mod2] at this; omega
          have h3 : shiftIdx t hpos so 2 ≠ prevIdx t hpos (shiftIdx t hpos u dO3) := fun h => by
            have := nextIdx_mod2 t hpos (prevIdx t hpos (shiftIdx t hpos u dO3))
            rw [nextIdx_prevIdx, ← h, hso2m, shiftIdx_mod2] at this; omega
          split_ifs <;> simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h3]
        have hne_so : shiftIdx t hpos so 2 ≠ so := fun h => by
          have := shiftIdx_inj_range t hpos so (a := 2) (b := 0) (by omega) (by omega)
            (h.trans (shiftIdx_zero t hpos so).symm); omega
        have hne_se : shiftIdx t hpos so 2 ≠ se := fun h => by rw [h] at hso2m; omega
        have hne_se2 : shiftIdx t hpos so 2 ≠ shiftIdx t hpos se 2 := fun h => by
          have := shiftIdx_mod2 t hpos se 2; rw [← h, hso2m] at this; omega
        simp [xO3, wO3, hrv0, Pi.single_eq_of_ne hne_so, Pi.single_eq_of_ne hne_se,
          Pi.single_eq_of_ne hne_se2]
    · rcases both_pairs_cancel t hpos se so hse_m hso_m
        (Hmap t (runVec t hpos S (shiftIdx t hpos u d))) with ⟨c0, c1, d0, d1, hc⟩
      let xd : Fin (6 * t) → F2 :=
        runVec t hpos S (shiftIdx t hpos u d) +
        (c0 • Pi.single se 1 + c1 • Pi.single (shiftIdx t hpos se 2) 1 +
         d0 • Pi.single so 1 + d1 • Pi.single (shiftIdx t hpos so 2) 1)
      have hxd_G : xd ∈ GoodMax t hpos S := by
        refine ⟨Submodule.add_mem _ (runVec_mem_Vset t hpos u hL5 hLn5 hd hmem)
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
            (Submodule.smul_mem _ c0 hdE_sing0)
            (Submodule.smul_mem _ c1 (hse2_eq ▸ hdE_sing2)))
            (Submodule.smul_mem _ d0 hdO_sing0))
            (Submodule.smul_mem _ d1 (hso2_eq ▸ hdO_sing2))), ?_⟩
        change Hmap t xd = 0
        rw [show Hmap t xd = Hmap t (runVec t hpos S (shiftIdx t hpos u d)) +
            Hmap t (runVec t hpos S (shiftIdx t hpos u d)) by simp only [xd, map_add, hc]]
        ext b; exact zmod2_add_self _
      refine ⟨xd, hxd_G, ?_⟩
      have hne1 : shiftIdx t hpos u d ≠ se := fun h =>
        hd_basis (Or.inl (shiftIdx_inj_range t hpos u hd (by omega) h))
      have hne2 : shiftIdx t hpos u d ≠ shiftIdx t hpos se 2 := fun h => by
        rw [hse2_eq] at h
        exact hd_basis (Or.inr (Or.inl (shiftIdx_inj_range t hpos u hd (by omega) h)))
      have hne3 : shiftIdx t hpos u d ≠ so := fun h =>
        hd_basis (Or.inr (Or.inr (Or.inl (shiftIdx_inj_range t hpos u hd (by omega) h))))
      have hne4 : shiftIdx t hpos u d ≠ shiftIdx t hpos so 2 := fun h => by
        rw [hso2_eq] at h
        exact hd_basis (Or.inr (Or.inr (Or.inr (shiftIdx_inj_range t hpos u hd (by omega) h))))
      simp [xd, hrv_val, Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2,
        Pi.single_eq_of_ne hne3, Pi.single_eq_of_ne hne4]

lemma sites_ge3_imp_GoodMax (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t)
    (u : Fin (6 * t)) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < 6 * t)
    (hs0 : 3 ≤ sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 0)
    (hs1 : 3 ≤ sitesS t (symmDiff (cycInt t hpos u L) (evenSet t)) 1) :
    suppU t (GoodMax t hpos (symmDiff (cycInt t hpos u L) (evenSet t))) =
      symmDiff (cycInt t hpos u L) (evenSet t) ∧
    Module.finrank F2 (GoodMax t hpos (symmDiff (cycInt t hpos u L) (evenSet t))) = 3 * t - 5 := by
  let T := cycInt t hpos u L
  let S := symmDiff T (evenSet t)
  have hsites := sites_symmDiff_cycInt t hpos u hLn
  have hL5 : 5 ≤ L := by have := hsites.1; omega
  have hLn5 : L ≤ 6 * t - 5 := by have := hsites.2; omega
  have hMain : Function.Surjective ((Hmap t).comp (Vset t hpos S).subtype) ∧
      ∀ d < 6 * t, shiftIdx t hpos u d ∈ S → ∃ x ∈ GoodMax t hpos S, x (shiftIdx t hpos u d) ≠ 0 := by
    by_cases hB : L = 5 ∧ u.val % 2 = 1
    · rcases hB with ⟨rfl, hu1⟩; exact caseB_L5 t hpos ht u hu1
    · by_cases hC : L = 6 * t - 5 ∧ u.val % 2 = 1
      · rcases hC with ⟨rfl, hu1⟩; exact caseC_L6t5 t hpos ht u hu1
      · exact caseA_both_pairs t hpos ht u hL5 hLn5 hs0 hs1 hB hC
  constructor
  · apply Finset.Subset.antisymm (suppU_GoodMax_subset t hpos S)
    intro i hiS
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and]
    let d : ℕ := (i.val + 6 * t - u.val) % (6 * t)
    have hd : d < 6 * t := Nat.mod_lt _ (by omega)
    have hsh : shiftIdx t hpos u d = i := by
      apply Fin.ext; dsimp [shiftIdx, d]
      have hu := u.isLt; have hiv := i.isLt
      by_cases hle : u.val ≤ i.val
      · have : (i.val + 6 * t - u.val) % (6 * t) = i.val - u.val := by
          rw [show i.val + 6 * t - u.val = (i.val - u.val) + 6 * t by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [this, show u.val + (i.val - u.val) = i.val by omega, Nat.mod_eq_of_lt hiv]
      · have : (i.val + 6 * t - u.val) % (6 * t) = i.val + 6 * t - u.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [this, show u.val + (i.val + 6 * t - u.val) = i.val + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hiv]
    rw [← hsh] at hiS ⊢
    exact hMain.2 d hd hiS
  · have hrunsS : runsS t hpos S = 3 * t - 1 := by
      have h1 := runsS_add_symmDiff_even t hpos S
      have hsym : symmDiff S (evenSet t) = T := by simp [S, symmDiff_symmDiff_cancel_right]
      rw [hsym, runsS_cycInt t hpos u hL1 hLn] at h1
      omega
    have hVfr : Module.finrank F2 (Vset t hpos S) = 3 * t - 1 := by
      rw [finrank_Vset t hpos S (by omega), hrunsS]
    let f : Vset t hpos S →ₗ[F2] (Fin 4 → F2) := (Hmap t).comp (Vset t hpos S).subtype
    have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hMain.1
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_top, Module.finrank_fin_fun, hVfr] at hrn
    have hker_eq : Module.finrank F2 (GoodMax t hpos S) = Module.finrank F2 (LinearMap.ker f) := by
      let e : GoodMax t hpos S ≃ₗ[F2] LinearMap.ker f :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          invFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact e.finrank_eq
    dsimp only [S, T] at hker_eq hrn ⊢
    omega

-- Stage 4: Exact counting of eligible nonempty S equals n * (n - 10)
lemma card_eligible_ge3 (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t) :
    ((Finset.univ : Finset (Finset (Fin (6 * t)))).filter (fun S =>
      runsS t hpos S = 3 * t - 1 ∧ 3 ≤ sitesS t S 0 ∧ 3 ≤ sitesS t S 1)).card =
      6 * t * (6 * t - 10) := by
  let P : Finset (Fin (6 * t) × ℕ) :=
    ((Finset.univ : Finset (Fin (6 * t))) ×ˢ Finset.Icc 5 (6 * t - 5)).filter (fun p =>
      if p.1.val % 2 = 0 then 6 ≤ p.2 ∧ p.2 ≤ 6 * t - 6 else True)
  have hcardP : P.card = 6 * t * (6 * t - 10) := by
    have h1 : P.card = ∑ u : Fin (6 * t),
        ((Finset.Icc 5 (6 * t - 5)).filter (fun L =>
          if u.val % 2 = 0 then 6 ≤ L ∧ L ≤ 6 * t - 6 else True)).card := by
      have hsum : (∑ u : Fin (6 * t),
          ((Finset.Icc 5 (6 * t - 5)).filter (fun L =>
            if u.val % 2 = 0 then 6 ≤ L ∧ L ≤ 6 * t - 6 else True)).card) =
          ∑ u : Fin (6 * t), ∑ L ∈ Finset.Icc 5 (6 * t - 5),
            if (if u.val % 2 = 0 then 6 ≤ L ∧ L ≤ 6 * t - 6 else True) then 1 else 0 := by
        refine Finset.sum_congr rfl (fun u _ => by rw [Finset.card_filter])
      rw [hsum, ← Finset.sum_product', ← Finset.card_filter]
    rw [h1]
    have hinner : ∀ u : Fin (6 * t),
        ((Finset.Icc 5 (6 * t - 5)).filter (fun L =>
          if u.val % 2 = 0 then 6 ≤ L ∧ L ≤ 6 * t - 6 else True)).card =
        if u.val % 2 = 0 then (6 * t - 11) else (6 * t - 9) := by
      intro u
      by_cases hu : u.val % 2 = 0
      · simp only [hu, ↓reduceIte]
        have heq : (Finset.Icc 5 (6 * t - 5)).filter (fun L => 6 ≤ L ∧ L ≤ 6 * t - 6) =
            Finset.Icc 6 (6 * t - 6) := by
          ext L; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [heq, Nat.card_Icc]; omega
      · simp only [hu, ↓reduceIte, Finset.filter_true, Nat.card_Icc]; omega
    simp_rw [hinner]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have hev : (Finset.univ.filter (fun u : Fin (6 * t) => u.val % 2 = 0)).card = 3 * t := by
      have hbij : (Finset.univ.filter (fun u : Fin (6 * t) => u.val % 2 = 0)).card =
          (Finset.univ : Finset (Fin (3 * t))).card :=
        Finset.card_bij (fun (i : Fin (6 * t)) _ => (⟨i.val / 2, by omega⟩ : Fin (3 * t)))
          (fun _ _ => Finset.mem_univ _)
          (fun a ha b hb hab => by
            have ha0 := (Finset.mem_filter.mp ha).2
            have hb0 := (Finset.mem_filter.mp hb).2
            have hv := congrArg Fin.val hab; dsimp at hv
            exact Fin.ext (by omega))
          (fun q _ => ⟨⟨2 * q.val, by have := q.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩,
            Fin.ext (by have := q.isLt; dsimp; omega)⟩)
      simpa using hbij
    have hodd : (Finset.univ.filter (fun u : Fin (6 * t) => ¬ u.val % 2 = 0)).card = 3 * t := by
      have hdisj : Disjoint (Finset.univ.filter (fun u : Fin (6 * t) => u.val % 2 = 0))
          (Finset.univ.filter (fun u : Fin (6 * t) => ¬ u.val % 2 = 0)) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hun : Finset.univ.filter (fun u : Fin (6 * t) => u.val % 2 = 0) ∪
          Finset.univ.filter (fun u : Fin (6 * t) => ¬ u.val % 2 = 0) = Finset.univ := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      have htot := Finset.card_union_of_disjoint hdisj
      rw [hun, Finset.card_univ, Fintype.card_fin, hev] at htot
      omega
    rw [hev, hodd]
    zify [(by omega : 11 ≤ 6 * t), (by omega : 9 ≤ 6 * t), (by omega : 10 ≤ 6 * t)]
    ring
  rw [← hcardP]
  refine (Finset.card_bij (fun p _ => symmDiff (cycInt t hpos p.1 p.2) (evenSet t)) ?_ ?_ ?_).symm
  · rintro ⟨u, L⟩ hp
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and] at hp
    rcases hp with ⟨⟨hL5, hLn5⟩, hcond⟩
    have hL1 : 1 ≤ L := by omega
    have hLn : L < 6 * t := by omega
    have hsites := sites_symmDiff_cycInt t hpos u hLn
    have hruns : runsS t hpos (symmDiff (cycInt t hpos u L) (evenSet t)) = 3 * t - 1 := by
      have h1 := runsS_add_symmDiff_even t hpos (symmDiff (cycInt t hpos u L) (evenSet t))
      rw [symmDiff_symmDiff_cancel_right, runsS_cycInt t hpos u hL1 hLn] at h1
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hruns, ?_, ?_⟩
    · by_cases hu : u.val % 2 = 0
      · rw [if_pos hu] at hcond; rw [hsites.2]; omega
      · rw [hsites.2]; omega
    · by_cases hu : u.val % 2 = 0
      · rw [if_pos hu] at hcond; rw [hsites.1]; omega
      · rw [hsites.1]; omega
  · rintro ⟨u1, L1⟩ hp1 ⟨u2, L2⟩ hp2 heq
    have hT : cycInt t hpos u1 L1 = cycInt t hpos u2 L2 := by
      have := congrArg (fun X => symmDiff X (evenSet t)) heq
      simpa [symmDiff_symmDiff_cancel_right] using this
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and] at hp1 hp2
    rcases cycInt_unique t hpos (by omega) (by omega) (by omega) (by omega) hT with ⟨hu, hL⟩
    exact Prod.ext hu hL
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨_, hruns, hs0, hs1⟩
    have hT_runs : runsS t hpos (symmDiff S (evenSet t)) = 1 := by
      have h1 := runsS_add_symmDiff_even t hpos S; omega
    rcases (runsS_eq_one_iff t hpos _).mp hT_runs with ⟨u, L, hL1, hLn, hTeq⟩
    have hSeq : symmDiff (cycInt t hpos u L) (evenSet t) = S := by
      rw [← hTeq, symmDiff_symmDiff_cancel_right]
    have hsites := sites_symmDiff_cycInt t hpos u hLn
    rw [hSeq] at hsites
    refine ⟨(u, L), ?_, hSeq⟩
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    by_cases hu : u.val % 2 = 0
    · rw [if_pos hu]; omega
    · rw [if_neg hu]; trivial

-- Unified statement helper avoiding Fintype (Submodule) comparison
lemma main_parts (t : ℕ) (hpos : 0 < t) (ht : 3 ≤ t)
    (S : Finset (Fin (6 * t)))
    (helig : runsS t hpos S = 3 * t - 1 ∧ 0 < sitesS t S 0 ∧ 0 < sitesS t S 1) :
    ((∃ U, goodP t hpos U ∧ suppU t U = S) ↔ 3 ≤ sitesS t S 0 ∧ 3 ≤ sitesS t S 1) ∧
    (3 ≤ sitesS t S 0 ∧ 3 ≤ sitesS t S 1 →
      (∃ U, goodP t hpos U ∧ suppU t U = S ∧ Module.finrank F2 U = 3 * t - 5) ∧
      (∀ U, goodP t hpos U → suppU t U = S → Module.finrank F2 U ≤ 3 * t - 5)) := by
  have hT_runs : runsS t hpos (symmDiff S (evenSet t)) = 1 := by
    have h1 := runsS_add_symmDiff_even t hpos S; omega
  rcases (runsS_eq_one_iff t hpos _).mp hT_runs with ⟨u, L, hL1, hLn, hTeq⟩
  have hSeq : symmDiff (cycInt t hpos u L) (evenSet t) = S := by
    rw [← hTeq, symmDiff_symmDiff_cancel_right]
  rw [← hSeq] at helig ⊢
  constructor
  · rw [exists_good_supp_iff]
    constructor
    · intro hsupp
      exact supp_GoodMax_imp_sites_ge3 t hpos ht u hL1 hLn helig.2.1 helig.2.2 hsupp
    · rintro ⟨hs0, hs1⟩
      exact (sites_ge3_imp_GoodMax t hpos ht u hL1 hLn hs0 hs1).1
  · rintro ⟨hs0, hs1⟩
    rcases sites_ge3_imp_GoodMax t hpos ht u hL1 hLn hs0 hs1 with ⟨hsupp, hfr⟩
    refine ⟨⟨GoodMax t hpos _, GoodMax_good t hpos _, hsupp, hfr⟩, ?_⟩
    intro U hg hUsupp
    have hle : U ≤ GoodMax t hpos _ := hUsupp ▸ good_le_GoodMax t hpos hg
    calc Module.finrank F2 U ≤ Module.finrank F2 (GoodMax t hpos _) := Submodule.finrank_mono hle
      _ = 3 * t - 5 := hfr

end PEqualNP.Outside.L_lib_886

theorem PEqualNP.Outside.L_lib_886 :
    ∀ (t : ℕ) (hpos : 0 < t), 3 ≤ t →
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let n := 6*t
      let a := 3*t
      let W := Fin n → F
      letI : Fintype (Submodule F W) := Fintype.ofFinite _
      let next := fun i : Fin n =>
        (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 5) hpos)⟩ : Fin n)
      let h := fun (i : Fin n) (b : Fin 4) =>
        if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
        then (1:F) else 0
      let good := fun U : Submodule F W =>
        (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
      let supp := fun U : Submodule F W =>
        Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
      let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
        (S.filter (fun i => i.val % 2 = p)).card
      let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
      let family := fun S : Finset (Fin n) =>
        (Finset.univ : Finset (Submodule F W)).filter (fun U => good U ∧ supp U = S)
      let eligible := fun S : Finset (Fin n) =>
        runs S = a-1 ∧ 0 < sites S 0 ∧ 0 < sites S 1
      (∀ S, eligible S →
        ((family S).Nonempty ↔ 3 ≤ sites S 0 ∧ 3 ≤ sites S 1) ∧
        ((family S).Nonempty → (family S).sup (fun U => Module.finrank F U) = a-5)) ∧
      ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => eligible S ∧ (family S).Nonempty)).card = n*(n-10) := by
  intro t hpos ht
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6 * t
  let a := 3 * t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 5) hpos)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1 : F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
    (S.filter (fun i => i.val % 2 = p)).card
  let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
  let family := fun S : Finset (Fin n) =>
    (Finset.univ : Finset (Submodule F W)).filter (fun U => good U ∧ supp U = S)
  let eligible := fun S : Finset (Fin n) =>
    runs S = a - 1 ∧ 0 < sites S 0 ∧ 0 < sites S 1
  have hh_eq : ∀ i b, h i b = PEqualNP.Outside.L_lib_886.hFn t i b := by
    intro i b; dsimp only [h, PEqualNP.Outside.L_lib_886.hFn]; split_ifs <;> rfl
  have hnext_eq : ∀ i, next i = PEqualNP.Outside.L_lib_886.nextIdx t hpos i := fun _ => rfl
  have hsites_eq : ∀ S p, sites S p = PEqualNP.Outside.L_lib_886.sitesS t S p := by
    intro S p; dsimp only [sites, PEqualNP.Outside.L_lib_886.sitesS]
    congr 1; ext i; simp only [Finset.mem_filter]
  have hruns_eq : ∀ S, runs S = PEqualNP.Outside.L_lib_886.runsS t hpos S := by
    intro S; dsimp only [runs, PEqualNP.Outside.L_lib_886.runsS]
    congr 1; ext i; simp only [Finset.mem_filter, hnext_eq]
  have hsupp_eq : ∀ U : Submodule F W, supp U = PEqualNP.Outside.L_lib_886.suppU t U := by
    intro U; ext i
    simp only [supp, PEqualNP.Outside.L_lib_886.suppU, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hgood_iff : ∀ U : Submodule F W, good U ↔ PEqualNP.Outside.L_lib_886.goodP t hpos U := by
    intro U; dsimp only [good, PEqualNP.Outside.L_lib_886.goodP]
    simp_rw [hh_eq, hnext_eq]
    exact Iff.rfl
  have hne_iff : ∀ S : Finset (Fin n),
      (family S).Nonempty ↔
      ∃ U : Submodule F W, PEqualNP.Outside.L_lib_886.goodP t hpos U ∧
        PEqualNP.Outside.L_lib_886.suppU t U = S := by
    intro S
    constructor
    · rintro ⟨U, hU⟩
      rcases (Finset.mem_filter.mp hU).2 with ⟨hg, hs⟩
      exact ⟨U, (hgood_iff U).mp hg, (hsupp_eq U).symm.trans hs⟩
    · rintro ⟨U, hg, hs⟩
      exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ U, (hgood_iff U).mpr hg,
        (hsupp_eq U).trans hs⟩⟩
  have hpart1 : ∀ S, eligible S →
      ((family S).Nonempty ↔ 3 ≤ sites S 0 ∧ 3 ≤ sites S 1) ∧
      ((family S).Nonempty → (family S).sup (fun U => Module.finrank F U) = a - 5) := by
    intro S hS
    have hS' : PEqualNP.Outside.L_lib_886.runsS t hpos S = 3 * t - 1 ∧
        0 < PEqualNP.Outside.L_lib_886.sitesS t S 0 ∧
        0 < PEqualNP.Outside.L_lib_886.sitesS t S 1 := by
      rw [← hruns_eq S, ← hsites_eq S 0, ← hsites_eq S 1]; exact hS
    have hm := PEqualNP.Outside.L_lib_886.main_parts t hpos ht S hS'
    have hiff : (family S).Nonempty ↔ 3 ≤ sites S 0 ∧ 3 ≤ sites S 1 := by
      rw [hne_iff S, hm.1, hsites_eq S 0, hsites_eq S 1]
    refine ⟨hiff, fun hne => ?_⟩
    have hge3 : 3 ≤ PEqualNP.Outside.L_lib_886.sitesS t S 0 ∧
        3 ≤ PEqualNP.Outside.L_lib_886.sitesS t S 1 := by
      rw [← hsites_eq S 0, ← hsites_eq S 1]; exact hiff.mp hne
    rcases hm.2 hge3 with ⟨⟨U0, hg0, hs0, hfr0⟩, hmax⟩
    apply le_antisymm
    · refine Finset.sup_le (fun U hU => ?_)
      rcases (Finset.mem_filter.mp hU).2 with ⟨hg, hs⟩
      exact hmax U ((hgood_iff U).mp hg) ((hsupp_eq U).symm.trans hs)
    · have hU0_mem : U0 ∈ family S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ U0, (hgood_iff U0).mpr hg0, (hsupp_eq U0).trans hs0⟩
      have hle := Finset.le_sup (f := fun U : Submodule F W => Module.finrank F ↥U) hU0_mem
      have heq0 : Module.finrank F ↥U0 = a - 5 := hfr0
      rw [← heq0]
      exact hle
  refine ⟨hpart1, ?_⟩
  rw [← PEqualNP.Outside.L_lib_886.card_eligible_ge3 t hpos ht]
  congr 1; ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hel, hne⟩
    have h3 := (hpart1 S hel).1.mp hne
    rw [← hruns_eq S, ← hsites_eq S 0, ← hsites_eq S 1]
    exact ⟨hel.1, h3.1, h3.2⟩
  · rintro ⟨hr, hs0, hs1⟩
    rw [← hruns_eq S] at hr
    rw [← hsites_eq S 0] at hs0
    rw [← hsites_eq S 1] at hs1
    have hel : eligible S := ⟨hr, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hs0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hs1⟩
    exact ⟨hel, (hpart1 S hel).1.mpr ⟨hs0, hs1⟩⟩

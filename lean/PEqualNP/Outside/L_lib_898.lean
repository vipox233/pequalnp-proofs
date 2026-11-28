import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_898

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


-- ============================================================================
-- L-lib-898 Section A: Lane Decomposition, Rank Split, and rFree = 2
-- ============================================================================

def laneSet (t : ℕ) (p : ℕ) : Finset (Fin (6 * t)) :=
  Finset.univ.filter (fun i => i.val % 2 = p)

def laneSub (t : ℕ) (S : Finset (Fin (6 * t))) (p : ℕ) : Finset (Fin (6 * t)) :=
  S.filter (fun i => i.val % 2 = p)

lemma card_laneSet (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) :
    (laneSet t p).card = 3 * t := by
  have hbij : (laneSet t p).card = (Finset.univ : Finset (Fin (3 * t))).card :=
    Finset.card_bij (fun (i : Fin (6 * t)) _ => (⟨i.val / 2, by omega⟩ : Fin (3 * t)))
      (fun _ _ => Finset.mem_univ _)
      (fun a ha b hb hab => by
        have ha0 := (Finset.mem_filter.mp ha).2
        have hb0 := (Finset.mem_filter.mp hb).2
        have hv := congrArg Fin.val hab; dsimp at hv
        exact Fin.ext (by omega))
      (fun q _ => ⟨⟨2 * q.val + p, by have := q.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩,
        Fin.ext (by have := q.isLt; dsimp; omega)⟩)
  simpa using hbij

lemma laneSub_card_eq_sites (t : ℕ) (S : Finset (Fin (6 * t))) (p : ℕ) :
    (laneSub t S p).card = sitesS t S p := rfl

lemma laneSub_subset_laneSet (t : ℕ) (S : Finset (Fin (6 * t))) (p : ℕ) :
    laneSub t S p ⊆ laneSet t p := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

lemma prevIdx_mod2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    (prevIdx t hpos i).val % 2 = 1 - i.val % 2 := by
  have h := nextIdx_mod2 t hpos (prevIdx t hpos i)
  rw [nextIdx_prevIdx] at h
  omega

def next2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) : Fin (6 * t) :=
  shiftIdx t hpos i 2

def prev2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) : Fin (6 * t) :=
  prevIdx t hpos (prevIdx t hpos i)

lemma next2_eq_next_next (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    next2 t hpos i = nextIdx t hpos (nextIdx t hpos i) := by
  unfold next2
  rw [← shiftIdx_one, ← shiftIdx_one, shiftIdx_add]

lemma next2_prev2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    next2 t hpos (prev2 t hpos i) = i := by
  rw [next2_eq_next_next, prev2, nextIdx_prevIdx, nextIdx_prevIdx]

lemma prev2_next2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    prev2 t hpos (next2 t hpos i) = i := by
  rw [next2_eq_next_next, prev2, prevIdx_nextIdx, prevIdx_nextIdx]

lemma next2_inj (t : ℕ) (hpos : 0 < t) : Function.Injective (next2 t hpos) := by
  intro a b hab
  have := congrArg (prev2 t hpos) hab
  rwa [prev2_next2, prev2_next2] at this

lemma prevIdx_inj (t : ℕ) (hpos : 0 < t) : Function.Injective (prevIdx t hpos) := by
  intro a b hab
  have := congrArg (nextIdx t hpos) hab
  rwa [nextIdx_prevIdx, nextIdx_prevIdx] at this

lemma prev2_inj (t : ℕ) (hpos : 0 < t) : Function.Injective (prev2 t hpos) := by
  intro a b hab
  have := congrArg (next2 t hpos) hab
  rwa [next2_prev2, next2_prev2] at this

lemma next2_mod2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    (next2 t hpos i).val % 2 = i.val % 2 := by
  rw [next2, shiftIdx_mod2]; omega

lemma prev2_mod2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    (prev2 t hpos i).val % 2 = i.val % 2 := by
  have h := next2_mod2 t hpos (prev2 t hpos i)
  rw [next2_prev2] at h; exact h.symm

lemma prevIdx_eq_shift (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    prevIdx t hpos i = shiftIdx t hpos i (6 * t - 1) := rfl

lemma prev2_eq_shift (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    prev2 t hpos i = shiftIdx t hpos i (6 * t - 2) := by
  apply next2_inj t hpos
  rw [next2_prev2, next2, shiftIdx_add, Nat.sub_add_cancel (by omega : 2 ≤ 6 * t)]
  apply Fin.ext; dsimp [shiftIdx]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma nextIdx_prev2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    nextIdx t hpos (prev2 t hpos i) = prevIdx t hpos i := by
  rw [prev2, nextIdx_prevIdx]

lemma prevIdx_next2 (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) :
    prevIdx t hpos (next2 t hpos i) = nextIdx t hpos i := by
  rw [next2_eq_next_next, prevIdx_nextIdx]

def blocksB (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : ℕ :=
  ((laneSub t S p).filter (fun j => next2 t hpos j ∉ laneSub t S p)).card

def adjB (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : Finset (Fin (6 * t)) :=
  (laneSet t (1 - p)).filter (fun i =>
    prevIdx t hpos i ∈ laneSub t S p ∨ nextIdx t hpos i ∈ laneSub t S p)

def freeOpp (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : Finset (Fin (6 * t)) :=
  (laneSub t S (1 - p)).filter (fun i =>
    prevIdx t hpos i ∉ laneSub t S p ∧ nextIdx t hpos i ∉ laneSub t S p)

def missFree (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : Finset (Fin (6 * t)) :=
  ((laneSet t (1 - p)) \ laneSub t S (1 - p)).filter (fun i =>
    prevIdx t hpos i ∉ laneSub t S p ∧ nextIdx t hpos i ∉ laneSub t S p)

def mergedInt (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : Finset (Fin (6 * t)) :=
  (laneSub t S (1 - p)).filter (fun i =>
    prevIdx t hpos i ∈ laneSub t S p ∧ nextIdx t hpos i ∈ laneSub t S p)

lemma blocksB_eq_starts (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) :
    ((laneSub t S p).filter (fun j => prev2 t hpos j ∉ laneSub t S p)).card =
      blocksB t hpos S p := by
  let B := laneSub t S p
  have h1 : B.card = (B.filter (fun j => next2 t hpos j ∈ B)).card +
      (B.filter (fun j => next2 t hpos j ∉ B)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    · rw [Finset.disjoint_left]; intro j ha hb
      exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have h2 : B.card = (B.filter (fun j => prev2 t hpos j ∈ B)).card +
      (B.filter (fun j => prev2 t hpos j ∉ B)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    · rw [Finset.disjoint_left]; intro j ha hb
      exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have h3 : (B.filter (fun j => next2 t hpos j ∈ B)).card =
      (B.filter (fun j => prev2 t hpos j ∈ B)).card :=
    Finset.card_bij (fun j _ => next2 t hpos j)
      (fun j hj => by
        rcases Finset.mem_filter.mp hj with ⟨hjB, hnj⟩
        exact Finset.mem_filter.mpr ⟨hnj, by rw [prev2_next2]; exact hjB⟩)
      (fun _ _ _ _ h => next2_inj t hpos h)
      (fun k hk => by
        rcases Finset.mem_filter.mp hk with ⟨hkB, hpk⟩
        exact ⟨prev2 t hpos k, Finset.mem_filter.mpr ⟨hpk, by rw [next2_prev2]; exact hkB⟩,
          next2_prev2 t hpos k⟩)
  unfold blocksB
  dsimp only [B] at h1 h2 h3
  omega

lemma blocksB_le_card (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) :
    blocksB t hpos S p ≤ (laneSub t S p).card :=
  Finset.card_filter_le _ _

lemma blocksB_pos_of_lt (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    (h0 : 0 < (laneSub t S p).card) (hlt : (laneSub t S p).card < 3 * t) :
    0 < blocksB t hpos S p := by
  by_contra hzero
  have h0' : blocksB t hpos S p = 0 := by omega
  have hcl : ∀ j ∈ laneSub t S p, next2 t hpos j ∈ laneSub t S p := by
    intro j hj
    by_contra hnot
    have hmem : j ∈ (laneSub t S p).filter (fun x => next2 t hpos x ∉ laneSub t S p) :=
      Finset.mem_filter.mpr ⟨hj, hnot⟩
    have := Finset.card_pos.mpr ⟨j, hmem⟩
    unfold blocksB at h0'
    omega
  rcases Finset.card_pos.mp h0 with ⟨j0, hj0⟩
  have hstep : ∀ k : ℕ, shiftIdx t hpos j0 (2 * k) ∈ laneSub t S p := by
    intro k
    induction k with
    | zero => simpa [shiftIdx_zero] using hj0
    | succ k ih =>
      have : shiftIdx t hpos j0 (2 * (k + 1)) = next2 t hpos (shiftIdx t hpos j0 (2 * k)) := by
        rw [next2, shiftIdx_add, Nat.mul_add]
      rw [this]; exact hcl _ ih
  have hsub : laneSet t p ⊆ laneSub t S p := by
    intro y hy
    have hy_p : y.val % 2 = p := (Finset.mem_filter.mp hy).2
    have hj0_p : j0.val % 2 = p := (Finset.mem_filter.mp hj0).2
    let d : ℕ := (y.val + 6 * t - j0.val) % (6 * t)
    have hd_even : d % 2 = 0 := by
      have h2 : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
      have hdm : d % 2 = (y.val + 6 * t - j0.val) % 2 := Nat.mod_mod_of_dvd _ h2
      have := j0.isLt; have := y.isLt
      omega
    have hsh : shiftIdx t hpos j0 d = y := by
      apply Fin.ext; dsimp [shiftIdx, d]
      have := j0.isLt; have := y.isLt
      by_cases hle : j0.val ≤ y.val
      · have h1 : (y.val + 6 * t - j0.val) % (6 * t) = y.val - j0.val := by
          rw [show y.val + 6 * t - j0.val = (y.val - j0.val) + 6 * t by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1, show j0.val + (y.val - j0.val) = y.val by omega, Nat.mod_eq_of_lt (by omega)]
      · have h1 : (y.val + 6 * t - j0.val) % (6 * t) = y.val + 6 * t - j0.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [h1, show j0.val + (y.val + 6 * t - j0.val) = y.val + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have : 2 * (d / 2) = d := by omega
    rw [← hsh, ← this]
    exact hstep (d / 2)
  have hle := Finset.card_le_card hsub
  rw [card_laneSet t p hp] at hle
  omega

lemma card_adjB (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    (adjB t hpos S p).card = (laneSub t S p).card + blocksB t hpos S p := by
  let B := laneSub t S p
  let A1 := (laneSet t (1 - p)).filter (fun i => prevIdx t hpos i ∈ B)
  let A2 := (laneSet t (1 - p)).filter (fun i => prevIdx t hpos i ∉ B ∧ nextIdx t hpos i ∈ B)
  have hdisj : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro i h1 h2
    exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2
  have hun : A1 ∪ A2 = adjB t hpos S p := by
    ext i
    simp only [A1, A2, adjB, Finset.mem_union, Finset.mem_filter]
    tauto
  have hA1 : A1.card = B.card :=
    Finset.card_bij (fun i _ => prevIdx t hpos i)
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun _ _ _ _ h => prevIdx_inj t hpos h)
      (fun j hj => by
        have hjp : j.val % 2 = p := (Finset.mem_filter.mp hj).2
        refine ⟨nextIdx t hpos j, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          by rw [prevIdx_nextIdx]; exact hj⟩, prevIdx_nextIdx t hpos j⟩
        rw [nextIdx_mod2, hjp])
  have hA2 : A2.card = (B.filter (fun j => prev2 t hpos j ∉ B)).card :=
    Finset.card_bij (fun i _ => nextIdx t hpos i)
      (fun i hi => by
        rcases Finset.mem_filter.mp hi with ⟨_, hpre, hnxt⟩
        refine Finset.mem_filter.mpr ⟨hnxt, ?_⟩
        rw [prev2, prevIdx_nextIdx]; exact hpre)
      (fun _ _ _ _ h => nextIdx_inj t hpos h)
      (fun j hj => by
        rcases Finset.mem_filter.mp hj with ⟨hjB, hpre2⟩
        have hjp : j.val % 2 = p := (Finset.mem_filter.mp hjB).2
        refine ⟨prevIdx t hpos j, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          hpre2, by rw [nextIdx_prevIdx]; exact hjB⟩, nextIdx_prevIdx t hpos j⟩
        rw [prevIdx_mod2, hjp])
  rw [← hun, Finset.card_union_of_disjoint hdisj, hA1, hA2, blocksB_eq_starts]

lemma card_freeOpp_add (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    (freeOpp t hpos S p).card + (laneSub t S p).card + blocksB t hpos S p +
      (missFree t hpos S p).card = 3 * t := by
  have hdisj1 : Disjoint (freeOpp t hpos S p) (missFree t hpos S p) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h2).1).2 (Finset.mem_filter.mp h1).1
  have hdisj2 : Disjoint (freeOpp t hpos S p ∪ missFree t hpos S p) (adjB t hpos S p) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    have hor := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · rcases (Finset.mem_filter.mp h1).2 with ⟨ha, hb⟩
      exact hor.elim ha hb
    · rcases (Finset.mem_filter.mp h1).2 with ⟨ha, hb⟩
      exact hor.elim ha hb
  have hun : (freeOpp t hpos S p ∪ missFree t hpos S p) ∪ adjB t hpos S p = laneSet t (1 - p) := by
    ext i
    simp only [freeOpp, missFree, adjB, laneSub, laneSet, Finset.mem_union,
      Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hcard := Finset.card_union_of_disjoint hdisj2
  rw [hun, Finset.card_union_of_disjoint hdisj1, card_adjB t hpos S p hp,
    card_laneSet t (1 - p) (by omega)] at hcard
  omega

lemma runsS_add_mergedInt (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    runsS t hpos S + (mergedInt t hpos S p).card =
      (freeOpp t hpos S p).card + (laneSub t S p).card := by
  let A := laneSub t S (1 - p)
  let B := laneSub t S p
  have hruns_split : runsS t hpos S =
      (A.filter (fun i => nextIdx t hpos i ∉ B)).card +
      (B.filter (fun j => nextIdx t hpos j ∉ A)).card := by
    have hdisj : Disjoint (A.filter (fun i => nextIdx t hpos i ∉ B))
        (B.filter (fun j => nextIdx t hpos j ∉ A)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      have hi1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have hi2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      omega
    have hun : A.filter (fun i => nextIdx t hpos i ∉ B) ∪
        B.filter (fun j => nextIdx t hpos j ∉ A) = S.filter (fun i => nextIdx t hpos i ∉ S) := by
      ext i
      simp only [A, B, laneSub, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨⟨hiS, hip⟩, hni⟩ | ⟨⟨hiS, hip⟩, hni⟩)
        · refine ⟨hiS, fun hniS => hni ⟨hniS, ?_⟩⟩
          rw [nextIdx_mod2, hip]; omega
        · refine ⟨hiS, fun hniS => hni ⟨hniS, ?_⟩⟩
          rw [nextIdx_mod2, hip]
      · rintro ⟨hiS, hniS⟩
        by_cases hip : i.val % 2 = p
        · right; exact ⟨⟨hiS, hip⟩, fun h => hniS h.1⟩
        · left; exact ⟨⟨hiS, by omega⟩, fun h => hniS h.1⟩
    unfold runsS
    rw [← hun, Finset.card_union_of_disjoint hdisj]
  let R1 := A.filter (fun i => prevIdx t hpos i ∈ B ∧ nextIdx t hpos i ∉ B)
  have hA_split : (A.filter (fun i => nextIdx t hpos i ∉ B)).card =
      (freeOpp t hpos S p).card + R1.card := by
    have hdisj : Disjoint (freeOpp t hpos S p) R1 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
    have hun : freeOpp t hpos S p ∪ R1 = A.filter (fun i => nextIdx t hpos i ∉ B) := by
      ext i; simp only [freeOpp, R1, A, B, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← hun, Finset.card_union_of_disjoint hdisj]
  have hRM : R1.card + (mergedInt t hpos S p).card =
      (B.filter (fun j => nextIdx t hpos j ∈ A)).card := by
    have hdisj : Disjoint R1 (mergedInt t hpos S p) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
    rw [← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_bij (fun i _ => prevIdx t hpos i) ?_ (fun _ _ _ _ h => prevIdx_inj t hpos h) ?_
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_filter.mp hi with ⟨hiA, hpre, _⟩
        exact Finset.mem_filter.mpr ⟨hpre, by rw [nextIdx_prevIdx]; exact hiA⟩
      · rcases Finset.mem_filter.mp hi with ⟨hiA, hpre, _⟩
        exact Finset.mem_filter.mpr ⟨hpre, by rw [nextIdx_prevIdx]; exact hiA⟩
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjB, hnjA⟩
      refine ⟨nextIdx t hpos j, ?_, prevIdx_nextIdx t hpos j⟩
      by_cases h2 : nextIdx t hpos (nextIdx t hpos j) ∈ B
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnjA, by rw [prevIdx_nextIdx]; exact hjB, h2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnjA, by rw [prevIdx_nextIdx]; exact hjB, h2⟩)
  have hB_split : (B.filter (fun j => nextIdx t hpos j ∈ A)).card +
      (B.filter (fun j => nextIdx t hpos j ∉ A)).card = B.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    · rw [Finset.disjoint_left]; intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  dsimp only [A, B] at hruns_split hA_split hRM hB_split
  omega

lemma runsS_identity (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    runsS t hpos S + blocksB t hpos S p + (missFree t hpos S p).card +
      (mergedInt t hpos S p).card = 3 * t := by
  have h1 := runsS_add_mergedInt t hpos S p hp
  have h2 := card_freeOpp_add t hpos S p hp
  omega

lemma two_mul_B_le (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hle : (laneSub t S p).card ≤ (laneSub t S (1 - p)).card) :
    2 * (laneSub t S p).card + (missFree t hpos S p).card ≤
      3 * t + blocksB t hpos S p + (mergedInt t hpos S p).card := by
  let A := laneSub t S (1 - p)
  let B := laneSub t S p
  let unmerged := ((laneSet t (1 - p)) \ A).filter (fun i =>
    prevIdx t hpos i ∈ B ∧ nextIdx t hpos i ∈ B)
  have hunm_add : unmerged.card + (mergedInt t hpos S p).card + blocksB t hpos S p = B.card := by
    have hdisj : Disjoint unmerged (mergedInt t hpos S p) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2 (Finset.mem_filter.mp h2).1
    have hall : (unmerged ∪ mergedInt t hpos S p).card =
        (B.filter (fun j => next2 t hpos j ∈ B)).card :=
      Finset.card_bij (fun i _ => prevIdx t hpos i)
        (fun i hi => by
          rcases Finset.mem_union.mp hi with hi | hi
          · rcases Finset.mem_filter.mp hi with ⟨_, hpre, hnxt⟩
            exact Finset.mem_filter.mpr ⟨hpre, by rw [next2_eq_next_next, nextIdx_prevIdx]; exact hnxt⟩
          · rcases Finset.mem_filter.mp hi with ⟨_, hpre, hnxt⟩
            exact Finset.mem_filter.mpr ⟨hpre, by rw [next2_eq_next_next, nextIdx_prevIdx]; exact hnxt⟩)
        (fun _ _ _ _ h => prevIdx_inj t hpos h)
        (fun j hj => by
          rcases Finset.mem_filter.mp hj with ⟨hjB, hn2B⟩
          have hjp : j.val % 2 = p := (Finset.mem_filter.mp hjB).2
          have hnj_lane : nextIdx t hpos j ∈ laneSet t (1 - p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [nextIdx_mod2, hjp]⟩
          refine ⟨nextIdx t hpos j, ?_, prevIdx_nextIdx t hpos j⟩
          by_cases hnjA : nextIdx t hpos j ∈ A
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnjA,
              by rw [prevIdx_nextIdx]; exact hjB, by rw [← next2_eq_next_next]; exact hn2B⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hnj_lane, hnjA⟩,
              by rw [prevIdx_nextIdx]; exact hjB, by rw [← next2_eq_next_next]; exact hn2B⟩))
    have hBsplit : (B.filter (fun j => next2 t hpos j ∈ B)).card + blocksB t hpos S p = B.card := by
      unfold blocksB
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext j; simp only [B, Finset.mem_union, Finset.mem_filter]; tauto
      · rw [Finset.disjoint_left]; intro j h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [Finset.card_union_of_disjoint hdisj] at hall
    omega
  have hdisj_out : Disjoint (missFree t hpos S p) unmerged := by
    rw [Finset.disjoint_left]; intro i h1 h2
    exact (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
  have hsub_out : missFree t hpos S p ∪ unmerged ⊆ laneSet t (1 - p) \ A := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_filter.mp hi).1
    · exact (Finset.mem_filter.mp hi).1
  have hle_out := Finset.card_le_card hsub_out
  rw [Finset.card_union_of_disjoint hdisj_out,
    Finset.card_sdiff_of_subset (laneSub_subset_laneSet t S (1 - p)),
    card_laneSet t (1 - p) (by omega)] at hle_out
  have hA_le : A.card ≤ 3 * t := by
    have := Finset.card_le_card (laneSub_subset_laneSet t S (1 - p))
    rwa [card_laneSet t (1 - p) (by omega)] at this
  dsimp only [A, B] at hunm_add hle_out hA_le
  omega

lemma three_t_le_of_smaller (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hle : (laneSub t S p).card ≤ (laneSub t S (1 - p)).card) :
    3 * t ≤ 2 * (freeOpp t hpos S p).card + 3 * blocksB t hpos S p +
      (missFree t hpos S p).card + (mergedInt t hpos S p).card := by
  have h1 := two_mul_B_le t hpos S p hp hle
  have h2 := card_freeOpp_add t hpos S p hp
  omega

-- Lane projection and 2-bit syndrome helpers
def laneBit (p : ℕ) (k : Fin 2) : Fin 4 :=
  if p = 0 then ⟨k.val, by omega⟩ else ⟨k.val + 2, by omega⟩

def projLane (p : ℕ) : (Fin 4 → F2) →ₗ[F2] (Fin 2 → F2) :=
  { toFun := fun y k => y (laneBit p k)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def hLane (t : ℕ) (p : ℕ) (i : Fin (6 * t)) : Fin 2 → F2 :=
  fun k => hFn t i (laneBit p k)

lemma laneBit_div2 (p : ℕ) (hp : p = 0 ∨ p = 1) (k : Fin 2) :
    (laneBit p k).val / 2 = p := by
  rcases hp with rfl | rfl <;> fin_cases k <;> rfl

lemma laneBit_mod2 (p : ℕ) (hp : p = 0 ∨ p = 1) (k : Fin 2) :
    (laneBit p k).val % 2 = k.val := by
  rcases hp with rfl | rfl <;> fin_cases k <;> rfl

lemma hLane_other (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) (i : Fin (6 * t))
    (hne : i.val % 2 ≠ p) : hLane t p i = 0 := by
  ext k
  simp only [hLane, Pi.zero_apply]
  exact hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hne)

lemma hLane_val (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) (i : Fin (6 * t))
    (hi : i.val % 2 = p) (k : Fin 2) :
    hLane t p i k = if i.val / 2 % 3 = k.val ∨ i.val / 2 % 3 = 2 then (1 : F2) else 0 := by
  simp only [hLane, hFn, laneBit_div2 p hp k, laneBit_mod2 p hp k, hi, true_and]

lemma hLane_ne_zero (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) (i : Fin (6 * t))
    (hi : i.val % 2 = p) : hLane t p i ≠ 0 := by
  intro h0
  have h00 := congrFun h0 0
  have h01 := congrFun h0 1
  rw [hLane_val t p hp i hi 0] at h00
  rw [hLane_val t p hp i hi 1] at h01
  have hr : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rcases hr with hr | hr | hr <;> simp [hr] at h00 h01

lemma hLane_eq_iff (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) (i j : Fin (6 * t))
    (hi : i.val % 2 = p) (hj : j.val % 2 = p) :
    hLane t p i = hLane t p j ↔ i.val / 2 % 3 = j.val / 2 % 3 := by
  constructor
  · intro heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    rw [hLane_val t p hp i hi 0, hLane_val t p hp j hj 0] at h0
    rw [hLane_val t p hp i hi 1, hLane_val t p hp j hj 1] at h1
    have hri : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
    have hrj : j.val / 2 % 3 = 0 ∨ j.val / 2 % 3 = 1 ∨ j.val / 2 % 3 = 2 := by omega
    rcases hri with hri | hri | hri <;> rcases hrj with hrj | hrj | hrj <;>
      simp [hri, hrj] at h0 h1 ⊢
  · intro hmod
    ext k
    rw [hLane_val t p hp i hi k, hLane_val t p hp j hj k, hmod]

lemma hLane_span_of_ne (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) (i j : Fin (6 * t))
    (hi : i.val % 2 = p) (hj : j.val % 2 = p)
    (hne : i.val / 2 % 3 ≠ j.val / 2 % 3) (y : Fin 2 → F2) :
    ∃ c0 c1 : F2, c0 • hLane t p i + c1 • hLane t p j = y := by
  have hri : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  have hrj : j.val / 2 % 3 = 0 ∨ j.val / 2 % 3 = 1 ∨ j.val / 2 % 3 = 2 := by omega
  rcases hri with hri | hri | hri <;> rcases hrj with hrj | hrj | hrj
  · exact absurd (hri.trans hrj.symm) hne
  · refine ⟨y 0, y 1, ?_⟩
    ext k; fin_cases k <;> simp [hLane_val t p hp i hi, hLane_val t p hp j hj, hri, hrj]
  · refine ⟨y 0 + y 1, y 1, ?_⟩
    ext k; fin_cases k <;> simp [hLane_val t p hp i hi, hLane_val t p hp j hj, hri, hrj]
    calc y 0 + y 1 + y 1 = y 0 + (y 1 + y 1) := by ring
      _ = y 0 := by rw [zmod2_add_self, add_zero]
  · refine ⟨y 1, y 0, ?_⟩
    ext k; fin_cases k <;> simp [hLane_val t p hp i hi, hLane_val t p hp j hj, hri, hrj]
  · exact absurd (hri.trans hrj.symm) hne
  · refine ⟨y 0 + y 1, y 0, ?_⟩
    ext k; fin_cases k <;> simp [hLane_val t p hp i hi, hLane_val t p hp j hj, hri, hrj]
    calc y 0 + y 1 + y 0 = y 1 + (y 0 + y 0) := by ring
      _ = y 1 := by rw [zmod2_add_self, add_zero]
  · refine ⟨y 1, y 0 + y 1, ?_⟩
    ext k; fin_cases k <;> simp [hLane_val t p hp i hi, hLane_val t p hp j hj, hri, hrj]
    calc y 1 + (y 0 + y 1) = y 0 + (y 1 + y 1) := by ring
      _ = y 0 := by rw [zmod2_add_self, add_zero]
  · refine ⟨y 0, y 0 + y 1, ?_⟩
    ext k; fin_cases k <;> simp [hLane_val t p hp i hi, hLane_val t p hp j hj, hri, hrj]
    calc y 0 + (y 0 + y 1) = (y 0 + y 0) + y 1 := by ring
      _ = y 1 := by rw [zmod2_add_self, zero_add]
  · exact absurd (hri.trans hrj.symm) hne

lemma hLane_sum_triple (t : ℕ) (hpos : 0 < t) (p : ℕ) (i : Fin (6 * t)) :
    hLane t p i + hLane t p (shiftIdx t hpos i 2) + hLane t p (shiftIdx t hpos i 4) = 0 := by
  ext k
  exact hFn_sum_triple t hpos i (laneBit p k)

lemma hLane_pair_eq_third (t : ℕ) (hpos : 0 < t) (p : ℕ) (i : Fin (6 * t)) :
    hLane t p i + hLane t p (shiftIdx t hpos i 2) = hLane t p (shiftIdx t hpos i 4) := by
  have h := hLane_sum_triple t hpos p i
  ext k
  have hk := congrFun h k
  simp only [Pi.add_apply, Pi.zero_apply] at hk ⊢
  calc hLane t p i k + hLane t p (shiftIdx t hpos i 2) k
      = (hLane t p i k + hLane t p (shiftIdx t hpos i 2) k + hLane t p (shiftIdx t hpos i 4) k) +
          hLane t p (shiftIdx t hpos i 4) k := by
            rw [add_assoc, zmod2_add_self, add_zero]
    _ = hLane t p (shiftIdx t hpos i 4) k := by rw [hk, zero_add]

lemma hLane_prev_next_eq_prev3 (t : ℕ) (hpos : 0 < t) (p : ℕ) (m : Fin (6 * t)) :
    hLane t p (prevIdx t hpos m) + hLane t p (nextIdx t hpos m) =
      hLane t p (prevIdx t hpos (prev2 t hpos m)) := by
  have h := hLane_pair_eq_third t hpos p (prevIdx t hpos (prev2 t hpos m))
  have h1 : shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 2 = prevIdx t hpos m := by
    rw [← next2, next2_eq_next_next, nextIdx_prevIdx, nextIdx_prev2]
  have h2 : shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 4 = nextIdx t hpos m := by
    have : shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 4 =
        shiftIdx t hpos (shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 2) 2 := by
      rw [shiftIdx_add]
    rw [this, h1, ← next2, next2_eq_next_next, nextIdx_prevIdx]
  rw [h1, h2] at h
  ext k
  have hk := congrFun h k
  simp only [Pi.add_apply] at hk ⊢
  calc hLane t p (prevIdx t hpos m) k + hLane t p (nextIdx t hpos m) k
      = hLane t p (prevIdx t hpos m) k +
          (hLane t p (prevIdx t hpos (prev2 t hpos m)) k + hLane t p (prevIdx t hpos m) k) := by
            rw [← hk]
    _ = hLane t p (prevIdx t hpos (prev2 t hpos m)) k := by
          have : hLane t p (prevIdx t hpos m) k +
              (hLane t p (prevIdx t hpos (prev2 t hpos m)) k + hLane t p (prevIdx t hpos m) k) =
              hLane t p (prevIdx t hpos (prev2 t hpos m)) k +
              (hLane t p (prevIdx t hpos m) k + hLane t p (prevIdx t hpos m) k) := by ring
          rw [this, zmod2_add_self, add_zero]

lemma hLane_prev3_eq_next3 (t : ℕ) (hpos : 0 < t) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (m : Fin (6 * t)) (hm : m.val % 2 = 1 - p) :
    hLane t p (prevIdx t hpos (prev2 t hpos m)) = hLane t p (nextIdx t hpos (next2 t hpos m)) := by
  have h1 : (prevIdx t hpos (prev2 t hpos m)).val % 2 = p := by
    rw [prevIdx_mod2, prev2_mod2, hm]; omega
  have h2 : (nextIdx t hpos (next2 t hpos m)).val % 2 = p := by
    rw [nextIdx_mod2, next2_mod2, hm]; omega
  have hshift : shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 6 =
      nextIdx t hpos (next2 t hpos m) := by
    have s0 : shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 6 =
        next2 t hpos (next2 t hpos (next2 t hpos (prevIdx t hpos (prev2 t hpos m)))) := by
      simp only [next2, shiftIdx_add]
    have s1 : next2 t hpos (prevIdx t hpos (prev2 t hpos m)) = prevIdx t hpos m := by
      rw [next2_eq_next_next, nextIdx_prevIdx, nextIdx_prev2]
    have s2 : next2 t hpos (prevIdx t hpos m) = nextIdx t hpos m := by
      rw [next2_eq_next_next, nextIdx_prevIdx]
    have s3 : next2 t hpos (nextIdx t hpos m) = nextIdx t hpos (next2 t hpos m) := by
      rw [next2_eq_next_next, next2_eq_next_next]
    rw [s0, s1, s2, s3]
  rw [← hshift, hLane_eq_iff t p hp _ _ h1 (by rw [hshift]; exact h2)]
  have hs6 : (shiftIdx t hpos (prevIdx t hpos (prev2 t hpos m)) 6).val / 2 % 3 =
      (prevIdx t hpos (prev2 t hpos m)).val / 2 % 3 := by
    let x0 := prevIdx t hpos (prev2 t hpos m)
    let x1 := shiftIdx t hpos x0 2
    let x2 := shiftIdx t hpos x1 2
    let x3 := shiftIdx t hpos x2 2
    have h4 : shiftIdx t hpos x0 6 = x3 := by simp only [x3, x2, x1, shiftIdx_add]
    have d1 : x1.val / 2 % 3 = (x0.val / 2 + 1) % 3 := shiftIdx_two_div2_mod3 t hpos x0
    have d2 : x2.val / 2 % 3 = (x1.val / 2 + 1) % 3 := shiftIdx_two_div2_mod3 t hpos x1
    have d3 : x3.val / 2 % 3 = (x2.val / 2 + 1) % 3 := shiftIdx_two_div2_mod3 t hpos x2
    change (shiftIdx t hpos x0 6).val / 2 % 3 = x0.val / 2 % 3
    rw [h4, d3, Nat.add_mod (x2.val / 2) 1, d2, Nat.add_mod (x1.val / 2) 1, d1]
    omega
  exact hs6.symm

def HV (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) :
    Vset t hpos S →ₗ[F2] (Fin 4 → F2) :=
  (Hmap t).comp (Vset t hpos S).subtype

noncomputable def rB (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : ℕ :=
  Module.finrank F2 (LinearMap.range ((projLane p).comp (HV t hpos S)))

noncomputable def freeImg (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) :
    Submodule F2 (Fin 4 → F2) :=
  Submodule.span F2
    (((freeOpp t hpos S p).image (fun i => Hmap t (Pi.single i (1 : F2)))) : Set (Fin 4 → F2))

noncomputable def rFree (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) : ℕ :=
  Module.finrank F2 (freeImg t hpos S p)

lemma freeOpp_single_mem_Vset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) {i : Fin (6 * t)} (hi : i ∈ freeOpp t hpos S p) :
    Pi.single i (1 : F2) ∈ Vset t hpos S := by
  rcases Finset.mem_filter.mp hi with ⟨hiA, hpre, hnxt⟩
  rcases Finset.mem_filter.mp hiA with ⟨hiS, hip⟩
  refine single_mem_Vset t hpos S i hiS ?_ ?_
  · intro hS; apply hpre; exact Finset.mem_filter.mpr ⟨hS, by rw [prevIdx_mod2, hip]; omega⟩
  · intro hS; apply hnxt; exact Finset.mem_filter.mpr ⟨hS, by rw [nextIdx_mod2, hip]; omega⟩

lemma freeImg_le_range_inf_ker (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    freeImg t hpos S p ≤ LinearMap.range (HV t hpos S) ⊓ LinearMap.ker (projLane p) := by
  unfold freeImg
  rw [Submodule.span_le]
  intro y hy
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨i, hi, rfl⟩
  refine ⟨⟨⟨Pi.single i (1 : F2), freeOpp_single_mem_Vset t hpos S p hp hi⟩, rfl⟩, ?_⟩
  ext k
  change Hmap t (Pi.single i (1 : F2)) (laneBit p k) = 0
  rw [Hmap_single]
  have hip : i.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  exact hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k, hip]; omega)

lemma rFree_add_rB_le_rankHV (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    rFree t hpos S p + rB t hpos S p ≤ Module.finrank F2 (LinearMap.range (HV t hpos S)) := by
  let R := LinearMap.range (HV t hpos S)
  let g : R →ₗ[F2] (Fin 2 → F2) := (projLane p).comp R.subtype
  have hrg : LinearMap.range g = LinearMap.range ((projLane p).comp (HV t hpos S)) := by
    ext z; simp only [g, R, LinearMap.mem_range, LinearMap.comp_apply, Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨y, x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨⟨HV t hpos S x, x, rfl⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrg] at hrn
  have hle_ker : rFree t hpos S p ≤ Module.finrank F2 (LinearMap.ker g) := by
    let e : (R ⊓ LinearMap.ker (projLane p) : Submodule F2 (Fin 4 → F2)) ≃ₗ[F2] LinearMap.ker g :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [← e.finrank_eq]
    exact Submodule.finrank_mono (freeImg_le_range_inf_ker t hpos S p hp)
  unfold rB
  have h1 : Module.finrank F2 (LinearMap.range ((projLane p).comp (HV t hpos S))) +
      Module.finrank F2 (LinearMap.ker g) = Module.finrank F2 (LinearMap.range (HV t hpos S)) := hrn
  omega

lemma finrank_GoodMax_add_rankHV (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (hruns : 0 < runsS t hpos S) :
    Module.finrank F2 (GoodMax t hpos S) + Module.finrank F2 (LinearMap.range (HV t hpos S)) =
      runsS t hpos S := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (HV t hpos S)
  rw [finrank_Vset t hpos S hruns] at hrn
  have hker : Module.finrank F2 (GoodMax t hpos S) = Module.finrank F2 (LinearMap.ker (HV t hpos S)) := by
    let e : GoodMax t hpos S ≃ₗ[F2] LinearMap.ker (HV t hpos S) :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  omega

lemma master_ineq (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hruns : 0 < runsS t hpos S)
    (hfr : 3 * t - 5 ≤ Module.finrank F2 (GoodMax t hpos S)) :
    blocksB t hpos S p + (missFree t hpos S p).card + (mergedInt t hpos S p).card +
      rFree t hpos S p + rB t hpos S p ≤ 5 := by
  have h1 := runsS_identity t hpos S p hp
  have h2 := finrank_GoodMax_add_rankHV t hpos S hruns
  have h3 := rFree_add_rB_le_rankHV t hpos S p hp
  omega

lemma rB_le_two (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (p : ℕ) :
    rB t hpos S p ≤ 2 := by
  unfold rB
  calc Module.finrank F2 (LinearMap.range ((projLane p).comp (HV t hpos S)))
      ≤ Module.finrank F2 (Fin 2 → F2) := Submodule.finrank_le _
    _ = 2 := by rw [Module.finrank_fin_fun]

lemma rFree_le_two (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    rFree t hpos S p ≤ 2 := by
  have hle : freeImg t hpos S p ≤ LinearMap.ker (projLane p) :=
    le_trans (freeImg_le_range_inf_ker t hpos S p hp) inf_le_right
  have hker_fr : Module.finrank F2 (LinearMap.ker (projLane p)) ≤ 2 := by
    have hsurj : Function.Surjective (projLane p) := by
      intro z
      refine ⟨fun b => if b = laneBit p 0 then z 0 else if b = laneBit p 1 then z 1 else 0, ?_⟩
      ext k
      have hne : laneBit p 0 ≠ laneBit p 1 := by
        rcases hp with rfl | rfl <;> decide
      fin_cases k
      · simp [projLane]
      · simp [projLane, hne.symm]
    have hrn := LinearMap.finrank_range_add_finrank_ker (projLane p)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at hrn
    omega
  exact le_trans (Submodule.finrank_mono hle) hker_fr

lemma rFree_eq_zero_imp_empty (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) (h0 : rFree t hpos S p = 0) :
    freeOpp t hpos S p = ∅ := by
  by_contra hne
  rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨i, hi⟩
  have hmem : Hmap t (Pi.single i (1 : F2)) ∈ freeImg t hpos S p :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hnz : Hmap t (Pi.single i (1 : F2)) ≠ 0 := by
    intro hz
    have hip : i.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    apply hLane_ne_zero t (1 - p) (by omega) i hip
    ext k
    have := congrFun hz (laneBit (1 - p) k)
    simpa [hLane, Hmap_single] using this
  have hbot : freeImg t hpos S p = ⊥ := Submodule.finrank_eq_zero.mp h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hnz hmem

lemma rFree_eq_two_of_diff_mod3 (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    {i1 i2 : Fin (6 * t)} (h1 : i1 ∈ freeOpp t hpos S p) (h2 : i2 ∈ freeOpp t hpos S p)
    (hne : i1.val / 2 % 3 ≠ i2.val / 2 % 3) :
    rFree t hpos S p = 2 := by
  apply le_antisymm (rFree_le_two t hpos S p hp)
  have hip1 : i1.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
  have hip2 : i2.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
  have hm1 : Hmap t (Pi.single i1 (1 : F2)) ∈ freeImg t hpos S p :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i1, h1, rfl⟩))
  have hm2 : Hmap t (Pi.single i2 (1 : F2)) ∈ freeImg t hpos S p :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i2, h2, rfl⟩))
  let q : freeImg t hpos S p →ₗ[F2] (Fin 2 → F2) :=
    (projLane (1 - p)).comp (freeImg t hpos S p).subtype
  have hsurj : Function.Surjective q := by
    intro y
    rcases hLane_span_of_ne t (1 - p) (by omega) i1 i2 hip1 hip2 hne y with ⟨c0, c1, hc⟩
    refine ⟨c0 • ⟨_, hm1⟩ + c1 • ⟨_, hm2⟩, ?_⟩
    ext k
    have hkc := congrFun hc k
    simpa [q, projLane, hLane, Hmap_single] using hkc
  have hrn := LinearMap.finrank_range_add_finrank_ker q
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  unfold rFree; omega

lemma freeOpp_card_le_of_rFree_le_one (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hr : rFree t hpos S p ≤ 1) :
    (freeOpp t hpos S p).card ≤ blocksB t hpos S p + (missFree t hpos S p).card := by
  have hsame : ∀ i1 ∈ freeOpp t hpos S p, ∀ i2 ∈ freeOpp t hpos S p,
      i1.val / 2 % 3 = i2.val / 2 % 3 := by
    intro i1 h1 i2 h2
    by_contra hne
    have := rFree_eq_two_of_diff_mod3 t hpos S p hp h1 h2 hne
    omega
  let F := freeOpp t hpos S p
  let L1 := F.image (prevIdx t hpos)
  let L2 := F.image (nextIdx t hpos)
  have hdisj : Disjoint L1 L2 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨i1, hi1, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨i2, hi2, heq⟩
    have hshift : next2 t hpos i2 = i1 := by
      rw [next2_eq_next_next, heq, nextIdx_prevIdx]
    have hp1 : i1.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hi1).1).2
    have hp2 : i2.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hi2).1).2
    have hm := hsame i1 hi1 i2 hi2
    have hd2 : i1.val / 2 % 3 = (i2.val / 2 + 1) % 3 := by
      rw [← hshift, next2, shiftIdx_two_div2_mod3]
    omega
  have hsub : L1 ∪ L2 ⊆ laneSet t p \ laneSub t S p := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rcases Finset.mem_filter.mp hi with ⟨hiA, hpre, _⟩
      have hip : i.val % 2 = 1 - p := (Finset.mem_filter.mp hiA).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [prevIdx_mod2, hip]; omega⟩, hpre⟩
    · rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rcases Finset.mem_filter.mp hi with ⟨hiA, _, hnxt⟩
      have hip : i.val % 2 = 1 - p := (Finset.mem_filter.mp hiA).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [nextIdx_mod2, hip]; omega⟩, hnxt⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (prevIdx_inj t hpos),
    Finset.card_image_of_injective _ (nextIdx_inj t hpos),
    Finset.card_sdiff_of_subset (laneSub_subset_laneSet t S p),
    card_laneSet t p hp] at hle
  have hB_le : (laneSub t S p).card ≤ 3 * t := by
    have := Finset.card_le_card (laneSub_subset_laneSet t S p)
    rwa [card_laneSet t p hp] at this
  have hadd := card_freeOpp_add t hpos S p hp
  dsimp only [F] at hle
  omega

-- Explicit local vectors isoVec (3-site) and pairVec (5-site)
def isoVec (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (j : Fin (6 * t)) :
    Fin (6 * t) → F2 :=
  fun x =>
    if x = j ∨ (x = prevIdx t hpos j ∧ prevIdx t hpos j ∈ S) ∨
       (x = nextIdx t hpos j ∧ nextIdx t hpos j ∈ S)
    then 1 else 0

lemma shiftIdx_ne_self_of_pos (t : ℕ) (hpos : 0 < t) (i : Fin (6 * t)) {d : ℕ}
    (hd0 : 0 < d) (hdn : d < 6 * t) : shiftIdx t hpos i d ≠ i := by
  intro heq
  have h := shiftIdx_inj_range t hpos i hdn (by omega : 0 < 6 * t)
    (heq.trans (shiftIdx_zero t hpos i).symm)
  omega

lemma isoVec_mem_Vset (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) {j : Fin (6 * t)} (hj : j ∈ laneSub t S p)
    (hpre : prevIdx t hpos j ∉ mergedInt t hpos S p)
    (hnxt : nextIdx t hpos j ∉ mergedInt t hpos S p) :
    isoVec t hpos S j ∈ Vset t hpos S := by
  have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
  have hjp : j.val % 2 = p := (Finset.mem_filter.mp hj).2
  have hpre_out : prevIdx t hpos j ∈ S → prev2 t hpos j ∉ S := by
    intro h1 h2
    apply hpre
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h1, by rw [prevIdx_mod2, hjp]⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨h2, by rw [prevIdx_mod2, prevIdx_mod2, hjp]; omega⟩
    · rw [nextIdx_prevIdx]; exact hj
  have hnxt_out : nextIdx t hpos j ∈ S → next2 t hpos j ∉ S := by
    intro h1 h2
    apply hnxt
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h1, by rw [nextIdx_mod2, hjp]⟩, ?_, ?_⟩
    · rw [prevIdx_nextIdx]; exact hj
    · exact Finset.mem_filter.mpr ⟨by rw [← next2_eq_next_next]; exact h2, by rw [nextIdx_mod2, nextIdx_mod2, hjp]; omega⟩
  have hne_pj : prevIdx t hpos j ≠ j := by
    intro h; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx] at this
    exact shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega) this.symm
  have hne_nj : nextIdx t hpos j ≠ j :=
    shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega)
  have hne_pn : prevIdx t hpos j ≠ nextIdx t hpos j := by
    intro h; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, ← next2_eq_next_next] at this
    exact shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega) this.symm
  have hne_n2p : next2 t hpos j ≠ prevIdx t hpos j := by
    intro h; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx] at this
    have h3 : nextIdx t hpos (next2 t hpos j) = shiftIdx t hpos j 3 := by
      rw [next2, ← shiftIdx_one, shiftIdx_add]
    rw [h3] at this
    exact shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega) this
  have hne_p2n : prev2 t hpos j ≠ nextIdx t hpos j := by
    intro h; have := congrArg (next2 t hpos) h; rw [next2_prev2] at this
    have h3 : next2 t hpos (nextIdx t hpos j) = shiftIdx t hpos j 3 := by
      rw [next2, ← shiftIdx_one, shiftIdx_add]
    rw [h3] at this
    exact shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega) this.symm
  refine ⟨fun x hx => ?_, fun x hx hnx => ?_⟩
  · unfold isoVec
    rw [if_neg]
    rintro (rfl | ⟨rfl, h1⟩ | ⟨rfl, h1⟩)
    · exact hx hjS
    · exact hx h1
    · exact hx h1
  · unfold isoVec
    by_cases hx1 : x = j
    · subst hx1
      rw [if_pos (Or.inl rfl), if_pos (Or.inr (Or.inr ⟨rfl, hnx⟩))]
    · by_cases hx2 : x = prevIdx t hpos j
      · subst hx2
        rw [nextIdx_prevIdx, if_pos (Or.inr (Or.inl ⟨rfl, hx⟩)), if_pos (Or.inl rfl)]
      · by_cases hx3 : x = nextIdx t hpos j
        · subst hx3
          exact False.elim (hnxt_out hx (by rwa [next2_eq_next_next]))
        · rw [if_neg (by tauto), if_neg]
          rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
          · exact hx2 (by rw [← prevIdx_nextIdx t hpos x, h])
          · exact hpre_out (h ▸ hnx) (by rw [prev2, ← h, prevIdx_nextIdx]; exact hx)
          · exact hx1 (nextIdx_inj t hpos h)

lemma projLane_Hmap_isoVec (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) {j : Fin (6 * t)} (hj : j.val % 2 = p) :
    projLane p (Hmap t (isoVec t hpos S j)) = hLane t p j := by
  ext k
  change ∑ x : Fin (6 * t), hFn t x (laneBit p k) * isoVec t hpos S j x = hFn t j (laneBit p k)
  rw [Finset.sum_eq_single j]
  · simp [isoVec]
  · intro x _ hxj
    by_cases hxp : x.val % 2 = p
    · have hne1 : x ≠ prevIdx t hpos j := by
        intro h; subst h; rw [prevIdx_mod2, hj] at hxp; omega
      have hne2 : x ≠ nextIdx t hpos j := by
        intro h; subst h; rw [nextIdx_mod2, hj] at hxp; omega
      simp [isoVec, hxj, hne1, hne2]
    · rw [hFn_other_lane t x (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hxp), zero_mul]
  · intro h; exact False.elim (h (Finset.mem_univ j))

def pairVec (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t))) (m : Fin (6 * t)) :
    Fin (6 * t) → F2 :=
  fun x =>
    if x = prevIdx t hpos m ∨ x = m ∨ x = nextIdx t hpos m ∨
       (x = prev2 t hpos m ∧ prev2 t hpos m ∈ S) ∨
       (x = next2 t hpos m ∧ next2 t hpos m ∈ S)
    then 1 else 0

lemma pairVec_mem_Vset (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) {m : Fin (6 * t)} (hm : m ∈ mergedInt t hpos S p)
    (hpre2 : prev2 t hpos m ∉ mergedInt t hpos S p)
    (hnxt2 : next2 t hpos m ∉ mergedInt t hpos S p) :
    pairVec t hpos S m ∈ Vset t hpos S := by
  rcases Finset.mem_filter.mp hm with ⟨hmA, hpmB, hnmB⟩
  have hmS : m ∈ S := (Finset.mem_filter.mp hmA).1
  have hmp : m.val % 2 = 1 - p := (Finset.mem_filter.mp hmA).2
  have hpmS : prevIdx t hpos m ∈ S := (Finset.mem_filter.mp hpmB).1
  have hnmS : nextIdx t hpos m ∈ S := (Finset.mem_filter.mp hnmB).1
  have hpre3_out : prev2 t hpos m ∈ S → prevIdx t hpos (prev2 t hpos m) ∉ S := by
    intro h1 h2
    apply hpre2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h1, by rw [prev2_mod2, hmp]⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨h2, by rw [prevIdx_mod2, prev2_mod2, hmp]; omega⟩
    · rw [nextIdx_prev2]; exact hpmB
  have hnxt3_out : next2 t hpos m ∈ S → nextIdx t hpos (next2 t hpos m) ∉ S := by
    intro h1 h2
    apply hnxt2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h1, by rw [next2_mod2, hmp]⟩, ?_, ?_⟩
    · rw [prevIdx_next2]; exact hnmB
    · exact Finset.mem_filter.mpr ⟨h2, by rw [nextIdx_mod2, next2_mod2, hmp]; omega⟩
  have hshift_ne : ∀ d1 d2 : ℕ, d1 < 6 * t → d2 < 6 * t → d1 ≠ d2 →
      shiftIdx t hpos m d1 ≠ shiftIdx t hpos m d2 := by
    intro d1 d2 h1 h2 hne heq
    exact hne (shiftIdx_inj_range t hpos m h1 h2 heq)
  refine ⟨fun x hx => ?_, fun x hx hnx => ?_⟩
  · unfold pairVec
    rw [if_neg]
    rintro (rfl | rfl | rfl | ⟨rfl, h1⟩ | ⟨rfl, h1⟩)
    · exact hx hpmS
    · exact hx hmS
    · exact hx hnmS
    · exact hx h1
    · exact hx h1
  · unfold pairVec
    by_cases hx1 : x = prevIdx t hpos m
    · subst hx1
      rw [nextIdx_prevIdx, if_pos (Or.inl rfl), if_pos (Or.inr (Or.inl rfl))]
    · by_cases hx2 : x = m
      · subst hx2
        rw [if_pos (Or.inr (Or.inl rfl)), if_pos (Or.inr (Or.inr (Or.inl rfl)))]
      · by_cases hx3 : x = nextIdx t hpos m
        · subst hx3
          rw [← next2_eq_next_next, if_pos (Or.inr (Or.inr (Or.inl rfl))),
            if_pos (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [next2_eq_next_next]; exact hnx⟩))))]
        · by_cases hx4 : x = prev2 t hpos m
          · subst hx4
            rw [nextIdx_prev2, if_pos (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hx⟩)))),
              if_pos (Or.inl rfl)]
          · by_cases hx5 : x = next2 t hpos m
            · subst hx5
              exact False.elim (hnxt3_out hx hnx)
            · rw [if_neg (by tauto), if_neg]
              rintro (h | h | h | ⟨h, _⟩ | ⟨h, _⟩)
              · exact hx4 (by rw [← prevIdx_nextIdx t hpos x, h]; rfl)
              · exact hx1 (by rw [← prevIdx_nextIdx t hpos x, h])
              · exact hx2 (nextIdx_inj t hpos h)
              · exact hpre3_out (h ▸ hnx) (by rw [← h, prevIdx_nextIdx]; exact hx)
              · exact hx3 (nextIdx_inj t hpos (by rw [← next2_eq_next_next]; exact h))

lemma projLane_Hmap_pairVec (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) {m : Fin (6 * t)} (hmp : m.val % 2 = 1 - p) :
    projLane p (Hmap t (pairVec t hpos S m)) =
      hLane t p (prevIdx t hpos m) + hLane t p (nextIdx t hpos m) := by
  ext k
  change ∑ x : Fin (6 * t), hFn t x (laneBit p k) * pairVec t hpos S m x =
    hFn t (prevIdx t hpos m) (laneBit p k) + hFn t (nextIdx t hpos m) (laneBit p k)
  have hne_pn : prevIdx t hpos m ≠ nextIdx t hpos m := by
    intro h; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, ← next2_eq_next_next] at this
    exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) this.symm
  have hzero : ∀ x : Fin (6 * t), x ≠ prevIdx t hpos m → x ≠ nextIdx t hpos m →
      hFn t x (laneBit p k) * pairVec t hpos S m x = 0 := by
    intro x h1 h2
    by_cases hxp : x.val % 2 = p
    · have h3 : x ≠ m := by intro h; subst h; omega
      have h4 : x ≠ prev2 t hpos m := by intro h; subst h; rw [prev2_mod2, hmp] at hxp; omega
      have h5 : x ≠ next2 t hpos m := by intro h; subst h; rw [next2_mod2, hmp] at hxp; omega
      simp [pairVec, h1, h2, h3, h4, h5]
    · rw [hFn_other_lane t x (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hxp), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ ({prevIdx t hpos m, nextIdx t hpos m} : Finset _))]
  · rw [Finset.sum_pair hne_pn]
    simp [pairVec]
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hzero x hx.1 hx.2

lemma rB_eq_two_of_diff_mod3 (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    {v1 v2 : Vset t hpos S} {j1 j2 : Fin (6 * t)}
    (hj1 : j1.val % 2 = p) (hj2 : j2.val % 2 = p)
    (heq1 : projLane p (Hmap t v1.1) = hLane t p j1)
    (heq2 : projLane p (Hmap t v2.1) = hLane t p j2)
    (hne : j1.val / 2 % 3 ≠ j2.val / 2 % 3) :
    rB t hpos S p = 2 := by
  apply le_antisymm (rB_le_two t hpos S p)
  have hsurj : Function.Surjective ((projLane p).comp (HV t hpos S)) := by
    intro y
    rcases hLane_span_of_ne t p hp j1 j2 hj1 hj2 hne y with ⟨c0, c1, hc⟩
    refine ⟨c0 • v1 + c1 • v2, ?_⟩
    simp only [LinearMap.comp_apply, map_add, map_smul, HV, Submodule.coe_subtype]
    rw [heq1, heq2, hc]
  unfold rB
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]

lemma card_lane_mod3 (t : ℕ) (p : ℕ) (hp : p = 0 ∨ p = 1) (r : ℕ) (hr : r < 3) :
    ((laneSet t p).filter (fun i => i.val / 2 % 3 = r)).card = t := by
  have hbij : ((laneSet t p).filter (fun i => i.val / 2 % 3 = r)).card =
      (Finset.univ : Finset (Fin t)).card :=
    Finset.card_bij (fun i _ => (⟨i.val / 6, by omega⟩ : Fin t))
      (fun _ _ => Finset.mem_univ _)
      (fun a ha b hb hab => by
        have ha1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
        have ha2 := (Finset.mem_filter.mp ha).2
        have hb1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
        have hb2 := (Finset.mem_filter.mp hb).2
        have hv := congrArg Fin.val hab; dsimp at hv
        exact Fin.ext (by omega))
      (fun q _ => ⟨⟨6 * q.val + 2 * r + p, by have := q.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩,
          by dsimp; omega⟩,
        Fin.ext (by have := q.isLt; dsimp; omega)⟩)
  simpa using hbij

lemma card_B_le_of_rB_eq_one (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hrB : rB t hpos S p = 1) :
    (laneSub t S p).card ≤ t + 2 * (mergedInt t hpos S p).card := by
  let B := laneSub t S p
  let M := mergedInt t hpos S p
  let Biso := B.filter (fun j => prevIdx t hpos j ∉ M ∧ nextIdx t hpos j ∉ M)
  let Btouch := B.filter (fun j => prevIdx t hpos j ∈ M ∨ nextIdx t hpos j ∈ M)
  have hsplit : B.card = Biso.card + Btouch.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext j; simp only [Biso, Btouch, Finset.mem_union, Finset.mem_filter]; tauto
    · rw [Finset.disjoint_left]; intro j h1 h2
      rcases (Finset.mem_filter.mp h1).2 with ⟨ha, hb⟩
      exact (Finset.mem_filter.mp h2).2.elim ha hb
  have hiso_le : Biso.card ≤ t := by
    by_cases hemp : Biso = ∅
    · rw [hemp, Finset.card_empty]; omega
    · rcases Finset.nonempty_iff_ne_empty.mpr hemp with ⟨j0, hj0⟩
      let r0 := j0.val / 2 % 3
      have hsub : Biso ⊆ (laneSet t p).filter (fun i => i.val / 2 % 3 = r0) := by
        intro j hj
        have hjB := (Finset.mem_filter.mp hj).1
        have hjp : j.val % 2 = p := (Finset.mem_filter.mp hjB).2
        have hj0B := (Finset.mem_filter.mp hj0).1
        have hj0p : j0.val % 2 = p := (Finset.mem_filter.mp hj0B).2
        refine Finset.mem_filter.mpr ⟨laneSub_subset_laneSet t S p hjB, ?_⟩
        by_contra hne
        have hv1 : isoVec t hpos S j ∈ Vset t hpos S :=
          isoVec_mem_Vset t hpos ht S p hp hjB (Finset.mem_filter.mp hj).2.1 (Finset.mem_filter.mp hj).2.2
        have hv2 : isoVec t hpos S j0 ∈ Vset t hpos S :=
          isoVec_mem_Vset t hpos ht S p hp hj0B (Finset.mem_filter.mp hj0).2.1 (Finset.mem_filter.mp hj0).2.2
        have h2 := rB_eq_two_of_diff_mod3 t hpos S p hp hjp hj0p
          (v1 := ⟨_, hv1⟩) (v2 := ⟨_, hv2⟩)
          (projLane_Hmap_isoVec t hpos ht S p hp hjp)
          (projLane_Hmap_isoVec t hpos ht S p hp hj0p) hne
        omega
      calc Biso.card ≤ ((laneSet t p).filter (fun i => i.val / 2 % 3 = r0)).card :=
            Finset.card_le_card hsub
        _ = t := card_lane_mod3 t p hp r0 (by omega)
  have htouch_le : Btouch.card ≤ 2 * M.card := by
    have hsub : Btouch ⊆ M.image (prevIdx t hpos) ∪ M.image (nextIdx t hpos) := by
      intro j hj
      rcases (Finset.mem_filter.mp hj).2 with hm | hm
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨prevIdx t hpos j, hm, nextIdx_prevIdx t hpos j⟩)
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨nextIdx t hpos j, hm, prevIdx_nextIdx t hpos j⟩)
    calc Btouch.card ≤ (M.image (prevIdx t hpos) ∪ M.image (nextIdx t hpos)).card :=
          Finset.card_le_card hsub
      _ ≤ (M.image (prevIdx t hpos)).card + (M.image (nextIdx t hpos)).card :=
          Finset.card_union_le _ _
      _ ≤ M.card + M.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * M.card := by ring
  dsimp only [B, M] at hsplit htouch_le
  omega

lemma two_mul_blocksB_le_of_rB_zero (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hrB : rB t hpos S p = 0) :
    2 * blocksB t hpos S p ≤ (mergedInt t hpos S p).card := by
  have hzero : ∀ v ∈ Vset t hpos S, projLane p (Hmap t v) = 0 := by
    intro v hv
    have hbot : LinearMap.range ((projLane p).comp (HV t hpos S)) = ⊥ :=
      Submodule.finrank_eq_zero.mp hrB
    have hmem : projLane p (Hmap t v) ∈ LinearMap.range ((projLane p).comp (HV t hpos S)) :=
      ⟨⟨v, hv⟩, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  let B := laneSub t S p
  let M := mergedInt t hpos S p
  let starts := B.filter (fun j => prev2 t hpos j ∉ B)
  have h1 : ∀ j ∈ starts, nextIdx t hpos j ∈ M := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjB, hpre2⟩
    have hjp : j.val % 2 = p := (Finset.mem_filter.mp hjB).2
    have hpreM : prevIdx t hpos j ∉ M := by
      intro hm; exact hpre2 (Finset.mem_filter.mp hm).2.1
    by_contra hnxtM
    have hv := isoVec_mem_Vset t hpos ht S p hp hjB hpreM hnxtM
    have hz := hzero _ hv
    rw [projLane_Hmap_isoVec t hpos ht S p hp hjp] at hz
    exact hLane_ne_zero t p hp j hjp hz
  have h2 : ∀ j ∈ starts, shiftIdx t hpos j 3 ∈ M := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjB, hpre2⟩
    have hjp : j.val % 2 = p := (Finset.mem_filter.mp hjB).2
    have hm1 : nextIdx t hpos j ∈ M := h1 j hj
    have hpm : prev2 t hpos (nextIdx t hpos j) ∉ M := by
      rw [prev2, prevIdx_nextIdx]
      intro hm; exact hpre2 (Finset.mem_filter.mp hm).2.1
    by_contra hnxt2M
    have hn2eq : next2 t hpos (nextIdx t hpos j) = shiftIdx t hpos j 3 := by
      rw [next2, ← shiftIdx_one, shiftIdx_add]
    have hv := pairVec_mem_Vset t hpos ht S p hp hm1 hpm (hn2eq.symm ▸ hnxt2M)
    have hz := hzero _ hv
    rw [projLane_Hmap_pairVec t hpos ht S p hp (by rw [nextIdx_mod2, hjp]),
      hLane_prev_next_eq_prev3] at hz
    have h3p : (prevIdx t hpos (prev2 t hpos (nextIdx t hpos j))).val % 2 = p := by
      rw [prevIdx_mod2, prev2_mod2, nextIdx_mod2, hjp]; omega
    exact hLane_ne_zero t p hp _ h3p hz
  have hdisj : Disjoint (starts.image (nextIdx t hpos))
      (starts.image (fun j => shiftIdx t hpos j 3)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨j1, hj1, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨j2, hj2, heq⟩
    have hj2B : j2 ∈ B := (Finset.mem_filter.mp hj2).1
    have hj1pre : prev2 t hpos j1 ∉ B := (Finset.mem_filter.mp hj1).2
    have hjeq : prev2 t hpos j1 = j2 := by
      apply next2_inj t hpos
      rw [next2_prev2]
      apply nextIdx_inj t hpos
      have : nextIdx t hpos (next2 t hpos j2) = shiftIdx t hpos j2 3 := by
        rw [next2, ← shiftIdx_one, shiftIdx_add]
      rw [this, heq]
    exact hj1pre (hjeq.symm ▸ hj2B)
  have hsub : starts.image (nextIdx t hpos) ∪ starts.image (fun j => shiftIdx t hpos j 3) ⊆ M := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩; exact h1 j hj
    · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩; exact h2 j hj
  have hinj3 : Function.Injective (fun j : Fin (6 * t) => shiftIdx t hpos j 3) := by
    intro a b hab
    have h3 : ∀ x, shiftIdx t hpos (shiftIdx t hpos x 3) (6 * t - 3) = x := by
      intro x; rw [shiftIdx_add, Nat.add_sub_cancel' (by omega : 3 ≤ 6 * t)]
      apply Fin.ext; dsimp [shiftIdx]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
    have := congrArg (fun x => shiftIdx t hpos x (6 * t - 3)) hab
    rwa [h3 a, h3 b] at this
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (nextIdx_inj t hpos),
    Finset.card_image_of_injective _ hinj3,
    blocksB_eq_starts] at hle
  dsimp only [M] at hle
  omega

lemma rFree_eq_two (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hruns : 0 < runsS t hpos S)
    (hfr : 3 * t - 5 ≤ Module.finrank F2 (GoodMax t hpos S))
    (hBpos : 0 < (laneSub t S p).card)
    (hBlt : (laneSub t S p).card < 3 * t)
    (hBsmaller : (laneSub t S p).card ≤ (laneSub t S (1 - p)).card) :
    rFree t hpos S p = 2 ∧
      blocksB t hpos S p + (missFree t hpos S p).card + (mergedInt t hpos S p).card +
        rB t hpos S p ≤ 3 := by
  have hm := master_ineq t hpos S p hp hruns hfr
  have hs_pos : 1 ≤ blocksB t hpos S p := blocksB_pos_of_lt t hpos S p hp hBpos hBlt
  have h3t := three_t_le_of_smaller t hpos S p hp hBsmaller
  have hrF_le := rFree_le_two t hpos S p hp
  have hrB_le := rB_le_two t hpos S p
  have hrF2 : rFree t hpos S p = 2 := by
    by_contra hne
    have hrF1 : rFree t hpos S p ≤ 1 := by omega
    have hF_le := freeOpp_card_le_of_rFree_le_one t hpos ht S p hp hrF1
    have hadd := card_freeOpp_add t hpos S p hp
    have hrf_cases : rFree t hpos S p = 0 ∨ rFree t hpos S p = 1 := by omega
    have hrb_cases : rB t hpos S p = 0 ∨ rB t hpos S p = 1 ∨ rB t hpos S p = 2 := by omega
    rcases hrb_cases with hrb | hrb | hrb
    · have h2s := two_mul_blocksB_le_of_rB_zero t hpos ht S p hp hrb
      rcases hrf_cases with hrf | hrf
      · have hF0 : (freeOpp t hpos S p).card = 0 := by
          rw [rFree_eq_zero_imp_empty t hpos S p hp hrf, Finset.card_empty]
        omega
      · omega
    · have hB_le := card_B_le_of_rB_eq_one t hpos ht S p hp hrb
      rcases hrf_cases with hrf | hrf
      · have hF0 : (freeOpp t hpos S p).card = 0 := by
          rw [rFree_eq_zero_imp_empty t hpos S p hp hrf, Finset.card_empty]
        omega
      · omega
    · rcases hrf_cases with hrf | hrf
      · have hF0 : (freeOpp t hpos S p).card = 0 := by
          rw [rFree_eq_zero_imp_empty t hpos S p hp hrf, Finset.card_empty]
        omega
      · omega
  exact ⟨hrF2, by omega⟩

-- ============================================================================
-- L-lib-898 Section B1: Rank Upper Bound, Pair Cancellation, and Single-Block Lemma
-- ============================================================================

lemma bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact False.elim (by simpa using h)

lemma mem_if_singleton {α : Type*} [DecidableEq α] (b : Bool) (a x : α) :
    x ∈ (if b then ({a} : Finset α) else ∅) ↔ b = true ∧ x = a := by
  cases b <;> simp

lemma finrank_span_sing_le_one {V : Type*} [AddCommGroup V] [Module F2 V] (v : V) :
    Module.finrank F2 (Submodule.span F2 ({v} : Set V)) ≤ 1 := by
  have hr : LinearMap.range (LinearMap.toSpanSingleton F2 V v) = Submodule.span F2 ({v} : Set V) := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.toSpanSingleton_apply, Submodule.mem_span_singleton]
  rw [← hr]
  calc Module.finrank F2 (LinearMap.range (LinearMap.toSpanSingleton F2 V v))
      ≤ Module.finrank F2 F2 := LinearMap.finrank_range_le _
    _ = 1 := Module.finrank_self F2

lemma finrank_ker_projLane (p : ℕ) (hp : p = 0 ∨ p = 1) :
    Module.finrank F2 (LinearMap.ker (projLane p)) = 2 := by
  have hsurj : Function.Surjective (projLane p) := by
    intro z
    refine ⟨fun b => if b = laneBit p 0 then z 0 else if b = laneBit p 1 then z 1 else 0, ?_⟩
    ext k
    have hne : laneBit p 0 ≠ laneBit p 1 := by
      rcases hp with rfl | rfl <;> decide
    fin_cases k
    · simp [projLane]
    · simp [projLane, hne.symm]
  have hrn := LinearMap.finrank_range_add_finrank_ker (projLane p)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hrn
  omega

lemma rankHV_le_rB_add_two (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1) :
    Module.finrank F2 (LinearMap.range (HV t hpos S)) ≤ rB t hpos S p + 2 := by
  let R := LinearMap.range (HV t hpos S)
  let g : R →ₗ[F2] (Fin 2 → F2) := (projLane p).comp R.subtype
  have hrg : LinearMap.range g = LinearMap.range ((projLane p).comp (HV t hpos S)) := by
    ext z; simp only [g, R, LinearMap.mem_range, LinearMap.comp_apply, Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨y, x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨⟨HV t hpos S x, x, rfl⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrg] at hrn
  have hker_le : Module.finrank F2 (LinearMap.ker g) ≤ 2 := by
    let e : (R ⊓ LinearMap.ker (projLane p) : Submodule F2 (Fin 4 → F2)) ≃ₗ[F2] LinearMap.ker g :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [← e.finrank_eq]
    calc Module.finrank F2 (R ⊓ LinearMap.ker (projLane p) : Submodule F2 (Fin 4 → F2))
        ≤ Module.finrank F2 (LinearMap.ker (projLane p)) := Submodule.finrank_mono inf_le_right
      _ = 2 := finrank_ker_projLane p hp
  unfold rB
  have h1 : Module.finrank F2 (LinearMap.range ((projLane p).comp (HV t hpos S))) +
      Module.finrank F2 (LinearMap.ker g) = Module.finrank F2 (LinearMap.range (HV t hpos S)) := hrn
  omega

lemma shiftIdx_ne_of_ne (t : ℕ) (hpos : 0 < t) (j : Fin (6 * t)) {a b : ℕ}
    (ha : a < 6 * t) (hb : b < 6 * t) (hne : a ≠ b) :
    shiftIdx t hpos j a ≠ shiftIdx t hpos j b := by
  intro heq
  exact hne (shiftIdx_inj_range t hpos j ha hb heq)

lemma prevIdx_shiftIdx_pos (t : ℕ) (hpos : 0 < t) (j : Fin (6 * t)) {d : ℕ} (hd : 1 ≤ d) :
    prevIdx t hpos (shiftIdx t hpos j d) = shiftIdx t hpos j (d - 1) := by
  apply nextIdx_inj t hpos
  rw [nextIdx_prevIdx, ← shiftIdx_one, shiftIdx_add, Nat.sub_add_cancel hd]

lemma nextIdx_shiftIdx' (t : ℕ) (hpos : 0 < t) (j : Fin (6 * t)) (d : ℕ) :
    nextIdx t hpos (shiftIdx t hpos j d) = shiftIdx t hpos j (d + 1) := by
  rw [← shiftIdx_one, shiftIdx_add]

lemma shiftIdx_two_ne_mod3 (t : ℕ) (hpos : 0 < t) (j : Fin (6 * t)) (d : ℕ) :
    (shiftIdx t hpos j d).val / 2 % 3 ≠ (shiftIdx t hpos j (d + 2)).val / 2 % 3 := by
  have h1 : shiftIdx t hpos j (d + 2) = shiftIdx t hpos (shiftIdx t hpos j d) 2 := by
    rw [shiftIdx_add]
  rw [h1, shiftIdx_two_div2_mod3]
  omega

lemma pair_cancel_opp (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    {u1 u2 : Fin (6 * t)} (hu1 : u1 ∈ freeOpp t hpos S p) (hu2 : u2 ∈ freeOpp t hpos S p)
    (hne : u1.val / 2 % 3 ≠ u2.val / 2 % 3)
    {v : Fin (6 * t) → F2} (hvV : v ∈ Vset t hpos S)
    (hvB : projLane p (Hmap t v) = 0) :
    ∃ c0 c1 : F2,
      v + c0 • Pi.single u1 (1 : F2) + c1 • Pi.single u2 (1 : F2) ∈ GoodMax t hpos S := by
  have hu1p : u1.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hu1).1).2
  have hu2p : u2.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hu2).1).2
  rcases hLane_span_of_ne t (1 - p) (by omega) u1 u2 hu1p hu2p hne
      (projLane (1 - p) (Hmap t v)) with ⟨c0, c1, hc⟩
  refine ⟨c0, c1, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.add_mem _ hvV
      (Submodule.smul_mem _ c0 (freeOpp_single_mem_Vset t hpos S p hp hu1)))
      (Submodule.smul_mem _ c1 (freeOpp_single_mem_Vset t hpos S p hp hu2))
  · ext b
    simp only [LinearMap.mem_ker, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, Hmap_single]
    have hcheck : ∀ (q : ℕ) (hq : q = 0 ∨ q = 1) (k : Fin 2),
        Hmap t v (laneBit q k) + c0 * hFn t u1 (laneBit q k) + c1 * hFn t u2 (laneBit q k) = 0 := by
      intro q hq k
      by_cases hqp : q = p
      · subst hqp
        have hv0 : Hmap t v (laneBit q k) = 0 := congrFun hvB k
        have h1 : hFn t u1 (laneBit q k) = 0 :=
          hFn_other_lane t u1 (laneBit q k) (by rw [laneBit_div2 q hp k, hu1p]; omega)
        have h2 : hFn t u2 (laneBit q k) = 0 :=
          hFn_other_lane t u2 (laneBit q k) (by rw [laneBit_div2 q hp k, hu2p]; omega)
        rw [hv0, h1, h2]; ring
      · have hq1 : q = 1 - p := by omega
        subst hq1
        have hck := congrFun hc k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hLane, projLane,
          LinearMap.coe_mk, AddHom.coe_mk] at hck
        calc Hmap t v (laneBit (1 - p) k) + c0 * hFn t u1 (laneBit (1 - p) k) +
              c1 * hFn t u2 (laneBit (1 - p) k)
            = Hmap t v (laneBit (1 - p) k) +
              (c0 * hFn t u1 (laneBit (1 - p) k) + c1 * hFn t u2 (laneBit (1 - p) k)) := by ring
          _ = Hmap t v (laneBit (1 - p) k) + Hmap t v (laneBit (1 - p) k) := by rw [hck]
          _ = 0 := zmod2_add_self _
    rcases hp with rfl | rfl <;> rcases fin4_cases b with rfl | rfl | rfl | rfl
    · exact hcheck 0 (Or.inl rfl) 0
    · exact hcheck 0 (Or.inl rfl) 1
    · exact hcheck 1 (Or.inr rfl) 0
    · exact hcheck 1 (Or.inr rfl) 1
    · exact hcheck 0 (Or.inl rfl) 0
    · exact hcheck 0 (Or.inl rfl) 1
    · exact hcheck 1 (Or.inr rfl) 0
    · exact hcheck 1 (Or.inr rfl) 1

lemma supp_of_Vset_cancel (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    {u1 u2 : Fin (6 * t)} (hu1 : u1 ∈ freeOpp t hpos S p) (hu2 : u2 ∈ freeOpp t hpos S p)
    (hne : u1.val / 2 % 3 ≠ u2.val / 2 % 3)
    {v : Fin (6 * t) → F2} (hvV : v ∈ Vset t hpos S)
    (hvB : projLane p (Hmap t v) = 0)
    {i : Fin (6 * t)} (hvi : v i = 1) (hi1 : i ≠ u1) (hi2 : i ≠ u2) :
    ∃ x ∈ GoodMax t hpos S, x i ≠ 0 := by
  rcases pair_cancel_opp t hpos S p hp hu1 hu2 hne hvV hvB with ⟨c0, c1, hx⟩
  refine ⟨_, hx, ?_⟩
  simp [hvi, Pi.single_eq_of_ne hi1, Pi.single_eq_of_ne hi2]

lemma supp_freeOpp_of_two_pairs (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    {u1 u2 w1 w2 : Fin (6 * t)}
    (hu1 : u1 ∈ freeOpp t hpos S p) (hu2 : u2 ∈ freeOpp t hpos S p)
    (hw1 : w1 ∈ freeOpp t hpos S p) (hw2 : w2 ∈ freeOpp t hpos S p)
    (hneu : u1.val / 2 % 3 ≠ u2.val / 2 % 3)
    (hnew : w1.val / 2 % 3 ≠ w2.val / 2 % 3)
    (hd11 : u1 ≠ w1) (hd12 : u1 ≠ w2) (hd21 : u2 ≠ w1) (hd22 : u2 ≠ w2) :
    rFree t hpos S p = 2 ∧
      ∀ i ∈ freeOpp t hpos S p, ∃ x ∈ GoodMax t hpos S, x i ≠ 0 := by
  refine ⟨rFree_eq_two_of_diff_mod3 t hpos S p hp hu1 hu2 hneu, fun i hi => ?_⟩
  have hvV : Pi.single i (1 : F2) ∈ Vset t hpos S := freeOpp_single_mem_Vset t hpos S p hp hi
  have hvB : projLane p (Hmap t (Pi.single i (1 : F2))) = 0 := by
    ext k
    change Hmap t (Pi.single i (1 : F2)) (laneBit p k) = 0
    rw [Hmap_single]
    have hip : i.val % 2 = 1 - p := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    exact hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k, hip]; omega)
  by_cases h1 : i ≠ u1 ∧ i ≠ u2
  · exact supp_of_Vset_cancel t hpos S p hp hu1 hu2 hneu hvV hvB (by simp) h1.1 h1.2
  · have hi_in : i = u1 ∨ i = u2 := by tauto
    have hw : i ≠ w1 ∧ i ≠ w2 := by
      rcases hi_in with rfl | rfl
      · exact ⟨hd11, hd12⟩
      · exact ⟨hd21, hd22⟩
    exact supp_of_Vset_cancel t hpos S p hp hw1 hw2 hnew hvV hvB (by simp) hw.1 hw.2

lemma single_block_subset (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hs1 : blocksB t hpos S p = 1)
    {j : Fin (6 * t)} (hj : j ∈ laneSub t S p) (hpre2 : prev2 t hpos j ∉ laneSub t S p)
    {k : ℕ} (hk1 : 1 ≤ k) (hkt : k < 3 * t)
    (hout : shiftIdx t hpos j (2 * k) ∉ laneSub t S p)
    (hin : ∀ d < k, shiftIdx t hpos j (2 * d) ∈ laneSub t S p) :
    laneSub t S p = (Finset.range k).image (fun d => shiftIdx t hpos j (2 * d)) := by
  apply Finset.Subset.antisymm
  · intro y hy
    by_contra hnot
    have hjp : j.val % 2 = p := (Finset.mem_filter.mp hj).2
    have hyp : y.val % 2 = p := (Finset.mem_filter.mp hy).2
    let d0 : ℕ := (y.val + 6 * t - j.val) % (6 * t)
    have hd0_lt : d0 < 6 * t := Nat.mod_lt _ (by omega)
    have hd0_even : d0 % 2 = 0 := by
      have h2 : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
      have hdm : d0 % 2 = (y.val + 6 * t - j.val) % 2 := Nat.mod_mod_of_dvd _ h2
      have := j.isLt; have := y.isLt
      omega
    have hsh : shiftIdx t hpos j d0 = y := by
      apply Fin.ext; dsimp [shiftIdx, d0]
      have := j.isLt; have := y.isLt
      by_cases hle : j.val ≤ y.val
      · have h1 : (y.val + 6 * t - j.val) % (6 * t) = y.val - j.val := by
          rw [show y.val + 6 * t - j.val = (y.val - j.val) + 6 * t by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1, show j.val + (y.val - j.val) = y.val by omega, Nat.mod_eq_of_lt (by omega)]
      · have h1 : (y.val + 6 * t - j.val) % (6 * t) = y.val + 6 * t - j.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [h1, show j.val + (y.val + 6 * t - j.val) = y.val + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    let q0 := d0 / 2
    have hq0_eq : 2 * q0 = d0 := by omega
    have hq0_lt : q0 < 3 * t := by omega
    have hq0_ge : k ≤ q0 := by
      by_contra hlt
      apply hnot
      exact Finset.mem_image.mpr ⟨q0, Finset.mem_range.mpr (by omega), hq0_eq.symm ▸ hsh⟩
    have hq0_gt : k < q0 := by
      by_contra hle
      have heq : q0 = k := by omega
      apply hout
      rw [← heq, hq0_eq, hsh]; exact hy
    have hex : ∃ m, k < m ∧ m < 3 * t ∧ shiftIdx t hpos j (2 * m) ∈ laneSub t S p :=
      ⟨q0, hq0_gt, hq0_lt, by rw [hq0_eq, hsh]; exact hy⟩
    classical
    let m0 := Nat.find hex
    rcases Nat.find_spec hex with ⟨hm0_k, hm0_lt, hm0_in⟩
    let y0 := shiftIdx t hpos j (2 * m0)
    have hy0_pre2 : prev2 t hpos y0 ∉ laneSub t S p := by
      have hpeq : prev2 t hpos y0 = shiftIdx t hpos j (2 * (m0 - 1)) := by
        apply next2_inj t hpos
        rw [next2_prev2, next2, shiftIdx_add]
        dsimp only [y0]
        congr 1; omega
      rw [hpeq]
      by_cases hmk : m0 - 1 = k
      · rw [hmk]; exact hout
      · intro hm_in
        have hmin := Nat.find_min hex (show m0 - 1 < m0 by omega)
        exact hmin ⟨by omega, by omega, hm_in⟩
    have hy0_ne : y0 ≠ j :=
      shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega)
    let starts := (laneSub t S p).filter (fun x => prev2 t hpos x ∉ laneSub t S p)
    have hsub2 : ({j, y0} : Finset _) ⊆ starts := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨hj, hpre2⟩
      · rw [Finset.mem_singleton.mp hx]
        exact Finset.mem_filter.mpr ⟨hm0_in, hy0_pre2⟩
    have hle2 := Finset.card_le_card hsub2
    rw [Finset.card_pair hy0_ne.symm] at hle2
    have hst := blocksB_eq_starts t hpos S p
    dsimp only [starts] at hle2
    omega
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
    exact hin d (Finset.mem_range.mp hd)

-- ============================================================================
-- L-lib-898 Section B2: Family 2 (rB = 0, c = a - 3, count = 4 * n)
-- ============================================================================

def mkFam2 (t : ℕ) (hpos : 0 < t) (j : Fin (6 * t)) (bL bR : Bool) : Finset (Fin (6 * t)) :=
  let p := j.val % 2
  let B : Finset (Fin (6 * t)) := {j, shiftIdx t hpos j 2, shiftIdx t hpos j 4}
  let A0 : Finset (Fin (6 * t)) :=
    (laneSet t (1 - p)).filter (fun i =>
      i ≠ prevIdx t hpos j ∧ i ≠ shiftIdx t hpos j 5)
  let AL : Finset (Fin (6 * t)) := if bL then {prevIdx t hpos j} else ∅
  let AR : Finset (Fin (6 * t)) := if bR then {shiftIdx t hpos j 5} else ∅
  B ∪ A0 ∪ AL ∪ AR

def Fam2Set (t : ℕ) (hpos : 0 < t) : Finset (Finset (Fin (6 * t))) :=
  (Finset.univ : Finset (Fin (6 * t) × Bool × Bool)).image
    (fun x => mkFam2 t hpos x.1 x.2.1 x.2.2)

lemma mkFam2_laneSub_p (t : ℕ) (hpos : 0 < t) (j : Fin (6 * t)) (bL bR : Bool) :
    laneSub t (mkFam2 t hpos j bL bR) (j.val % 2) =
      {j, shiftIdx t hpos j 2, shiftIdx t hpos j 4} := by
  let p := j.val % 2
  have hp : p = 0 ∨ p = 1 := by omega
  ext x
  simp only [laneSub, mkFam2, laneSet, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨((hB | ⟨hxp, _⟩) | hL) | hR, hxp'⟩
    · exact hB
    · omega
    · cases bL <;> simp at hL
      rw [hL, prevIdx_mod2] at hxp'; omega
    · cases bR <;> simp at hR
      rw [hR, shiftIdx_mod2] at hxp'; omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨Or.inl (Or.inl (Or.inl (Or.inl rfl))), rfl⟩
    · exact ⟨Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))), by rw [shiftIdx_mod2]; omega⟩
    · exact ⟨Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))), by rw [shiftIdx_mod2]; omega⟩

lemma mkFam2_props (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (j : Fin (6 * t)) (bL bR : Bool) :
    let S := mkFam2 t hpos j bL bR
    let p := j.val % 2
    sitesS t S p = 3 ∧ 3 < sitesS t S (1 - p) ∧
    runsS t hpos S = 3 * t - 3 ∧
    suppU t (GoodMax t hpos S) = S ∧
    Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
  intro S p
  have hp : p = 0 ∨ p = 1 := by omega
  have hBp : laneSub t S p = {j, shiftIdx t hpos j 2, shiftIdx t hpos j 4} :=
    mkFam2_laneSub_p t hpos j bL bR
  have hne02 : j ≠ shiftIdx t hpos j 2 := by
    have := shiftIdx_ne_of_ne t hpos j (a := 0) (b := 2) (by omega) (by omega) (by omega)
    rwa [shiftIdx_zero] at this
  have hne04 : j ≠ shiftIdx t hpos j 4 := by
    have := shiftIdx_ne_of_ne t hpos j (a := 0) (b := 4) (by omega) (by omega) (by omega)
    rwa [shiftIdx_zero] at this
  have hne24 : shiftIdx t hpos j 2 ≠ shiftIdx t hpos j 4 :=
    shiftIdx_ne_of_ne t hpos j (a := 2) (b := 4) (by omega) (by omega) (by omega)
  have hcardB : sitesS t S p = 3 := by
    rw [← laneSub_card_eq_sites, hBp, Finset.card_insert_of_notMem,
      Finset.card_pair hne24]
    simp [hne02, hne04]
  have hA0_sub : (laneSet t (1 - p)).filter (fun i =>
      i ≠ prevIdx t hpos j ∧ i ≠ shiftIdx t hpos j 5) ⊆ laneSub t S (1 - p) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
  have hcardA_gt : 3 < sitesS t S (1 - p) := by
    have h1 : (laneSet t (1 - p)).card ≤
        ((laneSet t (1 - p)).filter (fun i => i ≠ prevIdx t hpos j ∧ i ≠ shiftIdx t hpos j 5)).card + 2 := by
      have hsub : laneSet t (1 - p) ⊆
          (laneSet t (1 - p)).filter (fun i => i ≠ prevIdx t hpos j ∧ i ≠ shiftIdx t hpos j 5) ∪
          {prevIdx t hpos j, shiftIdx t hpos j 5} := by
        intro i hi
        by_cases h : i ≠ prevIdx t hpos j ∧ i ≠ shiftIdx t hpos j 5
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
        · exact Finset.mem_union_right _ (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hle := Finset.card_le_card hsub
      have hun := Finset.card_union_le
        ((laneSet t (1 - p)).filter (fun i => i ≠ prevIdx t hpos j ∧ i ≠ shiftIdx t hpos j 5))
        {prevIdx t hpos j, shiftIdx t hpos j 5}
      have h2 : ({prevIdx t hpos j, shiftIdx t hpos j 5} : Finset _).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      omega
    have hle2 := Finset.card_le_card hA0_sub
    rw [card_laneSet t (1 - p) (by omega)] at h1
    rw [laneSub_card_eq_sites] at hle2
    omega
  -- Check blocksB = 1, missFree = ∅, mergedInt = {j+1, j+3}
  have hblocks : blocksB t hpos S p = 1 := by
    unfold blocksB
    rw [hBp]
    have hfilt : ({j, shiftIdx t hpos j 2, shiftIdx t hpos j 4} : Finset (Fin (6 * t))).filter
        (fun x => next2 t hpos x ∉ ({j, shiftIdx t hpos j 2, shiftIdx t hpos j 4} : Finset _)) =
        {shiftIdx t hpos j 4} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hnot⟩
        · exact False.elim (hnot (Or.inr (Or.inl rfl)))
        · exact False.elim (hnot (Or.inr (Or.inr (by rw [next2, shiftIdx_add]))))
        · rfl
      · rintro rfl
        refine ⟨Or.inr (Or.inr rfl), ?_⟩
        rw [next2, shiftIdx_add]
        rintro (h | h | h)
        · exact shiftIdx_ne_of_ne t hpos j (a := 6) (b := 0) (by omega) (by omega) (by omega) (by rwa [shiftIdx_zero])
        · exact shiftIdx_ne_of_ne t hpos j (a := 6) (b := 2) (by omega) (by omega) (by omega) h
        · exact shiftIdx_ne_of_ne t hpos j (a := 6) (b := 4) (by omega) (by omega) (by omega) h
    rw [hfilt, Finset.card_singleton]
  have hmiss : missFree t hpos S p = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hsd, hpre, hnxt⟩
    rcases Finset.mem_sdiff.mp hsd with ⟨hiL, hiA⟩
    have hi_eq : i = prevIdx t hpos j ∨ i = shiftIdx t hpos j 5 := by
      by_contra hne
      apply hiA
      exact hA0_sub (Finset.mem_filter.mpr ⟨hiL, by tauto⟩)
    rcases hi_eq with rfl | rfl
    · apply hnxt; rw [nextIdx_prevIdx, hBp]; simp
    · apply hpre; rw [prevIdx_shiftIdx_pos t hpos j (by omega), hBp]; simp
  have hj1_in : shiftIdx t hpos j 1 ∈ laneSub t S (1 - p) := by
    apply hA0_sub
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftIdx_mod2]; omega⟩, ?_, ?_⟩
    · rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
    · exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
  have hj3_in : shiftIdx t hpos j 3 ∈ laneSub t S (1 - p) := by
    apply hA0_sub
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftIdx_mod2]; omega⟩, ?_, ?_⟩
    · rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
    · exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
  have hmerged : mergedInt t hpos S p = {shiftIdx t hpos j 1, shiftIdx t hpos j 3} := by
    ext i
    simp only [mergedInt, Finset.mem_filter, hBp, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, (h1 | h1 | h1), (h2 | h2 | h2)⟩
      · have h1' := congrArg (nextIdx t hpos) h1; rw [nextIdx_prevIdx] at h1'
        have h2' := congrArg (prevIdx t hpos) h2; rw [prevIdx_nextIdx] at h2'
        have h3 : shiftIdx t hpos j 1 = prevIdx t hpos j := by rw [shiftIdx_one, ← h1', h2']
        rw [prevIdx_eq_shift] at h3
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) h3)
      · left; have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, ← shiftIdx_one] at this
      · have ha : i = shiftIdx t hpos j 1 := by
          have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, ← shiftIdx_one] at this
        have hb : i = shiftIdx t hpos j 3 := by
          have := congrArg (prevIdx t hpos) h2; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) (ha.symm.trans hb))
      · have ha : i = shiftIdx t hpos j 3 := by
          have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
        have hb : i = prevIdx t hpos j := by
          have := congrArg (prevIdx t hpos) h2; rwa [prevIdx_nextIdx] at this
        rw [prevIdx_eq_shift] at hb
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) (ha.symm.trans hb))
      · have ha : i = shiftIdx t hpos j 3 := by
          have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
        have hb : i = shiftIdx t hpos j 1 := by
          have := congrArg (prevIdx t hpos) h2; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) (ha.symm.trans hb))
      · right; have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
      · have ha : i = shiftIdx t hpos j 5 := by
          have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
        have hb : i = prevIdx t hpos j := by
          have := congrArg (prevIdx t hpos) h2; rwa [prevIdx_nextIdx] at this
        rw [prevIdx_eq_shift] at hb
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) (ha.symm.trans hb))
      · have ha : i = shiftIdx t hpos j 5 := by
          have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
        have hb : i = shiftIdx t hpos j 1 := by
          have := congrArg (prevIdx t hpos) h2; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) (ha.symm.trans hb))
      · have ha : i = shiftIdx t hpos j 5 := by
          have := congrArg (nextIdx t hpos) h1; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
        have hb : i = shiftIdx t hpos j 3 := by
          have := congrArg (prevIdx t hpos) h2; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this
        exact False.elim (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega) (ha.symm.trans hb))
    · rintro (rfl | rfl)
      · exact ⟨hj1_in, Or.inl (by rw [prevIdx_shiftIdx_pos t hpos j (by omega), shiftIdx_zero]),
          Or.inr (Or.inl (by rw [nextIdx_shiftIdx']))⟩
      · exact ⟨hj3_in, Or.inr (Or.inl (by rw [prevIdx_shiftIdx_pos t hpos j (by omega)])),
          Or.inr (Or.inr (by rw [nextIdx_shiftIdx']))⟩
  have hruns : runsS t hpos S = 3 * t - 3 := by
    have hid := runsS_identity t hpos S p hp
    rw [hblocks, hmiss, Finset.card_empty, hmerged,
      Finset.card_pair (shiftIdx_ne_of_ne t hpos j (a := 1) (b := 3) (by omega) (by omega) (by omega))] at hid
    omega
  -- Two disjoint spanning pairs in freeOpp: (j+7, j+9) and (j+11, j+13)
  have hfree_of_odd : ∀ d : ℕ, d % 2 = 1 → 7 ≤ d → d ≤ 13 → shiftIdx t hpos j d ∈ freeOpp t hpos S p := by
    intro d hd_odd hd7 hd13
    refine Finset.mem_filter.mpr ⟨hA0_sub (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftIdx_mod2]; omega⟩,
        by rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)⟩), ?_, ?_⟩
    · rw [prevIdx_shiftIdx_pos t hpos j (by omega), hBp]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)⟩
    · rw [nextIdx_shiftIdx', hBp]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)⟩
  have hu1 : shiftIdx t hpos j 7 ∈ freeOpp t hpos S p := hfree_of_odd 7 rfl (by omega) (by omega)
  have hu2 : shiftIdx t hpos j 9 ∈ freeOpp t hpos S p := hfree_of_odd 9 rfl (by omega) (by omega)
  have hw1 : shiftIdx t hpos j 11 ∈ freeOpp t hpos S p := hfree_of_odd 11 rfl (by omega) (by omega)
  have hw2 : shiftIdx t hpos j 13 ∈ freeOpp t hpos S p := hfree_of_odd 13 rfl (by omega) (by omega)
  have htwo := supp_freeOpp_of_two_pairs t hpos S p hp hu1 hu2 hw1 hw2
    (shiftIdx_two_ne_mod3 t hpos j 7) (shiftIdx_two_ne_mod3 t hpos j 11)
    (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega))
    (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega))
    (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega))
    (shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega))
  -- projLane p (Hmap t x) = 0 for all x ∈ Vset S
  have hrB_zero : ∀ x ∈ Vset t hpos S, projLane p (Hmap t x) = 0 := by
    intro x hx
    have hj01 : x j = x (shiftIdx t hpos j 1) :=
      hx.2 j (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
        (by rw [← shiftIdx_one]; exact (Finset.mem_filter.mp hj1_in).1)
    have hj12 : x (shiftIdx t hpos j 1) = x (shiftIdx t hpos j 2) := by
      have := hx.2 (shiftIdx t hpos j 1) (Finset.mem_filter.mp hj1_in).1
        (by rw [nextIdx_shiftIdx']; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
      rwa [nextIdx_shiftIdx'] at this
    have hj23 : x (shiftIdx t hpos j 2) = x (shiftIdx t hpos j 3) := by
      have := hx.2 (shiftIdx t hpos j 2)
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
        (by rw [nextIdx_shiftIdx']; exact (Finset.mem_filter.mp hj3_in).1)
      rwa [nextIdx_shiftIdx'] at this
    have hj34 : x (shiftIdx t hpos j 3) = x (shiftIdx t hpos j 4) := by
      have := hx.2 (shiftIdx t hpos j 3) (Finset.mem_filter.mp hj3_in).1
        (by rw [nextIdx_shiftIdx']; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
      rwa [nextIdx_shiftIdx'] at this
    have hx2 : x (shiftIdx t hpos j 2) = x j := (hj01.trans hj12).symm
    have hx4 : x (shiftIdx t hpos j 4) = x j := (hj01.trans (hj12.trans (hj23.trans hj34))).symm
    ext k
    change ∑ i : Fin (6 * t), hFn t i (laneBit p k) * x i = 0
    rw [← Finset.sum_subset (Finset.subset_univ ({j, shiftIdx t hpos j 2, shiftIdx t hpos j 4} : Finset _))]
    · rw [Finset.sum_insert (by simp [hne02, hne04]), Finset.sum_pair hne24, hx2, hx4]
      have ht3 := hFn_sum_triple t hpos j (laneBit p k)
      calc hFn t j (laneBit p k) * x j +
            (hFn t (shiftIdx t hpos j 2) (laneBit p k) * x j +
             hFn t (shiftIdx t hpos j 4) (laneBit p k) * x j)
          = (hFn t j (laneBit p k) + hFn t (shiftIdx t hpos j 2) (laneBit p k) +
             hFn t (shiftIdx t hpos j 4) (laneBit p k)) * x j := by ring
        _ = 0 * x j := by rw [ht3]
        _ = 0 := zero_mul _
    · intro i _ hi
      by_cases hiS : i ∈ S
      · by_cases hip : i.val % 2 = p
        · exfalso; apply hi
          rw [← hBp]; exact Finset.mem_filter.mpr ⟨hiS, hip⟩
        · rw [hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hip), zero_mul]
      · rw [hx.1 i hiS, mul_zero]
  have hrB0 : rB t hpos S p = 0 := by
    unfold rB
    rw [Submodule.finrank_eq_zero]
    rw [Submodule.eq_bot_iff]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    exact hrB_zero x hx
  have hfr : Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
    have h1 := finrank_GoodMax_add_rankHV t hpos S (by omega)
    have h2 := rFree_add_rB_le_rankHV t hpos S p hp
    have h3 := rankHV_le_rB_add_two t hpos S p hp
    rw [htwo.1, hrB0] at h2
    rw [hrB0] at h3
    rw [hruns] at h1
    omega
  -- Long run indicator for full support on S \ freeOpp
  let longV : Fin (6 * t) → F2 := fun x =>
    if x = j ∨ x = shiftIdx t hpos j 1 ∨ x = shiftIdx t hpos j 2 ∨
       x = shiftIdx t hpos j 3 ∨ x = shiftIdx t hpos j 4 ∨
       (x = prevIdx t hpos j ∧ prevIdx t hpos j ∈ S) ∨
       (x = shiftIdx t hpos j 5 ∧ shiftIdx t hpos j 5 ∈ S)
    then 1 else 0
  have hlongV : longV ∈ Vset t hpos S := by
    have hj6_out : shiftIdx t hpos j 6 ∉ S := by
      intro h6
      have h6B : shiftIdx t hpos j 6 ∈ laneSub t S p :=
        Finset.mem_filter.mpr ⟨h6, by rw [shiftIdx_mod2]; omega⟩
      rw [hBp] at h6B
      simp only [Finset.mem_insert, Finset.mem_singleton] at h6B
      rcases h6B with h | h | h
      · exact shiftIdx_ne_of_ne t hpos j (a := 6) (b := 0) (by omega) (by omega) (by omega) (by rwa [shiftIdx_zero])
      · exact shiftIdx_ne_of_ne t hpos j (a := 6) (b := 2) (by omega) (by omega) (by omega) h
      · exact shiftIdx_ne_of_ne t hpos j (a := 6) (b := 4) (by omega) (by omega) (by omega) h
    have hjp2_out : prev2 t hpos j ∉ S := by
      intro h2
      have h2B : prev2 t hpos j ∈ laneSub t S p :=
        Finset.mem_filter.mpr ⟨h2, by rw [prev2_mod2]⟩
      rw [hBp, prev2_eq_shift] at h2B
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2B
      rcases h2B with h | h | h
      · exact shiftIdx_ne_of_ne t hpos j (a := 6 * t - 2) (b := 0) (by omega) (by omega) (by omega) (by rwa [shiftIdx_zero])
      · exact shiftIdx_ne_of_ne t hpos j (a := 6 * t - 2) (b := 2) (by omega) (by omega) (by omega) h
      · exact shiftIdx_ne_of_ne t hpos j (a := 6 * t - 2) (b := 4) (by omega) (by omega) (by omega) h
    refine ⟨fun x hx => ?_, fun x hx hnx => ?_⟩
    · dsimp only [longV]; rw [if_neg]
      rintro (rfl | rfl | rfl | rfl | rfl | ⟨rfl, h1⟩ | ⟨rfl, h1⟩)
      · exact hx (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
      · exact hx (Finset.mem_filter.mp hj1_in).1
      · exact hx (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
      · exact hx (Finset.mem_filter.mp hj3_in).1
      · exact hx (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))))
      · exact hx h1
      · exact hx h1
    · dsimp only [longV]
      by_cases h0 : x = j
      · subst h0; rw [if_pos (Or.inl rfl), ← shiftIdx_one, if_pos (Or.inr (Or.inl rfl))]
      · by_cases h1 : x = shiftIdx t hpos j 1
        · subst h1; rw [nextIdx_shiftIdx', if_pos (Or.inr (Or.inl rfl)), if_pos (Or.inr (Or.inr (Or.inl rfl)))]
        · by_cases h2 : x = shiftIdx t hpos j 2
          · subst h2; rw [nextIdx_shiftIdx', if_pos (Or.inr (Or.inr (Or.inl rfl))),
              if_pos (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
          · by_cases h3 : x = shiftIdx t hpos j 3
            · subst h3; rw [nextIdx_shiftIdx', if_pos (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
                if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
            · by_cases h4 : x = shiftIdx t hpos j 4
              · subst h4; rw [nextIdx_shiftIdx', if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
                  if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [← nextIdx_shiftIdx']; exact hnx⟩))))))]
              · by_cases hp1 : x = prevIdx t hpos j
                · subst hp1; rw [nextIdx_prevIdx, if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hx⟩)))))),
                    if_pos (Or.inl rfl)]
                · by_cases h5 : x = shiftIdx t hpos j 5
                  · subst h5; rw [nextIdx_shiftIdx'] at hnx; exact False.elim (hj6_out hnx)
                  · rw [if_neg (by tauto), if_neg]
                    rintro (h | h | h | h | h | ⟨h, _⟩ | ⟨h, _⟩)
                    · exact hp1 (by rw [← prevIdx_nextIdx t hpos x, h])
                    · exact h0 (nextIdx_inj t hpos (by rwa [← shiftIdx_one]))
                    · exact h1 (nextIdx_inj t hpos (by rwa [nextIdx_shiftIdx']))
                    · exact h2 (nextIdx_inj t hpos (by rwa [nextIdx_shiftIdx']))
                    · exact h3 (nextIdx_inj t hpos (by rwa [nextIdx_shiftIdx']))
                    · exact hjp2_out (by rw [prev2, ← h, prevIdx_nextIdx]; exact hx)
                    · exact h4 (nextIdx_inj t hpos (by rwa [nextIdx_shiftIdx']))
  have hsupp : suppU t (GoodMax t hpos S) = S := by
    apply Finset.Subset.antisymm (suppU_GoodMax_subset t hpos S)
    intro i hiS
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hif : i ∈ freeOpp t hpos S p
    · exact htwo.2 i hif
    · have hi_long : longV i = 1 := by
        dsimp only [longV]; rw [if_pos]
        by_cases hip : i.val % 2 = p
        · have hiB : i ∈ laneSub t S p := Finset.mem_filter.mpr ⟨hiS, hip⟩
          rw [hBp] at hiB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hiB
          rcases hiB with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · have hiA : i ∈ laneSub t S (1 - p) := Finset.mem_filter.mpr ⟨hiS, by omega⟩
          have hor : prevIdx t hpos i ∈ laneSub t S p ∨ nextIdx t hpos i ∈ laneSub t S p := by
            by_contra hnot; apply hif; exact Finset.mem_filter.mpr ⟨hiA, by tauto⟩
          rw [hBp] at hor
          simp only [Finset.mem_insert, Finset.mem_singleton] at hor
          rcases hor with (h | h | h) | (h | h | h)
          · have : i = shiftIdx t hpos j 1 := by
              have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, ← shiftIdx_one] at this
            exact Or.inr (Or.inl this)
          · have : i = shiftIdx t hpos j 3 := by
              have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
            exact Or.inr (Or.inr (Or.inr (Or.inl this)))
          · have : i = shiftIdx t hpos j 5 := by
              have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨this, this ▸ hiS⟩)))))
          · have : i = prevIdx t hpos j := by
              have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at this
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨this, this ▸ hiS⟩)))))
          · have : i = shiftIdx t hpos j 1 := by
              have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this
            exact Or.inr (Or.inl this)
          · have : i = shiftIdx t hpos j 3 := by
              have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this
            exact Or.inr (Or.inr (Or.inr (Or.inl this)))
      have hi7 : i ≠ shiftIdx t hpos j 7 := fun h => hif (h ▸ hu1)
      have hi9 : i ≠ shiftIdx t hpos j 9 := fun h => hif (h ▸ hu2)
      exact supp_of_Vset_cancel t hpos S p hp hu1 hu2
        (shiftIdx_two_ne_mod3 t hpos j 7) hlongV (hrB_zero longV hlongV) hi_long hi7 hi9
  exact ⟨hcardB, hcardA_gt, hruns, hsupp, hfr⟩

lemma card_Fam2Set (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) :
    (Fam2Set t hpos).card = 4 * (6 * t) := by
  unfold Fam2Set
  rw [Finset.card_image_of_injOn]
  · simp; ring
  · rintro ⟨j1, bL1, bR1⟩ _ ⟨j2, bL2, bR2⟩ _ heq
    dsimp only at heq
    have hp1 := mkFam2_props t hpos ht j1 bL1 bR1
    have hp2 := mkFam2_props t hpos ht j2 bL2 bR2
    have hpar : j1.val % 2 = j2.val % 2 := by
      by_contra hne
      have h1 := hp1.1
      have h2 := hp2.2.1
      have h12 : 1 - j2.val % 2 = j1.val % 2 := by omega
      rw [h12, ← heq] at h2
      omega
    have hB_eq : ({j1, shiftIdx t hpos j1 2, shiftIdx t hpos j1 4} : Finset _) =
        {j2, shiftIdx t hpos j2 2, shiftIdx t hpos j2 4} := by
      rw [← mkFam2_laneSub_p t hpos j1 bL1 bR1, ← mkFam2_laneSub_p t hpos j2 bL2 bR2,
        heq, hpar]
    have hj_eq : j1 = j2 := by
      have hj1_mem : j1 ∈ ({j2, shiftIdx t hpos j2 2, shiftIdx t hpos j2 4} : Finset _) := by
        rw [← hB_eq]; simp
      have hj1_pre : prev2 t hpos j1 ∉ ({j2, shiftIdx t hpos j2 2, shiftIdx t hpos j2 4} : Finset _) := by
        rw [← hB_eq, prev2_eq_shift]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega),
          shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega),
          shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj1_mem
      rcases hj1_mem with rfl | rfl | rfl
      · rfl
      · exfalso; apply hj1_pre; rw [← next2, prev2_next2]; simp
      · exfalso; apply hj1_pre
        have : prev2 t hpos (shiftIdx t hpos j2 4) = shiftIdx t hpos j2 2 := by
          apply next2_inj t hpos; rw [next2_prev2, next2, shiftIdx_add]
        rw [this]; simp
    subst hj_eq
    have hmemL : ∀ bL bR, prevIdx t hpos j1 ∈ mkFam2 t hpos j1 bL bR ↔ bL = true := by
      intro bL bR
      simp only [mkFam2, laneSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_filter, Finset.mem_univ, true_and]
      have hne1 : prevIdx t hpos j1 ≠ j1 := by
        rw [prevIdx_eq_shift]; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega)
      have hne2 : prevIdx t hpos j1 ≠ shiftIdx t hpos j1 2 := by
        rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)
      have hne4 : prevIdx t hpos j1 ≠ shiftIdx t hpos j1 4 := by
        rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)
      have hne5 : prevIdx t hpos j1 ≠ shiftIdx t hpos j1 5 := by
        rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)
      cases bL <;> cases bR <;> simp [hne1, hne2, hne4, hne5]
    have hmemR : ∀ bL bR, shiftIdx t hpos j1 5 ∈ mkFam2 t hpos j1 bL bR ↔ bR = true := by
      intro bL bR
      simp only [mkFam2, laneSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_filter, Finset.mem_univ, true_and]
      have hne1 : shiftIdx t hpos j1 5 ≠ j1 :=
        shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega)
      have hne2 : shiftIdx t hpos j1 5 ≠ shiftIdx t hpos j1 2 :=
        shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)
      have hne4 : shiftIdx t hpos j1 5 ≠ shiftIdx t hpos j1 4 :=
        shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)
      have hnep : shiftIdx t hpos j1 5 ≠ prevIdx t hpos j1 := by
        rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)
      cases bL <;> cases bR <;> simp [hne1, hne2, hne4, hnep]
    have hbL : bL1 = bL2 :=
      bool_eq_of_iff ((hmemL bL1 bR1).symm.trans (by rw [heq]; exact hmemL bL2 bR2))
    have hbR : bR1 = bR2 :=
      bool_eq_of_iff ((hmemR bL1 bR1).symm.trans (by rw [heq]; exact hmemR bL2 bR2))
    subst hbL; subst hbR; rfl

lemma classify_rB_zero (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hBpos : 0 < (laneSub t S p).card) (hBlt : (laneSub t S p).card < 3 * t)
    (hrB0 : rB t hpos S p = 0)
    (hsum : blocksB t hpos S p + (missFree t hpos S p).card + (mergedInt t hpos S p).card ≤ 3) :
    S ∈ Fam2Set t hpos := by
  have hs_pos : 1 ≤ blocksB t hpos S p := blocksB_pos_of_lt t hpos S p hp hBpos hBlt
  have h2s := two_mul_blocksB_le_of_rB_zero t hpos ht S p hp hrB0
  have hs1 : blocksB t hpos S p = 1 := by omega
  have hq0 : (missFree t hpos S p).card = 0 := by omega
  have hM2 : (mergedInt t hpos S p).card = 2 := by omega
  have hzero : ∀ v ∈ Vset t hpos S, projLane p (Hmap t v) = 0 := by
    intro v hv
    have hbot : LinearMap.range ((projLane p).comp (HV t hpos S)) = ⊥ :=
      Submodule.finrank_eq_zero.mp hrB0
    have hmem : projLane p (Hmap t v) ∈ LinearMap.range ((projLane p).comp (HV t hpos S)) :=
      ⟨⟨v, hv⟩, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  have hst_pos : 0 < ((laneSub t S p).filter (fun j => prev2 t hpos j ∉ laneSub t S p)).card := by
    rw [blocksB_eq_starts]; omega
  rcases Finset.card_pos.mp hst_pos with ⟨j, hjst⟩
  rcases Finset.mem_filter.mp hjst with ⟨hjB, hjpre2⟩
  have hjp : j.val % 2 = p := (Finset.mem_filter.mp hjB).2
  have hpreM : prevIdx t hpos j ∉ mergedInt t hpos S p := by
    intro hm; exact hjpre2 (Finset.mem_filter.mp hm).2.1
  have hm1 : nextIdx t hpos j ∈ mergedInt t hpos S p := by
    by_contra hnot
    have hv := isoVec_mem_Vset t hpos ht S p hp hjB hpreM hnot
    have hz := hzero _ hv
    rw [projLane_Hmap_isoVec t hpos ht S p hp hjp] at hz
    exact hLane_ne_zero t p hp j hjp hz
  have hm3 : shiftIdx t hpos j 3 ∈ mergedInt t hpos S p := by
    have hpm : prev2 t hpos (nextIdx t hpos j) ∉ mergedInt t hpos S p := by
      rw [prev2, prevIdx_nextIdx]; exact hpreM
    by_contra hnot
    have hn2eq : next2 t hpos (nextIdx t hpos j) = shiftIdx t hpos j 3 := by
      rw [next2, ← shiftIdx_one, shiftIdx_add]
    have hv := pairVec_mem_Vset t hpos ht S p hp hm1 hpm (hn2eq.symm ▸ hnot)
    have hz := hzero _ hv
    rw [projLane_Hmap_pairVec t hpos ht S p hp (by rw [nextIdx_mod2, hjp]),
      hLane_prev_next_eq_prev3] at hz
    have h3p : (prevIdx t hpos (prev2 t hpos (nextIdx t hpos j))).val % 2 = p := by
      rw [prevIdx_mod2, prev2_mod2, nextIdx_mod2, hjp]; omega
    exact hLane_ne_zero t p hp _ h3p hz
  have hMeq : mergedInt t hpos S p = {shiftIdx t hpos j 1, shiftIdx t hpos j 3} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hm1
      · rw [Finset.mem_singleton.mp hx]; exact hm3
    · rw [hM2, Finset.card_pair (shiftIdx_ne_of_ne t hpos j (a := 1) (b := 3) (by omega) (by omega) (by omega))]
  have hj2B : shiftIdx t hpos j 2 ∈ laneSub t S p := by
    have := (Finset.mem_filter.mp hm1).2.2
    rwa [← next2_eq_next_next] at this
  have hj4B : shiftIdx t hpos j 4 ∈ laneSub t S p := by
    have := (Finset.mem_filter.mp hm3).2.2
    rwa [nextIdx_shiftIdx'] at this
  have hj6_out : shiftIdx t hpos j 6 ∉ laneSub t S p := by
    intro hj6B
    have hpre6 : prevIdx t hpos (shiftIdx t hpos j 6) ∉ mergedInt t hpos S p := by
      rw [prevIdx_shiftIdx_pos t hpos j (by omega), hMeq]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)⟩
    have hnxt6 : nextIdx t hpos (shiftIdx t hpos j 6) ∉ mergedInt t hpos S p := by
      rw [nextIdx_shiftIdx', hMeq]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega),
        shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)⟩
    have hv := isoVec_mem_Vset t hpos ht S p hp hj6B hpre6 hnxt6
    have hz := hzero _ hv
    have hj6p : (shiftIdx t hpos j 6).val % 2 = p := (Finset.mem_filter.mp hj6B).2
    rw [projLane_Hmap_isoVec t hpos ht S p hp hj6p] at hz
    exact hLane_ne_zero t p hp _ hj6p hz
  have hBeq : laneSub t S p = {j, shiftIdx t hpos j 2, shiftIdx t hpos j 4} := by
    have hsb := single_block_subset t hpos S p hp hs1 hjB hjpre2 (k := 3) (by omega) (by omega) hj6_out
      (fun d hd => by
        interval_cases d
        · simpa [shiftIdx_zero] using hjB
        · exact hj2B
        · exact hj4B)
    rw [hsb]
    ext x; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨d, hd, rfl⟩
      interval_cases d
      · left; exact shiftIdx_zero t hpos j
      · right; left; rfl
      · right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by omega, shiftIdx_zero t hpos _⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
  have hmiss_emp : missFree t hpos S p = ∅ := Finset.card_eq_zero.mp hq0
  have hSeq : S = mkFam2 t hpos j (decide (prevIdx t hpos j ∈ S)) (decide (shiftIdx t hpos j 5 ∈ S)) := by
    ext x
    by_cases hxp : x.val % 2 = p
    · have h1 : x ∈ S ↔ x ∈ laneSub t S p := by simp [laneSub, hxp]
      have h2 : x ∈ mkFam2 t hpos j (decide (prevIdx t hpos j ∈ S)) (decide (shiftIdx t hpos j 5 ∈ S)) ↔
          x ∈ laneSub t (mkFam2 t hpos j (decide (prevIdx t hpos j ∈ S)) (decide (shiftIdx t hpos j 5 ∈ S))) p := by
        simp [laneSub, hxp]
      rw [h1, h2, hBeq, ← hjp, mkFam2_laneSub_p]
    · have hxp1 : x.val % 2 = 1 - p := by omega
      by_cases hxL : x = prevIdx t hpos j
      · subst hxL
        simp only [mkFam2, laneSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_filter, Finset.mem_univ, true_and, mem_if_singleton]
        have hne1 : prevIdx t hpos j ≠ j := by
          rw [prevIdx_eq_shift]; exact shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega)
        have hne2 : prevIdx t hpos j ≠ shiftIdx t hpos j 2 := by
          rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
        have hne4 : prevIdx t hpos j ≠ shiftIdx t hpos j 4 := by
          rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
        have hne5 : prevIdx t hpos j ≠ shiftIdx t hpos j 5 := by
          rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
        simp [hne1, hne2, hne4, hne5]
      · by_cases hxR : x = shiftIdx t hpos j 5
        · subst hxR
          simp only [mkFam2, laneSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            Finset.mem_filter, Finset.mem_univ, true_and, mem_if_singleton]
          have hne1 : shiftIdx t hpos j 5 ≠ j :=
            shiftIdx_ne_self_of_pos t hpos j (by omega) (by omega)
          have hne2 : shiftIdx t hpos j 5 ≠ shiftIdx t hpos j 2 :=
            shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
          have hne4 : shiftIdx t hpos j 5 ≠ shiftIdx t hpos j 4 :=
            shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
          have hnep : shiftIdx t hpos j 5 ≠ prevIdx t hpos j := by
            rw [prevIdx_eq_shift]; exact shiftIdx_ne_of_ne t hpos j (by omega) (by omega) (by omega)
          simp [hne1, hne2, hne4, hnep]
        · have hx_in_rhs : x ∈ mkFam2 t hpos j (decide (prevIdx t hpos j ∈ S)) (decide (shiftIdx t hpos j 5 ∈ S)) := by
            refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hjp]; exact hxp1⟩, hxL, hxR⟩
          have hx_in_S : x ∈ S := by
            by_cases hx1 : x = shiftIdx t hpos j 1
            · subst hx1; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm1).1).1
            · by_cases hx3 : x = shiftIdx t hpos j 3
              · subst hx3; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm3).1).1
              · by_contra hxnot
                have hmf : x ∈ missFree t hpos S p := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
                    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp1⟩,
                     fun h => hxnot (Finset.mem_filter.mp h).1⟩, ?_, ?_⟩
                  · rw [hBeq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    refine ⟨fun h => hx1 (by have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, ← shiftIdx_one] at this),
                      fun h => hx3 (by have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this),
                      fun h => hxR (by have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this)⟩
                  · rw [hBeq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    refine ⟨fun h => hxL (by have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at this),
                      fun h => hx1 (by have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this),
                      fun h => hx3 (by have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos j (by omega)] at this)⟩
                rw [hmiss_emp] at hmf; exact Finset.notMem_empty _ hmf
          simp [hx_in_S, hx_in_rhs]
  rw [hSeq]
  exact Finset.mem_image.mpr ⟨(j, decide (prevIdx t hpos j ∈ S), decide (shiftIdx t hpos j 5 ∈ S)),
    Finset.mem_univ _, rfl⟩

-- ============================================================================
-- L-lib-898 Section B3: Family 3A (rB = 1, M_int = 0, c = a - 2, count = 96 * C(t, 2))
-- ============================================================================

def pairsT (t : ℕ) : Finset (Fin t × Fin t) :=
  (Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => ab.1.val < ab.2.val)

lemma card_pairsT (t : ℕ) : (pairsT t).card = Nat.choose t 2 := by
  let gtT := (Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => ab.2.val < ab.1.val)
  let eqT := (Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => ab.1.val = ab.2.val)
  have hswap : gtT.card = (pairsT t).card :=
    Finset.card_bij (fun ab _ => (ab.2, ab.1))
      (fun ab hab => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hab).2⟩)
      (fun a _ b _ h => by cases a; cases b; simp at h; exact Prod.ext h.2 h.1)
      (fun ab hab => ⟨(ab.2, ab.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hab).2⟩, rfl⟩)
  have heq : eqT.card = t := by
    have hbij : eqT.card = (Finset.univ : Finset (Fin t)).card :=
      Finset.card_bij (fun ab _ => ab.1)
        (fun _ _ => Finset.mem_univ _)
        (fun a ha b hb h => by
          have hae := (Finset.mem_filter.mp ha).2
          have hbe := (Finset.mem_filter.mp hb).2
          exact Prod.ext h (Fin.ext (by rw [← hae, ← hbe, h])))
        (fun a _ => ⟨(a, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)
    simpa using hbij
  have hd1 : Disjoint (pairsT t) gtT := by
    rw [Finset.disjoint_left]; intro ab h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hd2 : Disjoint (pairsT t ∪ gtT) eqT := by
    rw [Finset.disjoint_left]; intro ab h1 h2
    have h2e := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · have := (Finset.mem_filter.mp h1).2; omega
    · have := (Finset.mem_filter.mp h1).2; omega
  have hun : (pairsT t ∪ gtT) ∪ eqT = Finset.univ := by
    ext ab; simp only [pairsT, gtT, eqT, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  have htot := Finset.card_union_of_disjoint hd2
  rw [hun, Finset.card_union_of_disjoint hd1, hswap, heq, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin] at htot
  rw [Nat.choose_two_right]
  have hmul : 2 * (t * (t - 1) / 2) = t * (t - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self t).two_dvd
  have hsq : t * (t - 1) + t = t * t := by
    cases t with
    | zero => simp
    | succ k => simp; ring
  omega

def mkFam3A (t : ℕ) (hpos : 0 < t) (r : Fin 6) (ab : Fin t × Fin t)
    (b1 b2 b3 b4 : Bool) : Finset (Fin (6 * t)) :=
  let p := r.val % 2
  let j1 : Fin (6 * t) := ⟨6 * ab.1.val + r.val, by have := ab.1.isLt; have := r.isLt; omega⟩
  let j2 : Fin (6 * t) := ⟨6 * ab.2.val + r.val, by have := ab.2.isLt; have := r.isLt; omega⟩
  let B : Finset (Fin (6 * t)) := {j1, j2}
  let A0 : Finset (Fin (6 * t)) :=
    (laneSet t (1 - p)).filter (fun i =>
      i ≠ prevIdx t hpos j1 ∧ i ≠ nextIdx t hpos j1 ∧
      i ≠ prevIdx t hpos j2 ∧ i ≠ nextIdx t hpos j2)
  let A1 : Finset (Fin (6 * t)) := if b1 then {prevIdx t hpos j1} else ∅
  let A2 : Finset (Fin (6 * t)) := if b2 then {nextIdx t hpos j1} else ∅
  let A3 : Finset (Fin (6 * t)) := if b3 then {prevIdx t hpos j2} else ∅
  let A4 : Finset (Fin (6 * t)) := if b4 then {nextIdx t hpos j2} else ∅
  B ∪ A0 ∪ A1 ∪ A2 ∪ A3 ∪ A4

def Fam3ASet (t : ℕ) (hpos : 0 < t) : Finset (Finset (Fin (6 * t))) :=
  (((Finset.univ : Finset (Fin 6)) ×ˢ pairsT t) ×ˢ
    (Finset.univ : Finset (Bool × Bool × Bool × Bool))).image
    (fun x => mkFam3A t hpos x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)

lemma mkFam3A_laneSub_p (t : ℕ) (hpos : 0 < t) (r : Fin 6) (ab : Fin t × Fin t)
    (b1 b2 b3 b4 : Bool) :
    let j1 : Fin (6 * t) := ⟨6 * ab.1.val + r.val, by have := ab.1.isLt; have := r.isLt; omega⟩
    let j2 : Fin (6 * t) := ⟨6 * ab.2.val + r.val, by have := ab.2.isLt; have := r.isLt; omega⟩
    laneSub t (mkFam3A t hpos r ab b1 b2 b3 b4) (r.val % 2) = {j1, j2} := by
  intro j1 j2
  have hp : r.val % 2 = 0 ∨ r.val % 2 = 1 := by omega
  have hj1p : j1.val % 2 = r.val % 2 := by dsimp [j1]; omega
  have hj2p : j2.val % 2 = r.val % 2 := by dsimp [j2]; omega
  ext x
  simp only [laneSub, mkFam3A, laneSet, Finset.mem_filter, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨((((hB | ⟨hxp, _⟩) | h1) | h2) | h3) | h4, hxp'⟩
    · exact hB
    · omega
    · cases b1 <;> simp at h1; rw [h1, prevIdx_mod2, hj1p] at hxp'; omega
    · cases b2 <;> simp at h2; rw [h2, nextIdx_mod2, hj1p] at hxp'; omega
    · cases b3 <;> simp at h3; rw [h3, prevIdx_mod2, hj2p] at hxp'; omega
    · cases b4 <;> simp at h4; rw [h4, nextIdx_mod2, hj2p] at hxp'; omega
  · rintro (rfl | rfl)
    · exact ⟨Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))), hj1p⟩
    · exact ⟨Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))), hj2p⟩

lemma mkFam3A_props (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (r : Fin 6) (ab : Fin t × Fin t) (hab : ab.1.val < ab.2.val)
    (b1 b2 b3 b4 : Bool) :
    let S := mkFam3A t hpos r ab b1 b2 b3 b4
    let p := r.val % 2
    sitesS t S p = 2 ∧ 4 < sitesS t S (1 - p) ∧
    runsS t hpos S = 3 * t - 2 ∧
    suppU t (GoodMax t hpos S) = S ∧
    Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
  intro S p
  have hp : p = 0 ∨ p = 1 := by omega
  let j1 : Fin (6 * t) := ⟨6 * ab.1.val + r.val, by have := ab.1.isLt; have := r.isLt; omega⟩
  let j2 : Fin (6 * t) := ⟨6 * ab.2.val + r.val, by have := ab.2.isLt; have := r.isLt; omega⟩
  let d : ℕ := ab.2.val - ab.1.val
  have hd1 : 1 ≤ d := by omega
  have hdt : d < t := by have := ab.2.isLt; omega
  have hj2_eq : j2 = shiftIdx t hpos j1 (6 * d) := by
    apply Fin.ext; dsimp [j1, j2, shiftIdx, d]
    have := ab.2.isLt; have := r.isLt
    rw [show 6 * ab.1.val + r.val + 6 * (ab.2.val - ab.1.val) = 6 * ab.2.val + r.val by omega,
      Nat.mod_eq_of_lt (by omega)]
  have hj1p : j1.val % 2 = p := by dsimp [j1, p]; omega
  have hj2p : j2.val % 2 = p := by dsimp [j2, p]; omega
  have hj12_mod3 : j1.val / 2 % 3 = j2.val / 2 % 3 := by dsimp [j1, j2]; omega
  have hBp : laneSub t S p = {j1, j2} := mkFam3A_laneSub_p t hpos r ab b1 b2 b3 b4
  have hne12 : j1 ≠ j2 := by intro h; have := congrArg Fin.val h; dsimp [j1, j2] at this; omega
  have hcardB : sitesS t S p = 2 := by
    rw [← laneSub_card_eq_sites, hBp, Finset.card_pair hne12]
  have hA0_sub : (laneSet t (1 - p)).filter (fun i =>
      i ≠ prevIdx t hpos j1 ∧ i ≠ nextIdx t hpos j1 ∧
      i ≠ prevIdx t hpos j2 ∧ i ≠ nextIdx t hpos j2) ⊆ laneSub t S (1 - p) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hi))))
  have hcardA_gt : 4 < sitesS t S (1 - p) := by
    have h1 : (laneSet t (1 - p)).card ≤
        ((laneSet t (1 - p)).filter (fun i =>
          i ≠ prevIdx t hpos j1 ∧ i ≠ nextIdx t hpos j1 ∧
          i ≠ prevIdx t hpos j2 ∧ i ≠ nextIdx t hpos j2)).card + 4 := by
      have hsub : laneSet t (1 - p) ⊆
          (laneSet t (1 - p)).filter (fun i =>
            i ≠ prevIdx t hpos j1 ∧ i ≠ nextIdx t hpos j1 ∧
            i ≠ prevIdx t hpos j2 ∧ i ≠ nextIdx t hpos j2) ∪
          {prevIdx t hpos j1, nextIdx t hpos j1, prevIdx t hpos j2, nextIdx t hpos j2} := by
        intro i hi
        by_cases h : i ≠ prevIdx t hpos j1 ∧ i ≠ nextIdx t hpos j1 ∧
            i ≠ prevIdx t hpos j2 ∧ i ≠ nextIdx t hpos j2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
        · exact Finset.mem_union_right _ (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hle := Finset.card_le_card hsub
      have hun := Finset.card_union_le
        ((laneSet t (1 - p)).filter (fun i =>
          i ≠ prevIdx t hpos j1 ∧ i ≠ nextIdx t hpos j1 ∧
          i ≠ prevIdx t hpos j2 ∧ i ≠ nextIdx t hpos j2))
        {prevIdx t hpos j1, nextIdx t hpos j1, prevIdx t hpos j2, nextIdx t hpos j2}
      have h4 : ({prevIdx t hpos j1, nextIdx t hpos j1, prevIdx t hpos j2, nextIdx t hpos j2} : Finset _).card ≤ 4 :=
        le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
          (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
            (le_trans (Finset.card_insert_le _ _) (by simp)))))
      omega
    have hle2 := Finset.card_le_card hA0_sub
    rw [card_laneSet t (1 - p) (by omega)] at h1
    rw [laneSub_card_eq_sites] at hle2
    omega
  have hblocks : blocksB t hpos S p = 2 := by
    unfold blocksB
    rw [hBp]
    have hfilt : ({j1, j2} : Finset _).filter (fun x => next2 t hpos x ∉ ({j1, j2} : Finset _)) =
        {j1, j2} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, and_iff_left_iff_imp]
      rintro (rfl | rfl) (h | h)
      · exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega) h
      · have h3 := shiftIdx_two_div2_mod3 t hpos j1; rw [show shiftIdx t hpos j1 2 = j2 from h] at h3; omega
      · have h3 := shiftIdx_two_div2_mod3 t hpos j2; rw [show shiftIdx t hpos j2 2 = j1 from h] at h3; omega
      · exact shiftIdx_ne_self_of_pos t hpos j2 (by omega) (by omega) h
    rw [hfilt, Finset.card_pair hne12]
  have hmiss : missFree t hpos S p = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hsd, hpre, hnxt⟩
    rcases Finset.mem_sdiff.mp hsd with ⟨hiL, hiA⟩
    have hor : i = prevIdx t hpos j1 ∨ i = nextIdx t hpos j1 ∨
        i = prevIdx t hpos j2 ∨ i = nextIdx t hpos j2 := by
      by_contra hnot
      exact hiA (hA0_sub (Finset.mem_filter.mpr ⟨hiL, by tauto⟩))
    rcases hor with rfl | rfl | rfl | rfl
    · apply hnxt; rw [nextIdx_prevIdx, hBp]; simp
    · apply hpre; rw [prevIdx_nextIdx, hBp]; simp
    · apply hnxt; rw [nextIdx_prevIdx, hBp]; simp
    · apply hpre; rw [prevIdx_nextIdx, hBp]; simp
  have hmerged : mergedInt t hpos S p = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨_, hpre, hnxt⟩
    rw [hBp] at hpre hnxt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpre hnxt
    have h2eq : next2 t hpos (prevIdx t hpos i) = nextIdx t hpos i := by
      rw [next2_eq_next_next, nextIdx_prevIdx]
    rcases hpre with h1 | h1 <;> rcases hnxt with h2 | h2
    · rw [h1, h2] at h2eq; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega) h2eq
    · rw [h1, h2] at h2eq
      have h3 := shiftIdx_two_div2_mod3 t hpos j1; rw [show shiftIdx t hpos j1 2 = j2 from h2eq] at h3; omega
    · rw [h1, h2] at h2eq
      have h3 := shiftIdx_two_div2_mod3 t hpos j2; rw [show shiftIdx t hpos j2 2 = j1 from h2eq] at h3; omega
    · rw [h1, h2] at h2eq; exact shiftIdx_ne_self_of_pos t hpos j2 (by omega) (by omega) h2eq
  have hruns : runsS t hpos S = 3 * t - 2 := by
    have hid := runsS_identity t hpos S p hp
    rw [hblocks, hmiss, hmerged, Finset.card_empty] at hid
    omega
  -- Pick two distinct k1, k2 ∈ Fin t \ {0, d}
  have hex_k : ∃ k1 k2 : Fin t, k1 ≠ k2 ∧ k1.val ≠ 0 ∧ k1.val ≠ d ∧ k2.val ≠ 0 ∧ k2.val ≠ d := by
    let G := ((Finset.univ : Finset (Fin t)).erase ⟨0, hpos⟩).erase ⟨d, hdt⟩
    have hGcard : 2 ≤ G.card := by
      have h1 : ((Finset.univ : Finset (Fin t)).erase ⟨0, hpos⟩).card = t - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      have h2 : (⟨d, hdt⟩ : Fin t) ∈ (Finset.univ : Finset (Fin t)).erase ⟨0, hpos⟩ :=
        Finset.mem_erase.mpr ⟨fun h => by have := congrArg Fin.val h; dsimp at this; omega, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem h2, h1]; omega
    rcases Finset.one_lt_card.mp (by omega : 1 < G.card) with ⟨k1, hk1, k2, hk2, hne⟩
    have hk1_0 : k1.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hk1).2).1 (Fin.ext h)
    have hk1_d : k1.val ≠ d := fun h => (Finset.mem_erase.mp hk1).1 (Fin.ext h)
    have hk2_0 : k2.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hk2).2).1 (Fin.ext h)
    have hk2_d : k2.val ≠ d := fun h => (Finset.mem_erase.mp hk2).1 (Fin.ext h)
    exact ⟨k1, k2, hne, hk1_0, hk1_d, hk2_0, hk2_d⟩
  rcases hex_k with ⟨k1, k2, hk12, hk1_0, hk1_d, hk2_0, hk2_d⟩
  have hfree_k : ∀ k : Fin t, k.val ≠ 0 → k.val ≠ d →
      shiftIdx t hpos j1 (6 * k.val + 1) ∈ freeOpp t hpos S p ∧
      shiftIdx t hpos j1 (6 * k.val + 3) ∈ freeOpp t hpos S p := by
    intro k hk0 hkd
    have hlt := k.isLt
    have hmem_of : ∀ s : ℕ, (s = 1 ∨ s = 3) →
        shiftIdx t hpos j1 (6 * k.val + s) ∈ freeOpp t hpos S p := by
      intro s hs
      have hpre_ne : prevIdx t hpos (shiftIdx t hpos j1 (6 * k.val + s)) ∉ laneSub t S p := by
        rw [prevIdx_shiftIdx_pos t hpos j1 (by omega), hBp, hj2_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega),
          shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)⟩
      have hnxt_ne : nextIdx t hpos (shiftIdx t hpos j1 (6 * k.val + s)) ∉ laneSub t S p := by
        rw [nextIdx_shiftIdx', hBp, hj2_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega),
          shiftIdx_ne_of_ne t hpos j1 (by omega) (by omega) (by omega)⟩
      refine Finset.mem_filter.mpr ⟨hA0_sub (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftIdx_mod2]; omega⟩,
          fun h => hnxt_ne (by rw [h, nextIdx_prevIdx, hBp]; simp),
          fun h => hpre_ne (by rw [h, prevIdx_nextIdx, hBp]; simp),
          fun h => hnxt_ne (by rw [h, nextIdx_prevIdx, hBp]; simp),
          fun h => hpre_ne (by rw [h, prevIdx_nextIdx, hBp]; simp)⟩), hpre_ne, hnxt_ne⟩
    exact ⟨hmem_of 1 (Or.inl rfl), hmem_of 3 (Or.inr rfl)⟩
  rcases hfree_k k1 hk1_0 hk1_d with ⟨hu1, hu2⟩
  rcases hfree_k k2 hk2_0 hk2_d with ⟨hw1, hw2⟩
  have hk12v : k1.val ≠ k2.val := fun h => hk12 (Fin.ext h)
  have htwo := supp_freeOpp_of_two_pairs t hpos S p hp hu1 hu2 hw1 hw2
    (shiftIdx_two_ne_mod3 t hpos j1 (6 * k1.val + 1))
    (shiftIdx_two_ne_mod3 t hpos j1 (6 * k2.val + 1))
    (shiftIdx_ne_of_ne t hpos j1 (by have := k1.isLt; omega) (by have := k2.isLt; omega) (by omega))
    (shiftIdx_ne_of_ne t hpos j1 (by have := k1.isLt; omega) (by have := k2.isLt; omega) (by omega))
    (shiftIdx_ne_of_ne t hpos j1 (by have := k1.isLt; omega) (by have := k2.isLt; omega) (by omega))
    (shiftIdx_ne_of_ne t hpos j1 (by have := k1.isLt; omega) (by have := k2.isLt; omega) (by omega))
  -- Compute rB = 1
  have hrB_eq : ∀ x ∈ Vset t hpos S, projLane p (Hmap t x) = (x j1 + x j2) • hLane t p j1 := by
    intro x hx
    ext k
    change ∑ i : Fin (6 * t), hFn t i (laneBit p k) * x i = (x j1 + x j2) * hFn t j1 (laneBit p k)
    rw [← Finset.sum_subset (Finset.subset_univ ({j1, j2} : Finset _))]
    · rw [Finset.sum_pair hne12]
      have hj2h : hFn t j2 (laneBit p k) = hFn t j1 (laneBit p k) :=
        congrFun ((hLane_eq_iff t p hp j1 j2 hj1p hj2p).mpr hj12_mod3).symm k
      rw [hj2h]; ring
    · intro i _ hi
      by_cases hiS : i ∈ S
      · by_cases hip : i.val % 2 = p
        · exfalso; apply hi; rw [← hBp]; exact Finset.mem_filter.mpr ⟨hiS, hip⟩
        · rw [hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hip), zero_mul]
      · rw [hx.1 i hiS, mul_zero]
  have hv1V : isoVec t hpos S j1 ∈ Vset t hpos S :=
    isoVec_mem_Vset t hpos ht S p hp (by rw [hBp]; simp) (by rw [hmerged]; simp) (by rw [hmerged]; simp)
  have hv2V : isoVec t hpos S j2 ∈ Vset t hpos S :=
    isoVec_mem_Vset t hpos ht S p hp (by rw [hBp]; simp) (by rw [hmerged]; simp) (by rw [hmerged]; simp)
  have hrB1 : rB t hpos S p = 1 := by
    have hle1 : rB t hpos S p ≤ 1 := by
      have hsub : LinearMap.range ((projLane p).comp (HV t hpos S)) ≤
          Submodule.span F2 ({hLane t p j1} : Set (Fin 2 → F2)) := by
        rintro y ⟨⟨x, hx⟩, rfl⟩
        change projLane p (Hmap t x) ∈ _
        rw [hrB_eq x hx]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
      calc rB t hpos S p ≤ Module.finrank F2 (Submodule.span F2 ({hLane t p j1} : Set (Fin 2 → F2))) :=
            Submodule.finrank_mono hsub
        _ ≤ 1 := finrank_span_sing_le_one _
    have hge1 : 1 ≤ rB t hpos S p := by
      by_contra h0
      unfold rB at h0
      have hbot : LinearMap.range ((projLane p).comp (HV t hpos S)) = ⊥ :=
        Submodule.finrank_eq_zero.mp (by omega)
      have hmem : projLane p (Hmap t (isoVec t hpos S j1)) ∈
          LinearMap.range ((projLane p).comp (HV t hpos S)) := ⟨⟨_, hv1V⟩, rfl⟩
      rw [hbot, Submodule.mem_bot, projLane_Hmap_isoVec t hpos ht S p hp hj1p] at hmem
      exact hLane_ne_zero t p hp j1 hj1p hmem
    omega
  have hfr : Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
    have h1 := finrank_GoodMax_add_rankHV t hpos S (by omega)
    have h2 := rFree_add_rB_le_rankHV t hpos S p hp
    have h3 := rankHV_le_rB_add_two t hpos S p hp
    rw [htwo.1, hrB1] at h2
    rw [hrB1] at h3
    rw [hruns] at h1
    omega
  -- Full support using isoVec j1 + isoVec j2
  have hdisj_iso : ∀ i : Fin (6 * t),
      ¬((i = j1 ∨ i = prevIdx t hpos j1 ∨ i = nextIdx t hpos j1) ∧
        (i = j2 ∨ i = prevIdx t hpos j2 ∨ i = nextIdx t hpos j2)) := by
    intro i ⟨h1, h2⟩
    have hd_mod : ∀ a b : ℕ, a < 6 * t → b < 6 * t → a ≠ b →
        shiftIdx t hpos j1 a ≠ shiftIdx t hpos j1 b := fun a b ha hb hne =>
      shiftIdx_ne_of_ne t hpos j1 ha hb hne
    have hp1 : prevIdx t hpos j1 = shiftIdx t hpos j1 (6 * t - 1) := rfl
    have hn1 : nextIdx t hpos j1 = shiftIdx t hpos j1 1 := rfl
    have hp2 : prevIdx t hpos j2 = shiftIdx t hpos j1 (6 * d - 1) := by
      rw [hj2_eq, prevIdx_shiftIdx_pos t hpos j1 (by omega)]
    have hn2 : nextIdx t hpos j2 = shiftIdx t hpos j1 (6 * d + 1) := by
      rw [hj2_eq, nextIdx_shiftIdx']
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with h | h | h
    · exact hne12 h
    · rw [hp2] at h; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega) h.symm
    · rw [hn2] at h; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega) h.symm
    · rw [hp1, hj2_eq] at h; exact hd_mod (6 * t - 1) (6 * d) (by omega) (by omega) (by omega) h
    · rw [hp1, hp2] at h; exact hd_mod (6 * t - 1) (6 * d - 1) (by omega) (by omega) (by omega) h
    · rw [hp1, hn2] at h; exact hd_mod (6 * t - 1) (6 * d + 1) (by omega) (by omega) (by omega) h
    · rw [hn1, hj2_eq] at h; exact hd_mod 1 (6 * d) (by omega) (by omega) (by omega) h
    · rw [hn1, hp2] at h; exact hd_mod 1 (6 * d - 1) (by omega) (by omega) (by omega) h
    · rw [hn1, hn2] at h; exact hd_mod 1 (6 * d + 1) (by omega) (by omega) (by omega) h
  have hsupp : suppU t (GoodMax t hpos S) = S := by
    apply Finset.Subset.antisymm (suppU_GoodMax_subset t hpos S)
    intro i hiS
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hif : i ∈ freeOpp t hpos S p
    · exact htwo.2 i hif
    · let vsum := isoVec t hpos S j1 + isoVec t hpos S j2
      have hvsumV : vsum ∈ Vset t hpos S := Submodule.add_mem _ hv1V hv2V
      have hvsumB : projLane p (Hmap t vsum) = 0 := by
        simp only [vsum, map_add]
        rw [projLane_Hmap_isoVec t hpos ht S p hp hj1p,
          projLane_Hmap_isoVec t hpos ht S p hp hj2p,
          (hLane_eq_iff t p hp j1 j2 hj1p hj2p).mpr hj12_mod3]
        ext k; exact zmod2_add_self _
      have hor : (i = j1 ∨ i = prevIdx t hpos j1 ∨ i = nextIdx t hpos j1) ∨
          (i = j2 ∨ i = prevIdx t hpos j2 ∨ i = nextIdx t hpos j2) := by
        by_cases hip : i.val % 2 = p
        · have hiB : i ∈ laneSub t S p := Finset.mem_filter.mpr ⟨hiS, hip⟩
          rw [hBp] at hiB
          simp only [Finset.mem_insert, Finset.mem_singleton] at hiB
          rcases hiB with rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr (Or.inl rfl)
        · have hiA : i ∈ laneSub t S (1 - p) := Finset.mem_filter.mpr ⟨hiS, by omega⟩
          have hn : prevIdx t hpos i ∈ laneSub t S p ∨ nextIdx t hpos i ∈ laneSub t S p := by
            by_contra hnot; apply hif; exact Finset.mem_filter.mpr ⟨hiA, by tauto⟩
          rw [hBp] at hn
          simp only [Finset.mem_insert, Finset.mem_singleton] at hn
          rcases hn with (h | h) | (h | h)
          · exact Or.inl (Or.inr (Or.inr (by have h' := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx] at h')))
          · exact Or.inr (Or.inr (Or.inr (by have h' := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx] at h')))
          · exact Or.inl (Or.inr (Or.inl (by have h' := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at h')))
          · exact Or.inr (Or.inr (Or.inl (by have h' := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at h')))
      have hvi : vsum i = 1 := by
        dsimp only [vsum, Pi.add_apply]
        rcases hor with h1 | h2
        · have hn2 : ¬(i = j2 ∨ i = prevIdx t hpos j2 ∨ i = nextIdx t hpos j2) :=
            fun h2 => hdisj_iso i ⟨h1, h2⟩
          have hv1 : isoVec t hpos S j1 i = 1 := by
            dsimp only [isoVec]; rw [if_pos]
            rcases h1 with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨rfl, hiS⟩)
            · exact Or.inr (Or.inr ⟨rfl, hiS⟩)
          have hv2 : isoVec t hpos S j2 i = 0 := by
            dsimp only [isoVec]; rw [if_neg]
            rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
            · exact hn2 (Or.inl h)
            · exact hn2 (Or.inr (Or.inl h))
            · exact hn2 (Or.inr (Or.inr h))
          rw [hv1, hv2, add_zero]
        · have hn1 : ¬(i = j1 ∨ i = prevIdx t hpos j1 ∨ i = nextIdx t hpos j1) :=
            fun h1 => hdisj_iso i ⟨h1, h2⟩
          have hv1 : isoVec t hpos S j1 i = 0 := by
            dsimp only [isoVec]; rw [if_neg]
            rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
            · exact hn1 (Or.inl h)
            · exact hn1 (Or.inr (Or.inl h))
            · exact hn1 (Or.inr (Or.inr h))
          have hv2 : isoVec t hpos S j2 i = 1 := by
            dsimp only [isoVec]; rw [if_pos]
            rcases h2 with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨rfl, hiS⟩)
            · exact Or.inr (Or.inr ⟨rfl, hiS⟩)
          rw [hv1, hv2, zero_add]
      have hiu1 : i ≠ shiftIdx t hpos j1 (6 * k1.val + 1) := fun h => hif (h ▸ hu1)
      have hiu2 : i ≠ shiftIdx t hpos j1 (6 * k1.val + 3) := fun h => hif (h ▸ hu2)
      exact supp_of_Vset_cancel t hpos S p hp hu1 hu2
        (shiftIdx_two_ne_mod3 t hpos j1 (6 * k1.val + 1)) hvsumV hvsumB hvi hiu1 hiu2
  exact ⟨hcardB, hcardA_gt, hruns, hsupp, hfr⟩

lemma mkFam3A_mem_boundary (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (r : Fin 6) (ab : Fin t × Fin t) (hab : ab.1.val < ab.2.val)
    (b1 b2 b3 b4 : Bool) :
    let j1 : Fin (6 * t) := ⟨6 * ab.1.val + r.val, by have := ab.1.isLt; have := r.isLt; omega⟩
    let j2 : Fin (6 * t) := ⟨6 * ab.2.val + r.val, by have := ab.2.isLt; have := r.isLt; omega⟩
    (prevIdx t hpos j1 ∈ mkFam3A t hpos r ab b1 b2 b3 b4 ↔ b1 = true) ∧
    (nextIdx t hpos j1 ∈ mkFam3A t hpos r ab b1 b2 b3 b4 ↔ b2 = true) ∧
    (prevIdx t hpos j2 ∈ mkFam3A t hpos r ab b1 b2 b3 b4 ↔ b3 = true) ∧
    (nextIdx t hpos j2 ∈ mkFam3A t hpos r ab b1 b2 b3 b4 ↔ b4 = true) := by
  intro j1 j2
  let d := ab.2.val - ab.1.val
  have hj2_sh : j2 = shiftIdx t hpos j1 (6 * d) := by
    apply Fin.ext; dsimp [j1, j2, shiftIdx, d]
    have := ab.2.isLt; have := r.isLt
    rw [show 6 * ab.1.val + r.val + 6 * (ab.2.val - ab.1.val) = 6 * ab.2.val + r.val by omega,
      Nat.mod_eq_of_lt (by omega)]
  have hd_lt : d < t := by have := ab.2.isLt; omega
  have h6neq : ∀ a b : ℕ, a < 6 * t → b < 6 * t → a ≠ b →
      shiftIdx t hpos j1 a ≠ shiftIdx t hpos j1 b := fun a b ha hb hne =>
    shiftIdx_ne_of_ne t hpos j1 ha hb hne
  have hp1_sh : prevIdx t hpos j1 = shiftIdx t hpos j1 (6 * t - 1) := rfl
  have hn1_sh : nextIdx t hpos j1 = shiftIdx t hpos j1 1 := rfl
  have hp2_sh : prevIdx t hpos j2 = shiftIdx t hpos j1 (6 * d - 1) := by
    rw [hj2_sh, prevIdx_shiftIdx_pos t hpos j1 (by omega)]
  have hn2_sh : nextIdx t hpos j2 = shiftIdx t hpos j1 (6 * d + 1) := by
    rw [hj2_sh, nextIdx_shiftIdx']
  have hne_0_p1 : prevIdx t hpos j1 ≠ j1 := by rw [hp1_sh]; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega)
  have hne_d_p1 : prevIdx t hpos j1 ≠ j2 := by rw [hp1_sh, hj2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_0_n1 : nextIdx t hpos j1 ≠ j1 := by rw [hn1_sh]; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega)
  have hne_d_n1 : nextIdx t hpos j1 ≠ j2 := by rw [hn1_sh, hj2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_0_p2 : prevIdx t hpos j2 ≠ j1 := by rw [hp2_sh]; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega)
  have hne_d_p2 : prevIdx t hpos j2 ≠ j2 := by rw [hp2_sh, hj2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_0_n2 : nextIdx t hpos j2 ≠ j1 := by rw [hn2_sh]; exact shiftIdx_ne_self_of_pos t hpos j1 (by omega) (by omega)
  have hne_d_n2 : nextIdx t hpos j2 ≠ j2 := by rw [hn2_sh, hj2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_p1_n1 : prevIdx t hpos j1 ≠ nextIdx t hpos j1 := by rw [hp1_sh, hn1_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_p1_p2 : prevIdx t hpos j1 ≠ prevIdx t hpos j2 := by rw [hp1_sh, hp2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_p1_n2 : prevIdx t hpos j1 ≠ nextIdx t hpos j2 := by rw [hp1_sh, hn2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_n1_p2 : nextIdx t hpos j1 ≠ prevIdx t hpos j2 := by rw [hn1_sh, hp2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_n1_n2 : nextIdx t hpos j1 ≠ nextIdx t hpos j2 := by rw [hn1_sh, hn2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  have hne_p2_n2 : prevIdx t hpos j2 ≠ nextIdx t hpos j2 := by rw [hp2_sh, hn2_sh]; exact h6neq _ _ (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mkFam3A, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
      mem_if_singleton]
    simp [j1, j2, hne_0_p1, hne_d_p1, hne_p1_n1, hne_p1_p2, hne_p1_n2]
  · simp only [mkFam3A, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
      mem_if_singleton]
    simp [j1, j2, hne_0_n1, hne_d_n1, hne_p1_n1.symm, hne_n1_p2, hne_n1_n2]
  · simp only [mkFam3A, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
      mem_if_singleton]
    simp [j1, j2, hne_0_p2, hne_d_p2, hne_p1_p2.symm, hne_n1_p2.symm, hne_p2_n2]
  · simp only [mkFam3A, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
      mem_if_singleton]
    simp [j1, j2, hne_0_n2, hne_d_n2, hne_p1_n2.symm, hne_n1_n2.symm, hne_p2_n2.symm]

lemma card_Fam3ASet (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) :
    (Fam3ASet t hpos).card = 96 * Nat.choose t 2 := by
  unfold Fam3ASet
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      card_pairsT, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_bool]
    ring
  · rintro ⟨⟨r1, ab1⟩, b11, b12, b13, b14⟩ h1 ⟨⟨r2, ab2⟩, b21, b22, b23, b24⟩ h2 heq
    dsimp only at heq
    have hab1 : ab1.1.val < ab1.2.val :=
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp h1).1).2).2
    have hab2 : ab2.1.val < ab2.2.val :=
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp h2).1).2).2
    have hp1 := mkFam3A_props t hpos ht r1 ab1 hab1 b11 b12 b13 b14
    have hp2 := mkFam3A_props t hpos ht r2 ab2 hab2 b21 b22 b23 b24
    have hpar : r1.val % 2 = r2.val % 2 := by
      by_contra hne
      have h1s := hp1.1; have h2s := hp2.2.1
      have h12 : 1 - r2.val % 2 = r1.val % 2 := by omega
      rw [h12, ← heq] at h2s; omega
    let j11 : Fin (6 * t) := ⟨6 * ab1.1.val + r1.val, by have := ab1.1.isLt; have := r1.isLt; omega⟩
    let j12 : Fin (6 * t) := ⟨6 * ab1.2.val + r1.val, by have := ab1.2.isLt; have := r1.isLt; omega⟩
    let j21 : Fin (6 * t) := ⟨6 * ab2.1.val + r2.val, by have := ab2.1.isLt; have := r2.isLt; omega⟩
    let j22 : Fin (6 * t) := ⟨6 * ab2.2.val + r2.val, by have := ab2.2.isLt; have := r2.isLt; omega⟩
    have hBeq : ({j11, j12} : Finset _) = {j21, j22} := by
      have e1 := mkFam3A_laneSub_p t hpos r1 ab1 b11 b12 b13 b14
      have e2 := mkFam3A_laneSub_p t hpos r2 ab2 b21 b22 b23 b24
      dsimp only at e1 e2
      rw [← e1, ← e2, heq, hpar]
    have hj_lt1 : j11.val < j12.val := by dsimp [j11, j12]; omega
    have hj_lt2 : j21.val < j22.val := by dsimp [j21, j22]; omega
    have hj_eq : j11 = j21 ∧ j12 = j22 := by
      have hm1 : j11 ∈ ({j21, j22} : Finset _) := by rw [← hBeq]; simp
      have hm2 : j12 ∈ ({j21, j22} : Finset _) := by rw [← hBeq]; simp
      have hn1 : j21 ∈ ({j11, j12} : Finset _) := by rw [hBeq]; simp
      have hn2 : j22 ∈ ({j11, j12} : Finset _) := by rw [hBeq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2 hn1 hn2
      rcases hm1 with h | h <;> rcases hm2 with h' | h'
      · exfalso; rw [h, h'] at hj_lt1; omega
      · exact ⟨h, h'⟩
      · exfalso; rw [h, h'] at hj_lt1; omega
      · exfalso; rw [h, h'] at hj_lt1; omega
    have hr_eq : r1 = r2 := by
      have hv := congrArg Fin.val hj_eq.1; dsimp [j11, j21] at hv
      have := r1.isLt; have := r2.isLt
      exact Fin.ext (by omega)
    have hab_eq : ab1 = ab2 := by
      have hv1 := congrArg Fin.val hj_eq.1; dsimp [j11, j21] at hv1
      have hv2 := congrArg Fin.val hj_eq.2; dsimp [j12, j22] at hv2
      have := r1.isLt; have := r2.isLt
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    subst hr_eq; subst hab_eq
    have hm1 := mkFam3A_mem_boundary t hpos ht r1 ab1 hab1 b11 b12 b13 b14
    have hm2 := mkFam3A_mem_boundary t hpos ht r1 ab1 hab1 b21 b22 b23 b24
    have hb1 : b11 = b21 :=
      bool_eq_of_iff (hm1.1.symm.trans (by rw [heq]; exact hm2.1))
    have hb2 : b12 = b22 :=
      bool_eq_of_iff (hm1.2.1.symm.trans (by rw [heq]; exact hm2.2.1))
    have hb3 : b13 = b23 :=
      bool_eq_of_iff (hm1.2.2.1.symm.trans (by rw [heq]; exact hm2.2.2.1))
    have hb4 : b14 = b24 :=
      bool_eq_of_iff (hm1.2.2.2.symm.trans (by rw [heq]; exact hm2.2.2.2))
    subst hb1; subst hb2; subst hb3; subst hb4; rfl

lemma classify_rB_one_M0 (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hBpos : 0 < (laneSub t S p).card) (hBlt : (laneSub t S p).card < 3 * t)
    (hrB1 : rB t hpos S p = 1) (hM0 : (mergedInt t hpos S p).card = 0)
    (hsupp : suppU t (GoodMax t hpos S) = S)
    (hsum : blocksB t hpos S p + (missFree t hpos S p).card ≤ 2) :
    S ∈ Fam3ASet t hpos := by
  have hMemp : mergedInt t hpos S p = ∅ := Finset.card_eq_zero.mp hM0
  have hsame : ∀ j1 ∈ laneSub t S p, ∀ j2 ∈ laneSub t S p, j1.val / 2 % 3 = j2.val / 2 % 3 := by
    intro j1 h1 j2 h2
    by_contra hne
    have hv1 := isoVec_mem_Vset t hpos ht S p hp h1 (by rw [hMemp]; simp) (by rw [hMemp]; simp)
    have hv2 := isoVec_mem_Vset t hpos ht S p hp h2 (by rw [hMemp]; simp) (by rw [hMemp]; simp)
    have hj1p := (Finset.mem_filter.mp h1).2
    have hj2p := (Finset.mem_filter.mp h2).2
    have h2r := rB_eq_two_of_diff_mod3 t hpos S p hp hj1p hj2p
      (v1 := ⟨_, hv1⟩) (v2 := ⟨_, hv2⟩)
      (projLane_Hmap_isoVec t hpos ht S p hp hj1p)
      (projLane_Hmap_isoVec t hpos ht S p hp hj2p) hne
    omega
  have hblocks_eq : blocksB t hpos S p = (laneSub t S p).card := by
    unfold blocksB
    congr 1
    rw [Finset.filter_eq_self]
    intro j hj hn2
    have hm := hsame j hj (next2 t hpos j) hn2
    rw [next2, shiftIdx_two_div2_mod3] at hm
    omega
  have hBne1 : (laneSub t S p).card ≠ 1 := by
    intro h1
    rcases Finset.card_eq_one.mp h1 with ⟨j0, hj0⟩
    have hj0B : j0 ∈ laneSub t S p := by rw [hj0]; simp
    have hj0S : j0 ∈ S := (Finset.mem_filter.mp hj0B).1
    have hj0p : j0.val % 2 = p := (Finset.mem_filter.mp hj0B).2
    have hmem_supp : j0 ∈ suppU t (GoodMax t hpos S) := by rw [hsupp]; exact hj0S
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_supp
    rcases hmem_supp with ⟨x, hxGM, hxj0⟩
    have hzero : projLane p (Hmap t x) = 0 := by
      ext k; change Hmap t x (laneBit p k) = 0
      exact congrFun hxGM.2 (laneBit p k)
    have hval : projLane p (Hmap t x) = x j0 • hLane t p j0 := by
      ext k
      change ∑ i : Fin (6 * t), hFn t i (laneBit p k) * x i = x j0 * hFn t j0 (laneBit p k)
      rw [Finset.sum_eq_single j0]
      · ring
      · intro i _ hij
        by_cases hiS : i ∈ S
        · by_cases hip : i.val % 2 = p
          · exfalso; apply hij
            have hiB : i ∈ laneSub t S p := Finset.mem_filter.mpr ⟨hiS, hip⟩
            rw [hj0] at hiB; exact Finset.mem_singleton.mp hiB
          · rw [hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hip), zero_mul]
        · rw [hxGM.1.1 i hiS, mul_zero]
      · intro h; exact False.elim (h (Finset.mem_univ j0))
    rw [hval, (zmod2_ne_zero_iff _).mp hxj0, one_smul] at hzero
    exact hLane_ne_zero t p hp j0 hj0p hzero
  have hB2 : (laneSub t S p).card = 2 := by omega
  have hq0 : (missFree t hpos S p).card = 0 := by omega
  have hmiss_emp : missFree t hpos S p = ∅ := Finset.card_eq_zero.mp hq0
  rcases Finset.card_eq_two.mp hB2 with ⟨u1, u2, hne_u, hBu⟩
  let j1 := if u1.val < u2.val then u1 else u2
  let j2 := if u1.val < u2.val then u2 else u1
  have hBeq : laneSub t S p = {j1, j2} := by
    dsimp only [j1, j2]; split_ifs
    · exact hBu
    · rw [hBu, Finset.pair_comm]
  have hj1_lt : j1.val < j2.val := by
    have hne_v : u1.val ≠ u2.val := fun h => hne_u (Fin.ext h)
    dsimp only [j1, j2]; split_ifs <;> omega
  have hj1B : j1 ∈ laneSub t S p := by rw [hBeq]; simp
  have hj2B : j2 ∈ laneSub t S p := by rw [hBeq]; simp
  have hj1p : j1.val % 2 = p := (Finset.mem_filter.mp hj1B).2
  have hj2p : j2.val % 2 = p := (Finset.mem_filter.mp hj2B).2
  have hj12m : j1.val / 2 % 3 = j2.val / 2 % 3 := hsame j1 hj1B j2 hj2B
  have hmod6 : j1.val % 6 = j2.val % 6 := by omega
  let r : Fin 6 := ⟨j1.val % 6, Nat.mod_lt _ (by omega)⟩
  let a : Fin t := ⟨j1.val / 6, by have := j1.isLt; omega⟩
  let b : Fin t := ⟨j2.val / 6, by have := j2.isLt; omega⟩
  have hab : a.val < b.val := by dsimp [a, b]; omega
  have hj1_repr : (⟨6 * a.val + r.val, by have := a.isLt; have := r.isLt; omega⟩ : Fin (6 * t)) = j1 :=
    Fin.ext (by dsimp [a, r]; omega)
  have hj2_repr : (⟨6 * b.val + r.val, by have := b.isLt; have := r.isLt; omega⟩ : Fin (6 * t)) = j2 :=
    Fin.ext (by dsimp [b, r]; omega)
  have hrp : r.val % 2 = p := by dsimp [r]; omega
  let b1 := decide (prevIdx t hpos j1 ∈ S)
  let b2 := decide (nextIdx t hpos j1 ∈ S)
  let b3 := decide (prevIdx t hpos j2 ∈ S)
  let b4 := decide (nextIdx t hpos j2 ∈ S)
  have hSeq : S = mkFam3A t hpos r (a, b) b1 b2 b3 b4 := by
    have hmb := mkFam3A_mem_boundary t hpos ht r (a, b) hab b1 b2 b3 b4
    dsimp only at hmb
    rw [hj1_repr, hj2_repr] at hmb
    ext x
    by_cases hxp : x.val % 2 = p
    · have h1 : x ∈ S ↔ x ∈ laneSub t S p := by simp [laneSub, hxp]
      have h2 : x ∈ mkFam3A t hpos r (a, b) b1 b2 b3 b4 ↔
          x ∈ laneSub t (mkFam3A t hpos r (a, b) b1 b2 b3 b4) p := by simp [laneSub, hxp]
      rw [h1, h2, hBeq, ← hrp, mkFam3A_laneSub_p, hj1_repr, hj2_repr]
    · have hxp1 : x.val % 2 = 1 - p := by omega
      by_cases hx1 : x = prevIdx t hpos j1
      · subst hx1; rw [hmb.1]; simp [b1]
      · by_cases hx2 : x = nextIdx t hpos j1
        · subst hx2; rw [hmb.2.1]; simp [b2]
        · by_cases hx3 : x = prevIdx t hpos j2
          · subst hx3; rw [hmb.2.2.1]; simp [b3]
          · by_cases hx4 : x = nextIdx t hpos j2
            · subst hx4; rw [hmb.2.2.2]; simp [b4]
            · have hx_rhs : x ∈ mkFam3A t hpos r (a, b) b1 b2 b3 b4 := by
                refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))))
                rw [hj1_repr, hj2_repr]
                exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hrp]; exact hxp1⟩,
                  hx1, hx2, hx3, hx4⟩
              have hx_S : x ∈ S := by
                by_contra hxnot
                have hmf : x ∈ missFree t hpos S p := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
                    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp1⟩,
                     fun h => hxnot (Finset.mem_filter.mp h).1⟩, ?_, ?_⟩
                  · rw [hBeq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨fun h => hx2 (by have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx] at this),
                      fun h => hx4 (by have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx] at this)⟩
                  · rw [hBeq]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨fun h => hx1 (by have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at this),
                      fun h => hx3 (by have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at this)⟩
                rw [hmiss_emp] at hmf; exact Finset.notMem_empty _ hmf
              simp [hx_S, hx_rhs]
  rw [hSeq]
  exact Finset.mem_image.mpr ⟨((r, (a, b)), (b1, b2, b3, b4)),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩, Finset.mem_univ _⟩, rfl⟩


-- ============================================================================
-- L-lib-898 Section B4: Family 3B (rB = 1, M_int = 1, c = a - 2, count = 12 * n)
-- ============================================================================

lemma fin3_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  fin_cases k <;> simp

lemma prevIdx_prev2_eq_shift (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) (m : Fin (6 * t)) :
    prevIdx t hpos (prev2 t hpos m) = shiftIdx t hpos m (6 * t - 3) := by
  apply nextIdx_inj t hpos
  rw [nextIdx_prevIdx, prev2_eq_shift, nextIdx_shiftIdx']
  congr 1; omega

lemma nextIdx_next2_eq_shift (t : ℕ) (hpos : 0 < t) (m : Fin (6 * t)) :
    nextIdx t hpos (next2 t hpos m) = shiftIdx t hpos m 3 := by
  rw [next2, nextIdx_shiftIdx']

lemma prev2_prev2_eq_shift (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) (m : Fin (6 * t)) :
    prev2 t hpos (prev2 t hpos m) = shiftIdx t hpos m (6 * t - 4) := by
  apply next2_inj t hpos
  rw [next2_prev2, prev2_eq_shift, next2, shiftIdx_add]
  congr 1; omega

lemma next2_next2_eq_shift (t : ℕ) (hpos : 0 < t) (m : Fin (6 * t)) :
    next2 t hpos (next2 t hpos m) = shiftIdx t hpos m 4 := by
  rw [next2, next2, shiftIdx_add]

def mkFam3B_B (t : ℕ) (hpos : 0 < t) (m : Fin (6 * t)) (kind : Fin 3) : Finset (Fin (6 * t)) :=
  if kind = 0 then {shiftIdx t hpos m (6 * t - 3), shiftIdx t hpos m (6 * t - 1), shiftIdx t hpos m 1}
  else if kind = 1 then {shiftIdx t hpos m (6 * t - 1), shiftIdx t hpos m 1, shiftIdx t hpos m 3}
  else {shiftIdx t hpos m (6 * t - 3), shiftIdx t hpos m (6 * t - 1), shiftIdx t hpos m 1, shiftIdx t hpos m 3}

def mkFam3B_left (t : ℕ) (hpos : 0 < t) (m : Fin (6 * t)) (kind : Fin 3) : Fin (6 * t) :=
  if kind = 1 then shiftIdx t hpos m (6 * t - 2) else shiftIdx t hpos m (6 * t - 4)

def mkFam3B_right (t : ℕ) (hpos : 0 < t) (m : Fin (6 * t)) (kind : Fin 3) : Fin (6 * t) :=
  if kind = 0 then shiftIdx t hpos m 2 else shiftIdx t hpos m 4

def mkFam3B (t : ℕ) (hpos : 0 < t) (m : Fin (6 * t)) (kind : Fin 3)
    (bL bR : Bool) : Finset (Fin (6 * t)) :=
  let p := 1 - m.val % 2
  let B := mkFam3B_B t hpos m kind
  let Afree := (laneSet t (1 - p)).filter (fun i =>
    prevIdx t hpos i ∉ B ∧ nextIdx t hpos i ∉ B)
  let AL : Finset (Fin (6 * t)) := if bL then {mkFam3B_left t hpos m kind} else ∅
  let AR : Finset (Fin (6 * t)) := if bR then {mkFam3B_right t hpos m kind} else ∅
  B ∪ Afree ∪ {m} ∪ AL ∪ AR

def Fam3BSet (t : ℕ) (hpos : 0 < t) : Finset (Finset (Fin (6 * t))) :=
  (Finset.univ : Finset (Fin (6 * t) × Fin 3 × Bool × Bool)).image
    (fun x => mkFam3B t hpos x.1 x.2.1 x.2.2.1 x.2.2.2)

lemma mkFam3B_laneSub_p (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (m : Fin (6 * t)) (kind : Fin 3) (bL bR : Bool) :
    laneSub t (mkFam3B t hpos m kind bL bR) (1 - m.val % 2) = mkFam3B_B t hpos m kind := by
  let p := 1 - m.val % 2
  have hp : p = 0 ∨ p = 1 := by omega
  have h1p : 1 - p = m.val % 2 := by omega
  have hBp : ∀ x ∈ mkFam3B_B t hpos m kind, x.val % 2 = p := by
    intro x hx
    unfold mkFam3B_B at hx
    rcases fin3_cases kind with rfl | rfl | rfl <;>
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] at hx
    · rcases hx with rfl | rfl | rfl <;> rw [shiftIdx_mod2] <;> omega
    · rcases hx with rfl | rfl | rfl <;> rw [shiftIdx_mod2] <;> omega
    · rcases hx with rfl | rfl | rfl | rfl <;> rw [shiftIdx_mod2] <;> omega
  have hLp : (mkFam3B_left t hpos m kind).val % 2 = 1 - p := by
    unfold mkFam3B_left; split_ifs <;> rw [shiftIdx_mod2] <;> omega
  have hRp : (mkFam3B_right t hpos m kind).val % 2 = 1 - p := by
    unfold mkFam3B_right; split_ifs <;> rw [shiftIdx_mod2] <;> omega
  ext x
  simp only [laneSub, mkFam3B, laneSet, Finset.mem_filter, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨(((hB | ⟨hxp, _⟩) | rfl) | hL) | hR, hxp'⟩
    · exact hB
    · omega
    · omega
    · cases bL <;> simp at hL; rw [hL] at hxp'; omega
    · cases bR <;> simp at hR; rw [hR] at hxp'; omega
  · intro hxB
    exact ⟨Or.inl (Or.inl (Or.inl (Or.inl hxB))), hBp x hxB⟩

lemma mkFam3B_basic (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (m : Fin (6 * t)) (kind : Fin 3) (bL bR : Bool) :
    let S := mkFam3B t hpos m kind bL bR
    let p := 1 - m.val % 2
    sitesS t S p = (if kind = 2 then 4 else 3) ∧
    4 < sitesS t S (1 - p) ∧
    mergedInt t hpos S p = {m} ∧
    runsS t hpos S = 3 * t - 2 ∧
    Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 ∧
    (∀ i ∈ freeOpp t hpos S p, ∃ x ∈ GoodMax t hpos S, x i ≠ 0) ∧
    shiftIdx t hpos m 6 ∈ freeOpp t hpos S p ∧
    shiftIdx t hpos m 8 ∈ freeOpp t hpos S p := by
  intro S p
  have hp : p = 0 ∨ p = 1 := by omega
  have h1p : 1 - p = m.val % 2 := by omega
  have hBp : laneSub t S p = mkFam3B_B t hpos m kind :=
    mkFam3B_laneSub_p t hpos ht m kind bL bR
  let B := mkFam3B_B t hpos m kind
  have hsh_ne : ∀ a b : ℕ, a < 6 * t → b < 6 * t → a ≠ b →
      shiftIdx t hpos m a ≠ shiftIdx t hpos m b := fun a b ha hb hne =>
    shiftIdx_ne_of_ne t hpos m ha hb hne
  have hcardB : sitesS t S p = if kind = 2 then 4 else 3 := by
    rw [← laneSub_card_eq_sites, hBp]
    unfold mkFam3B_B
    rcases fin3_cases kind with rfl | rfl | rfl
    · simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact hsh_ne _ _ (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
    · simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact hsh_ne _ _ (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
    · simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
      · exact hsh_ne _ _ (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega),
          hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
  -- B is a subset of {m-3, m-1, m+1, m+3}
  have hB_sub4 : ∀ x ∈ B, x = shiftIdx t hpos m (6 * t - 3) ∨ x = shiftIdx t hpos m (6 * t - 1) ∨
      x = shiftIdx t hpos m 1 ∨ x = shiftIdx t hpos m 3 := by
    intro x hx; dsimp only [B, mkFam3B_B] at hx
    rcases fin3_cases kind with rfl | rfl | rfl <;>
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] at hx <;> tauto
  have hfree_even : ∀ d : ℕ, d % 2 = 0 → 6 ≤ d → d ≤ 14 → shiftIdx t hpos m d ∈ freeOpp t hpos S p := by
    intro d hd_ev hd6 hd14
    have hpreB : prevIdx t hpos (shiftIdx t hpos m d) ∉ B := by
      rw [prevIdx_shiftIdx_pos t hpos m (by omega)]
      intro hmem
      rcases hB_sub4 _ hmem with h | h | h | h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
    have hnxtB : nextIdx t hpos (shiftIdx t hpos m d) ∉ B := by
      rw [nextIdx_shiftIdx']
      intro hmem
      rcases hB_sub4 _ hmem with h | h | h | h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
    have hmem_Afree : shiftIdx t hpos m d ∈ (laneSet t (1 - p)).filter (fun i =>
        prevIdx t hpos i ∉ B ∧ nextIdx t hpos i ∉ B) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [shiftIdx_mod2]; omega⟩, hpreB, hnxtB⟩
    have hmem_S : shiftIdx t hpos m d ∈ S :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem_Afree)))
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem_S, by rw [shiftIdx_mod2]; omega⟩, ?_, ?_⟩
    · rw [hBp]; exact hpreB
    · rw [hBp]; exact hnxtB
  have hcardA_gt : 4 < sitesS t S (1 - p) := by
    let Q5 : Finset (Fin (6 * t)) :=
      {shiftIdx t hpos m 6, shiftIdx t hpos m 8, shiftIdx t hpos m 10, shiftIdx t hpos m 12, shiftIdx t hpos m 14}
    have hsub : Q5 ⊆ laneSub t S (1 - p) := by
      intro x hx
      simp only [Q5, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact (Finset.mem_filter.mp (hfree_even 6 rfl (by omega) (by omega))).1
      · exact (Finset.mem_filter.mp (hfree_even 8 rfl (by omega) (by omega))).1
      · exact (Finset.mem_filter.mp (hfree_even 10 rfl (by omega) (by omega))).1
      · exact (Finset.mem_filter.mp (hfree_even 12 rfl (by omega) (by omega))).1
      · exact (Finset.mem_filter.mp (hfree_even 14 rfl (by omega) (by omega))).1
    have hQ5 : Q5.card = 5 := by
      dsimp only [Q5]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair]
      · exact hsh_ne 12 14 (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne 10 12 (by omega) (by omega) (by omega), hsh_ne 10 14 (by omega) (by omega) (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne 8 10 (by omega) (by omega) (by omega), hsh_ne 8 12 (by omega) (by omega) (by omega),
          hsh_ne 8 14 (by omega) (by omega) (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne 6 8 (by omega) (by omega) (by omega), hsh_ne 6 10 (by omega) (by omega) (by omega),
          hsh_ne 6 12 (by omega) (by omega) (by omega), hsh_ne 6 14 (by omega) (by omega) (by omega)⟩
    have hle := Finset.card_le_card hsub
    rw [hQ5, laneSub_card_eq_sites] at hle
    omega
  -- Check blocksB = 1, missFree = ∅, mergedInt = {m}
  have hblocks : blocksB t hpos S p = 1 := by
    unfold blocksB
    rw [hBp]
    have hnext2_sh : ∀ d : ℕ, next2 t hpos (shiftIdx t hpos m d) = shiftIdx t hpos m (d + 2) := by
      intro d; rw [next2, shiftIdx_add]
    have hmod_wrap : shiftIdx t hpos m (6 * t - 3 + 2) = shiftIdx t hpos m (6 * t - 1) := by
      congr 1; omega
    have hmod_wrap1 : shiftIdx t hpos m (6 * t - 1 + 2) = shiftIdx t hpos m 1 := by
      apply Fin.ext; dsimp [shiftIdx]
      rw [show m.val + (6 * t - 1 + 2) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]
    rcases fin3_cases kind with rfl | rfl | rfl
    · have hfilt : (mkFam3B_B t hpos m 0).filter (fun x => next2 t hpos x ∉ mkFam3B_B t hpos m 0) =
          {shiftIdx t hpos m 1} := by
        ext x; unfold mkFam3B_B
        simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hnot⟩
          · exfalso; apply hnot; rw [hnext2_sh, hmod_wrap]; simp
          · exfalso; apply hnot; rw [hnext2_sh, hmod_wrap1]; simp
          · rfl
        · rintro rfl; refine ⟨Or.inr (Or.inr rfl), ?_⟩
          rw [hnext2_sh]; rintro (h | h | h) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      rw [hfilt, Finset.card_singleton]
    · have hfilt : (mkFam3B_B t hpos m 1).filter (fun x => next2 t hpos x ∉ mkFam3B_B t hpos m 1) =
          {shiftIdx t hpos m 3} := by
        ext x; unfold mkFam3B_B
        simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl, hnot⟩
          · exfalso; apply hnot; rw [hnext2_sh, hmod_wrap1]; simp
          · exfalso; apply hnot; rw [hnext2_sh]; simp
          · rfl
        · rintro rfl; refine ⟨Or.inr (Or.inr rfl), ?_⟩
          rw [hnext2_sh]; rintro (h | h | h) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      rw [hfilt, Finset.card_singleton]
    · have hfilt : (mkFam3B_B t hpos m 2).filter (fun x => next2 t hpos x ∉ mkFam3B_B t hpos m 2) =
          {shiftIdx t hpos m 3} := by
        ext x; unfold mkFam3B_B
        simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl | rfl | rfl, hnot⟩
          · exfalso; apply hnot; rw [hnext2_sh, hmod_wrap]; simp
          · exfalso; apply hnot; rw [hnext2_sh, hmod_wrap1]; simp
          · exfalso; apply hnot; rw [hnext2_sh]; simp
          · rfl
        · rintro rfl; refine ⟨Or.inr (Or.inr (Or.inr rfl)), ?_⟩
          rw [hnext2_sh]; rintro (h | h | h | h) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      rw [hfilt, Finset.card_singleton]
  have hmiss : missFree t hpos S p = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hsd, hpre, hnxt⟩
    rcases Finset.mem_sdiff.mp hsd with ⟨hiL, hiA⟩
    rw [hBp] at hpre hnxt
    apply hiA
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hiL).2⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiL, hpre, hnxt⟩))))
  have hm_in_S : m ∈ S :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self m)))
  have hm_m1_B : prevIdx t hpos m ∈ B := by
    rw [prevIdx_eq_shift]; dsimp only [B, mkFam3B_B]
    rcases fin3_cases kind with rfl | rfl | rfl <;> simp
  have hm_p1_B : nextIdx t hpos m ∈ B := by
    rw [← shiftIdx_one]; dsimp only [B, mkFam3B_B]
    rcases fin3_cases kind with rfl | rfl | rfl <;> simp
  have hmerged : mergedInt t hpos S p = {m} := by
    ext i
    simp only [mergedInt, hBp, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hiA, hpre, hnxt⟩
      have hiS : i ∈ S := (Finset.mem_filter.mp hiA).1
      have hi_not_Afree : i ∉ (laneSet t (1 - p)).filter (fun x => prevIdx t hpos x ∉ B ∧ nextIdx t hpos x ∉ B) := by
        intro h; exact (Finset.mem_filter.mp h).2.1 hpre
      have hi_not_B : i ∉ B := by
        intro hB
        have hip := (Finset.mem_filter.mp hiA).2
        have hBp_i : i.val % 2 = p := by
          have : i ∈ laneSub t S p := by rw [hBp]; exact hB
          exact (Finset.mem_filter.mp this).2
        omega
      -- i must be m or mkFam3B_left or mkFam3B_right
      have hi_cases : i = m ∨ i = mkFam3B_left t hpos m kind ∨ i = mkFam3B_right t hpos m kind := by
        simp only [S, mkFam3B, Finset.mem_union, Finset.mem_singleton] at hiS
        rcases hiS with (((hB | hAf) | rfl) | hL) | hR
        · exact False.elim (hi_not_B hB)
        · exact False.elim (hi_not_Afree hAf)
        · exact Or.inl rfl
        · cases bL <;> simp at hL; exact Or.inr (Or.inl hL)
        · cases bR <;> simp at hR; exact Or.inr (Or.inr hR)
      rcases hi_cases with rfl | rfl | rfl
      · rfl
      · exfalso
        dsimp only [mkFam3B_left] at hpre
        rcases fin3_cases kind with rfl | rfl | rfl
        · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at hpre
          rw [prevIdx_shiftIdx_pos t hpos m (by omega)] at hpre
          rcases hB_sub4 _ hpre with h | h | h | h <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · simp only [Fin.isValue, ↓reduceIte] at hpre
          rw [prevIdx_shiftIdx_pos t hpos m (by omega)] at hpre
          dsimp only [B, mkFam3B_B] at hpre
          simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hpre
          rcases hpre with h | h | h <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at hpre
          rw [prevIdx_shiftIdx_pos t hpos m (by omega)] at hpre
          rcases hB_sub4 _ hpre with h | h | h | h <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · exfalso
        dsimp only [mkFam3B_right] at hnxt
        rcases fin3_cases kind with rfl | rfl | rfl
        · simp only [Fin.isValue, ↓reduceIte] at hnxt
          rw [nextIdx_shiftIdx'] at hnxt
          dsimp only [B, mkFam3B_B] at hnxt
          simp only [Fin.isValue, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hnxt
          rcases hnxt with h | h | h <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at hnxt
          rw [nextIdx_shiftIdx'] at hnxt
          rcases hB_sub4 _ hnxt with h | h | h | h <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at hnxt
          rw [nextIdx_shiftIdx'] at hnxt
          rcases hB_sub4 _ hnxt with h | h | h | h <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
    · rintro rfl
      exact ⟨Finset.mem_filter.mpr ⟨hm_in_S, by omega⟩, hm_m1_B, hm_p1_B⟩
  have hruns : runsS t hpos S = 3 * t - 2 := by
    have hid := runsS_identity t hpos S p hp
    rw [hblocks, hmiss, Finset.card_empty, hmerged, Finset.card_singleton] at hid
    omega
  -- Two disjoint spanning pairs in freeOpp: (m+6, m+8) and (m+10, m+12)
  have hu1 : shiftIdx t hpos m 6 ∈ freeOpp t hpos S p := hfree_even 6 rfl (by omega) (by omega)
  have hu2 : shiftIdx t hpos m 8 ∈ freeOpp t hpos S p := hfree_even 8 rfl (by omega) (by omega)
  have hw1 : shiftIdx t hpos m 10 ∈ freeOpp t hpos S p := hfree_even 10 rfl (by omega) (by omega)
  have hw2 : shiftIdx t hpos m 12 ∈ freeOpp t hpos S p := hfree_even 12 rfl (by omega) (by omega)
  have htwo := supp_freeOpp_of_two_pairs t hpos S p hp hu1 hu2 hw1 hw2
    (shiftIdx_two_ne_mod3 t hpos m 6) (shiftIdx_two_ne_mod3 t hpos m 10)
    (hsh_ne 6 10 (by omega) (by omega) (by omega))
    (hsh_ne 6 12 (by omega) (by omega) (by omega))
    (hsh_ne 8 10 (by omega) (by omega) (by omega))
    (hsh_ne 8 12 (by omega) (by omega) (by omega))
  -- Compute rB = 1
  have hm3_eq_h : hLane t p (shiftIdx t hpos m (6 * t - 3)) = hLane t p (shiftIdx t hpos m 3) := by
    rw [← prevIdx_prev2_eq_shift t hpos ht m, ← nextIdx_next2_eq_shift t hpos m]
    exact hLane_prev3_eq_next3 t hpos p hp m (by omega)
  have hpair_eq_h : hLane t p (shiftIdx t hpos m (6 * t - 1)) + hLane t p (shiftIdx t hpos m 1) =
      hLane t p (shiftIdx t hpos m 3) := by
    rw [← prevIdx_eq_shift, shiftIdx_one, hLane_prev_next_eq_prev3,
      prevIdx_prev2_eq_shift t hpos ht m, hm3_eq_h]
  have hrB_span : ∀ x ∈ Vset t hpos S,
      projLane p (Hmap t x) ∈ Submodule.span F2 ({hLane t p (shiftIdx t hpos m 3)} : Set (Fin 2 → F2)) := by
    intro x hx
    have hxm1 : x (shiftIdx t hpos m (6 * t - 1)) = x m := by
      have := hx.2 (prevIdx t hpos m) (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hm_m1_B)))) (by rw [nextIdx_prevIdx]; exact hm_in_S)
      rwa [nextIdx_prevIdx, prevIdx_eq_shift] at this
    have hxp1 : x (shiftIdx t hpos m 1) = x m := by
      have := hx.2 m hm_in_S (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hm_p1_B))))
      rw [← shiftIdx_one] at this; exact this.symm
    have hproj_sub : ∀ (c : F2),
        (∀ k : Fin 2, ∑ i ∈ B, hFn t i (laneBit p k) * x i = c * hFn t (shiftIdx t hpos m 3) (laneBit p k)) →
        projLane p (Hmap t x) ∈ Submodule.span F2 ({hLane t p (shiftIdx t hpos m 3)} : Set (Fin 2 → F2)) := by
      intro c hc
      have hproj : projLane p (Hmap t x) = c • hLane t p (shiftIdx t hpos m 3) := by
        ext k
        change ∑ i : Fin (6 * t), hFn t i (laneBit p k) * x i = c * hFn t (shiftIdx t hpos m 3) (laneBit p k)
        rw [← Finset.sum_subset (Finset.subset_univ B)]
        · exact hc k
        · intro i _ hiB
          by_cases hiS : i ∈ S
          · by_cases hip : i.val % 2 = p
            · exfalso; apply hiB; dsimp only [B]; rw [← hBp]; exact Finset.mem_filter.mpr ⟨hiS, hip⟩
            · rw [hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hip), zero_mul]
          · rw [hx.1 i hiS, mul_zero]
      rw [hproj]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
    rcases fin3_cases kind with rfl | rfl | rfl
    · refine hproj_sub (x (shiftIdx t hpos m (6 * t - 3)) + x m) (fun k => ?_)
      have hk_m3 := congrFun hm3_eq_h k
      have hk_pair := congrFun hpair_eq_h k
      simp only [hLane, Pi.add_apply] at hk_m3 hk_pair
      dsimp only [B, mkFam3B_B]
      simp only [Fin.isValue, ↓reduceIte]
      rw [Finset.sum_insert, Finset.sum_pair, hxm1, hxp1, hk_m3]
      · calc hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m (6 * t - 3)) +
              (hFn t (shiftIdx t hpos m (6 * t - 1)) (laneBit p k) * x m +
               hFn t (shiftIdx t hpos m 1) (laneBit p k) * x m)
            = hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m (6 * t - 3)) +
              (hFn t (shiftIdx t hpos m (6 * t - 1)) (laneBit p k) +
               hFn t (shiftIdx t hpos m 1) (laneBit p k)) * x m := by ring
          _ = (x (shiftIdx t hpos m (6 * t - 3)) + x m) * hFn t (shiftIdx t hpos m 3) (laneBit p k) := by
              rw [hk_pair]; ring
      · exact hsh_ne _ _ (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
    · refine hproj_sub (x m + x (shiftIdx t hpos m 3)) (fun k => ?_)
      have hk_pair := congrFun hpair_eq_h k
      simp only [hLane, Pi.add_apply] at hk_pair
      dsimp only [B, mkFam3B_B]
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [Finset.sum_insert, Finset.sum_pair, hxm1, hxp1]
      · calc hFn t (shiftIdx t hpos m (6 * t - 1)) (laneBit p k) * x m +
              (hFn t (shiftIdx t hpos m 1) (laneBit p k) * x m +
               hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m 3))
            = (hFn t (shiftIdx t hpos m (6 * t - 1)) (laneBit p k) +
               hFn t (shiftIdx t hpos m 1) (laneBit p k)) * x m +
              hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m 3) := by ring
          _ = (x m + x (shiftIdx t hpos m 3)) * hFn t (shiftIdx t hpos m 3) (laneBit p k) := by
              rw [hk_pair]; ring
      · exact hsh_ne _ _ (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
    · refine hproj_sub (x (shiftIdx t hpos m (6 * t - 3)) + x m + x (shiftIdx t hpos m 3)) (fun k => ?_)
      have hk_m3 := congrFun hm3_eq_h k
      have hk_pair := congrFun hpair_eq_h k
      simp only [hLane, Pi.add_apply] at hk_m3 hk_pair
      dsimp only [B, mkFam3B_B]
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_pair, hxm1, hxp1, hk_m3]
      · calc hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m (6 * t - 3)) +
              (hFn t (shiftIdx t hpos m (6 * t - 1)) (laneBit p k) * x m +
               (hFn t (shiftIdx t hpos m 1) (laneBit p k) * x m +
                hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m 3)))
            = hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m (6 * t - 3)) +
              (hFn t (shiftIdx t hpos m (6 * t - 1)) (laneBit p k) +
               hFn t (shiftIdx t hpos m 1) (laneBit p k)) * x m +
              hFn t (shiftIdx t hpos m 3) (laneBit p k) * x (shiftIdx t hpos m 3) := by ring
          _ = (x (shiftIdx t hpos m (6 * t - 3)) + x m + x (shiftIdx t hpos m 3)) *
              hFn t (shiftIdx t hpos m 3) (laneBit p k) := by
              rw [hk_pair]; ring
      · exact hsh_ne _ _ (by omega) (by omega) (by omega)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega),
          hsh_ne _ _ (by omega) (by omega) (by omega)⟩
  have hpairV : pairVec t hpos S m ∈ Vset t hpos S := by
    refine pairVec_mem_Vset t hpos ht S p hp (by rw [hmerged]; simp) ?_ ?_
    · rw [hmerged, Finset.mem_singleton, prev2_eq_shift]
      exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
    · rw [hmerged, Finset.mem_singleton, next2]
      exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
  have hrB1 : rB t hpos S p = 1 := by
    have hle1 : rB t hpos S p ≤ 1 := by
      have hsub : LinearMap.range ((projLane p).comp (HV t hpos S)) ≤
          Submodule.span F2 ({hLane t p (shiftIdx t hpos m 3)} : Set (Fin 2 → F2)) := by
        rintro y ⟨⟨x, hx⟩, rfl⟩; exact hrB_span x hx
      calc rB t hpos S p ≤ Module.finrank F2 (Submodule.span F2 ({hLane t p (shiftIdx t hpos m 3)} : Set (Fin 2 → F2))) :=
            Submodule.finrank_mono hsub
        _ ≤ 1 := finrank_span_sing_le_one _
    have hge1 : 1 ≤ rB t hpos S p := by
      by_contra h0
      unfold rB at h0
      have hbot : LinearMap.range ((projLane p).comp (HV t hpos S)) = ⊥ :=
        Submodule.finrank_eq_zero.mp (by omega)
      have hmem : projLane p (Hmap t (pairVec t hpos S m)) ∈
          LinearMap.range ((projLane p).comp (HV t hpos S)) := ⟨⟨_, hpairV⟩, rfl⟩
      rw [hbot, Submodule.mem_bot, projLane_Hmap_pairVec t hpos ht S p hp (by omega),
        prevIdx_eq_shift, ← shiftIdx_one, hpair_eq_h] at hmem
      exact hLane_ne_zero t p hp _ (by rw [shiftIdx_mod2]; omega) hmem
    omega
  have hfr : Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
    have h1 := finrank_GoodMax_add_rankHV t hpos S (by omega)
    have h2 := rFree_add_rB_le_rankHV t hpos S p hp
    have h3 := rankHV_le_rB_add_two t hpos S p hp
    rw [htwo.1, hrB1] at h2
    rw [hrB1] at h3
    rw [hruns] at h1
    omega
  exact ⟨hcardB, hcardA_gt, hmerged, hruns, hfr, htwo.2, hu1, hu2⟩

lemma mkFam3B_supp (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (m : Fin (6 * t)) (kind : Fin 3) (bL bR : Bool) :
    suppU t (GoodMax t hpos (mkFam3B t hpos m kind bL bR)) = mkFam3B t hpos m kind bL bR := by
  let S := mkFam3B t hpos m kind bL bR
  let p := 1 - m.val % 2
  have hp : p = 0 ∨ p = 1 := by omega
  let B := mkFam3B_B t hpos m kind
  have hBp : laneSub t S p = B := mkFam3B_laneSub_p t hpos ht m kind bL bR
  have hbas := mkFam3B_basic t hpos ht m kind bL bR
  have hmerged : mergedInt t hpos S p = {m} := hbas.2.2.1
  have hfree_supp : ∀ i ∈ freeOpp t hpos S p, ∃ x ∈ GoodMax t hpos S, x i ≠ 0 := hbas.2.2.2.2.2.1
  have hu1 : shiftIdx t hpos m 6 ∈ freeOpp t hpos S p := hbas.2.2.2.2.2.2.1
  have hu2 : shiftIdx t hpos m 8 ∈ freeOpp t hpos S p := hbas.2.2.2.2.2.2.2
  have hsh_ne : ∀ a b : ℕ, a < 6 * t → b < 6 * t → a ≠ b →
      shiftIdx t hpos m a ≠ shiftIdx t hpos m b := fun a b ha hb hne =>
    shiftIdx_ne_of_ne t hpos m ha hb hne
  have hm3_eq_h : hLane t p (shiftIdx t hpos m (6 * t - 3)) = hLane t p (shiftIdx t hpos m 3) := by
    rw [← prevIdx_prev2_eq_shift t hpos ht m, ← nextIdx_next2_eq_shift t hpos m]
    exact hLane_prev3_eq_next3 t hpos p hp m (by omega)
  have hpair_eq_h : hLane t p (shiftIdx t hpos m (6 * t - 1)) + hLane t p (shiftIdx t hpos m 1) =
      hLane t p (shiftIdx t hpos m 3) := by
    rw [← prevIdx_eq_shift, shiftIdx_one, hLane_prev_next_eq_prev3,
      prevIdx_prev2_eq_shift t hpos ht m, hm3_eq_h]
  have hpairV : pairVec t hpos S m ∈ Vset t hpos S := by
    refine pairVec_mem_Vset t hpos ht S p hp (by rw [hmerged]; simp) ?_ ?_
    · rw [hmerged, Finset.mem_singleton, prev2_eq_shift]
      exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
    · rw [hmerged, Finset.mem_singleton, next2]
      exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
  have hm_m1_B : prevIdx t hpos m ∈ B := by
    rw [prevIdx_eq_shift]; dsimp only [B, mkFam3B_B]
    rcases fin3_cases kind with rfl | rfl | rfl <;> simp
  have hm_p1_B : nextIdx t hpos m ∈ B := by
    rw [← shiftIdx_one]; dsimp only [B, mkFam3B_B]
    rcases fin3_cases kind with rfl | rfl | rfl <;> simp
  apply Finset.Subset.antisymm (suppU_GoodMax_subset t hpos S)
  intro i hiS
  simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hif : i ∈ freeOpp t hpos S p
  · exact hfree_supp i hif
  · have hiu1 : i ≠ shiftIdx t hpos m 6 := fun h => hif (h ▸ hu1)
    have hiu2 : i ≠ shiftIdx t hpos m 8 := fun h => hif (h ▸ hu2)
    have hcov : ∀ (j0 : Fin (6 * t)), j0 ∈ B →
        (j0 = shiftIdx t hpos m (6 * t - 3) ∨ j0 = shiftIdx t hpos m 3) →
        (pairVec t hpos S m + isoVec t hpos S j0) i = 1 →
        ∃ x ∈ GoodMax t hpos S, x i ≠ 0 := by
      intro j0 hj0B hj0eq hval
      have hj0_sub : j0 ∈ laneSub t S p := by rw [hBp]; exact hj0B
      have hj0_pre : prevIdx t hpos j0 ∉ mergedInt t hpos S p := by
        rw [hmerged, Finset.mem_singleton]
        rcases hj0eq with rfl | rfl <;> rw [prevIdx_shiftIdx_pos t hpos m (by omega)] <;>
          exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
      have hj0_nxt : nextIdx t hpos j0 ∉ mergedInt t hpos S p := by
        rw [hmerged, Finset.mem_singleton]
        rcases hj0eq with rfl | rfl <;> rw [nextIdx_shiftIdx'] <;>
          exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
      have hj0V : isoVec t hpos S j0 ∈ Vset t hpos S :=
        isoVec_mem_Vset t hpos ht S p hp hj0_sub hj0_pre hj0_nxt
      have hvV : pairVec t hpos S m + isoVec t hpos S j0 ∈ Vset t hpos S :=
        Submodule.add_mem _ hpairV hj0V
      have hvB : projLane p (Hmap t (pairVec t hpos S m + isoVec t hpos S j0)) = 0 := by
        rw [map_add, map_add, projLane_Hmap_pairVec t hpos ht S p hp (by omega),
          projLane_Hmap_isoVec t hpos ht S p hp (Finset.mem_filter.mp hj0_sub).2,
          prevIdx_eq_shift, ← shiftIdx_one, hpair_eq_h]
        rcases hj0eq with rfl | rfl
        · rw [hm3_eq_h]; ext k; exact zmod2_add_self _
        · ext k; exact zmod2_add_self _
      exact supp_of_Vset_cancel t hpos S p hp hu1 hu2 (shiftIdx_two_ne_mod3 t hpos m 6) hvV hvB hval hiu1 hiu2
    have hi_nonfree : i ∈ B ∨ i = m ∨ i = mkFam3B_left t hpos m kind ∨ i = mkFam3B_right t hpos m kind := by
      simp only [S, mkFam3B, Finset.mem_union, Finset.mem_singleton] at hiS
      rcases hiS with (((hB | hAf) | rfl) | hL) | hR
      · exact Or.inl hB
      · exfalso; apply hif
        rcases Finset.mem_filter.mp hAf with ⟨hiL, hpre, hnxt⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hiL).2⟩, by rw [hBp]; exact hpre, by rw [hBp]; exact hnxt⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hAf)))
      · exact Or.inr (Or.inl rfl)
      · cases bL <;> simp at hL; exact Or.inr (Or.inr (Or.inl hL))
      · cases bR <;> simp at hR; exact Or.inr (Or.inr (Or.inr hR))
    have hpre_m3 : prevIdx t hpos (shiftIdx t hpos m (6 * t - 3)) = shiftIdx t hpos m (6 * t - 4) := by
      rw [prevIdx_shiftIdx_pos t hpos m (by omega)]; congr 1
    have hnxt_m3 : nextIdx t hpos (shiftIdx t hpos m (6 * t - 3)) = shiftIdx t hpos m (6 * t - 2) := by
      rw [nextIdx_shiftIdx']; congr 1; omega
    have hpre_p3 : prevIdx t hpos (shiftIdx t hpos m 3) = shiftIdx t hpos m 2 := by
      rw [prevIdx_shiftIdx_pos t hpos m (by omega)]
    have hnxt_p3 : nextIdx t hpos (shiftIdx t hpos m 3) = shiftIdx t hpos m 4 := by
      rw [nextIdx_shiftIdx']
    have h_use_L : kind ≠ 1 →
        (i = shiftIdx t hpos m (6 * t - 4) ∨ i = shiftIdx t hpos m (6 * t - 3) ∨
         i = shiftIdx t hpos m (6 * t - 1) ∨ i = m ∨ i = shiftIdx t hpos m 1 ∨
         i = shiftIdx t hpos m 2) →
        ∃ x ∈ GoodMax t hpos S, x i ≠ 0 := by
      intro hk hi_in
      have hj0B : shiftIdx t hpos m (6 * t - 3) ∈ B := by
        dsimp only [B, mkFam3B_B]
        rcases fin3_cases kind with rfl | rfl | rfl
        · simp
        · exact absurd rfl hk
        · simp
      apply hcov (shiftIdx t hpos m (6 * t - 3)) hj0B (Or.inl rfl)
      simp only [Pi.add_apply, pairVec, isoVec, hpre_m3, hnxt_m3,
        prevIdx_eq_shift, prev2_eq_shift,
        show next2 t hpos m = shiftIdx t hpos m 2 from rfl,
        show nextIdx t hpos m = shiftIdx t hpos m 1 from rfl]
      rcases hi_in with rfl | rfl | rfl | him | rfl | rfl
      · rw [if_neg, if_pos (Or.inr (Or.inl ⟨rfl, hiS⟩)), zero_add]
        rintro (h | h | h | ⟨h, _⟩ | ⟨h, _⟩)
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [if_neg, if_pos (Or.inl rfl), zero_add]
        rintro (h | h | h | ⟨h, _⟩ | ⟨h, _⟩)
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [if_pos (Or.inl rfl), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [him, if_pos (Or.inr (Or.inl rfl)), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) h.symm
      · rw [if_pos (Or.inr (Or.inr (Or.inl rfl))), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hiS⟩)))), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
    have h_use_R : kind ≠ 0 →
        (i = shiftIdx t hpos m (6 * t - 2) ∨ i = shiftIdx t hpos m (6 * t - 1) ∨
         i = m ∨ i = shiftIdx t hpos m 1 ∨ i = shiftIdx t hpos m 3 ∨
         i = shiftIdx t hpos m 4) →
        ∃ x ∈ GoodMax t hpos S, x i ≠ 0 := by
      intro hk hi_in
      have hj0B : shiftIdx t hpos m 3 ∈ B := by
        dsimp only [B, mkFam3B_B]
        rcases fin3_cases kind with rfl | rfl | rfl
        · exact absurd rfl hk
        · simp
        · simp
      apply hcov (shiftIdx t hpos m 3) hj0B (Or.inr rfl)
      simp only [Pi.add_apply, pairVec, isoVec, hpre_p3, hnxt_p3,
        prevIdx_eq_shift, prev2_eq_shift,
        show next2 t hpos m = shiftIdx t hpos m 2 from rfl,
        show nextIdx t hpos m = shiftIdx t hpos m 1 from rfl]
      rcases hi_in with rfl | rfl | him | rfl | rfl | rfl
      · rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hiS⟩)))), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [if_pos (Or.inl rfl), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [him, if_pos (Or.inr (Or.inl rfl)), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) h.symm
      · rw [if_pos (Or.inr (Or.inr (Or.inl rfl))), if_neg, add_zero]
        rintro (h | ⟨h, _⟩ | ⟨h, _⟩) <;> exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [if_neg, if_pos (Or.inl rfl), zero_add]
        rintro (h | h | h | ⟨h, _⟩ | ⟨h, _⟩)
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
      · rw [if_neg, if_pos (Or.inr (Or.inr ⟨rfl, hiS⟩)), zero_add]
        rintro (h | h | h | ⟨h, _⟩ | ⟨h, _⟩)
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
        · exact hsh_ne _ _ (by omega) (by omega) (by omega) h
    rcases fin3_cases kind with rfl | rfl | rfl
    · apply h_use_L (by decide)
      dsimp only [B, mkFam3B_B, mkFam3B_left, mkFam3B_right] at hi_nonfree
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] at hi_nonfree
      rcases hi_nonfree with (h | h | h) | h | h | h <;> simp [h]
    · apply h_use_R (by decide)
      dsimp only [B, mkFam3B_B, mkFam3B_left, mkFam3B_right] at hi_nonfree
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] at hi_nonfree
      rcases hi_nonfree with (h | h | h) | h | h | h <;> simp [h]
    · dsimp only [B, mkFam3B_B, mkFam3B_left, mkFam3B_right] at hi_nonfree
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] at hi_nonfree
      rcases hi_nonfree with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl
      · exact h_use_L (by decide) (Or.inr (Or.inl rfl))
      · exact h_use_L (by decide) (Or.inr (Or.inr (Or.inl rfl)))
      · exact h_use_L (by decide) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact h_use_R (by decide) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact h_use_L (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact h_use_L (by decide) (Or.inl rfl)
      · exact h_use_R (by decide) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

lemma mkFam3B_props (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (m : Fin (6 * t)) (kind : Fin 3) (bL bR : Bool) :
    let S := mkFam3B t hpos m kind bL bR
    let p := 1 - m.val % 2
    sitesS t S p = (if kind = 2 then 4 else 3) ∧
    4 < sitesS t S (1 - p) ∧
    mergedInt t hpos S p = {m} ∧
    runsS t hpos S = 3 * t - 2 ∧
    suppU t (GoodMax t hpos S) = S ∧
    Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
  have hb := mkFam3B_basic t hpos ht m kind bL bR
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, mkFam3B_supp t hpos ht m kind bL bR, hb.2.2.2.2.1⟩

lemma card_Fam3BSet (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) :
    (Fam3BSet t hpos).card = 12 * (6 * t) := by
  unfold Fam3BSet
  rw [Finset.card_image_of_injOn]
  · simp; ring
  · rintro ⟨m1, k1, bL1, bR1⟩ _ ⟨m2, k2, bL2, bR2⟩ _ heq
    dsimp only at heq
    have hp1 := mkFam3B_props t hpos ht m1 k1 bL1 bR1
    have hp2 := mkFam3B_props t hpos ht m2 k2 bL2 bR2
    have hpar : 1 - m1.val % 2 = 1 - m2.val % 2 := by
      by_contra hne
      have h1 := hp1.1; have h2 := hp2.2.1
      have h12 : 1 - (1 - m2.val % 2) = 1 - m1.val % 2 := by omega
      rw [h12, ← heq] at h2
      split_ifs at h1 <;> omega
    have hm_eq : m1 = m2 := by
      have hm1 := hp1.2.2.1
      have hm2 := hp2.2.2.1
      rw [← hpar, ← heq, hm1] at hm2
      exact Finset.singleton_injective hm2
    subst hm_eq
    have hBeq : mkFam3B_B t hpos m1 k1 = mkFam3B_B t hpos m1 k2 := by
      rw [← mkFam3B_laneSub_p t hpos ht m1 k1 bL1 bR1, ← mkFam3B_laneSub_p t hpos ht m1 k2 bL2 bR2, heq]
    have hsh_ne : ∀ a b : ℕ, a < 6 * t → b < 6 * t → a ≠ b →
        shiftIdx t hpos m1 a ≠ shiftIdx t hpos m1 b := fun a b ha hb hne =>
      shiftIdx_ne_of_ne t hpos m1 ha hb hne
    have hk_eq : k1 = k2 := by
      have hm3_iff : ∀ k : Fin 3, shiftIdx t hpos m1 (6 * t - 3) ∈ mkFam3B_B t hpos m1 k ↔ k ≠ 1 := by
        intro k; unfold mkFam3B_B
        rcases fin3_cases k with rfl | rfl | rfl
        · simp
        · simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton,
            ne_eq, not_true_eq_false, iff_false, not_or]
          exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega),
            hsh_ne _ _ (by omega) (by omega) (by omega)⟩
        · simp
      have hp3_iff : ∀ k : Fin 3, shiftIdx t hpos m1 3 ∈ mkFam3B_B t hpos m1 k ↔ k ≠ 0 := by
        intro k; unfold mkFam3B_B
        rcases fin3_cases k with rfl | rfl | rfl
        · simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton,
            ne_eq, not_true_eq_false, iff_false, not_or]
          exact ⟨hsh_ne _ _ (by omega) (by omega) (by omega), hsh_ne _ _ (by omega) (by omega) (by omega),
            hsh_ne _ _ (by omega) (by omega) (by omega)⟩
        · simp
        · simp
      have h1 : (k1 ≠ 1) ↔ (k2 ≠ 1) := (hm3_iff k1).symm.trans (by rw [hBeq]; exact hm3_iff k2)
      have h2 : (k1 ≠ 0) ↔ (k2 ≠ 0) := (hp3_iff k1).symm.trans (by rw [hBeq]; exact hp3_iff k2)
      rcases fin3_cases k1 with rfl | rfl | rfl <;> rcases fin3_cases k2 with rfl | rfl | rfl <;>
        first | rfl
              | exact False.elim ((h1.mp (by decide)) rfl)
              | exact False.elim ((h1.mpr (by decide)) rfl)
              | exact False.elim ((h2.mp (by decide)) rfl)
              | exact False.elim ((h2.mpr (by decide)) rfl)
    subst hk_eq
    have hmem_LR : ∀ bL bR,
        (mkFam3B_left t hpos m1 k1 ∈ mkFam3B t hpos m1 k1 bL bR ↔ bL = true) ∧
        (mkFam3B_right t hpos m1 k1 ∈ mkFam3B t hpos m1 k1 bL bR ↔ bR = true) := by
      intro bL bR
      have hL_not_B : mkFam3B_left t hpos m1 k1 ∉ mkFam3B_B t hpos m1 k1 := by
        intro h
        have hp1' : (mkFam3B_left t hpos m1 k1).val % 2 = m1.val % 2 := by
          unfold mkFam3B_left; split_ifs <;> rw [shiftIdx_mod2] <;> omega
        have hp2' : (mkFam3B_left t hpos m1 k1).val % 2 = 1 - m1.val % 2 := by
          have : mkFam3B_left t hpos m1 k1 ∈ laneSub t (mkFam3B t hpos m1 k1 bL bR) (1 - m1.val % 2) := by
            rw [mkFam3B_laneSub_p t hpos ht m1 k1 bL bR]; exact h
          exact (Finset.mem_filter.mp this).2
        omega
      have hR_not_B : mkFam3B_right t hpos m1 k1 ∉ mkFam3B_B t hpos m1 k1 := by
        intro h
        have hp1' : (mkFam3B_right t hpos m1 k1).val % 2 = m1.val % 2 := by
          unfold mkFam3B_right; split_ifs <;> rw [shiftIdx_mod2] <;> omega
        have hp2' : (mkFam3B_right t hpos m1 k1).val % 2 = 1 - m1.val % 2 := by
          have : mkFam3B_right t hpos m1 k1 ∈ laneSub t (mkFam3B t hpos m1 k1 bL bR) (1 - m1.val % 2) := by
            rw [mkFam3B_laneSub_p t hpos ht m1 k1 bL bR]; exact h
          exact (Finset.mem_filter.mp this).2
        omega
      have hL_not_Af : mkFam3B_left t hpos m1 k1 ∉ (laneSet t (1 - (1 - m1.val % 2))).filter (fun i =>
          prevIdx t hpos i ∉ mkFam3B_B t hpos m1 k1 ∧ nextIdx t hpos i ∉ mkFam3B_B t hpos m1 k1) := by
        intro h; apply (Finset.mem_filter.mp h).2.2
        unfold mkFam3B_left mkFam3B_B
        rcases fin3_cases k1 with rfl | rfl | rfl <;>
          simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, nextIdx_shiftIdx',
            show 6 * t - 4 + 1 = 6 * t - 3 by omega, show 6 * t - 2 + 1 = 6 * t - 1 by omega,
            Finset.mem_insert, Finset.mem_singleton] <;> tauto
      have hR_not_Af : mkFam3B_right t hpos m1 k1 ∉ (laneSet t (1 - (1 - m1.val % 2))).filter (fun i =>
          prevIdx t hpos i ∉ mkFam3B_B t hpos m1 k1 ∧ nextIdx t hpos i ∉ mkFam3B_B t hpos m1 k1) := by
        intro h; apply (Finset.mem_filter.mp h).2.1
        unfold mkFam3B_right mkFam3B_B
        rcases fin3_cases k1 with rfl | rfl | rfl <;>
          simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq,
            prevIdx_shiftIdx_pos t hpos m1 (d := 2) (by omega),
            prevIdx_shiftIdx_pos t hpos m1 (d := 4) (by omega),
            Finset.mem_insert, Finset.mem_singleton] <;> tauto
      have hL_ne_m : mkFam3B_left t hpos m1 k1 ≠ m1 := by
        unfold mkFam3B_left; split_ifs <;>
          exact shiftIdx_ne_self_of_pos t hpos m1 (by omega) (by omega)
      have hR_ne_m : mkFam3B_right t hpos m1 k1 ≠ m1 := by
        unfold mkFam3B_right; split_ifs <;>
          exact shiftIdx_ne_self_of_pos t hpos m1 (by omega) (by omega)
      have hL_ne_R : mkFam3B_left t hpos m1 k1 ≠ mkFam3B_right t hpos m1 k1 := by
        unfold mkFam3B_left mkFam3B_right
        rcases fin3_cases k1 with rfl | rfl | rfl <;> simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] <;>
          exact hsh_ne _ _ (by omega) (by omega) (by omega)
      constructor
      · simp only [mkFam3B, Finset.mem_union, Finset.mem_singleton, mem_if_singleton]
        simp [hL_not_B, hL_not_Af, hL_ne_m, hL_ne_R]
      · simp only [mkFam3B, Finset.mem_union, Finset.mem_singleton, mem_if_singleton]
        simp [hR_not_B, hR_not_Af, hR_ne_m, hL_ne_R.symm]
    have hbL : bL1 = bL2 :=
      bool_eq_of_iff ((hmem_LR bL1 bR1).1.symm.trans (by rw [heq]; exact (hmem_LR bL2 bR2).1))
    have hbR : bR1 = bR2 :=
      bool_eq_of_iff ((hmem_LR bL1 bR1).2.symm.trans (by rw [heq]; exact (hmem_LR bL2 bR2).2))
    subst hbL; subst hbR; rfl

lemma min_sites_eq (t : ℕ) (S : Finset (Fin (6 * t))) {p : ℕ} (hp : p = 0 ∨ p = 1) :
    min (sitesS t S 0) (sitesS t S 1) = min (sitesS t S p) (sitesS t S (1 - p)) := by
  rcases hp with rfl | rfl
  · rfl
  · exact min_comm _ _

lemma sites_pos_of_pair (t : ℕ) (S : Finset (Fin (6 * t))) {p : ℕ} (hp : p = 0 ∨ p = 1)
    (h1 : 0 < sitesS t S p) (h2 : 0 < sitesS t S (1 - p)) :
    0 < sitesS t S 0 ∧ 0 < sitesS t S 1 := by
  rcases hp with rfl | rfl
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

lemma disjoint_Fam3A_Fam3B (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) :
    Disjoint (Fam3ASet t hpos) (Fam3BSet t hpos) := by
  rw [Finset.disjoint_left]
  intro S hA hB
  rcases Finset.mem_image.mp hA with ⟨⟨⟨r, ab⟩, b1, b2, b3, b4⟩, hxA, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨⟨m, k, bL, bR⟩, _, heq⟩
  have hab : ab.1.val < ab.2.val :=
    (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp hxA).1).2).2
  have hpA := mkFam3A_props t hpos ht r ab hab b1 b2 b3 b4
  have hpB := mkFam3B_props t hpos ht m k bL bR
  have hminA : min (sitesS t (mkFam3A t hpos r ab b1 b2 b3 b4) 0)
      (sitesS t (mkFam3A t hpos r ab b1 b2 b3 b4) 1) = 2 := by
    rw [min_sites_eq t (mkFam3A t hpos r ab b1 b2 b3 b4) (p := r.val % 2) (by omega)]
    have h1 := hpA.1; have h2 := hpA.2.1; omega
  have hminB : 3 ≤ min (sitesS t (mkFam3B t hpos m k bL bR) 0)
      (sitesS t (mkFam3B t hpos m k bL bR) 1) := by
    rw [min_sites_eq t (mkFam3B t hpos m k bL bR) (p := 1 - m.val % 2) (by omega)]
    have h1 := hpB.1; have h2 := hpB.2.1; split_ifs at h1 <;> omega
  rw [heq, hminA] at hminB
  omega

lemma classify_rB_one_M1 (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (S : Finset (Fin (6 * t))) (p : ℕ) (hp : p = 0 ∨ p = 1)
    (hBpos : 0 < (laneSub t S p).card) (hBlt : (laneSub t S p).card < 3 * t)
    (hrB1 : rB t hpos S p = 1) (hMpos : 1 ≤ (mergedInt t hpos S p).card)
    (hsupp : suppU t (GoodMax t hpos S) = S)
    (hsum : blocksB t hpos S p + (missFree t hpos S p).card + (mergedInt t hpos S p).card ≤ 2) :
    S ∈ Fam3BSet t hpos := by
  have hs_pos : 1 ≤ blocksB t hpos S p := blocksB_pos_of_lt t hpos S p hp hBpos hBlt
  have hs1 : blocksB t hpos S p = 1 := by omega
  have hq0 : (missFree t hpos S p).card = 0 := by omega
  have hM1 : (mergedInt t hpos S p).card = 1 := by omega
  have hmiss_emp : missFree t hpos S p = ∅ := Finset.card_eq_zero.mp hq0
  rcases Finset.card_eq_one.mp hM1 with ⟨m, hMeq⟩
  have hmM : m ∈ mergedInt t hpos S p := by rw [hMeq]; simp
  rcases Finset.mem_filter.mp hmM with ⟨hmA, hm_preB, hm_nxtB⟩
  have hmp : m.val % 2 = 1 - p := (Finset.mem_filter.mp hmA).2
  have hp_eq : p = 1 - m.val % 2 := by omega
  have hsh_ne : ∀ a b : ℕ, a < 6 * t → b < 6 * t → a ≠ b →
      shiftIdx t hpos m a ≠ shiftIdx t hpos m b := fun a b ha hb hne =>
    shiftIdx_ne_of_ne t hpos m ha hb hne
  have hpairV : pairVec t hpos S m ∈ Vset t hpos S := by
    refine pairVec_mem_Vset t hpos ht S p hp hmM ?_ ?_
    · rw [hMeq, Finset.mem_singleton, prev2_eq_shift]
      exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
    · rw [hMeq, Finset.mem_singleton, next2]
      exact shiftIdx_ne_self_of_pos t hpos m (by omega) (by omega)
  have hpair_val : projLane p (Hmap t (pairVec t hpos S m)) = hLane t p (shiftIdx t hpos m (6 * t - 3)) := by
    rw [projLane_Hmap_pairVec t hpos ht S p hp hmp, hLane_prev_next_eq_prev3,
      prevIdx_prev2_eq_shift t hpos ht m]
  have hm3_p : (shiftIdx t hpos m (6 * t - 3)).val % 2 = p := by rw [shiftIdx_mod2]; omega
  -- Any j ∈ B \ {m-1, m+1} must have same val/2%3 as shiftIdx m (6*t - 3)
  have hother_mod3 : ∀ j ∈ laneSub t S p, j ≠ prevIdx t hpos m → j ≠ nextIdx t hpos m →
      j.val / 2 % 3 = (shiftIdx t hpos m (6 * t - 3)).val / 2 % 3 := by
    intro j hj hne1 hne2
    by_contra hne
    have hpreM : prevIdx t hpos j ∉ mergedInt t hpos S p := by
      rw [hMeq, Finset.mem_singleton]
      intro h; exact hne2 (by have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx] at this)
    have hnxtM : nextIdx t hpos j ∉ mergedInt t hpos S p := by
      rw [hMeq, Finset.mem_singleton]
      intro h; exact hne1 (by have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx] at this)
    have hv := isoVec_mem_Vset t hpos ht S p hp hj hpreM hnxtM
    have hjp : j.val % 2 = p := (Finset.mem_filter.mp hj).2
    have h2 := rB_eq_two_of_diff_mod3 t hpos S p hp hjp hm3_p
      (v1 := ⟨_, hv⟩) (v2 := ⟨_, hpairV⟩)
      (projLane_Hmap_isoVec t hpos ht S p hp hjp) hpair_val hne
    omega
  have hm5_out : shiftIdx t hpos m (6 * t - 5) ∉ laneSub t S p := by
    intro h5
    have hmod := hother_mod3 _ h5
      (by rw [prevIdx_eq_shift]; exact hsh_ne _ _ (by omega) (by omega) (by omega))
      (by rw [← shiftIdx_one]; exact hsh_ne _ _ (by omega) (by omega) (by omega))
    have hstep : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 5)) 2 = shiftIdx t hpos m (6 * t - 3) := by
      rw [shiftIdx_add]; congr 1; omega
    have hd := shiftIdx_two_div2_mod3 t hpos (shiftIdx t hpos m (6 * t - 5))
    rw [hstep] at hd; omega
  have hp5_out : shiftIdx t hpos m 5 ∉ laneSub t S p := by
    intro h5
    have hmod := hother_mod3 _ h5
      (by rw [prevIdx_eq_shift]; exact hsh_ne _ _ (by omega) (by omega) (by omega))
      (by rw [← shiftIdx_one]; exact hsh_ne _ _ (by omega) (by omega) (by omega))
    have h3eq : (shiftIdx t hpos m (6 * t - 3)).val / 2 % 3 = (shiftIdx t hpos m 3).val / 2 % 3 := by
      have h := hLane_prev3_eq_next3 t hpos p hp m hmp
      rw [prevIdx_prev2_eq_shift t hpos ht m, nextIdx_next2_eq_shift] at h
      exact (hLane_eq_iff t p hp _ _ hm3_p (by rw [shiftIdx_mod2]; omega)).mp h
    have hstep : shiftIdx t hpos (shiftIdx t hpos m 3) 2 = shiftIdx t hpos m 5 := by
      rw [shiftIdx_add]
    have hd := shiftIdx_two_div2_mod3 t hpos (shiftIdx t hpos m 3)
    rw [hstep] at hd; omega
  -- Case split on m-3 ∈ B and m+3 ∈ B
  have hnot_both_out : ¬(shiftIdx t hpos m (6 * t - 3) ∉ laneSub t S p ∧
      shiftIdx t hpos m 3 ∉ laneSub t S p) := by
    rintro ⟨hlout, hrout⟩
    have hpre2_out : prev2 t hpos (prevIdx t hpos m) ∉ laneSub t S p := by
      have : prev2 t hpos (prevIdx t hpos m) = shiftIdx t hpos m (6 * t - 3) := by
        rw [← prevIdx_prev2_eq_shift t hpos ht m, prev2, prev2]
      rwa [this]
    have hk2_out : shiftIdx t hpos (prevIdx t hpos m) (2 * 2) ∉ laneSub t S p := by
      have : shiftIdx t hpos (prevIdx t hpos m) 4 = shiftIdx t hpos m 3 := by
        rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
        rw [show m.val + (6 * t - 1 + 4) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]
      rwa [show 2 * 2 = 4 by rfl, this]
    have hBeq2 := single_block_subset t hpos S p hp hs1 hm_preB hpre2_out (k := 2) (by omega) (by omega) hk2_out
      (fun d hd => by
        interval_cases d
        · simpa [shiftIdx_zero] using hm_preB
        · have : shiftIdx t hpos (prevIdx t hpos m) 2 = nextIdx t hpos m := by
            rw [← next2, next2_eq_next_next, nextIdx_prevIdx]
          rwa [this])
    have hmS : m ∈ S := (Finset.mem_filter.mp hmA).1
    have hmem_supp : m ∈ suppU t (GoodMax t hpos S) := by rw [hsupp]; exact hmS
    simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_supp
    rcases hmem_supp with ⟨x, hxGM, hxm⟩
    have hxm1 : x (prevIdx t hpos m) = x m := by
      have := hxGM.1.2 (prevIdx t hpos m) (Finset.mem_filter.mp hm_preB).1 (by rw [nextIdx_prevIdx]; exact hmS)
      rwa [nextIdx_prevIdx] at this
    have hxp1 : x (nextIdx t hpos m) = x m :=
      (hxGM.1.2 m hmS (Finset.mem_filter.mp hm_nxtB).1).symm
    have hzero : projLane p (Hmap t x) = 0 := by
      ext k; exact congrFun hxGM.2 (laneBit p k)
    have hne_pn : prevIdx t hpos m ≠ nextIdx t hpos m := by
      rw [prevIdx_eq_shift, ← shiftIdx_one]; exact hsh_ne _ _ (by omega) (by omega) (by omega)
    have hval : projLane p (Hmap t x) = x m • hLane t p (shiftIdx t hpos m (6 * t - 3)) := by
      ext k
      change ∑ i : Fin (6 * t), hFn t i (laneBit p k) * x i =
        x m * hFn t (shiftIdx t hpos m (6 * t - 3)) (laneBit p k)
      rw [← Finset.sum_subset (Finset.subset_univ ({prevIdx t hpos m, nextIdx t hpos m} : Finset _))]
      · rw [Finset.sum_pair hne_pn, hxm1, hxp1]
        have hk := congrFun (hLane_prev_next_eq_prev3 t hpos p m) k
        rw [prevIdx_prev2_eq_shift t hpos ht m] at hk
        simp only [hLane, Pi.add_apply] at hk
        calc hFn t (prevIdx t hpos m) (laneBit p k) * x m + hFn t (nextIdx t hpos m) (laneBit p k) * x m
            = (hFn t (prevIdx t hpos m) (laneBit p k) + hFn t (nextIdx t hpos m) (laneBit p k)) * x m := by ring
          _ = x m * hFn t (shiftIdx t hpos m (6 * t - 3)) (laneBit p k) := by rw [hk]; ring
      · intro i _ hi
        by_cases hiS : i ∈ S
        · by_cases hip : i.val % 2 = p
          · exfalso; apply hi
            have hiB : i ∈ laneSub t S p := Finset.mem_filter.mpr ⟨hiS, hip⟩
            rw [hBeq2] at hiB
            rcases Finset.mem_image.mp hiB with ⟨d, hd, rfl⟩
            have hd2 : d < 2 := Finset.mem_range.mp hd
            interval_cases d
            · rw [shiftIdx_zero]; simp
            · have : shiftIdx t hpos (prevIdx t hpos m) 2 = nextIdx t hpos m := by
                rw [← next2, next2_eq_next_next, nextIdx_prevIdx]
              rw [this]; simp
          · rw [hFn_other_lane t i (laneBit p k) (by rw [laneBit_div2 p hp k]; exact hip), zero_mul]
        · rw [hxGM.1.1 i hiS, mul_zero]
    rw [hval, (zmod2_ne_zero_iff _).mp hxm, one_smul] at hzero
    exact hLane_ne_zero t p hp _ hm3_p hzero
  -- Determine kind : Fin 3 and exact B
  have hkind_ex : ∃ kind : Fin 3, laneSub t S p = mkFam3B_B t hpos m kind := by
    by_cases hL : shiftIdx t hpos m (6 * t - 3) ∈ laneSub t S p
    · by_cases hR : shiftIdx t hpos m 3 ∈ laneSub t S p
      · refine ⟨2, ?_⟩
        have hpre : prev2 t hpos (shiftIdx t hpos m (6 * t - 3)) ∉ laneSub t S p := by
          have : prev2 t hpos (shiftIdx t hpos m (6 * t - 3)) = shiftIdx t hpos m (6 * t - 5) := by
            apply next2_inj t hpos; rw [next2_prev2, next2, shiftIdx_add]; congr 1; omega
          rwa [this]
        have hout : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) (2 * 4) ∉ laneSub t S p := by
          have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 8 = shiftIdx t hpos m 5 := by
            rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 3 + 8) = (m.val + 5) + 6 * t by omega, Nat.add_mod_right]
          rwa [show 2 * 4 = 8 by rfl, this]
        have hsb := single_block_subset t hpos S p hp hs1 hL hpre (k := 4) (by omega) (by omega) hout
          (fun d hd => by
            interval_cases d
            · simpa [shiftIdx_zero] using hL
            · have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 2 = prevIdx t hpos m := by
                rw [shiftIdx_add, prevIdx_eq_shift]; congr 1; omega
              rwa [this]
            · have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 4 = nextIdx t hpos m := by
                rw [shiftIdx_add, ← shiftIdx_one]; apply Fin.ext; dsimp [shiftIdx]
                rw [show m.val + (6 * t - 3 + 4) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]
              rwa [this]
            · have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 6 = shiftIdx t hpos m 3 := by
                rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
                rw [show m.val + (6 * t - 3 + 6) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]
              rwa [this])
        rw [hsb]; unfold mkFam3B_B
        ext x; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Finset.mem_image, Finset.mem_range,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨d, hd, rfl⟩; interval_cases d
          · left; exact shiftIdx_zero t hpos _
          · right; left; rw [shiftIdx_add]; congr 1; omega
          · right; right; left; rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 3 + 4) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]
          · right; right; right; rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 3 + 6) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨0, by omega, shiftIdx_zero t hpos _⟩
          · exact ⟨1, by omega, by rw [shiftIdx_add]; congr 1; omega⟩
          · exact ⟨2, by omega, by
              rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
              rw [show m.val + (6 * t - 3 + 4) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]⟩
          · exact ⟨3, by omega, by
              rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
              rw [show m.val + (6 * t - 3 + 6) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]⟩
      · refine ⟨0, ?_⟩
        have hpre : prev2 t hpos (shiftIdx t hpos m (6 * t - 3)) ∉ laneSub t S p := by
          have : prev2 t hpos (shiftIdx t hpos m (6 * t - 3)) = shiftIdx t hpos m (6 * t - 5) := by
            apply next2_inj t hpos; rw [next2_prev2, next2, shiftIdx_add]; congr 1; omega
          rwa [this]
        have hout : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) (2 * 3) ∉ laneSub t S p := by
          have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 6 = shiftIdx t hpos m 3 := by
            rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 3 + 6) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]
          rwa [show 2 * 3 = 6 by rfl, this]
        have hsb := single_block_subset t hpos S p hp hs1 hL hpre (k := 3) (by omega) (by omega) hout
          (fun d hd => by
            interval_cases d
            · simpa [shiftIdx_zero] using hL
            · have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 2 = prevIdx t hpos m := by
                rw [shiftIdx_add, prevIdx_eq_shift]; congr 1; omega
              rwa [this]
            · have : shiftIdx t hpos (shiftIdx t hpos m (6 * t - 3)) 4 = nextIdx t hpos m := by
                rw [shiftIdx_add, ← shiftIdx_one]; apply Fin.ext; dsimp [shiftIdx]
                rw [show m.val + (6 * t - 3 + 4) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]
              rwa [this])
        rw [hsb]; unfold mkFam3B_B
        ext x; simp only [Fin.isValue, ↓reduceIte, Finset.mem_image, Finset.mem_range,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨d, hd, rfl⟩; interval_cases d
          · left; exact shiftIdx_zero t hpos _
          · right; left; rw [shiftIdx_add]; congr 1; omega
          · right; right; rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 3 + 4) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]
        · rintro (rfl | rfl | rfl)
          · exact ⟨0, by omega, shiftIdx_zero t hpos _⟩
          · exact ⟨1, by omega, by rw [shiftIdx_add]; congr 1; omega⟩
          · exact ⟨2, by omega, by
              rw [shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
              rw [show m.val + (6 * t - 3 + 4) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]⟩
    · have hR : shiftIdx t hpos m 3 ∈ laneSub t S p := by tauto
      refine ⟨1, ?_⟩
      have hpre : prev2 t hpos (prevIdx t hpos m) ∉ laneSub t S p := by
        have : prev2 t hpos (prevIdx t hpos m) = shiftIdx t hpos m (6 * t - 3) := by
          rw [← prevIdx_prev2_eq_shift t hpos ht m, prev2, prev2]
        rwa [this]
      have hout : shiftIdx t hpos (prevIdx t hpos m) (2 * 3) ∉ laneSub t S p := by
        have : shiftIdx t hpos (prevIdx t hpos m) 6 = shiftIdx t hpos m 5 := by
          rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
          rw [show m.val + (6 * t - 1 + 6) = (m.val + 5) + 6 * t by omega, Nat.add_mod_right]
        rwa [show 2 * 3 = 6 by rfl, this]
      have hsb := single_block_subset t hpos S p hp hs1 hm_preB hpre (k := 3) (by omega) (by omega) hout
        (fun d hd => by
          interval_cases d
          · simpa [shiftIdx_zero] using hm_preB
          · have : shiftIdx t hpos (prevIdx t hpos m) 2 = nextIdx t hpos m := by
              rw [← next2, next2_eq_next_next, nextIdx_prevIdx]
            rwa [this]
          · have : shiftIdx t hpos (prevIdx t hpos m) 4 = shiftIdx t hpos m 3 := by
              rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
              rw [show m.val + (6 * t - 1 + 4) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]
            rwa [this])
      rw [hsb]; unfold mkFam3B_B
      ext x; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Finset.mem_image, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨d, hd, rfl⟩; interval_cases d
        · left; rw [shiftIdx_zero, prevIdx_eq_shift]
        · right; left; rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
          rw [show m.val + (6 * t - 1 + 2) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]
        · right; right; rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
          rw [show m.val + (6 * t - 1 + 4) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, by omega, by rw [shiftIdx_zero, prevIdx_eq_shift]⟩
        · exact ⟨1, by omega, by
            rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 1 + 2) = (m.val + 1) + 6 * t by omega, Nat.add_mod_right]⟩
        · exact ⟨2, by omega, by
            rw [prevIdx_eq_shift, shiftIdx_add]; apply Fin.ext; dsimp [shiftIdx]
            rw [show m.val + (6 * t - 1 + 4) = (m.val + 3) + 6 * t by omega, Nat.add_mod_right]⟩
  rcases hkind_ex with ⟨kind, hBeq⟩
  let bL := decide (mkFam3B_left t hpos m kind ∈ S)
  let bR := decide (mkFam3B_right t hpos m kind ∈ S)
  have hSeq : S = mkFam3B t hpos m kind bL bR := by
    ext x
    by_cases hxp : x.val % 2 = p
    · have h1 : x ∈ S ↔ x ∈ laneSub t S p := by simp [laneSub, hxp]
      have h2 : x ∈ mkFam3B t hpos m kind bL bR ↔
          x ∈ laneSub t (mkFam3B t hpos m kind bL bR) p := by simp [laneSub, hxp]
      rw [h1, h2, hBeq, hp_eq, mkFam3B_laneSub_p t hpos ht m kind bL bR]
    · have hxp1 : x.val % 2 = 1 - p := by omega
      have hx_not_B : x ∉ mkFam3B_B t hpos m kind := by
        intro h; rw [← hBeq] at h; exact hxp (Finset.mem_filter.mp h).2
      have h1p : 1 - (1 - m.val % 2) = 1 - p := by omega
      by_cases hx_free : prevIdx t hpos x ∉ mkFam3B_B t hpos m kind ∧ nextIdx t hpos x ∉ mkFam3B_B t hpos m kind
      · have hx_S : x ∈ S := by
          by_contra hxnot
          have hmf : x ∈ missFree t hpos S p :=
            Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp1⟩, fun h => hxnot (Finset.mem_filter.mp h).1⟩,
              by rw [hBeq]; exact hx_free.1, by rw [hBeq]; exact hx_free.2⟩
          rw [hmiss_emp] at hmf; exact Finset.notMem_empty _ hmf
        have hx_rhs : x ∈ mkFam3B t hpos m kind bL bR :=
          Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, hx_free⟩))))
        simp [hx_S, hx_rhs]
      · -- x is adjacent to B: either x = m, or x = mkFam3B_left, or x = mkFam3B_right, or x is an unmerged internal site
        by_cases hxm : x = m
        · rw [hxm]
          have h1 : m ∈ S := (Finset.mem_filter.mp hmA).1
          have h2 : m ∈ mkFam3B t hpos m kind bL bR :=
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self m)))
          simp [h1, h2]
        · by_cases hxL : x = mkFam3B_left t hpos m kind
          · subst hxL
            have hL_ne_R : mkFam3B_left t hpos m kind ≠ mkFam3B_right t hpos m kind := by
              unfold mkFam3B_left mkFam3B_right
              rcases fin3_cases kind with rfl | rfl | rfl <;> simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] <;>
                exact hsh_ne _ _ (by omega) (by omega) (by omega)
            simp only [mkFam3B, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, mem_if_singleton]
            simp [bL, hx_not_B, hx_free, hxm, hL_ne_R]
          · by_cases hxR : x = mkFam3B_right t hpos m kind
            · subst hxR
              have hR_ne_L : mkFam3B_right t hpos m kind ≠ mkFam3B_left t hpos m kind := by
                unfold mkFam3B_left mkFam3B_right
                rcases fin3_cases kind with rfl | rfl | rfl <;> simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] <;>
                  exact hsh_ne _ _ (by omega) (by omega) (by omega)
              simp only [mkFam3B, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, mem_if_singleton]
              simp [bR, hx_not_B, hx_free, hxm, hR_ne_L]
            · -- Then x MUST have both prevIdx x ∈ B and nextIdx x ∈ B (internal site != m), so x ∉ S and x ∉ rhs
              have hx_both : prevIdx t hpos x ∈ mkFam3B_B t hpos m kind ∧
                  nextIdx t hpos x ∈ mkFam3B_B t hpos m kind := by
                have hor : prevIdx t hpos x ∈ mkFam3B_B t hpos m kind ∨
                    nextIdx t hpos x ∈ mkFam3B_B t hpos m kind := by tauto
                unfold mkFam3B_B at hor ⊢
                unfold mkFam3B_left at hxL
                unfold mkFam3B_right at hxR
                rcases fin3_cases kind with rfl | rfl | rfl <;>
                  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] at hor hxL hxR ⊢
                · rcases hor with (h | h | h) | (h | h | h)
                  · have hx2 : x = shiftIdx t hpos m (6 * t - 2) := by
                      have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                      rw [this]; congr 1; omega
                    subst hx2
                    exact ⟨Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)]; congr 1),
                      Or.inr (Or.inl (by rw [nextIdx_shiftIdx']; congr 1; omega))⟩
                  · exfalso; apply hxm; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, ← prevIdx_eq_shift, nextIdx_prevIdx] at this; exact this
                  · exfalso; apply hxR; have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                  · exfalso; apply hxL; have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this; exact this
                  · have hx2 : x = shiftIdx t hpos m (6 * t - 2) := by
                      have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this
                      exact this
                    subst hx2
                    exact ⟨Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)]; congr 1),
                      Or.inr (Or.inl (by rw [nextIdx_shiftIdx']; congr 1; omega))⟩
                  · exfalso; apply hxm; have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, shiftIdx_one, prevIdx_nextIdx] at this; exact this
                · rcases hor with (h | h | h) | (h | h | h)
                  · exfalso; apply hxm; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, ← prevIdx_eq_shift, nextIdx_prevIdx] at this; exact this
                  · have hx2 : x = shiftIdx t hpos m 2 := by
                      have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                    subst hx2
                    exact ⟨Or.inr (Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)])),
                      Or.inr (Or.inr (by rw [nextIdx_shiftIdx']))⟩
                  · exfalso; apply hxR; have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                  · exfalso; apply hxL; have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this; exact this
                  · exfalso; apply hxm; have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, shiftIdx_one, prevIdx_nextIdx] at this; exact this
                  · have hx2 : x = shiftIdx t hpos m 2 := by
                      have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this
                    subst hx2
                    exact ⟨Or.inr (Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)])),
                      Or.inr (Or.inr (by rw [nextIdx_shiftIdx']))⟩
                · rcases hor with (h | h | h | h) | (h | h | h | h)
                  · have hx2 : x = shiftIdx t hpos m (6 * t - 2) := by
                      have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                      rw [this]; congr 1; omega
                    subst hx2
                    exact ⟨Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)]; congr 1),
                      Or.inr (Or.inl (by rw [nextIdx_shiftIdx']; congr 1; omega))⟩
                  · exfalso; apply hxm; have := congrArg (nextIdx t hpos) h; rw [nextIdx_prevIdx, ← prevIdx_eq_shift, nextIdx_prevIdx] at this; exact this
                  · have hx2 : x = shiftIdx t hpos m 2 := by
                      have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                    subst hx2
                    exact ⟨Or.inr (Or.inr (Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)]))),
                      Or.inr (Or.inr (Or.inr (by rw [nextIdx_shiftIdx'])))⟩
                  · exfalso; apply hxR; have := congrArg (nextIdx t hpos) h; rwa [nextIdx_prevIdx, nextIdx_shiftIdx'] at this
                  · exfalso; apply hxL; have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this; exact this
                  · have hx2 : x = shiftIdx t hpos m (6 * t - 2) := by
                      have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this
                      exact this
                    subst hx2
                    exact ⟨Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)]; congr 1),
                      Or.inr (Or.inl (by rw [nextIdx_shiftIdx']; congr 1; omega))⟩
                  · exfalso; apply hxm; have := congrArg (prevIdx t hpos) h; rw [prevIdx_nextIdx, shiftIdx_one, prevIdx_nextIdx] at this; exact this
                  · have hx2 : x = shiftIdx t hpos m 2 := by
                      have := congrArg (prevIdx t hpos) h; rwa [prevIdx_nextIdx, prevIdx_shiftIdx_pos t hpos m (by omega)] at this
                    subst hx2
                    exact ⟨Or.inr (Or.inr (Or.inl (by rw [prevIdx_shiftIdx_pos t hpos m (by omega)]))),
                      Or.inr (Or.inr (Or.inr (by rw [nextIdx_shiftIdx'])))⟩
              have hx_not_S : x ∉ S := by
                intro hxS
                have hxM : x ∈ mergedInt t hpos S p :=
                  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxS, hxp1⟩,
                    by rw [hBeq]; exact hx_both.1, by rw [hBeq]; exact hx_both.2⟩
                rw [hMeq, Finset.mem_singleton] at hxM
                exact hxm hxM
              have hx_not_rhs : x ∉ mkFam3B t hpos m kind bL bR := by
                simp only [mkFam3B, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter]
                cases bL <;> cases bR <;> simp [hx_not_B, hx_free, hxm, hxL, hxR]
              simp [hx_not_S, hx_not_rhs]
  rw [hSeq]
  exact Finset.mem_image.mpr ⟨(m, kind, bL, bR), Finset.mem_univ _, rfl⟩

-- ============================================================================
-- L-lib-898 Section B5: Master Classification, Counting, and Final Theorem
-- ============================================================================

def EligibleGe3 (t : ℕ) (hpos : 0 < t) : Finset (Finset (Fin (6 * t))) :=
  (Finset.univ : Finset (Finset (Fin (6 * t)))).filter (fun S =>
    runsS t hpos S = 3 * t - 1 ∧ 3 ≤ sitesS t S 0 ∧ 3 ≤ sitesS t S 1)

lemma Vset_univ_finrank_le_one (t : ℕ) (hpos : 0 < t) :
    Module.finrank F2 (Vset t hpos Finset.univ) ≤ 1 := by
  let ev0 : Vset t hpos Finset.univ →ₗ[F2] F2 :=
    { toFun := fun x => x.1 ⟨0, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev0 := by
    intro x y hxy
    apply Subtype.ext; ext i
    have hconst : ∀ (v : Vset t hpos Finset.univ) (k : ℕ) (hk : k < 6 * t),
        v.1 ⟨k, hk⟩ = v.1 ⟨0, by omega⟩ := by
      intro v k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hstep := v.2.2 ⟨k, by omega⟩ (Finset.mem_univ _) (Finset.mem_univ _)
        have hnxt : nextIdx t hpos ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
          apply Fin.ext; dsimp [nextIdx]; exact Nat.mod_eq_of_lt hk
        rw [hnxt] at hstep
        rw [← hstep, ih (by omega)]
    rw [hconst x i.val i.isLt, hconst y i.val i.isLt]
    exact hxy
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_self] at hle

lemma runsS_pos_of_nonempty_ne_univ (t : ℕ) (hpos : 0 < t) (S : Finset (Fin (6 * t)))
    (hne : S.Nonempty) (hnu : S ≠ Finset.univ) :
    0 < runsS t hpos S := by
  by_contra h0
  have hzero : runsS t hpos S = 0 := by omega
  have hcl : ∀ i ∈ S, nextIdx t hpos i ∈ S := by
    intro i hi
    by_contra hnot
    have hmem : i ∈ S.filter (fun x => nextIdx t hpos x ∉ S) := Finset.mem_filter.mpr ⟨hi, hnot⟩
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    unfold runsS at hzero; omega
  rcases hne with ⟨i0, hi0⟩
  have hstep : ∀ k : ℕ, shiftIdx t hpos i0 k ∈ S := by
    intro k
    induction k with
    | zero => simpa [shiftIdx_zero] using hi0
    | succ k ih =>
      rw [← nextIdx_shiftIdx']; exact hcl _ ih
  apply hnu
  ext y; simp only [Finset.mem_univ, iff_true]
  let d : ℕ := (y.val + 6 * t - i0.val) % (6 * t)
  have hsh : shiftIdx t hpos i0 d = y := by
    apply Fin.ext; dsimp [shiftIdx, d]
    have := i0.isLt; have := y.isLt
    by_cases hle : i0.val ≤ y.val
    · have h1 : (y.val + 6 * t - i0.val) % (6 * t) = y.val - i0.val := by
        rw [show y.val + 6 * t - i0.val = (y.val - i0.val) + 6 * t by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1, show i0.val + (y.val - i0.val) = y.val by omega, Nat.mod_eq_of_lt (by omega)]
    · have h1 : (y.val + 6 * t - i0.val) % (6 * t) = y.val + 6 * t - i0.val :=
        Nat.mod_eq_of_lt (by omega)
      rw [h1, show i0.val + (y.val + 6 * t - i0.val) = y.val + 6 * t by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [← hsh]; exact hstep d

lemma layer_classify (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t)
    (U : Submodule F2 (Fin (6 * t) → F2))
    (hg : goodP t hpos U)
    (hs0 : 0 < sitesS t (suppU t U) 0) (hs1 : 0 < sitesS t (suppU t U) 1)
    (hfrU : Module.finrank F2 U = 3 * t - 5) :
    U = GoodMax t hpos (suppU t U) ∧
    ((runsS t hpos (suppU t U) = 3 * t - 1 ∧ suppU t U ∈ EligibleGe3 t hpos) ∨
     (runsS t hpos (suppU t U) = 3 * t - 2 ∧ suppU t U ∈ Fam3ASet t hpos ∪ Fam3BSet t hpos) ∨
     (runsS t hpos (suppU t U) = 3 * t - 3 ∧ suppU t U ∈ Fam2Set t hpos)) := by
  let S := suppU t U
  have hleGM : U ≤ GoodMax t hpos S := good_le_GoodMax t hpos hg
  have hsuppGM : suppU t (GoodMax t hpos S) = S := (exists_good_supp_iff t hpos S).mp ⟨U, hg, rfl⟩
  have hfrGM_ge : 3 * t - 5 ≤ Module.finrank F2 (GoodMax t hpos S) := by
    rw [← hfrU]; exact Submodule.finrank_mono hleGM
  have hne : S.Nonempty := by
    rcases Finset.card_pos.mp hs0 with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).1⟩
  have hnu : S ≠ Finset.univ := by
    intro huniv
    have h1 := Vset_univ_finrank_le_one t hpos
    have h2 : Module.finrank F2 (GoodMax t hpos S) ≤ Module.finrank F2 (Vset t hpos Finset.univ) := by
      rw [huniv]; exact Submodule.finrank_mono inf_le_left
    omega
  have hruns_pos : 0 < runsS t hpos S := runsS_pos_of_nonempty_ne_univ t hpos S hne hnu
  let p : ℕ := if sitesS t S 0 ≤ sitesS t S 1 then 0 else 1
  have hp : p = 0 ∨ p = 1 := by dsimp [p]; split_ifs <;> simp
  have hBpos : 0 < (laneSub t S p).card := by
    rw [laneSub_card_eq_sites]; dsimp [p]; split_ifs <;> omega
  have hBsmaller : (laneSub t S p).card ≤ (laneSub t S (1 - p)).card := by
    rw [laneSub_card_eq_sites, laneSub_card_eq_sites]
    by_cases hle : sitesS t S 0 ≤ sitesS t S 1 <;> simp [p, hle] <;> omega
  have hBlt : (laneSub t S p).card < 3 * t := by
    by_contra hge
    have hB_le : (laneSub t S p).card ≤ 3 * t := by
      have := Finset.card_le_card (laneSub_subset_laneSet t S p)
      rwa [card_laneSet t p hp] at this
    have hA_le : (laneSub t S (1 - p)).card ≤ 3 * t := by
      have := Finset.card_le_card (laneSub_subset_laneSet t S (1 - p))
      rwa [card_laneSet t (1 - p) (by omega)] at this
    have hB_eq : laneSub t S p = laneSet t p :=
      Finset.eq_of_subset_of_card_le (laneSub_subset_laneSet t S p)
        (by rw [card_laneSet t p hp]; omega)
    have hA_eq : laneSub t S (1 - p) = laneSet t (1 - p) :=
      Finset.eq_of_subset_of_card_le (laneSub_subset_laneSet t S (1 - p))
        (by rw [card_laneSet t (1 - p) (by omega)]; omega)
    apply hnu
    ext x; simp only [Finset.mem_univ, iff_true]
    by_cases hxp : x.val % 2 = p
    · have : x ∈ laneSet t p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp⟩
      rw [← hB_eq] at this; exact (Finset.mem_filter.mp this).1
    · have : x ∈ laneSet t (1 - p) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      rw [← hA_eq] at this; exact (Finset.mem_filter.mp this).1
  have hrF := rFree_eq_two t hpos ht S p hp hruns_pos hfrGM_ge hBpos hBlt hBsmaller
  have hs_pos : 1 ≤ blocksB t hpos S p := blocksB_pos_of_lt t hpos S p hp hBpos hBlt
  have hrB_le := rB_le_two t hpos S p
  have hrB_cases : rB t hpos S p = 0 ∨ rB t hpos S p = 1 ∨ rB t hpos S p = 2 := by omega
  rcases hrB_cases with hrB0 | hrB1 | hrB2
  · have hmem2 : S ∈ Fam2Set t hpos :=
      classify_rB_zero t hpos ht S p hp hBpos hBlt hrB0 (by omega)
    rcases Finset.mem_image.mp hmem2 with ⟨⟨j, bL, bR⟩, _, hSeq⟩
    have hpr := mkFam2_props t hpos ht j bL bR
    rw [hSeq] at hpr
    have hUeq : U = GoodMax t hpos S := Submodule.eq_of_le_of_finrank_eq hleGM (by omega)
    exact ⟨hUeq, Or.inr (Or.inr ⟨hpr.2.2.1, hmem2⟩)⟩
  · have hmem3 : S ∈ Fam3ASet t hpos ∪ Fam3BSet t hpos := by
      by_cases hM0 : (mergedInt t hpos S p).card = 0
      · exact Finset.mem_union_left _ (classify_rB_one_M0 t hpos ht S p hp hBpos hBlt hrB1 hM0 hsuppGM (by omega))
      · exact Finset.mem_union_right _ (classify_rB_one_M1 t hpos ht S p hp hBpos hBlt hrB1 (by omega) hsuppGM (by omega))
    have hruns_fr : runsS t hpos S = 3 * t - 2 ∧ Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
      rcases Finset.mem_union.mp hmem3 with hA | hB
      · rcases Finset.mem_image.mp hA with ⟨⟨⟨r, ab⟩, b1, b2, b3, b4⟩, hxA, hSeq⟩
        have hab : ab.1.val < ab.2.val :=
          (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp hxA).1).2).2
        have hpr := mkFam3A_props t hpos ht r ab hab b1 b2 b3 b4
        rw [hSeq] at hpr; exact ⟨hpr.2.2.1, hpr.2.2.2.2⟩
      · rcases Finset.mem_image.mp hB with ⟨⟨m, k, bL, bR⟩, _, hSeq⟩
        have hpr := mkFam3B_props t hpos ht m k bL bR
        rw [hSeq] at hpr; exact ⟨hpr.2.2.2.1, hpr.2.2.2.2.2⟩
    have hUeq : U = GoodMax t hpos S := Submodule.eq_of_le_of_finrank_eq hleGM (by omega)
    exact ⟨hUeq, Or.inr (Or.inl ⟨hruns_fr.1, hmem3⟩)⟩
  · have hruns1 : runsS t hpos S = 3 * t - 1 := by
      have hid := runsS_identity t hpos S p hp; omega
    have hmp := main_parts t hpos (by omega) S ⟨hruns1, hs0, hs1⟩
    have hge3 : 3 ≤ sitesS t S 0 ∧ 3 ≤ sitesS t S 1 := hmp.1.mp ⟨U, hg, rfl⟩
    have hfrGM : Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5 := by
      have hle5 := (hmp.2 hge3).2 (GoodMax t hpos S) (GoodMax_good t hpos S) hsuppGM
      omega
    have hUeq : U = GoodMax t hpos S := Submodule.eq_of_le_of_finrank_eq hleGM (by omega)
    exact ⟨hUeq, Or.inl ⟨hruns1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hruns1, hge3.1, hge3.2⟩⟩⟩

open Classical in
lemma L_lib_898_main (t : ℕ) (hpos : 0 < t) (ht : 4 ≤ t) :
    letI : Fintype (Submodule F2 (Fin (6 * t) → F2)) := Fintype.ofFinite _
    let layer := (Finset.univ : Finset (Submodule F2 (Fin (6 * t) → F2))).filter (fun U =>
      goodP t hpos U ∧ 0 < sitesS t (suppU t U) 0 ∧ 0 < sitesS t (suppU t U) 1 ∧
      Module.finrank F2 U = 3 * t - 5)
    layer.card = 12 * t * (7 * t - 1) ∧
    ∀ c : ℕ, (layer.filter (fun U => runsS t hpos (suppU t U) = c)).card =
      if c = 3 * t - 1 then 6 * t * (6 * t - 10)
      else if c = 3 * t - 2 then 12 * (6 * t) + 96 * Nat.choose t 2
      else if c = 3 * t - 3 then 4 * (6 * t)
      else 0 := by
  letI : Fintype (Submodule F2 (Fin (6 * t) → F2)) := Fintype.ofFinite _
  let layer := (Finset.univ : Finset (Submodule F2 (Fin (6 * t) → F2))).filter (fun U =>
    goodP t hpos U ∧ 0 < sitesS t (suppU t U) 0 ∧ 0 < sitesS t (suppU t U) 1 ∧
    Module.finrank F2 U = 3 * t - 5)
  -- Helper bijection between a stratum of layer and a support set T
  have hbij_stratum : ∀ (c : ℕ) (T : Finset (Finset (Fin (6 * t)))),
      (∀ U ∈ layer, runsS t hpos (suppU t U) = c → U = GoodMax t hpos (suppU t U) ∧ suppU t U ∈ T) →
      (∀ S ∈ T, runsS t hpos S = c ∧ 0 < sitesS t S 0 ∧ 0 < sitesS t S 1 ∧
        suppU t (GoodMax t hpos S) = S ∧ Module.finrank F2 (GoodMax t hpos S) = 3 * t - 5) →
      (layer.filter (fun U => runsS t hpos (suppU t U) = c)).card = T.card := by
    intro c T hfwd hbwd
    refine Finset.card_bij (fun U _ => suppU t U) ?_ ?_ ?_
    · intro U hU
      rcases Finset.mem_filter.mp hU with ⟨hUL, hrc⟩
      exact (hfwd U hUL hrc).2
    · intro U1 hU1 U2 hU2 hseq
      rcases Finset.mem_filter.mp hU1 with ⟨hU1L, hr1⟩
      rcases Finset.mem_filter.mp hU2 with ⟨hU2L, hr2⟩
      rw [(hfwd U1 hU1L hr1).1, (hfwd U2 hU2L hr2).1, hseq]
    · intro S hS
      rcases hbwd S hS with ⟨hrc, hs0, hs1, hsupp, hfr⟩
      refine ⟨GoodMax t hpos S, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, GoodMax_good t hpos S, by rw [hsupp]; exact hs0,
         by rw [hsupp]; exact hs1, hfr⟩, by rw [hsupp]; exact hrc⟩, hsupp⟩
  have hstrata : ∀ c : ℕ, (layer.filter (fun U => runsS t hpos (suppU t U) = c)).card =
      if c = 3 * t - 1 then 6 * t * (6 * t - 10)
      else if c = 3 * t - 2 then 12 * (6 * t) + 96 * Nat.choose t 2
      else if c = 3 * t - 3 then 4 * (6 * t)
      else 0 := by
    intro c
    by_cases hc1 : c = 3 * t - 1
    · subst hc1
      rw [if_pos rfl]
      rw [hbij_stratum (3 * t - 1) (EligibleGe3 t hpos)]
      · exact card_eligible_ge3 t hpos (by omega)
      · intro U hUL hrc
        rcases (Finset.mem_filter.mp hUL).2 with ⟨hg, hs0, hs1, hfr⟩
        rcases layer_classify t hpos ht U hg hs0 hs1 hfr with ⟨hUeq, h1 | h2 | h3⟩
        · exact ⟨hUeq, h1.2⟩
        · omega
        · omega
      · intro S hS
        rcases (Finset.mem_filter.mp hS).2 with ⟨hr, hs0, hs1⟩
        have hmp := main_parts t hpos (by omega) S ⟨hr, by omega, by omega⟩
        have hsupp : suppU t (GoodMax t hpos S) = S :=
          (exists_good_supp_iff t hpos S).mp (hmp.1.mpr ⟨hs0, hs1⟩)
        rcases (hmp.2 ⟨hs0, hs1⟩).1 with ⟨U0, hg0, hsU0, hfr0⟩
        have hle0 : U0 ≤ GoodMax t hpos S := hsU0 ▸ good_le_GoodMax t hpos hg0
        have hge5 : 3 * t - 5 ≤ Module.finrank F2 (GoodMax t hpos S) := by
          rw [← hfr0]; exact Submodule.finrank_mono hle0
        have hle5 := (hmp.2 ⟨hs0, hs1⟩).2 (GoodMax t hpos S) (GoodMax_good t hpos S) hsupp
        exact ⟨hr, by omega, by omega, hsupp, by omega⟩
    · rw [if_neg hc1]
      by_cases hc2 : c = 3 * t - 2
      · subst hc2
        rw [if_pos rfl]
        rw [hbij_stratum (3 * t - 2) (Fam3ASet t hpos ∪ Fam3BSet t hpos)]
        · rw [Finset.card_union_of_disjoint (disjoint_Fam3A_Fam3B t hpos ht),
            card_Fam3ASet t hpos ht, card_Fam3BSet t hpos ht, Nat.add_comm]
        · intro U hUL hrc
          rcases (Finset.mem_filter.mp hUL).2 with ⟨hg, hs0, hs1, hfr⟩
          rcases layer_classify t hpos ht U hg hs0 hs1 hfr with ⟨hUeq, h1 | h2 | h3⟩
          · omega
          · exact ⟨hUeq, h2.2⟩
          · omega
        · intro S hS
          rcases Finset.mem_union.mp hS with hA | hB
          · rcases Finset.mem_image.mp hA with ⟨⟨⟨r, ab⟩, b1, b2, b3, b4⟩, hxA, rfl⟩
            have hab : ab.1.val < ab.2.val :=
              (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp hxA).1).2).2
            have hpr := mkFam3A_props t hpos ht r ab hab b1 b2 b3 b4
            have h1 := hpr.1; have h2 := hpr.2.1
            have hpos01 := sites_pos_of_pair t (mkFam3A t hpos r ab b1 b2 b3 b4) (p := r.val % 2)
              (by omega) (by omega) (by omega)
            exact ⟨hpr.2.2.1, hpos01.1, hpos01.2, hpr.2.2.2.1, hpr.2.2.2.2⟩
          · rcases Finset.mem_image.mp hB with ⟨⟨m, k, bL, bR⟩, _, rfl⟩
            have hpr := mkFam3B_props t hpos ht m k bL bR
            have h1 := hpr.1; have h2 := hpr.2.1
            have hpos01 := sites_pos_of_pair t (mkFam3B t hpos m k bL bR) (p := 1 - m.val % 2)
              (by omega) (by split_ifs at h1 <;> omega) (by omega)
            exact ⟨hpr.2.2.2.1, hpos01.1, hpos01.2, hpr.2.2.2.2.1, hpr.2.2.2.2.2⟩
      · rw [if_neg hc2]
        by_cases hc3 : c = 3 * t - 3
        · subst hc3
          rw [if_pos rfl]
          rw [hbij_stratum (3 * t - 3) (Fam2Set t hpos)]
          · exact card_Fam2Set t hpos ht
          · intro U hUL hrc
            rcases (Finset.mem_filter.mp hUL).2 with ⟨hg, hs0, hs1, hfr⟩
            rcases layer_classify t hpos ht U hg hs0 hs1 hfr with ⟨hUeq, h1 | h2 | h3⟩
            · omega
            · omega
            · exact ⟨hUeq, h3.2⟩
          · intro S hS
            rcases Finset.mem_image.mp hS with ⟨⟨j, bL, bR⟩, _, rfl⟩
            have hpr := mkFam2_props t hpos ht j bL bR
            have h1 := hpr.1; have h2 := hpr.2.1
            have hpos01 := sites_pos_of_pair t (mkFam2 t hpos j bL bR) (p := j.val % 2)
              (by omega) (by omega) (by omega)
            exact ⟨hpr.2.2.1, hpos01.1, hpos01.2, hpr.2.2.2.1, hpr.2.2.2.2⟩
        · rw [if_neg hc3]
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro U hU
          rcases Finset.mem_filter.mp hU with ⟨hUL, hrc⟩
          rcases (Finset.mem_filter.mp hUL).2 with ⟨hg, hs0, hs1, hfr⟩
          rcases layer_classify t hpos ht U hg hs0 hs1 hfr with ⟨_, h1 | h2 | h3⟩
          · exact hc1 (hrc.symm.trans h1.1)
          · exact hc2 (hrc.symm.trans h2.1)
          · exact hc3 (hrc.symm.trans h3.1)
  refine ⟨?_, hstrata⟩
  let L1 := layer.filter (fun U => runsS t hpos (suppU t U) = 3 * t - 1)
  let L2 := layer.filter (fun U => runsS t hpos (suppU t U) = 3 * t - 2)
  let L3 := layer.filter (fun U => runsS t hpos (suppU t U) = 3 * t - 3)
  have hd12 : Disjoint L1 L2 := by
    rw [Finset.disjoint_left]; intro U h1 h2
    have a := (Finset.mem_filter.mp h1).2; have b := (Finset.mem_filter.mp h2).2; omega
  have hd123 : Disjoint (L1 ∪ L2) L3 := by
    rw [Finset.disjoint_left]; intro U h1 h2
    have c := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · have a := (Finset.mem_filter.mp h1).2; omega
    · have b := (Finset.mem_filter.mp h1).2; omega
  have hun : (L1 ∪ L2) ∪ L3 = layer := by
    ext U; simp only [L1, L2, L3, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro hUL
      rcases (Finset.mem_filter.mp hUL).2 with ⟨hg, hs0, hs1, hfr⟩
      rcases layer_classify t hpos ht U hg hs0 hs1 hfr with ⟨_, h1 | h2 | h3⟩
      · exact Or.inl (Or.inl ⟨hUL, h1.1⟩)
      · exact Or.inl (Or.inr ⟨hUL, h2.1⟩)
      · exact Or.inr ⟨hUL, h3.1⟩
  have htot : layer.card = L1.card + L2.card + L3.card := by
    rw [← hun, Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12]
  have hc1 := hstrata (3 * t - 1)
  have hc2 := hstrata (3 * t - 2)
  have hc3 := hstrata (3 * t - 3)
  rw [if_pos rfl] at hc1
  rw [if_neg (by omega), if_pos rfl] at hc2
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl] at hc3
  rw [htot, hc1, hc2, hc3]
  have hch : 96 * Nat.choose t 2 = 48 * (t * (t - 1)) := by
    rw [Nat.choose_two_right]
    have hmul : 2 * (t * (t - 1) / 2) = t * (t - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self t).two_dvd
    omega
  rw [hch]
  zify [(by omega : 10 ≤ 6 * t), (by omega : 1 ≤ t), (by omega : 1 ≤ 7 * t)]
  ring

end PEqualNP.Outside.L_lib_898

theorem PEqualNP.Outside.L_lib_898 :
    ∀ (t : ℕ) (hpos : 0 < t), 4 ≤ t →
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
      let spaces := (Finset.univ : Finset (Submodule F W)).filter good
      let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
      let runs := fun S : Finset (Fin n) =>
        (S.filter (fun i => next i ∉ S)).card
      let layer := mixed.filter (fun U : Submodule F W => Module.finrank F U = a-5)
      layer.card = 12*t*(7*t-1) ∧
        ∀ c : ℕ, (layer.filter (fun U => runs (supp U) = c)).card =
          if c = a-1 then n*(n-10)
          else if c = a-2 then 12*n + 96*Nat.choose t 2
          else if c = a-3 then 4*n
          else 0 := by
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
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
  let runs := fun S : Finset (Fin n) =>
    (S.filter (fun i => next i ∉ S)).card
  let layer := mixed.filter (fun U : Submodule F W => Module.finrank F U = a - 5)
  have hh_eq : ∀ i b, h i b = PEqualNP.Outside.L_lib_898.hFn t i b := by
    intro i b
    dsimp only [h, PEqualNP.Outside.L_lib_898.hFn]
    by_cases hp : i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp]
  have hgood_iff : ∀ U : Submodule F W, good U ↔ PEqualNP.Outside.L_lib_898.goodP t hpos U := by
    intro U
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun x hx b => by simpa [hh_eq] using h1 x hx b, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun x hx b => by simpa [hh_eq] using h1 x hx b, h2⟩
  have hsupp_eq : ∀ U : Submodule F W, supp U = PEqualNP.Outside.L_lib_898.suppU t U := by
    intro U; ext i; simp only [supp, PEqualNP.Outside.L_lib_898.suppU, Finset.mem_filter,
      Finset.mem_univ, true_and]; exact Iff.rfl
  have hsites_eq : ∀ (S : Finset (Fin n)) (p : ℕ),
      sites S p = PEqualNP.Outside.L_lib_898.sitesS t S p := by
    intro S p; unfold sites PEqualNP.Outside.L_lib_898.sitesS
    congr 1; ext i; simp only [Finset.mem_filter]
  have hruns_eq : ∀ S : Finset (Fin n),
      runs S = PEqualNP.Outside.L_lib_898.runsS t hpos S := by
    intro S; unfold runs PEqualNP.Outside.L_lib_898.runsS
    congr 1; ext i; simp only [Finset.mem_filter]; exact Iff.rfl
  have hU_mem : ∀ U : Submodule F W, U ∈ layer ↔
      PEqualNP.Outside.L_lib_898.goodP t hpos U ∧
      0 < PEqualNP.Outside.L_lib_898.sitesS t (PEqualNP.Outside.L_lib_898.suppU t U) 0 ∧
      0 < PEqualNP.Outside.L_lib_898.sitesS t (PEqualNP.Outside.L_lib_898.suppU t U) 1 ∧
      Module.finrank F U = 3 * t - 5 := by
    intro U
    dsimp only [layer, mixed, spaces]
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    rw [hgood_iff U, ← hsupp_eq U, ← hsites_eq (supp U) 0, ← hsites_eq (supp U) 1]
    exact ⟨fun h => ⟨h.1.1.2, h.1.2.1, h.1.2.2, h.2⟩,
      fun h => ⟨⟨⟨Finset.mem_univ _, h.1⟩, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩
  have hmain := PEqualNP.Outside.L_lib_898.L_lib_898_main t hpos ht
  refine ⟨?_, fun c => ?_⟩
  · rw [← hmain.1]
    refine Finset.card_bij (fun U _ => U) ?_ (fun _ _ _ _ h => h) ?_
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hU_mem U).mp hU
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      exact ⟨U, (hU_mem U).mpr hU, rfl⟩
  · have hite : (if c = a - 1 then n * (n - 10)
        else if c = a - 2 then 12 * n + 96 * Nat.choose t 2
        else if c = a - 3 then 4 * n
        else 0) =
        @ite ℕ (c = 3 * t - 1) (Nat.decEq _ _) (6 * t * (6 * t - 10))
          (@ite ℕ (c = 3 * t - 2) (Nat.decEq _ _) (12 * (6 * t) + 96 * Nat.choose t 2)
            (@ite ℕ (c = 3 * t - 3) (Nat.decEq _ _) (4 * (6 * t)) 0)) := by
      by_cases h1 : c = 3 * t - 1
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : c = 3 * t - 2
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          by_cases h3 : c = 3 * t - 3
          · rw [if_pos h3, if_pos h3]
          · rw [if_neg h3, if_neg h3]
    rw [hite, ← hmain.2 c]
    refine Finset.card_bij (fun U _ => U) ?_ (fun _ _ _ _ h => h) ?_
    · intro U hU
      rw [Finset.mem_filter] at hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(hU_mem U).mp hU.1, ?_⟩
      rw [← hsupp_eq U, ← hruns_eq (supp U)]; exact hU.2
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      refine ⟨U, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨(hU_mem U).mpr hU.1, ?_⟩
      change runs (supp U) = c
      rw [hruns_eq (supp U), hsupp_eq U]; exact hU.2

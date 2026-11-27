import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_668_aux

open scoped Classical

abbrev K := ZMod 2
abbrev V (r : ℕ) := Fin r → K
abbrev W (r : ℕ) := V r → V r

lemma add_self_bit (a : K) : a + a = 0 := by
  fin_cases a <;> decide

lemma add_self_vec {r : ℕ} (a : V r) : a + a = 0 := by
  ext j
  exact add_self_bit (a j)

lemma flip_add {r : ℕ} {a b c : V r} : a + b = c ↔ b = a + c := by
  constructor <;> intro h
  · rw [← h, ← add_assoc, add_self_vec, zero_add]
  · rw [h, ← add_assoc, add_self_vec, zero_add]

lemma card_vec (r : ℕ) : Fintype.card (V r) = 2 ^ r := by
  simp [V, K, ZMod.card]

def dot {r : ℕ} (u v : V r) : K := ∑ j, u j * v j

def dotLeft {r : ℕ} (v : V r) : V r →ₗ[K] K where
  toFun u := dot u v
  map_add' x y := by simp [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

def dotRight {r : ℕ} (u : V r) : V r →ₗ[K] K where
  toFun v := dot u v
  map_add' x y := by simp [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

noncomputable def normalSet {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) : Finset (V r) := by
  classical
  exact Finset.univ.filter (fun n => ∀ x y, dot n (p x + tags x) = dot n (p y + tags y))

noncomputable def deficiency {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) : ℕ :=
  Nat.log 2 (normalSet tags p).card

lemma mem_normalSet {r : ℕ} {tags : V r → V r} {p : Equiv.Perm (V r)} {n : V r} :
    n ∈ normalSet tags p ↔ ∀ x y, dot n (p x + tags x) = dot n (p y + tags y) := by
  classical
  simp [normalSet]

lemma zero_mem_normalSet {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) :
    0 ∈ normalSet tags p := by
  apply mem_normalSet.mpr
  intro x y
  simp [dot]

def constantNormals {r : ℕ} (a : V r → V r) : Submodule K (V r) := by
  refine { carrier := {n | ∀ x y, dot n (a x) = dot n (a y)}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }
  · intro u v hu hv x y
    change dotLeft (a x) (u + v) = dotLeft (a y) (u + v)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (hu x y) (hv x y)
  · simp [dot]
  · intro c n hn x y
    change dotLeft (a x) (c • n) = dotLeft (a y) (c • n)
    rw [map_smul, map_smul]
    exact congrArg (c • ·) (hn x y)

lemma normalSet_card_rank {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) :
    (normalSet tags p).card = 2 ^ Module.finrank K (constantNormals (fun x => p x + tags x)) := by
  classical
  let N := constantNormals (fun x => p x + tags x)
  let : Fintype N := Fintype.ofFinite _
  calc
    (normalSet tags p).card = Fintype.card N := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun n => mem_normalSet)
    _ = _ := by rw [Module.card_eq_pow_finrank (K := K) (V := N), ZMod.card]

lemma deficiency_rank {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) :
    deficiency tags p = Module.finrank K (constantNormals (fun x => p x + tags x)) := by
  rw [deficiency, normalSet_card_rank, Nat.log_pow (by decide)]

lemma normalSet_card_deficiency {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) :
    (normalSet tags p).card = 2 ^ deficiency tags p := by
  rw [normalSet_card_rank, deficiency_rank]

lemma deficiency_le {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) :
    deficiency tags p ≤ r := by
  rw [deficiency_rank]
  exact (Submodule.finrank_le _).trans (le_of_eq (by simp [V, Module.finrank_fintype_fun_eq_card]))

lemma sum_linear_translate_zero {r : ℕ} {U : Type*} [AddCommGroup U] [Module K U]
    (L : V r →ₗ[K] U) (hn : ¬ Function.Injective L) (g : U → K) :
    ∑ a : V r, g (L a) = 0 := by
  classical
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hn
  let z := x + y
  have hz : z ≠ 0 := by
    intro h
    have h' := flip_add.mp (show x + y = 0 from h)
    exact hne (by simpa using h'.symm)
  have hLz : L z = 0 := by
    change L (x + y) = 0
    rw [map_add, hxy]
    calc
      L y + L y = L (y + y) := (map_add L _ _).symm
      _ = 0 := by rw [add_self_vec, map_zero]
  apply Finset.sum_involution (fun a _ => a + z)
  · intro a _
    rw [map_add, hLz, add_zero, add_self_bit]
  · intro a _ _ ha
    exact hz (add_left_cancel (ha.trans (add_zero a).symm))
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    rw [add_assoc, add_self_vec, add_zero]

lemma card_bits {A : Type*} [Fintype A] [DecidableEq A] : Fintype.card (A → K) = 2 ^ Fintype.card A := by
  rw [Fintype.card_fun, ZMod.card]

lemma sum_linear_affine_const {r : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (L : V r →ₗ[K] (A → K)) (h : Fintype.card A ≤ r) (b : A → K) (g : (A → K) → K) :
    ∑ a : V r, g (L a + b) = ∑ a : V r, g (L a) := by
  classical
  by_cases hi : Function.Injective L
  · have h₁ := Fintype.card_le_of_injective _ hi
    have h₂ : Fintype.card (A → K) ≤ Fintype.card (V r) := by
      rw [card_bits (A := A), card_vec]
      exact Nat.pow_le_pow_right (by decide) h
    have hb : Function.Bijective L := (Fintype.bijective_iff_injective_and_card L).2
      ⟨hi, Nat.le_antisymm h₁ h₂⟩
    let e := Equiv.ofBijective L hb
    calc
      (∑ a : V r, g (L a + b)) = ∑ u : A → K, g (u + b) :=
        Equiv.sum_comp e (fun u => g (u + b))
      _ = ∑ u : A → K, g u := Equiv.sum_comp (Equiv.addRight b) g
      _ = _ := (Equiv.sum_comp e g).symm
  · rw [sum_linear_translate_zero L hi (fun u => g (u + b)), sum_linear_translate_zero L hi g]

lemma sum_linear_affine_zero {r : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (L : V r →ₗ[K] (A → K)) (h : Fintype.card A < r) (b : A → K) (g : (A → K) → K) :
    ∑ a : V r, g (L a + b) = 0 := by
  apply sum_linear_translate_zero L _ (fun u => g (u + b))
  intro hi
  have h₁ := Fintype.card_le_of_injective _ hi
  rw [card_vec, card_bits] at h₁
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide) h)) h₁

def Low {r : ℕ} (f : W r → K) : Prop :=
  ∃ T : Finset (Finset (V r × Fin r)),
    (∀ mon ∈ T, mon.card < r) ∧ ∀ raw, f raw = ∑ mon ∈ T, ∏ j ∈ mon, raw j.1 j.2

def lineWord {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (base : W r) (a : V r) : W r :=
  fun i => (lin i).symm a + base i

def factorMap {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (mon : Finset (V r × Fin r)) :
    V r →ₗ[K] (mon → K) :=
  LinearMap.pi (fun j => (LinearMap.proj j.1.2).comp (lin j.1.1).symm.toLinearMap)

lemma low_parity {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (base : W r) (f : W r → K)
    (hf : Low f) : ∑ a : V r, f (lineWord lin base a) = 0 := by
  classical
  obtain ⟨T, hT, hf⟩ := hf
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun mon hmon => ?_
  let b : mon → K := fun j => base j.1.1 j.1.2
  calc
    (∑ a : V r, ∏ j ∈ mon, lineWord lin base a j.1 j.2) =
        ∑ a : V r, ∏ j : mon, (factorMap lin mon a + b) j := by
      apply Finset.sum_congr rfl
      intro a _
      change (∏ j ∈ mon, lineWord lin base a j.1 j.2) =
        ∏ j : mon, (fun t : V r × Fin r => lineWord lin base a t.1 t.2) j.1
      exact (Finset.prod_coe_sort mon (fun t => lineWord lin base a t.1 t.2)).symm
    _ = 0 := sum_linear_affine_zero (factorMap lin mon) (by simpa using hT mon hmon)
      b (fun u => ∏ j, u j)

def momentFactorMap {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (mon : Finset (V r × Fin r))
    (k : Fin r) : V r →ₗ[K] (Option mon → K) :=
  LinearMap.pi fun j => j.elim (LinearMap.proj k) (fun t =>
    (LinearMap.proj t.1.2).comp (lin t.1.1).symm.toLinearMap)

def momentOffset {r : ℕ} {mon : Finset (V r × Fin r)} (base : W r) : Option mon → K :=
  fun j => j.elim 0 (fun t => base t.1.1 t.1.2)

lemma moment_prod {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (base : W r)
    (mon : Finset (V r × Fin r)) (a : V r) (k : Fin r) :
    a k * (∏ j ∈ mon, lineWord lin base a j.1 j.2) =
      ∏ j : Option mon, (momentFactorMap lin mon k a + momentOffset (mon := mon) base) j := by
  classical
  rw [Fintype.prod_option]
  simp only [momentFactorMap, momentOffset, LinearMap.pi_apply, Pi.add_apply, Option.elim_none,
    Option.elim_some, LinearMap.proj_apply, add_zero, LinearMap.comp_apply, LinearEquiv.coe_coe]
  congr 1
  exact (Finset.prod_coe_sort mon (fun t => lineWord lin base a t.1 t.2)).symm

lemma low_first_coordinate {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (base : W r) (f : W r → K)
    (hf : Low f) (k : Fin r) :
    ∑ a : V r, a k * f (lineWord lin base a) = ∑ a : V r, a k * f (lineWord lin 0 a) := by
  classical
  obtain ⟨T, hT, hf⟩ := hf
  simp only [hf, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun mon hmon => ?_
  simp_rw [moment_prod]
  have hcard : Fintype.card (Option mon) ≤ r := by
    simpa using hT mon hmon
  have hz : (momentOffset (mon := mon) (0 : W r)) = 0 := by
    ext j
    cases j <;> rfl
  rw [sum_linear_affine_const (momentFactorMap lin mon k) hcard (momentOffset base)
      (fun u => ∏ j, u j), hz]
  simp only [add_zero]

def firstMoment {r : ℕ} (e : V r → K) : V r := ∑ a : V r, e a • a

lemma firstMoment_apply {r : ℕ} (e : V r → K) (k : Fin r) :
    firstMoment e k = ∑ a : V r, a k * e a := by
  simp only [firstMoment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

lemma firstMoment_dot {r : ℕ} (e : V r → K) (n : V r) :
    dot n (firstMoment e) = ∑ a : V r, e a * dot n a := by
  change dotRight n (∑ a : V r, e a • a) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => (dotRight n).map_smul (e a) a

def enc {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off : W r) (w : W r) : W r :=
  fun i => lin i (w i) + off i

def raw {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off : W r) (p : W r) : W r :=
  fun i => (lin i).symm (p i - off i)

lemma enc_raw {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off p : W r) :
    enc lin off (raw lin off p) = p := by
  ext i k
  simp [enc, raw]

lemma raw_enc {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off w : W r) :
    raw lin off (enc lin off w) = w := by
  ext i k
  simp [enc, raw]

lemma raw_shift {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off p : W r) (a : V r) :
    raw lin off (fun i => p i + a) = lineWord lin (raw lin off p) a := by
  funext i
  simp only [raw, lineWord, ← map_add]
  congr 1
  abel

noncomputable def indicator {r : ℕ} (t w : W r) (i : V r) : K := by
  classical
  exact if w i = t i then 1 else 0

def bad {r : ℕ} (target : W r) (pred : V r → W r → K) (w : W r) : Prop :=
  ∃ i, pred i w ≠ indicator target w i

noncomputable def errBit {r : ℕ} (target : W r) (pred : V r → W r → K) (w : W r) (i : V r) : K :=
  pred i w + indicator target w i

lemma errBit_of_not_bad {r : ℕ} {target : W r} {pred : V r → W r → K} {w : W r}
    (h : ¬ bad target pred w) (i : V r) : errBit target pred w i = 0 := by
  have hi : pred i w = indicator target w i := by
    by_contra hne
    exact h ⟨i, hne⟩
  rw [errBit, hi, add_self_bit]

lemma indicator_shift {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target p : W r)
    (a i : V r) : indicator target (raw lin off (fun x => p x + a)) i =
      if a = p i + enc lin off target i then 1 else 0 := by
  classical
  unfold indicator
  congr 1
  apply propext
  rw [← flip_add]
  constructor
  · intro h
    have he := congrFun (enc_raw lin off (fun x => p x + a)) i
    simpa only [enc, h] using he.symm
  · intro h
    change (lin i).symm (p i + a - off i) = target i
    rw [h]
    simp [enc]

def tagMap {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) (i : V r) : V r :=
  enc lin off target i + firstMoment (fun a => pred i (lineWord lin 0 a))

lemma shift_err_parity {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target p : W r)
    (pred : V r → W r → K) (hp : ∀ i, Low (pred i)) (i : V r) :
    ∑ a : V r, errBit target pred (raw lin off (fun x => p x + a)) i = 1 := by
  classical
  simp only [errBit, Finset.sum_add_distrib, indicator_shift]
  simp_rw [raw_shift]
  rw [low_parity lin (raw lin off p) _ (hp i), zero_add, Finset.sum_ite_eq']
  simp

lemma shift_err_moment {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target p : W r)
    (pred : V r → W r → K) (hp : ∀ i, Low (pred i)) (i : V r) :
    firstMoment (fun a => errBit target pred (raw lin off (fun x => p x + a)) i) =
      p i + tagMap lin off target pred i := by
  classical
  ext k
  simp only [firstMoment_apply, errBit, mul_add, Finset.sum_add_distrib, indicator_shift,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, tagMap, Pi.add_apply]
  simp_rw [raw_shift]
  rw [low_first_coordinate lin (raw lin off p) _ (hp i)]
  ac_rfl

noncomputable def failedShifts {r : ℕ} (lin : V r → V r ≃ₗ[K] V r)
    (off target p : W r) (pred : V r → W r → K) : Finset (V r) := by
  classical
  exact Finset.univ.filter (fun a => bad target pred (raw lin off (fun x => p x + a)))

lemma failedShifts_lower {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) (hp : ∀ i, Low (pred i)) (p : Equiv.Perm (V r)) :
    r + 1 - deficiency (tagMap lin off target pred) p ≤ (failedShifts lin off target p pred).card := by
  classical
  let S := failedShifts lin off target p pred
  let e := fun i a => errBit target pred (raw lin off (fun x => p x + a)) i
  have he0 (i a : V r) (ha : a ∉ S) : e i a = 0 := by
    apply errBit_of_not_bad
    simpa [S, failedShifts] using ha
  have he1 (i : V r) : ∑ a : V r, e i a = 1 := shift_err_parity lin off target p pred hp i
  have hne : S.Nonempty := by
    by_contra h
    have hz : ∑ a : V r, e 0 a = 0 := Finset.sum_eq_zero fun a _ => he0 0 a (fun ha => h ⟨a, ha⟩)
    exact one_ne_zero ((he1 0).symm.trans hz)
  obtain ⟨b, hb⟩ := hne
  let L : V r →ₗ[K] ((S.erase b) → K) := LinearMap.pi fun a => dotLeft ((a : V r) + b)
  let N := constantNormals fun x => p x + tagMap lin off target pred x
  have hspan : LinearMap.ker L ≤ N := by
    intro n hn
    have hc (a : V r) (ha : a ∈ S) : dot n a = dot n b := by
      by_cases hab : a = b
      · exact congrArg (dot n) hab
      · have hn' := congrFun (LinearMap.mem_ker.mp hn) ⟨a, Finset.mem_erase.mpr ⟨hab, ha⟩⟩
        change dotRight n (a + b) = 0 at hn'
        rw [map_add] at hn'
        have hh := congrArg (· + dot n b) hn'
        change dot n a + dot n b + dot n b = 0 + dot n b at hh
        simpa [add_assoc, add_self_bit] using hh
    have hconst (i : V r) : dot n (p i + tagMap lin off target pred i) = dot n b := by
      rw [← shift_err_moment lin off target p pred hp i, firstMoment_dot]
      change ∑ a : V r, e i a * dot n a = dot n b
      calc
        (∑ a : V r, e i a * dot n a) = ∑ a : V r, e i a * dot n b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases ha : a ∈ S
          · rw [hc a ha]
          · rw [he0 i a ha, zero_mul, zero_mul]
        _ = _ := by rw [← Finset.sum_mul, he1, one_mul]
    exact fun x y => (hconst x).trans (hconst y).symm
  have hk := Submodule.finrank_mono hspan
  have hr := L.finrank_range_add_finrank_ker
  have hc : Module.finrank K (V r) = r := by simp [V, Module.finrank_fintype_fun_eq_card]
  have hm : Module.finrank K ((S.erase b) → K) = S.card - 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Finset.card_erase_of_mem hb]
  have hl : Module.finrank K (LinearMap.range L) ≤ S.card - 1 :=
    (Submodule.finrank_le _).trans (le_of_eq hm)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨b, hb⟩
  rw [hc] at hr
  rw [deficiency_rank]
  change r + 1 - Module.finrank K N ≤ S.card
  omega

noncomputable def residual {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off : W r) : Finset (W r) := by
  classical
  exact Finset.univ.filter (fun w => Function.Bijective (enc lin off w))

noncomputable def errors {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) : Finset (W r) := by
  classical
  exact (residual lin off).filter (bad target pred)

lemma mem_residual {r : ℕ} {lin : V r → V r ≃ₗ[K] V r} {off w : W r} :
    w ∈ residual lin off ↔ Function.Bijective (enc lin off w) := by
  classical
  simp [residual]

lemma residual_card {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off : W r) :
    (residual lin off).card = (2 ^ r).factorial := by
  classical
  rw [← card_vec, ← Fintype.card_perm, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun p _ => raw lin off p) ?_ ?_ ?_
  · intro p _
    exact mem_residual.mpr (by rw [enc_raw]; exact p.bijective)
  · intro p _ q _ h
    apply Equiv.ext
    intro i
    exact congrFun (by simpa only [enc_raw] using congrArg (enc lin off) h) i
  · intro w hw
    exact ⟨Equiv.ofBijective _ (mem_residual.mp hw), Finset.mem_univ _, raw_enc lin off w⟩

lemma errors_sum {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) :
    (∑ p : Equiv.Perm (V r), if bad target pred (raw lin off p) then 1 else 0 : ℕ) =
      (errors lin off target pred).card := by
  classical
  unfold errors
  rw [Finset.card_filter]
  refine Finset.sum_bij' (fun p _ => raw lin off p)
      (fun w hw => Equiv.ofBijective _ (mem_residual.mp hw)) ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact mem_residual.mpr (by rw [enc_raw]; exact p.bijective)
  · intros
    exact Finset.mem_univ _
  · intro p _
    exact Equiv.ext (congrFun (enc_raw lin off p))
  · intro w _
    exact raw_enc lin off w
  · intros
    rfl

def shiftPerm {r : ℕ} (a : V r) : Equiv.Perm (Equiv.Perm (V r)) where
  toFun p := p.trans (Equiv.addRight a)
  invFun p := p.trans (Equiv.addRight (-a))
  left_inv p := by
    apply Equiv.ext
    intro x
    change p x + a + -a = p x
    abel
  right_inv p := by
    apply Equiv.ext
    intro x
    change p x + -a + a = p x
    abel

lemma sum_failedShifts {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) :
    (∑ p : Equiv.Perm (V r), (failedShifts lin off target p pred).card) =
      2 ^ r * (errors lin off target pred).card := by
  classical
  simp only [failedShifts, Finset.card_filter]
  rw [Finset.sum_comm]
  have hh (a : V r) :
      (∑ p : Equiv.Perm (V r), if bad target pred (raw lin off (fun x => p x + a)) then 1 else 0 : ℕ) =
        (errors lin off target pred).card := by
    rw [← errors_sum lin off target pred]
    exact Equiv.sum_comp (shiftPerm a) (fun p => if bad target pred (raw lin off p) then 1 else 0)
  simp [hh]

lemma orbit_bound {r : ℕ} (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) (hp : ∀ i, Low (pred i)) :
    (∑ p : Equiv.Perm (V r), (r + 1 - deficiency (tagMap lin off target pred) p)) ≤
      2 ^ r * (errors lin off target pred).card := by
  classical
  rw [← sum_failedShifts]
  exact Finset.sum_le_sum fun p _ => failedShifts_lower lin off target pred hp p

lemma sum_filter_exchange {α β : Type*} (s : Finset α) (t : Finset β) (R : α → β → Prop) :
    (∑ a ∈ s, (t.filter (R a)).card) =
      ∑ b ∈ t, (s.filter (fun a => R a b)).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

noncomputable def nonzeroVecs (r : ℕ) : Finset (V r) := by
  classical
  exact Finset.univ.erase 0

lemma mem_nonzeroVecs {r : ℕ} {n : V r} : n ∈ nonzeroVecs r ↔ n ≠ 0 := by
  classical
  simp [nonzeroVecs]

lemma card_nonzeroVecs (r : ℕ) : (nonzeroVecs r).card = 2 ^ r - 1 := by
  classical
  simp [nonzeroVecs]

noncomputable def nonzeroNormals {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) : Finset (V r) := by
  classical
  exact (normalSet tags p).erase 0

lemma mem_nonzeroNormals {r : ℕ} {tags : V r → V r} {p : Equiv.Perm (V r)} {n : V r} :
    n ∈ nonzeroNormals tags p ↔ n ≠ 0 ∧ n ∈ normalSet tags p := by
  classical
  simp [nonzeroNormals]

lemma card_nonzeroNormals {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) :
    (nonzeroNormals tags p).card = (normalSet tags p).card - 1 := by
  classical
  exact Finset.card_erase_of_mem (zero_mem_normalSet tags p)

noncomputable def distinctPairs {α : Type*} (s : Finset α) : Finset (α × α) := by
  classical
  exact (s ×ˢ s).filter (fun p => p.1 ≠ p.2)

lemma mem_distinctPairs {α : Type*} {s : Finset α} {a b : α} :
    (a, b) ∈ distinctPairs s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  classical
  simp [distinctPairs, and_assoc]

lemma card_distinctPairs {α : Type*} (s : Finset α) :
    (distinctPairs s).card = s.card * (s.card - 1) := by
  classical
  rw [distinctPairs, Finset.card_filter, Finset.sum_product]
  calc
    (∑ a ∈ s, ∑ b ∈ s, if a ≠ b then 1 else 0 : ℕ) =
        ∑ a ∈ s, (s.card - 1) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← Finset.card_filter, ← Finset.card_erase_of_mem ha]
      congr 1
      ext b
      simp [ne_comm, and_comm]
    _ = _ := by simp

lemma sum_normal_moment {r : ℕ} (tags : V r → V r) :
    (∑ p : Equiv.Perm (V r), ((normalSet tags p).card - 1)) =
      ∑ n ∈ nonzeroVecs r,
        ((Finset.univ : Finset (Equiv.Perm (V r))).filter (fun p => n ∈ normalSet tags p)).card := by
  classical
  have he := sum_filter_exchange (Finset.univ : Finset (Equiv.Perm (V r))) (nonzeroVecs r)
    (fun p n => n ∈ normalSet tags p)
  refine Eq.trans ?_ (he.trans ?_)
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [← card_nonzeroNormals]
    apply congrArg Finset.card
    ext n
    simp [mem_nonzeroNormals, mem_nonzeroVecs]
  · refine Finset.sum_congr rfl fun n _ => ?_
    apply congrArg Finset.card
    ext p
    simp

lemma sum_pair_moment {r : ℕ} (tags : V r → V r) :
    (∑ p : Equiv.Perm (V r), ((normalSet tags p).card - 1) * ((normalSet tags p).card - 1 - 1)) =
      ∑ nm ∈ distinctPairs (nonzeroVecs r),
        ((Finset.univ : Finset (Equiv.Perm (V r))).filter
          (fun p => nm.1 ∈ normalSet tags p ∧ nm.2 ∈ normalSet tags p)).card := by
  classical
  have he := sum_filter_exchange (Finset.univ : Finset (Equiv.Perm (V r))) (distinctPairs (nonzeroVecs r))
    (fun p nm => nm.1 ∈ normalSet tags p ∧ nm.2 ∈ normalSet tags p)
  refine Eq.trans ?_ (he.trans ?_)
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [← card_nonzeroNormals, ← card_distinctPairs]
    apply congrArg Finset.card
    apply Finset.ext
    rintro ⟨n,m⟩
    simp only [mem_distinctPairs, Finset.mem_filter, mem_nonzeroVecs, mem_nonzeroNormals]
    tauto
  · refine Finset.sum_congr rfl fun nm _ => ?_
    apply congrArg Finset.card
    ext p
    simp

lemma sum_add_missing_le {α : Type*} (s : Finset α) (f : α → ℕ) (c : ℕ)
    (h : ∀ a ∈ s, f a ≤ c) {a : α} (ha : a ∈ s) (hz : f a = 0) :
    (∑ x ∈ s, f x) + c ≤ s.card * c := by
  classical
  rw [← Finset.sum_erase_add _ _ ha, hz, add_zero]
  calc
    (∑ x ∈ s.erase a, f x) + c ≤ ∑ x ∈ s.erase a, c + c :=
      Nat.add_le_add_right (Finset.sum_le_sum fun x hx => h x (Finset.mem_of_mem_erase hx)) _
    _ = s.card * c := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem ha]
      rw [← Nat.add_one_mul]
      change (s.card - 1 + 1) * c = s.card * c
      rw [Nat.sub_add_cancel (show 1 ≤ s.card from Finset.card_pos.mpr ⟨a, ha⟩)]

noncomputable section Counting

abbrev MomentFiber {α β : Type*} (f : α → β) (b : β) := {x // f x = b}

def momentNormalCount {r : ℕ} (tags : V r → V r) (n : V r) : ℕ :=
  Nat.card {p : Equiv.Perm (V r) // n ∈ normalSet tags p}

def momentPairCount {r : ℕ} (tags : V r → V r) (n m : V r) : ℕ :=
  Nat.card {p : Equiv.Perm (V r) // n ∈ normalSet tags p ∧ m ∈ normalSet tags p}

def momentBalanced {r : ℕ} (tags : V r → V r) (n : V r) : Prop :=
  ∀ b : K, Nat.card (MomentFiber (fun x => dot n (tags x)) b) = 2 ^ (r - 1)

def momentPairBalanced {r : ℕ} (tags : V r → V r) (n m : V r) : Prop :=
  ∀ b : K × K, Nat.card (MomentFiber (fun x => (dot n (tags x), dot m (tags x))) b) = 2 ^ (r - 2)

theorem momentNormalCount_eq_finset {r : ℕ} (tags : V r → V r) (n : V r) :
    momentNormalCount tags n =
      (Finset.univ.filter fun p : Equiv.Perm (V r) => n ∈ normalSet tags p).card := by
  rw [momentNormalCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem momentPairCount_eq_finset {r : ℕ} (tags : V r → V r) (n m : V r) :
    momentPairCount tags n m =
      (Finset.univ.filter fun p : Equiv.Perm (V r) =>
        n ∈ normalSet tags p ∧ m ∈ normalSet tags p).card := by
  rw [momentPairCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

private def momentRestrict {α β : Type*} {f g : α → β}
    (p : {p : Equiv.Perm α // ∀ x, f (p x) = g x}) (b : β) :
    MomentFiber g b ≃ MomentFiber f b where
  toFun x := ⟨p.1 x, (p.2 x).trans x.2⟩
  invFun y := ⟨p.1.symm y, by rw [← p.2 (p.1.symm y), Equiv.apply_symm_apply, y.2]⟩
  left_inv x := Subtype.ext (p.1.symm_apply_apply x)
  right_inv y := Subtype.ext (p.1.apply_symm_apply y)

private def momentMatchingEquiv {α β : Type*} (f g : α → β) :
    {p : Equiv.Perm α // ∀ x, f (p x) = g x} ≃
      (∀ b : β, MomentFiber g b ≃ MomentFiber f b) where
  toFun := momentRestrict
  invFun e :=
    ⟨(Equiv.sigmaFiberEquiv g).symm.trans
        ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)),
      fun x => (e (g x) ⟨x, rfl⟩).2⟩
  left_inv p := by
    apply Subtype.ext
    ext x
    rfl
  right_inv e := by
    funext b
    ext x
    rcases x with ⟨x, h⟩
    subst b
    rfl

private theorem momentMatchingCard {α β : Type*} [Finite α] [Fintype β]
    (f g : α → β) (q : ℕ) (hf : ∀ b, Nat.card (MomentFiber f b) = q) :
    Nat.card {p : Equiv.Perm α // ∀ x, f (p x) = g x} =
      if ∀ b, Nat.card (MomentFiber g b) = q then (Nat.factorial q) ^ Nat.card β else 0 := by
  classical
  by_cases h : ∀ b, Nat.card (MomentFiber g b) = q
  · rw [ite_eq_left h, Nat.card_congr (momentMatchingEquiv f g), Nat.card_pi]
    have hb (b : β) : Nat.card (MomentFiber g b ≃ MomentFiber f b) = Nat.factorial q := by
      let _ : Fintype (MomentFiber g b) := Fintype.ofFinite _
      let _ : Fintype (MomentFiber f b) := Fintype.ofFinite _
      have e : MomentFiber g b ≃ MomentFiber f b := Fintype.equivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card] using (h b).trans (hf b).symm)
      rw [Nat.card_eq_fintype_card, Fintype.card_equiv e, ← Nat.card_eq_fintype_card, h b]
    simp only [hb, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  · rw [ite_eq_right h, Nat.card_eq_zero]
    exact Or.inl ⟨fun p => h (fun b => (Nat.card_congr (momentRestrict p b)).trans (hf b))⟩

private def momentLeftSub {β : Type*} [AddCommGroup β] (c : β) : β ≃ β where
  toFun t := c - t
  invFun t := c - t
  left_inv := sub_sub_cancel c
  right_inv := sub_sub_cancel c

private theorem momentShiftedBalance {α β : Type*} [AddCommGroup β]
    (g : α → β) (c : β) (q : ℕ) :
    (∀ b, Nat.card (MomentFiber (fun x => c - g x) b) = q) ↔
      (∀ b, Nat.card (MomentFiber g b) = q) := by
  let e := momentLeftSub c
  have hc (b : β) : Nat.card (MomentFiber (fun x => c - g x) b) =
      Nat.card (MomentFiber g (e.symm b)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => e.eq_symm_apply.symm)
  constructor
  · intro h b
    simpa only [Equiv.symm_apply_apply] using (hc (e b)).symm.trans (h (e b))
  · intro h b
    exact (hc b).trans (h (e.symm b))

private def momentConstantEquiv {α β : Type*} [AddCommGroup β]
    (f g : α → β) (x₀ : α) :
    {p : Equiv.Perm α // ∀ x y, f (p x) + g x = f (p y) + g y} ≃
      (Σ c : β, {p : Equiv.Perm α // ∀ x, f (p x) = c - g x}) where
  toFun p := ⟨f (p.1 x₀) + g x₀, p.1, fun x => eq_sub_iff_add_eq.mpr (p.2 x x₀)⟩
  invFun cp := ⟨cp.2.1, fun x y =>
    (eq_sub_iff_add_eq.mp (cp.2.2 x)).trans (eq_sub_iff_add_eq.mp (cp.2.2 y)).symm⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨c, p, hp⟩
    have h := eq_sub_iff_add_eq.mp (hp x₀)
    cases h
    rfl

private theorem momentConstantCard {α β : Type*} [Finite α] [Fintype β] [AddCommGroup β]
    (f g : α → β) (x₀ : α) (q : ℕ) (hf : ∀ b, Nat.card (MomentFiber f b) = q) :
    Nat.card {p : Equiv.Perm α // ∀ x y, f (p x) + g x = f (p y) + g y} =
      if ∀ b, Nat.card (MomentFiber g b) = q then
        Nat.card β * (Nat.factorial q) ^ Nat.card β else 0 := by
  classical
  rw [Nat.card_congr (momentConstantEquiv f g x₀), Nat.card_sigma]
  simp_rw [momentMatchingCard f _ q hf, momentShiftedBalance]
  split_ifs <;> simp [Nat.card_eq_fintype_card]

private def momentDotLinear {r : ℕ} (n : V r) : V r →ₗ[K] K where
  toFun := dot n
  map_add' := by
    intro u v
    simp [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    change (∑ j, n j * (c * v j)) = c * ∑ j, n j * v j
    simp only [Finset.mul_sum, mul_left_comm]

private def momentPairLinear {r : ℕ} (n m : V r) : V r →ₗ[K] (K × K) :=
  (momentDotLinear n).prod (momentDotLinear m)

private theorem momentDotSingle {r : ℕ} (n : V r) (i : Fin r) (a : K) :
    momentDotLinear n (Pi.single i a) = n i * a :=
  dotProduct_single n a i

private theorem momentBitCases : ∀ a : K, a = 0 ∨ a = 1 := by decide

private theorem momentCoordinate {r : ℕ} {n : V r} (hn : n ≠ 0) : ∃ i, n i = 1 := by
  by_contra! h
  apply hn
  funext i
  exact (momentBitCases (n i)).resolve_right (h i)

private theorem momentDotSurjective {r : ℕ} {n : V r} (hn : n ≠ 0) :
    Function.Surjective (momentDotLinear n) := by
  obtain ⟨i, hi⟩ := momentCoordinate hn
  intro a
  exact ⟨Pi.single i a, by rw [momentDotSingle, hi, one_mul]⟩

private theorem momentPairSurjectiveOfColumn {r : ℕ} {n m : V r} {i : Fin r}
    (hi : n i = 1) (hi' : m i = 0) (hm : m ≠ 0) :
    Function.Surjective (momentPairLinear n m) := by
  obtain ⟨j, hj⟩ := momentCoordinate hm
  rintro ⟨a, b⟩
  let w : V r := Pi.single i (a - n j * b) + Pi.single j b
  refine ⟨w, Prod.ext ?_ ?_⟩
  · change momentDotLinear n (Pi.single i (a - n j * b) + Pi.single j b) = a
    simp only [map_add, momentDotSingle, hi, one_mul, sub_add_cancel]
  · change momentDotLinear m (Pi.single i (a - n j * b) + Pi.single j b) = b
    simp only [map_add, momentDotSingle, hi', hj, zero_mul, one_mul, zero_add]

private theorem momentPairSurjective {r : ℕ} {n m : V r}
    (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) : Function.Surjective (momentPairLinear n m) := by
  have h : ∃ i, n i ≠ m i := by
    by_contra! h
    exact hnm (funext h)
  obtain ⟨i, hi⟩ := h
  rcases momentBitCases (n i) with h0 | h1
  · have hm1 := (momentBitCases (m i)).resolve_left fun hm0 => hi (h0.trans hm0.symm)
    rintro ⟨a, b⟩
    obtain ⟨w, hw⟩ := momentPairSurjectiveOfColumn hm1 h0 hn (b, a)
    exact ⟨w, Prod.ext (congrArg Prod.snd hw) (congrArg Prod.fst hw)⟩
  · have hm0 := (momentBitCases (m i)).resolve_right fun hm1 => hi (h1.trans hm1.symm)
    exact momentPairSurjectiveOfColumn h1 hm0 hm

private theorem momentLinearFiberCard {r : ℕ} {B : Type*} [AddCommGroup B] [Module K B]
    (d : V r →ₗ[K] B) (hd : Function.Surjective d) (b : B) :
    Nat.card (MomentFiber d b) = 2 ^ (r - Module.finrank K B) := by
  obtain ⟨w, hw⟩ := hd b
  let e : MomentFiber d b ≃ d.ker :=
    { toFun := fun x => ⟨x.1 - w, LinearMap.mem_ker.mpr (by rw [map_sub, x.2, hw, sub_self])⟩
      invFun := fun u => ⟨u.1 + w, by rw [map_add, LinearMap.mem_ker.mp u.2, hw, zero_add]⟩
      left_inv := fun x => Subtype.ext (sub_add_cancel x.1 w)
      right_inv := fun u => Subtype.ext (add_sub_cancel_right u.1 w) }
  have h := d.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hd, finrank_top, Module.finrank_pi, Fintype.card_fin] at h
  have hk : Module.finrank K d.ker = r - Module.finrank K B := by omega
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K), Nat.card_zmod, hk]

theorem momentSingleFiberCard {r : ℕ} {n : V r} (hn : n ≠ 0) (b : K) :
    Nat.card (MomentFiber (dot n) b) = 2 ^ (r - 1) := by
  have he : (momentDotLinear n : V r → K) = dot n := rfl
  simpa only [he, CommSemiring.finrank_self] using
    momentLinearFiberCard (momentDotLinear n) (momentDotSurjective hn) b

theorem momentPairFiberCard {r : ℕ} {n m : V r} (hn : n ≠ 0) (hm : m ≠ 0)
    (hnm : n ≠ m) (b : K × K) :
    Nat.card (MomentFiber (fun v => (dot n v, dot m v)) b) = 2 ^ (r - 2) := by
  have he : (momentPairLinear n m : V r → K × K) = fun v => (dot n v, dot m v) := rfl
  simpa only [he, Module.finrank_prod, CommSemiring.finrank_self, Nat.reduceAdd] using
    momentLinearFiberCard (momentPairLinear n m) (momentPairSurjective hn hm hnm) b

private theorem momentDotAdd {r : ℕ} (n x y : V r) :
    dot n (x + y) = dot n x + dot n y := (momentDotLinear n).map_add x y

private theorem momentDotSub {r : ℕ} (n x y : V r) :
    dot n (x - y) = dot n x - dot n y := (momentDotLinear n).map_sub x y

private theorem momentDotComm {r : ℕ} (n x : V r) : dot n x = dot x n := dotProduct_comm n x

private theorem ite_decidable_irrel (p : Prop) (a b : ℕ) (d d' : Decidable p) :
    @ite ℕ p d a b = @ite ℕ p d' a b :=
  congrArg (fun t => @ite ℕ p t a b) (Subsingleton.elim d d')

theorem momentNormalCount_eq {r : ℕ} (tags : V r → V r) {n : V r} (hn : n ≠ 0) :
    momentNormalCount tags n =
      if momentBalanced tags n then 2 * (Nat.factorial (2 ^ (r - 1))) ^ 2 else 0 := by
  have e : {p : Equiv.Perm (V r) // n ∈ normalSet tags p} ≃
      {p : Equiv.Perm (V r) // ∀ x y, dot n (p x) + dot n (tags x) =
        dot n (p y) + dot n (tags y)} :=
    Equiv.subtypeEquivRight (fun _ => by simp [normalSet, momentDotAdd])
  rw [momentNormalCount, Nat.card_congr e,
    momentConstantCard (dot n) (fun x => dot n (tags x)) 0 _ (momentSingleFiberCard hn)]
  simp only [Nat.card_zmod]
  exact ite_decidable_irrel _ _ _ _ _

theorem momentNormalCount_zero_or_max {r : ℕ} (tags : V r → V r) {n : V r} (hn : n ≠ 0) :
    momentNormalCount tags n = 0 ∨
      momentNormalCount tags n = 2 * (Nat.factorial (2 ^ (r - 1))) ^ 2 := by
  rw [momentNormalCount_eq tags hn]
  split_ifs <;> simp

theorem momentNormalCount_id {r : ℕ} {n : V r} (hn : n ≠ 0) :
    momentNormalCount id n = 2 * (Nat.factorial (2 ^ (r - 1))) ^ 2 := by
  rw [momentNormalCount_eq id hn, ite_eq_left (show momentBalanced id n from momentSingleFiberCard hn)]

theorem momentPairCount_eq {r : ℕ} (tags : V r → V r) {n m : V r}
    (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) : momentPairCount tags n m =
      if momentPairBalanced tags n m then 4 * (Nat.factorial (2 ^ (r - 2))) ^ 4 else 0 := by
  let f (v : V r) : K × K := (dot n v, dot m v)
  have e : {p : Equiv.Perm (V r) // n ∈ normalSet tags p ∧ m ∈ normalSet tags p} ≃
      {p : Equiv.Perm (V r) // ∀ x y, f (p x) + f (tags x) = f (p y) + f (tags y)} :=
    Equiv.subtypeEquivRight (fun _ => by
      simp only [normalSet, Finset.mem_filter, Finset.mem_univ, true_and, momentDotAdd, f,
        Prod.mk_add_mk, Prod.mk.injEq]
      exact ⟨fun h x y => ⟨h.1 x y, h.2 x y⟩, fun h => ⟨fun x y => (h x y).1, fun x y => (h x y).2⟩⟩)
  rw [momentPairCount, Nat.card_congr e,
    momentConstantCard f (fun x => f (tags x)) 0 _ (momentPairFiberCard hn hm hnm)]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.reduceMul]
  exact ite_decidable_irrel _ _ _ _ _

theorem momentPairCount_id {r : ℕ} {n m : V r} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    momentPairCount id n m = 4 * (Nat.factorial (2 ^ (r - 2))) ^ 4 := by
  rw [momentPairCount_eq id hn hm hnm,
    ite_eq_left (show momentPairBalanced id n m from momentPairFiberCard hn hm hnm)]

private def momentSign (b : K) : ℤ := if b = 0 then 1 else -1

private theorem momentSignSum {α : Type*} [Fintype α] (f : α → K) {q : ℕ}
    (h : ∀ b, Nat.card (MomentFiber f b) = q) : ∑ x, momentSign (f x) = 0 := by
  classical
  calc
    (∑ x, momentSign (f x)) = ∑ b : K, ∑ x : MomentFiber f b, momentSign (f x) := by
      rw [← Fintype.sum_sigma']
      exact (Equiv.sigmaFiberEquiv f).sum_comp (fun x => momentSign (f x)) |>.symm
    _ = ∑ b : K, (q : ℤ) * momentSign b := by
      apply Finset.sum_congr rfl
      intro b _
      have hb (x : MomentFiber f b) : f x = b := x.2
      simp only [hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, h b]
    _ = 0 := by
      rw [show (Finset.univ : Finset K) = {0, 1} by decide]
      simp [momentSign, show (0 : K) ≠ 1 by decide]

theorem momentTags_bijective_of_all_balanced {r : ℕ} (tags : V r → V r)
    (h : ∀ n ≠ 0, momentBalanced tags n) : Function.Bijective tags := by
  classical
  have hs : Function.Surjective tags := by
    intro z
    by_contra hz
    let f (n x : V r) : ℤ := momentSign (dot n (tags x - z))
    have hx (x : V r) : (∑ n : V r, f n x) = 0 := by
      have hv : tags x - z ≠ 0 := sub_ne_zero.mpr (fun he => hz ⟨x, he⟩)
      simpa only [f, momentDotComm _ (tags x - z)] using
        momentSignSum (dot (tags x - z)) (momentSingleFiberCard hv)
    have hn (n : V r) (hne : n ≠ 0) : (∑ x : V r, f n x) = 0 := by
      let g (x : V r) := dot n (tags x) - dot n z
      have hg (b : K) : Nat.card (MomentFiber g b) = 2 ^ (r - 1) := by
        let e : MomentFiber g b ≃ MomentFiber (fun x => dot n (tags x)) (b + dot n z) :=
          Equiv.subtypeEquivRight (fun _ => sub_eq_iff_eq_add)
        exact (Nat.card_congr e).trans (h n hne (b + dot n z))
      simpa only [f, g, momentDotSub] using momentSignSum g hg
    have hsum : (∑ n : V r, ∑ x : V r, f n x) = 0 := by
      rw [Finset.sum_comm]
      simp only [hx, Finset.sum_const_zero]
    rw [Finset.sum_eq_single (0 : V r) (fun n _ hne => hn n hne) (by simp)] at hsum
    have hzero : (∑ x : V r, f (0 : V r) x) = (Fintype.card (V r) : ℤ) := by
      simp [f, momentSign, dot]
    rw [hzero] at hsum
    have hpos : 0 < Fintype.card (V r) := Fintype.card_pos
    omega
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem momentMissingNormal_of_not_bijective {r : ℕ} (tags : V r → V r)
    (h : ¬ Function.Bijective tags) : ∃ n : V r, n ≠ 0 ∧ momentNormalCount tags n = 0 := by
  by_contra! h'
  apply h
  apply momentTags_bijective_of_all_balanced
  intro n hn
  by_contra hb
  exact h' n hn ((momentNormalCount_eq tags hn).trans (ite_eq_right hb))

private theorem arithmetic_card_vec (r : ℕ) : Fintype.card (V r) = 2 ^ r := by
  simp [V, K, Fintype.card_pi, ZMod.card]

private theorem arithmetic_card_perm (r : ℕ) :
    Fintype.card (Equiv.Perm (V r)) = (2 ^ r).factorial := by
  rw [Fintype.card_perm, arithmetic_card_vec]

def normalCount {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) : ℕ :=
  (normalSet tags p).card - 1

def pairCount {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) : ℕ :=
  normalCount tags p * (normalCount tags p - 1)

private theorem arithmetic_le_pow_sub_one (d : ℕ) : d ≤ 2 ^ d - 1 :=
  Nat.le_sub_one_of_lt (Nat.lt_two_pow_self (n := d))

theorem deficiency_le_normalCount {r : ℕ} {tags : V r → V r} {p : Equiv.Perm (V r)}
    (hc : (normalSet tags p).card = 2 ^ deficiency tags p) :
    deficiency tags p ≤ normalCount tags p := by
  unfold normalCount
  rw [hc]
  exact arithmetic_le_pow_sub_one _

theorem six_normalCount_le {r : ℕ} {tags : V r → V r} {p : Equiv.Perm (V r)}
    (hc : (normalSet tags p).card = 2 ^ deficiency tags p) :
    6 * normalCount tags p ≤ 6 * deficiency tags p + pairCount tags p := by
  unfold pairCount normalCount
  rw [hc]
  generalize deficiency tags p = d
  rcases d with _ | _ | _ | d
  · decide
  · decide
  · decide
  · have hd : 8 ≤ (2 : ℕ) ^ (d + 1 + 1 + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ d + 1 + 1 + 1)
    have hm : 6 ≤ 2 ^ (d + 1 + 1 + 1) - 1 - 1 := by omega
    calc
      _ ≤ (2 ^ (d + 1 + 1 + 1) - 1) * (2 ^ (d + 1 + 1 + 1) - 1 - 1) := by
        rw [mul_comm 6]
        exact Nat.mul_le_mul_left _ hm
      _ ≤ _ := Nat.le_add_left _ _

theorem deficiency_sum_bijective {r : ℕ} (tags : V r → V r)
    (ht : Function.Bijective tags) :
    (∑ p : Equiv.Perm (V r), deficiency tags p) =
      ∑ p : Equiv.Perm (V r), deficiency id p := by
  classical
  let e : Equiv.Perm (V r) := Equiv.ofBijective tags ht
  let reindex : Equiv.Perm (Equiv.Perm (V r)) :=
    { toFun := fun p => e.symm.trans p
      invFun := fun p => e.trans p
      left_inv := by intro p; ext x; simp
      right_inv := by intro p; ext x; simp }
  refine Fintype.sum_equiv reindex _ _ fun p => ?_
  suffices normalSet tags p = normalSet id (reindex p) by simp only [deficiency, this]
  ext n
  simp only [normalSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ x y, dot n (p x + e x) = dot n (p y + e y)) ↔
    (∀ x y, dot n (p (e.symm x) + x) = dot n (p (e.symm y) + y))
  constructor
  · intro h x y
    simpa using h (e.symm x) (e.symm y)
  · intro h x y
    simpa using h (e x) (e y)

private theorem arithmetic_factorial_double (m : ℕ) :
    (2 * m).choose m * m.factorial ^ 2 = (2 * m).factorial := by
  simpa [two_mul, pow_two, ← mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial m m

private theorem three_mul_le_choose_double (m : ℕ) (hm : 2 ≤ m) :
    3 * m ≤ (2 * m).choose m := by
  calc
    3 * m ≤ m * (2 * m - 1) := by
      rw [mul_comm 3]
      exact Nat.mul_le_mul_left _ (by omega)
    _ = (2 * m).choose 2 := by
      rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    _ ≤ (2 * m).choose m := Nat.choose_le_centralBinom 2 m

theorem pair_moment_le_six_single (r : ℕ) (hr : 2 ≤ r) :
    (2 ^ r - 1) * (2 ^ r - 2) * (4 * (2 ^ (r - 2)).factorial ^ 4) ≤
      6 * (2 * (2 ^ (r - 1)).factorial ^ 2) := by
  by_cases he : r = 2
  · subst r
    decide
  let m : ℕ := 2 ^ (r - 2)
  have hm : 2 ≤ m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 1 ≤ r - 2)
  have hq : 2 ^ r = 4 * m := by
    conv_lhs => rw [show r = (r - 2) + 2 by omega, pow_add]
    change m * 2 ^ 2 = 4 * m
    ring
  have hh : 2 ^ (r - 1) = 2 * m := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    exact mul_comm _ _
  have hchoose : 3 * m * m.factorial ^ 2 ≤ (2 * m).factorial := by
    rw [← arithmetic_factorial_double m]
    exact Nat.mul_le_mul_right _ (three_mul_le_choose_double m hm)
  rw [hq, hh]
  calc
    _ ≤ (4 * m) * (4 * m) * (4 * m.factorial ^ 4) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..))
    _ ≤ 6 * (2 * (3 * m * m.factorial ^ 2) ^ 2) := by
      calc
        _ = 64 * (m ^ 2 * m.factorial ^ 4) := by ring
        _ ≤ 108 * (m ^ 2 * m.factorial ^ 4) := Nat.mul_le_mul_right _ (by decide)
        _ = _ := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hchoose 2))

theorem deficiency_sum_of_moment_gap {r : ℕ} (hr : 2 ≤ r) (tags : V r → V r)
    (hc : ∀ (t : V r → V r) (p : Equiv.Perm (V r)),
      (normalSet t p).card = 2 ^ deficiency t p)
    (hN : (∑ p : Equiv.Perm (V r), normalCount tags p) + 2 * (2 ^ (r - 1)).factorial ^ 2 ≤
      ∑ p : Equiv.Perm (V r), normalCount id p)
    (hP : (∑ p : Equiv.Perm (V r), pairCount id p) =
      (2 ^ r - 1) * (2 ^ r - 2) * (4 * (2 ^ (r - 2)).factorial ^ 4)) :
    (∑ p : Equiv.Perm (V r), deficiency tags p) ≤
      ∑ p : Equiv.Perm (V r), deficiency id p := by
  have htags : (∑ p : Equiv.Perm (V r), deficiency tags p) ≤
      ∑ p : Equiv.Perm (V r), normalCount tags p :=
    Finset.sum_le_sum fun p _ => deficiency_le_normalCount (hc tags p)
  have hid : 6 * (∑ p : Equiv.Perm (V r), normalCount id p) ≤
      6 * (∑ p : Equiv.Perm (V r), deficiency id p) + ∑ p : Equiv.Perm (V r), pairCount id p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => six_normalCount_le (hc id p)
  have hpair := pair_moment_le_six_single r hr
  omega

private theorem arithmetic_rank_sum {r : ℕ} (tags : V r → V r)
    (hd : ∀ p : Equiv.Perm (V r), deficiency tags p ≤ r) :
    (∑ p : Equiv.Perm (V r), (r + 1 - deficiency tags p)) +
      (∑ p : Equiv.Perm (V r), deficiency tags p) = (r + 1) * (2 ^ r).factorial := by
  rw [← Finset.sum_add_distrib, ← arithmetic_card_perm]
  calc
    _ = ∑ _ : Equiv.Perm (V r), (r + 1) := by
      apply Finset.sum_congr rfl
      intro p _
      have := hd p
      omega
    _ = _ := by simp [mul_comm]

theorem rank_sum_comparison {r : ℕ} (tags : V r → V r)
    (hd : ∀ (t : V r → V r) (p : Equiv.Perm (V r)), deficiency t p ≤ r)
    (hs : (∑ p : Equiv.Perm (V r), deficiency tags p) ≤
      ∑ p : Equiv.Perm (V r), deficiency id p) :
    (∑ p : Equiv.Perm (V r), (r + 1 - deficiency id p)) ≤
      ∑ p : Equiv.Perm (V r), (r + 1 - deficiency tags p) := by
  have ht := arithmetic_rank_sum tags (hd tags)
  have hi := arithmetic_rank_sum id (hd id)
  omega

theorem explicit_arithmetic_bound {r E : ℕ} (hr : 0 < r) (tags : V r → V r)
    (hc : ∀ p : Equiv.Perm (V r), (normalSet tags p).card = 2 ^ deficiency tags p)
    (hd : ∀ p : Equiv.Perm (V r), deficiency tags p ≤ r)
    (hN : (∑ p : Equiv.Perm (V r), normalCount tags p) ≤
      (2 ^ r - 1) * (2 * (2 ^ (r - 1)).factorial ^ 2))
    (hE : (∑ p : Equiv.Perm (V r), (r + 1 - deficiency tags p)) ≤ 2 ^ r * E) :
    ((r + 1) * (2 ^ r).choose (2 ^ r / 2) - 2 * (2 ^ r - 1)) *
      (2 ^ r - 1).factorial ≤ (2 ^ r).choose (2 ^ r / 2) * E := by
  let q : ℕ := 2 ^ r
  let m : ℕ := 2 ^ (r - 1)
  let h : ℕ := q.choose (q / 2)
  have hq : q = 2 * m := by
    dsimp only [q]
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    exact mul_comm _ _
  have hfact : h * m.factorial ^ 2 = q.factorial := by
    dsimp only [h]
    rw [hq, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact arithmetic_factorial_double m
  have hq_pos : 0 < q := pow_pos (by decide : 0 < (2 : ℕ)) _
  have hpred : q.factorial = q * (q - 1).factorial := by
    conv_lhs => rw [show q = (q - 1) + 1 by omega, Nat.factorial_succ]
    rw [show q - 1 + 1 = q by omega]
  have hD : (∑ p : Equiv.Perm (V r), deficiency tags p) ≤
      ∑ p : Equiv.Perm (V r), normalCount tags p :=
    Finset.sum_le_sum fun p _ => deficiency_le_normalCount (hc p)
  have hsum := arithmetic_rank_sum tags hd
  change (∑ p : Equiv.Perm (V r), normalCount tags p) ≤ (q - 1) * (2 * m.factorial ^ 2) at hN
  change (∑ p : Equiv.Perm (V r), (r + 1 - deficiency tags p)) ≤ q * E at hE
  change _ = (r + 1) * q.factorial at hsum
  have hbefore : (r + 1) * q.factorial ≤ q * E + (q - 1) * (2 * m.factorial ^ 2) := by omega
  have hafter : q * ((r + 1) * h * (q - 1).factorial) ≤
      q * (h * E + 2 * (q - 1) * (q - 1).factorial) := calc
    _ = h * ((r + 1) * q.factorial) := by rw [hpred]; ring
    _ ≤ h * (q * E + (q - 1) * (2 * m.factorial ^ 2)) := Nat.mul_le_mul_left h hbefore
    _ = h * (q * E) + 2 * (q - 1) * (h * m.factorial ^ 2) := by ring
    _ = _ := by rw [hfact, hpred]; ring
  have hcancel := Nat.le_of_mul_le_mul_left hafter hq_pos
  change ((r + 1) * h - 2 * (q - 1)) * (q - 1).factorial ≤ h * E
  rw [Nat.sub_mul]
  omega

def fullDeficiency {r : ℕ} (tags : V r → V r) (p : Equiv.Perm (V r)) : ℕ :=
  if deficiency tags p = r then 1 else 0

theorem rank_three_moment_identity {tags : V 3 → V 3} {p : Equiv.Perm (V 3)}
    (hc : (normalSet tags p).card = 2 ^ deficiency tags p) (hd : deficiency tags p ≤ 3) :
    6 * deficiency tags p + pairCount tags p = 6 * normalCount tags p + 18 * fullDeficiency tags p := by
  unfold pairCount normalCount fullDeficiency
  rw [hc]
  generalize deficiency tags p = d at hd ⊢
  interval_cases d <;> decide

private theorem arithmetic_dot_single {r : ℕ} (x : V r) (j : Fin r) :
    dot (Pi.single j (1 : K)) x = x j := by
  classical
  unfold dot
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ h
    simp [Pi.single_eq_of_ne h]
  · simp

private def arithmetic_translation {r : ℕ} (c : V r) : Equiv.Perm (V r) where
  toFun x := c - x
  invFun x := c - x
  left_inv x := sub_sub_cancel c x
  right_inv x := sub_sub_cancel c x

private theorem arithmetic_full_id_iff {r : ℕ} {p : Equiv.Perm (V r)}
    (hc : (normalSet id p).card = 2 ^ deficiency id p) :
    deficiency id p = r ↔ ∃ c : V r, arithmetic_translation c = p := by
  have hset : deficiency id p = r ↔ normalSet id p = Finset.univ := by
    rw [← Finset.card_eq_iff_eq_univ, arithmetic_card_vec]
    constructor
    · intro h
      rw [hc, h]
    · intro h
      rw [deficiency, h, Nat.log_pow (by decide : 1 < 2)]
  rw [hset]
  constructor
  · intro h
    have hconst (x : V r) : p x + x = p 0 := by
      ext j
      have hn : Pi.single j (1 : K) ∈ normalSet id p := by rw [h]; exact Finset.mem_univ _
      have hs := (Finset.mem_filter.mp hn).2 x 0
      simp only [id_eq, add_zero, arithmetic_dot_single] at hs
      exact hs
    refine ⟨p 0, ?_⟩
    apply Equiv.ext
    intro x
    change p 0 - x = p x
    rw [← hconst x, add_sub_cancel_right]
  · rintro ⟨c, rfl⟩
    have he (x : V r) : arithmetic_translation c x + x = c := sub_add_cancel c x
    apply Finset.eq_univ_of_forall
    intro n
    simp [normalSet, he]

theorem fullDeficiency_sum_id {r : ℕ}
    (hc : ∀ p : Equiv.Perm (V r), (normalSet id p).card = 2 ^ deficiency id p) :
    (∑ p : Equiv.Perm (V r), fullDeficiency id p) = 2 ^ r := by
  classical
  let s : Finset (Equiv.Perm (V r)) := Finset.univ.filter (fun p => deficiency id p = r)
  let e : V r ≃ ↥s := Equiv.ofBijective
    (fun c => ⟨arithmetic_translation c, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (arithmetic_full_id_iff (hc _)).mpr ⟨c, rfl⟩⟩⟩) (by
      constructor
      · intro c d h
        have hzero := DFunLike.congr_fun (congrArg Subtype.val h) (0 : V r)
        simpa [arithmetic_translation] using hzero
      · rintro ⟨p, hp⟩
        obtain ⟨c, hc'⟩ := (arithmetic_full_id_iff (hc p)).mp (Finset.mem_filter.mp hp).2
        exact ⟨c, Subtype.ext hc'⟩)
  calc
    _ = s.card := by
      dsimp only [s]
      rw [Finset.card_filter]
      rfl
    _ = Fintype.card (V r) := by simpa using (Fintype.card_congr e).symm
    _ = _ := arithmetic_card_vec r

private theorem rank_three_arithmetic {α : Type*} [Fintype α] (d n p f : α → ℕ)
    (hd : ∀ x, d x ≤ 3) (hm : ∀ x, 6 * d x + p x = 6 * n x + 18 * f x)
    (hn : ∑ x, n x = 8064) (hp : ∑ x, p x = 2688) (hf : ∑ x, f x = 8)
    (hcard : Fintype.card α = 40320) : (∑ x, (4 - d x)) = 153640 := by
  have he : 6 * (∑ x, d x) + ∑ x, p x = 6 * (∑ x, n x) + 18 * ∑ x, f x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hm x
  have hs : (∑ x, (4 - d x)) + (∑ x, d x) = 4 * Fintype.card α := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : α, (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro x _
        have := hd x
        omega
      _ = _ := by simp [mul_comm]
  omega

theorem rank_three_id_exact
    (hc : ∀ p : Equiv.Perm (V 3), (normalSet id p).card = 2 ^ deficiency id p)
    (hd : ∀ p : Equiv.Perm (V 3), deficiency id p ≤ 3)
    (hN : (∑ p : Equiv.Perm (V 3), normalCount id p) = 8064)
    (hP : (∑ p : Equiv.Perm (V 3), pairCount id p) = 2688) :
    (∑ p : Equiv.Perm (V 3), (4 - deficiency id p)) = 153640 := by
  exact rank_three_arithmetic (deficiency id) (normalCount id) (pairCount id)
    (fullDeficiency id) hd (fun p => rank_three_moment_identity (hc p) (hd p))
    hN hP (fullDeficiency_sum_id hc)
    ((arithmetic_card_perm 3).trans (by decide))

lemma identity_normal_total (r : ℕ) :
    (∑ p : Equiv.Perm (V r), normalCount id p) =
      (2 ^ r - 1) * (2 * (2 ^ (r - 1)).factorial ^ 2) := by
  classical
  unfold normalCount
  rw [sum_normal_moment]
  calc
    _ = ∑ _ ∈ nonzeroVecs r, 2 * (2 ^ (r - 1)).factorial ^ 2 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [← momentNormalCount_eq_finset]
      exact momentNormalCount_id (mem_nonzeroVecs.mp hn)
    _ = _ := by simp [card_nonzeroVecs]

lemma identity_pair_total (r : ℕ) :
    (∑ p : Equiv.Perm (V r), pairCount id p) =
      (2 ^ r - 1) * (2 ^ r - 2) * (4 * (2 ^ (r - 2)).factorial ^ 4) := by
  classical
  unfold pairCount normalCount
  rw [sum_pair_moment]
  calc
    _ = ∑ _ ∈ distinctPairs (nonzeroVecs r), 4 * (2 ^ (r - 2)).factorial ^ 4 := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨n,m⟩ hnm
      obtain ⟨hn, hm, hne⟩ := mem_distinctPairs.mp hnm
      rw [← momentPairCount_eq_finset]
      exact momentPairCount_id (mem_nonzeroVecs.mp hn) (mem_nonzeroVecs.mp hm) hne
    _ = _ := by simp [card_distinctPairs, card_nonzeroVecs, Nat.sub_sub]

lemma single_normal_bound {r : ℕ} (tags : V r → V r) {n : V r} (hn : n ∈ nonzeroVecs r) :
    ((Finset.univ : Finset (Equiv.Perm (V r))).filter
      (fun p => n ∈ normalSet tags p)).card ≤ 2 * (2 ^ (r - 1)).factorial ^ 2 := by
  classical
  rw [← momentNormalCount_eq_finset]
  rcases momentNormalCount_zero_or_max tags (mem_nonzeroVecs.mp hn) with h | h <;> simp [h]

lemma normal_total_bound {r : ℕ} (tags : V r → V r) :
    (∑ p : Equiv.Perm (V r), normalCount tags p) ≤
      (2 ^ r - 1) * (2 * (2 ^ (r - 1)).factorial ^ 2) := by
  classical
  unfold normalCount
  rw [sum_normal_moment]
  calc
    _ ≤ ∑ _ ∈ nonzeroVecs r, 2 * (2 ^ (r - 1)).factorial ^ 2 :=
      Finset.sum_le_sum fun n hn => single_normal_bound tags hn
    _ = _ := by simp [card_nonzeroVecs]

lemma minimum_rank_sum {r : ℕ} (hr : 2 ≤ r) (tags : V r → V r) :
    (∑ p : Equiv.Perm (V r), (r+1 - deficiency id p)) ≤
      ∑ p : Equiv.Perm (V r), (r+1 - deficiency tags p) := by
  classical
  apply rank_sum_comparison tags deficiency_le
  by_cases ht : Function.Bijective tags
  · exact le_of_eq (deficiency_sum_bijective tags ht)
  · apply deficiency_sum_of_moment_gap hr tags normalSet_card_deficiency _ (identity_pair_total r)
    obtain ⟨n, hn, hz⟩ := momentMissingNormal_of_not_bijective tags ht
    rw [momentNormalCount_eq_finset] at hz
    rw [identity_normal_total]
    unfold normalCount
    rw [sum_normal_moment tags]
    simpa only [card_nonzeroVecs] using
      sum_add_missing_le (nonzeroVecs r) (fun n =>
        ((Finset.univ : Finset (Equiv.Perm (V r))).filter (fun p => n ∈ normalSet tags p)).card)
        (2 * (2 ^ (r - 1)).factorial ^ 2) (fun _ => single_normal_bound tags)
        (mem_nonzeroVecs.mpr hn) hz

lemma main (r : ℕ) (hr : 0 < r) (lin : V r → V r ≃ₗ[K] V r) (off target : W r)
    (pred : V r → W r → K) (hp : ∀ i, Low (pred i)) :
    let q := 2 ^ r
    let h := q.choose (q / 2)
    (residual lin off).card = q.factorial ∧
      (r = 3 → 19205 ≤ (errors lin off target pred).card) ∧
      (2 ≤ r → (∑ p : Equiv.Perm (V r), (r+1 - deficiency id p)) ≤
        q * (errors lin off target pred).card) ∧
      (r+1) * h * (q-1).factorial ≤ h * (errors lin off target pred).card + 2 * (q-1) * (q-1).factorial := by
  classical
  have ho := orbit_bound lin off target pred hp
  have hi (hr' : 2 ≤ r) := (minimum_rank_sum hr' (tagMap lin off target pred)).trans ho
  refine ⟨residual_card lin off, ?_, hi, ?_⟩
  · intro h3
    subst r
    have hN : (∑ p : Equiv.Perm (V 3), normalCount id p) = 8064 := by
      rw [identity_normal_total]
      decide
    have hP : (∑ p : Equiv.Perm (V 3), pairCount id p) = 2688 := by
      rw [identity_pair_total]
      decide
    have hex := rank_three_id_exact (normalSet_card_deficiency id) (deficiency_le id) hN hP
    have h := hi (by decide : 2 ≤ 3)
    change (∑ p : Equiv.Perm (V 3), (4 - deficiency id p)) ≤
      8 * (errors lin off target pred).card at h
    rw [hex] at h
    have hdiv : 153640 / 8 ≤ (8 * (errors lin off target pred).card) / 8 :=
      Nat.div_le_div_right h
    simpa only [show 153640 / 8 = 19205 by decide,
      Nat.mul_div_cancel_left _ (by decide : 0 < 8)] using hdiv
  · let tags := tagMap lin off target pred
    have h := explicit_arithmetic_bound hr tags (normalSet_card_deficiency tags)
      (deficiency_le tags) (normal_total_bound tags) ho
    rw [Nat.sub_mul] at h
    exact Nat.sub_le_iff_le_add.mp h

end Counting

end PEqualNP.Outside.L_lib_668_aux

theorem PEqualNP.Outside.L_lib_668 :
    ∀ r : Nat, 0 < r →
      let K := ZMod 2
      let V := Fin r → K
      let W := V → V
      let I := V × Fin r
      let low := fun (f : W → K) => ∃ T : Finset (Finset I),
        (∀ mon ∈ T, mon.card < r) ∧ ∀ raw,
          f raw = ∑ mon ∈ T, ∏ j ∈ mon, raw j.1 j.2
      let dot := fun (u v : V) => ∑ j, u j * v j
      let deficiency := fun (tags : V → V) (p : Equiv.Perm V) =>
        Nat.log 2 ((Finset.univ : Finset V).filter (fun normal =>
          ∀ x y : V, dot normal (p x + tags x) = dot normal (p y + tags y))).card
      ∀ (lin : V → (V ≃ₗ[K] V)) (off target : V → V) (pred : V → W → K),
        (∀ i, low (pred i)) →
        let residual := (Finset.univ : Finset W).filter (fun word =>
          Function.Bijective (fun i => lin i (word i) + off i))
        let errors := residual.filter (fun w =>
          ∃ i, pred i w ≠ (if w i = target i then 1 else 0))
        let q := 2^r
        let h := Nat.choose q (q/2)
        residual.card = Nat.factorial q ∧ (r = 3 → 19205 ≤ errors.card) ∧
          (2 ≤ r → (∑ p : Equiv.Perm V, (r+1 - deficiency id p)) ≤ q*errors.card) ∧
          (r+1)*h*Nat.factorial (q-1) ≤ h*errors.card + 2*(q-1)*Nat.factorial (q-1) := by
  classical
  intro r hr K V W I low dot deficiency lin off target pred hp residual errors q h
  have hR : residual = PEqualNP.Outside.L_lib_668_aux.residual lin off := by
    ext w
    simp only [residual, PEqualNP.Outside.L_lib_668_aux.residual,
      Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  have hE : errors = PEqualNP.Outside.L_lib_668_aux.errors lin off target pred := by
    ext w
    simp only [errors, PEqualNP.Outside.L_lib_668_aux.errors, Finset.mem_filter,
      PEqualNP.Outside.L_lib_668_aux.bad, hR]
    refine and_congr_right fun _ => exists_congr fun i => ?_
    by_cases hi : w i = target i <;> simp [hi, PEqualNP.Outside.L_lib_668_aux.indicator]
  have hD (p : Equiv.Perm V) :
      deficiency id p = PEqualNP.Outside.L_lib_668_aux.deficiency id p := by
    dsimp only [deficiency, dot, PEqualNP.Outside.L_lib_668_aux.deficiency]
    apply congrArg (Nat.log 2)
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (PEqualNP.Outside.L_lib_668_aux.mem_normalSet
      (r := r) (tags := id) (p := p) (n := n)).symm
  simpa only [hR, hE, hD] using PEqualNP.Outside.L_lib_668_aux.main r hr lin off target pred hp

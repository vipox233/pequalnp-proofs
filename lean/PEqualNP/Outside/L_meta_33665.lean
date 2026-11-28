import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33665

def ix (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def rot (n : ℕ) (hn : 0 < n) (s : ℕ) (w : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  w (ix n hn (i.val + n - s % n))

def out (n : ℕ) (hn : 0 < n) (name c raw : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  let old := rot n hn 3 raw + name
  let y := fun j : Fin n => old j + old (ix n hn (j.val+2)) + old (ix n hn (j.val+n-2))
  y i + (1+y (ix n hn (i.val+1)))*y (ix n hn (i.val+2)) + rot n hn 4 raw i + c i

noncomputable def run (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)

noncomputable def base (n : ℕ) (j : Fin 4) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0

noncomputable def even (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = 0 then z i else 0

def mix (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  let old := rot n hn 3 w
  old i + old (ix n hn (i.val+2)) + old (ix n hn (i.val+n-2))

def dot (n : ℕ) (z x : Fin n → ZMod 2) : ZMod 2 := ∑ i, z i * x i

def adm (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) : Prop :=
  ∀ i : Fin n, x (ix n hn (i.val+1)) * x (ix n hn (i.val+2)) = 0

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma fn_add_self (n : ℕ) (a : Fin n → ZMod 2) : a + a = 0 := by
  funext i
  exact z2_add_self (a i)

lemma ix_val (n : ℕ) (hn : 0 < n) (j : ℕ) : (ix n hn j).val = j % n := rfl

lemma ix_eq_iff (n : ℕ) (hn : 0 < n) (a b : ℕ) : ix n hn a = ix n hn b ↔ a % n = b % n := by
  simp [ix, Fin.ext_iff]

lemma ix_self (n : ℕ) (hn : 0 < n) (a : Fin n) : ix n hn a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_add_n (n : ℕ) (hn : 0 < n) (a : ℕ) : ix n hn (a + n) = ix n hn a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_val_add (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    ix n hn ((ix n hn a).val + b) = ix n hn (a + b) := by
  rw [ix_eq_iff]
  simp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma dot_comm (n : ℕ) (z x : Fin n → ZMod 2) : dot n z x = dot n x z := by
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma dot_add_left (n : ℕ) (z z' x : Fin n → ZMod 2) :
    dot n (z + z') x = dot n z x + dot n z' x := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply]; ring)

lemma dot_add_right (n : ℕ) (z x x' : Fin n → ZMod 2) :
    dot n z (x + x') = dot n z x + dot n z x' := by
  rw [dot_comm, dot_add_left, dot_comm n x z, dot_comm n x' z]

lemma dot_smul_left (n : ℕ) (a : ZMod 2) (z x : Fin n → ZMod 2) :
    dot n (a • z) x = a * dot n z x := by
  unfold dot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma dot_zero_left (n : ℕ) (x : Fin n → ZMod 2) : dot n 0 x = 0 := by
  unfold dot
  simp

def dotL (n : ℕ) (x : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun z => dot n z x
    map_add' := fun z z' => dot_add_left n z z' x
    map_smul' := fun a z => dot_smul_left n a z x }

lemma mix_add (n : ℕ) (hn : 0 < n) (w w' : Fin n → ZMod 2) :
    mix n hn (w + w') = mix n hn w + mix n hn w' := by
  funext i
  simp only [mix, rot, Pi.add_apply]
  ring

lemma mix_smul (n : ℕ) (hn : 0 < n) (a : ZMod 2) (w : Fin n → ZMod 2) :
    mix n hn (a • w) = a • mix n hn w := by
  funext i
  simp only [mix, rot, Pi.smul_apply, smul_eq_mul]
  ring

def mixL (n : ℕ) (hn : 0 < n) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := mix n hn
    map_add' := mix_add n hn
    map_smul' := mix_smul n hn }

lemma mixL_apply (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) : mixL n hn w = mix n hn w := rfl

lemma mix_sub (n : ℕ) (hn : 0 < n) (w w' : Fin n → ZMod 2) :
    mix n hn (w - w') = mix n hn w - mix n hn w' := (mixL n hn).map_sub w w'

lemma even_apply (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) :
    even n z i = if i.val % 2 = 0 then z i else 0 := by
  unfold even
  split_ifs <;> rfl

lemma even_add (n : ℕ) (z z' : Fin n → ZMod 2) : even n (z + z') = even n z + even n z' := by
  funext i
  simp only [even_apply, Pi.add_apply]
  split_ifs <;> simp

lemma even_smul (n : ℕ) (a : ZMod 2) (z : Fin n → ZMod 2) : even n (a • z) = a • even n z := by
  funext i
  simp only [even_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

noncomputable def evenL (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := even n
    map_add' := even_add n
    map_smul' := even_smul n }

lemma evenL_apply (n : ℕ) (z : Fin n → ZMod 2) : evenL n z = even n z := rfl

lemma even_even (n : ℕ) (z : Fin n → ZMod 2) : even n (even n z) = even n z := by
  funext i
  simp only [even_apply]
  split_ifs <;> rfl

lemma dot_even (n : ℕ) (z x : Fin n → ZMod 2) : dot n (even n z) x = dot n z (even n x) := by
  unfold dot
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [even_apply]
  split_ifs <;> simp

lemma base_apply (n : ℕ) (j : Fin 4) (i : Fin n) :
    base n j i = if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : ZMod 2) else 0 := by
  unfold base
  split_ifs <;> rfl
lemma ix_shift (n : ℕ) (hn : 0 < n) (a s : ℕ) (hs : s ≤ n) :
    ix n hn ((ix n hn a).val + n - s) = ix n hn (a + (n - s)) := by
  have e : (ix n hn a).val + n - s = (ix n hn a).val + (n - s) := by omega
  rw [e, ix_val_add]

lemma mix_apply (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2) (i : Fin n) :
    mix n hn w i = w (ix n hn (i.val + n - 3)) + w (ix n hn (i.val + n - 1)) +
      w (ix n hn (i.val + n - 5)) := by
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [mix, rot, h3]
  rw [ix_shift n hn _ 3 (by omega), ix_shift n hn _ 3 (by omega)]
  have e1 : i.val + 2 + (n - 3) = i.val + n - 1 := by omega
  have e2 : i.val + n - 2 + (n - 3) = i.val + n - 5 + n := by omega
  rw [e1, e2, ix_add_n]

lemma mix_ix (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2) (a : ℕ) :
    mix n hn w (ix n hn (a + 5)) = w (ix n hn (a + 2)) + w (ix n hn (a + 4)) +
      w (ix n hn a) := by
  rw [mix_apply n hn h6n, ix_shift n hn _ 3 (by omega), ix_shift n hn _ 1 (by omega),
    ix_shift n hn _ 5 (by omega)]
  have e1 : a + 5 + (n - 3) = a + 2 + n := by omega
  have e2 : a + 5 + (n - 1) = a + 4 + n := by omega
  have e3 : a + 5 + (n - 5) = a + n := by omega
  rw [e1, e2, e3, ix_add_n, ix_add_n, ix_add_n]

lemma z2_mid (x y z : ZMod 2) (h : x + y + z = 0) : y = x + z := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;>
    rcases z2_cases z with rfl | rfl <;> revert h <;> decide

lemma ker_step (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2)
    (hw : mix n hn w = 0) (a : ℕ) :
    w (ix n hn (a + 4)) = w (ix n hn (a + 2)) + w (ix n hn a) := by
  have h := congrFun hw (ix n hn (a + 5))
  rw [mix_ix n hn h6n] at h
  exact z2_mid _ _ _ h

lemma ker_agree (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w w' : Fin n → ZMod 2)
    (hw : mix n hn w = 0) (hw' : mix n hn w' = 0)
    (h4 : ∀ a : ℕ, a < 4 → w (ix n hn a) = w' (ix n hn a)) :
    ∀ m : ℕ, w (ix n hn m) = w' (ix n hn m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 4
    · exact h4 m hm
    · obtain ⟨a, rfl⟩ : ∃ a, m = a + 4 := ⟨m - 4, by omega⟩
      rw [ker_step n hn h6n w hw a, ker_step n hn h6n w' hw' a,
        ih (a + 2) (by omega), ih a (by omega)]

lemma ker_mix_card (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Nat.card {w : Fin n → ZMod 2 // mix n hn w = 0} ≤ 16 := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  have hinj : Function.Injective
      (fun (w : {w : Fin n → ZMod 2 // mix n hn w = 0}) (a : Fin 4) => w.1 (ix n hn a.val)) := by
    intro w w' hww
    apply Subtype.ext
    funext i
    have h4 : ∀ a : ℕ, a < 4 → w.1 (ix n hn a) = w'.1 (ix n hn a) := by
      intro a ha
      exact congrFun hww ⟨a, ha⟩
    have := ker_agree n hn h6n w.1 w'.1 w.2 w'.2 h4 i.val
    rwa [ix_self] at this
  have hc := Nat.card_le_card_of_injective _ hinj
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rwa [h16] at hc

def baseBit (j : Fin 4) (q : ℕ) : ZMod 2 :=
  if q % 2 = j.val / 2 ∧ (q / 2 % 3 = j.val % 2 ∨ q / 2 % 3 = 2) then (1 : ZMod 2) else 0

lemma baseBit_mod (j : Fin 4) (q : ℕ) : baseBit j (q % 6) = baseBit j q := by
  have e1 : q % 6 % 2 = q % 2 := by omega
  have e2 : q % 6 / 2 % 3 = q / 2 % 3 := by omega
  unfold baseBit
  rw [e1, e2]

lemma baseBit_congr (j : Fin 4) (p q : ℕ) (h : p % 6 = q % 6) : baseBit j p = baseBit j q := by
  rw [← baseBit_mod j p, ← baseBit_mod j q, h]

lemma base_ix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (j : Fin 4) (a : ℕ) :
    base n j (ix n hn a) = baseBit j a := by
  rw [base_apply, ix_val]
  exact baseBit_congr j (a % n) a (Nat.mod_mod_of_dvd a h6)

lemma baseBit_fin : ∀ (j : Fin 4) (r : Fin 6),
    baseBit j (r.val + 3) + baseBit j (r.val + 1) + baseBit j (r.val + 5) = 0 := by
  decide

lemma baseBit_sum (j : Fin 4) (a : ℕ) :
    baseBit j (a + 3) + baseBit j (a + 1) + baseBit j (a + 5) = 0 := by
  have h := baseBit_fin j ⟨a % 6, Nat.mod_lt _ (by norm_num)⟩
  rw [baseBit_congr j (a + 3) (a % 6 + 3) (by omega), baseBit_congr j (a + 1) (a % 6 + 1) (by omega),
    baseBit_congr j (a + 5) (a % 6 + 5) (by omega)]
  exact h

def shiftEquiv (n : ℕ) (hn : 0 < n) (s : ℕ) (hs : s ≤ n) : Fin n ≃ Fin n where
  toFun i := ix n hn (i.val + s)
  invFun i := ix n hn (i.val + n - s)
  left_inv i := by
    show ix n hn ((ix n hn (i.val + s)).val + n - s) = i
    rw [ix_shift n hn _ s hs]
    have e : i.val + s + (n - s) = i.val + n := by omega
    rw [e, ix_add_n, ix_self]
  right_inv i := by
    show ix n hn ((ix n hn (i.val + n - s)).val + s) = i
    rw [ix_val_add]
    have e : i.val + n - s + s = i.val + n := by omega
    rw [e, ix_add_n, ix_self]

lemma sum_shift (n : ℕ) (hn : 0 < n) (s : ℕ) (hs : s ≤ n) (f g : Fin n → ZMod 2) :
    ∑ i, f i * g (ix n hn (i.val + n - s)) = ∑ i, f (ix n hn (i.val + s)) * g i := by
  rw [← Equiv.sum_comp (shiftEquiv n hn s hs) (fun i => f i * g (ix n hn (i.val + n - s)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e : ix n hn (((shiftEquiv n hn s hs) i).val + n - s) = i :=
    (shiftEquiv n hn s hs).left_inv i
  rw [e]
  rfl

lemma base_dot_mix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (j : Fin 4) (w : Fin n → ZMod 2) :
    dot n (base n j) (mix n hn w) = 0 := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  unfold dot
  have e1 : ∀ i : Fin n, base n j i * mix n hn w i =
      base n j i * w (ix n hn (i.val + n - 3)) + base n j i * w (ix n hn (i.val + n - 1)) +
        base n j i * w (ix n hn (i.val + n - 5)) := by
    intro i
    rw [mix_apply n hn h6n]
    ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_shift n hn 3 (by omega), sum_shift n hn 1 (by omega),
    sum_shift n hn 5 (by omega), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [base_ix n hn h6, base_ix n hn h6, base_ix n hn h6, ← add_mul, ← add_mul,
    baseBit_sum, zero_mul]

lemma even_base (n : ℕ) (j : Fin 4) :
    even n (base n j) = base n j ∨ even n (base n j) = 0 := by
  by_cases hj : j.val / 2 = 0
  · left
    funext i
    rw [even_apply, base_apply]
    split_ifs with h1 h2 h2
    · rfl
    · rfl
    · exfalso
      omega
    · rfl
  · right
    funext i
    rw [even_apply, base_apply, Pi.zero_apply]
    split_ifs with h1 h2
    · exfalso
      omega
    · rfl
    · rfl
def ansBit (x : ZMod 2) : ℕ := if x = 0 then 0 else 1

lemma ansBit_le (x : ZMod 2) : ansBit x ≤ 1 := by
  unfold ansBit
  split_ifs <;> omega

lemma ansBit_eq_iff (x y : ZMod 2) : ansBit x = ansBit y ↔ x - y = 0 := by
  revert x y
  decide

lemma run_succ (n h : ℕ) (ask : Fin (h+1) → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) :
    run n (h+1) ask w = 2 * run n h (fun j => ask j.castSucc) w +
      ansBit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w) w) := by
  unfold run ansBit
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  congr

lemma run_eq_iff (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w0 : Fin n → ZMod 2) :
    ∃ p : Fin h → ℕ, ∀ w, run n h ask w = run n h ask w0 ↔ ∀ j, ask j (p j) (w - w0) = 0 := by
  induction h with
  | zero =>
    refine ⟨fun _ => 0, fun w => ?_⟩
    constructor
    · intro _ j
      exact j.elim0
    · intro _
      rfl
  | succ h ih =>
    obtain ⟨p', hp'⟩ := ih (fun j => ask j.castSucc)
    refine ⟨@Fin.snoc h (fun _ => ℕ) p' (run n h (fun j => ask j.castSucc) w0), fun w => ?_⟩
    rw [run_succ, run_succ, Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hp' w]
    have hb1 := ansBit_le (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w) w)
    have hb2 := ansBit_le (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w0)
    constructor
    · intro he
      have h1 : run n h (fun j => ask j.castSucc) w = run n h (fun j => ask j.castSucc) w0 := by
        omega
      refine ⟨h1, ?_⟩
      rw [h1] at he
      have h2 : ansBit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w) =
          ansBit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w0) := by
        omega
      rw [ansBit_eq_iff, ← map_sub] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      rw [h1]
      congr 1
      rw [ansBit_eq_iff, ← map_sub]
      exact h2

def mixName (n : ℕ) (hn : 0 < n) (name : Fin n → ZMod 2) (j : Fin n) : ZMod 2 :=
  name j + name (ix n hn (j.val+2)) + name (ix n hn (j.val+n-2))

def outLin (n : ℕ) (hn : 0 < n) (name : Fin n → ZMod 2) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := fun w i => mix n hn w i + mix n hn w (ix n hn (i.val+2))
      + mixName n hn name (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2))
      + mixName n hn name (ix n hn (i.val+2)) * mix n hn w (ix n hn (i.val+1))
      + rot n hn 4 w i
    map_add' := fun w w' => by
      funext i
      simp only [mix_add, Pi.add_apply, rot]
      ring
    map_smul' := fun a w => by
      funext i
      simp only [mix_smul, Pi.smul_apply, smul_eq_mul, rot, RingHom.id_apply]
      ring }

lemma out_affine (n : ℕ) (hn : 0 < n) (name c : Fin n → ZMod 2) :
    ∃ (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (c0 : Fin n → ZMod 2),
      ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i =
        mix n hn w (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2)) + (L w + c0) i := by
  refine ⟨outLin n hn name, fun i => mixName n hn name i + mixName n hn name (ix n hn (i.val+2))
    + mixName n hn name (ix n hn (i.val+1)) * mixName n hn name (ix n hn (i.val+2)) + c i,
    fun w i => ?_⟩
  simp only [out, outLin, mixName, mix, rot, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ring

noncomputable def oddKer (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  K ⊓ Submodule.comap (mixL n hn) (LinearMap.ker (evenL n))

lemma mem_oddKer (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (x : Fin n → ZMod 2) : x ∈ oddKer n hn K ↔ x ∈ K ∧ even n (mix n hn x) = 0 := by
  unfold oddKer
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker, mixL_apply, evenL_apply]

lemma even_mix_oddKer (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (κ : ↥(oddKer n hn K)) : even n (mix n hn (κ : Fin n → ZMod 2)) = 0 :=
  ((mem_oddKer n hn K _).1 κ.2).2

noncomputable def tau (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (↥K × ↥(oddKer n hn K)) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  ((evenL n).comp ((mixL n hn).comp K.subtype)).coprod
    ((mixL n hn).comp (oddKer n hn K).subtype)

lemma tau_apply (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (u : ↥K × ↥(oddKer n hn K)) :
    tau n hn K u =
      even n (mix n hn (u.1 : Fin n → ZMod 2)) + mix n hn (u.2 : Fin n → ZMod 2) := rfl

def prodAt (n : ℕ) (hn : 0 < n) (i : Fin n) (x : Fin n → ZMod 2) : ZMod 2 :=
  x (ix n hn (i.val+1)) * x (ix n hn (i.val+2))

def crossAt (n : ℕ) (hn : 0 < n) (i : Fin n) (x x' : Fin n → ZMod 2) : ZMod 2 :=
  x (ix n hn (i.val+1)) * x' (ix n hn (i.val+2)) + x' (ix n hn (i.val+1)) * x (ix n hn (i.val+2))

lemma parity_cases (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) :
    ((ix n hn (i.val+1)).val % 2 = 0 ∧ (ix n hn (i.val+2)).val % 2 = 1) ∨
    ((ix n hn (i.val+1)).val % 2 = 1 ∧ (ix n hn (i.val+2)).val % 2 = 0) := by
  rw [ix_val, ix_val, Nat.mod_mod_of_dvd _ h2, Nat.mod_mod_of_dvd _ h2]
  omega

lemma apply_of_even_zero (n : ℕ) (x : Fin n → ZMod 2) (h : even n x = 0) (j : Fin n)
    (hj : j.val % 2 = 0) : x j = 0 := by
  have h1 := congrFun h j
  rw [even_apply] at h1
  split_ifs at h1
  exact h1

lemma even_apply_odd (n : ℕ) (x : Fin n → ZMod 2) (j : Fin n) (hj : j.val % 2 = 1) :
    even n x j = 0 := by
  rw [even_apply]
  split_ifs with h
  · omega
  · rfl

lemma even_apply_even (n : ℕ) (x : Fin n → ZMod 2) (j : Fin n) (hj : j.val % 2 = 0) :
    even n x j = x j := by
  rw [even_apply]
  split_ifs
  rfl

lemma prodAt_add (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x' = 0) : prodAt n hn i (x + x') = prodAt n hn i x + crossAt n hn i x x' := by
  unfold prodAt crossAt
  simp only [Pi.add_apply]
  rcases parity_cases n hn h2 i with ⟨ha, -⟩ | ⟨-, hb⟩
  · rw [apply_of_even_zero n x' h _ ha]
    ring
  · rw [apply_of_even_zero n x' h _ hb]
    ring

lemma crossAt_odd (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x = 0) (h' : even n x' = 0) : crossAt n hn i x x' = 0 := by
  unfold crossAt
  rcases parity_cases n hn h2 i with ⟨ha, -⟩ | ⟨-, hb⟩
  · rw [apply_of_even_zero n x h _ ha, apply_of_even_zero n x' h' _ ha]
    ring
  · rw [apply_of_even_zero n x h _ hb, apply_of_even_zero n x' h' _ hb]
    ring

lemma crossAt_add (n : ℕ) (hn : 0 < n) (i : Fin n) (x y x' : Fin n → ZMod 2) :
    crossAt n hn i (x + y) x' = crossAt n hn i x x' + crossAt n hn i y x' := by
  unfold crossAt
  simp only [Pi.add_apply]
  ring

lemma prodAt_even (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x' = 0) : prodAt n hn i (even n x + x') = crossAt n hn i x x' := by
  unfold prodAt crossAt
  simp only [Pi.add_apply]
  rcases parity_cases n hn h2 i with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [apply_of_even_zero n x' h _ ha, even_apply_even n x _ ha, even_apply_odd n x _ hb]
    ring
  · rw [apply_of_even_zero n x' h _ hb, even_apply_odd n x _ ha, even_apply_even n x _ hb]
    ring

lemma card_fiber_le_left (α β γ : Type) [Finite α] [Finite β] [Finite γ] (S : α → β → Prop)
    (T : α → γ → Prop) (h : ∀ a, Nat.card {b // S a b} ≤ Nat.card {c // T a c}) :
    Nat.card {p : α × β // S p.1 p.2} ≤ Nat.card {p : α × γ // T p.1 p.2} := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype S),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype T), Nat.card_sigma, Nat.card_sigma]
  exact Finset.sum_le_sum (fun a _ => h a)

lemma card_fiber_le_right (α β γ : Type) [Finite α] [Finite β] [Finite γ] (S : β → α → Prop)
    (T : γ → α → Prop) (h : ∀ a, Nat.card {b // S b a} ≤ Nat.card {c // T c a}) :
    Nat.card {p : β × α // S p.1 p.2} ≤ Nat.card {p : γ × α // T p.1 p.2} := by
  have h1 := card_fiber_le_left α β γ (fun a b => S b a) (fun a c => T c a) h
  have e1 : Nat.card {p : β × α // S p.1 p.2} = Nat.card {p : α × β // S p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm β α).subtypeEquiv (fun p => Iff.rfl))
  have e2 : Nat.card {p : γ × α // T p.1 p.2} = Nat.card {p : α × γ // T p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm γ α).subtypeEquiv (fun p => Iff.rfl))
  rw [e1, e2]
  exact h1

def Hit (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y0 e : Fin n → ZMod 2) (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : ↥K) : Prop :=
  ∀ i, prodAt n hn i (Y0 + mix n hn (k : Fin n → ZMod 2)) = (N (k : Fin n → ZMod 2) + e) i

def Tangent (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y0 : Fin n → ZMod 2) (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ↥K)
    (κ : ↥(oddKer n hn K)) : Prop :=
  ∀ i, crossAt n hn i (Y0 + mix n hn (k : Fin n → ZMod 2)) (mix n hn (κ : Fin n → ZMod 2)) =
      N (κ : Fin n → ZMod 2) i

def Tangent0 (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (k : ↥K) (κ : ↥(oddKer n hn K)) : Prop :=
  ∀ i, crossAt n hn i (mix n hn (k : Fin n → ZMod 2)) (mix n hn (κ : Fin n → ZMod 2)) = 0

lemma tangent_of_hits (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k g0 g : ↥K)
    (hg0 : Hit n hn K Y0 e N g0)
    (hm0 : (g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ oddKer n hn K)
    (hg : Hit n hn K Y0 e N g)
    (hd : (g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2) ∈ oddKer n hn K) :
    Tangent n hn K Y0 N k ⟨(g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2), hd⟩ := by
  intro i
  have o1 : even n (mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2))) = 0 :=
    ((mem_oddKer n hn K _).1 hd).2
  have o2 : even n (mix n hn ((g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2))) = 0 :=
    ((mem_oddKer n hn K _).1 hm0).2
  have e1 : Y0 + mix n hn (g : Fin n → ZMod 2) = (Y0 + mix n hn (g0 : Fin n → ZMod 2)) +
      mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2)) := by
    rw [mix_sub]
    abel
  have e2 : Y0 + mix n hn (g0 : Fin n → ZMod 2) = (Y0 + mix n hn (k : Fin n → ZMod 2)) +
      mix n hn ((g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2)) := by
    rw [mix_sub]
    abel
  have h1 := hg i
  rw [e1, prodAt_add n hn h2 i _ _ o1, hg0 i, e2, crossAt_add,
    crossAt_odd n hn h2 i _ _ o2 o1, add_zero] at h1
  show crossAt n hn i (Y0 + mix n hn (k : Fin n → ZMod 2))
    (mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2))) =
    N ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2)) i
  rw [map_sub, Pi.sub_apply]
  simp only [Pi.add_apply] at h1
  linear_combination h1

lemma hits_le_tangent (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ↥K) :
    Nat.card {g : ↥K // Hit n hn K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ oddKer n hn K} ≤
    Nat.card {κ : ↥(oddKer n hn K) // Tangent n hn K Y0 N k κ} := by
  rcases isEmpty_or_nonempty {g : ↥K // Hit n hn K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ oddKer n hn K} with hE | ⟨⟨g0, hg0, hm0⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · have hd : ∀ g : {g : ↥K // Hit n hn K Y0 e N g ∧
        (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ oddKer n hn K},
        (g.1 : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2) ∈ oddKer n hn K := by
      intro g
      have h := (oddKer n hn K).sub_mem g.2.2 hm0
      rw [sub_sub_sub_cancel_right] at h
      exact h
    refine Nat.card_le_card_of_injective (fun g =>
      ⟨⟨(g.1 : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2), hd g⟩,
        tangent_of_hits n hn h2 K Y0 e N k g0 g.1 hg0 hm0 g.2.1 (hd g)⟩) ?_
    intro g g' hgg
    simp only [Subtype.mk.injEq, sub_left_inj] at hgg
    exact Subtype.ext (Subtype.ext hgg)

lemma tangent_le_tangent0 (n : ℕ) (hn : 0 < n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (κ : ↥(oddKer n hn K)) :
    Nat.card {k : ↥K // Tangent n hn K Y0 N k κ} ≤
    Nat.card {k : ↥K // Tangent0 n hn K k κ} := by
  rcases isEmpty_or_nonempty {k : ↥K // Tangent n hn K Y0 N k κ} with hE | ⟨⟨k0, hk0⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · refine Nat.card_le_card_of_injective (fun k => ⟨k.1 - k0, ?_⟩) ?_
    · intro i
      have e1 : Y0 + mix n hn (k.1 : Fin n → ZMod 2) = (Y0 + mix n hn (k0 : Fin n → ZMod 2)) +
          mix n hn ((k.1 - k0 : ↥K) : Fin n → ZMod 2) := by
        rw [Submodule.coe_sub, mix_sub]
        abel
      have h1 := k.2 i
      rw [e1, crossAt_add, hk0 i] at h1
      exact add_left_cancel (h1.trans (add_zero _).symm)
    · intro k k' hkk
      exact Subtype.ext (sub_left_inj.mp (congrArg Subtype.val hkk))

lemma hits_le_pairs (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (oddKer n hn K) * Nat.card {k : ↥K // Hit n hn K Y0 e N k} ≤
    Nat.card {p : ↥K × ↥(oddKer n hn K) // Tangent n hn K Y0 N p.1 p.2} := by
  have h1 : Nat.card (↥(oddKer n hn K) × {k : ↥K // Hit n hn K Y0 e N k}) ≤
      Nat.card {p : ↥K × ↥K // Hit n hn K Y0 e N p.2 ∧
        (p.2 : Fin n → ZMod 2) - (p.1 : Fin n → ZMod 2) ∈ oddKer n hn K} := by
    refine Nat.card_le_card_of_injective (fun q =>
      ⟨(⟨(q.2.1 : Fin n → ZMod 2) - (q.1 : Fin n → ZMod 2),
        K.sub_mem q.2.1.2 ((mem_oddKer n hn K _).1 q.1.2).1⟩, q.2.1), ⟨q.2.2, ?_⟩⟩) ?_
    · show (q.2.1 : Fin n → ZMod 2) - ((q.2.1 : Fin n → ZMod 2) - (q.1 : Fin n → ZMod 2)) ∈
        oddKer n hn K
      rw [sub_sub_cancel]
      exact q.1.2
    · intro q q' hqq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at hqq
      have h3 : q.2 = q'.2 := Subtype.ext hqq.2
      have h4 := hqq.1
      rw [hqq.2] at h4
      exact Prod.ext (Subtype.ext (sub_right_injective h4)) h3
  rw [Nat.card_prod] at h1
  exact le_trans h1 (card_fiber_le_left ↥K ↥K ↥(oddKer n hn K)
    (fun k g => Hit n hn K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ oddKer n hn K)
    (fun k κ => Tangent n hn K Y0 N k κ)
    (fun k => hits_le_tangent n hn h2 K Y0 e N k))

lemma tangent0_card (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {p : ↥K × ↥(oddKer n hn K) // Tangent0 n hn K p.1 p.2} =
    Nat.card {u : ↥K × ↥(oddKer n hn K) // adm n hn (tau n hn K u)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun u => ?_))
  constructor
  · intro h i
    rw [tau_apply]
    exact (prodAt_even n hn h2 i _ _ (even_mix_oddKer n hn K u.2)).trans (h i)
  · intro h i
    have h1 := h i
    rw [tau_apply] at h1
    exact (prodAt_even n hn h2 i _ _ (even_mix_oddKer n hn K u.2)).symm.trans h1

lemma pairs_bound (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (oddKer n hn K) * Nat.card {k : ↥K // Hit n hn K Y0 e N k} ≤
    Nat.card {u : ↥K × ↥(oddKer n hn K) // adm n hn (tau n hn K u)} := by
  rw [← tangent0_card n hn h2 K]
  exact le_trans (hits_le_pairs n hn h2 K Y0 e N)
    (card_fiber_le_right ↥(oddKer n hn K) ↥K ↥K (fun k κ => Tangent n hn K Y0 N k κ)
      (fun k κ => Tangent0 n hn K k κ) (fun κ => tangent_le_tangent0 n hn K Y0 N κ))

lemma z2_move : ∀ X s t : ZMod 2, X + s = t ↔ X = s + t := by
  decide

lemma hit_card (n : ℕ) (hn : 0 < n) (name c : Fin n → ZMod 2)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (w0 : Fin n → ZMod 2)
    (A L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b c0 : Fin n → ZMod 2)
    (hL : ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i =
        mix n hn w (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2)) + (L w + c0) i) :
    Nat.card {k : K // ∀ i, out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} =
    Nat.card {k : ↥K // Hit n hn K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun k =>
    forall_congr' (fun i => ?_)))
  have e : (L (w0 + (k : Fin n → ZMod 2)) + c0) i + (A (w0 + (k : Fin n → ZMod 2)) + b) i =
      ((L + A) (k : Fin n → ZMod 2) + (L w0 + c0 + A w0 + b)) i := by
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    ring
  rw [hL, mix_add, z2_move, e]
  exact Iff.rfl

lemma z2_pred : ∀ x y s t l c : ZMod 2,
    (x * y + (l + c) = t * x + s * y + l + (s * t + c) ↔ (x - s) * (y - t) = 0) := by
  decide

lemma out_pred (n : ℕ) (hn : 0 < n) (name c wp : Fin n → ZMod 2) :
    ∃ (A' : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b' : Fin n → ZMod 2),
      ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i = (A' w + b') i ↔
        mix n hn (w - wp) (ix n hn (i.val+1)) * mix n hn (w - wp) (ix n hn (i.val+2)) = 0 := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  refine ⟨LinearMap.pi (fun i =>
      ((mix n hn wp (ix n hn (i.val+2))) • ((LinearMap.proj (ix n hn (i.val+1))) ∘ₗ mixL n hn) +
      (mix n hn wp (ix n hn (i.val+1))) • ((LinearMap.proj (ix n hn (i.val+2))) ∘ₗ mixL n hn) +
      (LinearMap.proj i) ∘ₗ L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)),
    fun i => mix n hn wp (ix n hn (i.val+1)) * mix n hn wp (ix n hn (i.val+2)) + c0 i, ?_⟩
  intro w i
  rw [hL w i, mix_sub]
  simp only [Pi.add_apply, Pi.sub_apply, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, mixL_apply, smul_eq_mul]
  exact z2_pred _ _ _ _ _ _

lemma coset_count (n : ℕ) (N : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (P : (Fin n → ZMod 2) → Prop)
    (hr1 : ∀ w, w - r w ∈ N) (hr2 : ∀ w, ∀ u ∈ N, r (r w + u) = r w) :
    Nat.card N * Nat.card {w : Fin n → ZMod 2 // P (w - r w)} =
      2^n * Nat.card {u : N // P (u : Fin n → ZMod 2)} := by
  have hΦ : Function.Involutive (fun x : (Fin n → ZMod 2) × N =>
      ((r x.1 + (x.2 : Fin n → ZMod 2), ⟨x.1 - r x.1, hr1 x.1⟩) : (Fin n → ZMod 2) × N)) := by
    rintro ⟨w, u⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show r (r w + (u : Fin n → ZMod 2)) + (w - r w) = w
      rw [hr2 w u u.2, add_sub_cancel]
    · show r w + (u : Fin n → ZMod 2) - r (r w + (u : Fin n → ZMod 2)) = u
      rw [hr2 w u u.2, add_sub_cancel_left]
  have e1 : {x : (Fin n → ZMod 2) × N // P (x.1 - r x.1)} ≃
      {x : (Fin n → ZMod 2) × N // P (x.2 : Fin n → ZMod 2)} :=
    Equiv.subtypeEquiv (Function.Involutive.toPerm _ hΦ) (fun x => Iff.rfl)
  have e2 : {x : (Fin n → ZMod 2) × N // P (x.1 - r x.1)} ≃
      {w : Fin n → ZMod 2 // P (w - r w)} × N :=
    Equiv.prodSubtypeFstEquivSubtypeProd (p := fun w => P (w - r w))
  have e3 : {x : (Fin n → ZMod 2) × N // P (x.2 : Fin n → ZMod 2)} ≃
      (Fin n → ZMod 2) × {u : N // P (u : Fin n → ZMod 2)} :=
    { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
      invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Nat.card_congr (e2.symm.trans (e1.trans e3))
  rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h1
  rw [mul_comm, h1]

lemma nonadaptive_aux (n : ℕ) (hn : 0 < n) (name c : Fin n → ZMod 2)
    (N : Submodule (ZMod 2) (Fin n → ZMod 2)) (R : (Fin n → ZMod 2) → ℕ)
    (hR : ∀ w w', R w = R w' ↔ w - w' ∈ N) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card N * Nat.card {w : Fin n → ZMod 2 // ∀ i, out n hn name c w i = (A (R w) w + b (R w)) i} =
      2^n * Nat.card {u : N // adm n hn (mix n hn (u : Fin n → ZMod 2))} := by
  have hrep : ∀ w, R (Function.invFun R (R w)) = R w := fun w => Function.invFun_eq ⟨w, rfl⟩
  choose A b hAb using fun p : ℕ => out_pred n hn name c (Function.invFun R p)
  refine ⟨A, b, ?_⟩
  have hgood : ∀ w, (∀ i, out n hn name c w i = (A (R w) w + b (R w)) i) ↔
      adm n hn (mix n hn (w - Function.invFun R (R w))) := by
    intro w
    unfold adm
    exact forall_congr' (fun i => hAb _ w i)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hgood)]
  refine coset_count n N (fun w => Function.invFun R (R w)) (fun x => adm n hn (mix n hn x))
    (fun w => (hR w _).mp (hrep w).symm) (fun w u hu => ?_)
  refine congrArg (Function.invFun R) (((hR _ _).mpr ?_).trans (hrep w))
  rw [add_sub_cancel_left]
  exact hu

lemma nonadaptive_count (n : ℕ) (hn : 0 < n) (h : ℕ)
    (name c : Fin n → ZMod 2) (φ : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card (LinearMap.ker (LinearMap.pi φ)) *
        Nat.card {w : Fin n → ZMod 2 // ∀ i, out n hn name c w i =
          (A (run n h (fun j _ => φ j) w) w + b (run n h (fun j _ => φ j) w)) i} =
      2^n * Nat.card {u : LinearMap.ker (LinearMap.pi φ) //
        adm n hn (mix n hn (u : Fin n → ZMod 2))} := by
  refine nonadaptive_aux n hn name c _ _ ?_
  intro w w'
  obtain ⟨p, hp⟩ := run_eq_iff n h (fun j _ => φ j) w'
  rw [hp w, LinearMap.mem_ker]
  constructor
  · intro hj
    funext j
    exact hj j
  · intro hj j
    exact congrFun hj j

lemma fib {U V : Type} [AddCommGroup U] [AddCommGroup V] [Module (ZMod 2) U]
    [Module (ZMod 2) V] (f : U →ₗ[ZMod 2] V) (P : V → Prop) :
    Nat.card {u : U // P (f u)} =
      Nat.card {x : V // (∃ u, f u = x) ∧ P x} * Nat.card (LinearMap.ker f) := by
  classical
  choose! sec hsec using fun (x : V) (h : ∃ u, f u = x) => h
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun u => (⟨f u.1, ⟨u.1, rfl⟩, u.2⟩, ⟨u.1 - sec (f u.1), by
        rw [LinearMap.mem_ker, map_sub, hsec _ ⟨u.1, rfl⟩, sub_self]⟩)
      invFun := fun y => ⟨sec y.1.1 + y.2.1, by
        rw [map_add, hsec _ y.1.2.1, LinearMap.mem_ker.mp y.2.2, add_zero]
        exact y.1.2.2⟩
      left_inv := fun u => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun y => by
        have e : f (sec y.1.1 + y.2.1) = y.1.1 := by
          rw [map_add, hsec _ y.1.2.1, LinearMap.mem_ker.mp y.2.2, add_zero]
        refine Prod.ext (Subtype.ext e) (Subtype.ext ?_)
        show sec y.1.1 + y.2.1 - sec (f (sec y.1.1 + y.2.1)) = y.2.1
        rw [e, add_sub_cancel_left] }

noncomputable def baseL (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearMap.pi (fun j => dotL n (base n j))

lemma baseL_apply (n : ℕ) (x : Fin n → ZMod 2) (j : Fin 4) :
    baseL n x j = dot n (base n j) x := dot_comm n _ _

lemma dot_single (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) :
    dot n z (Pi.single i 1) = z i := by
  simp [dot, Pi.single_apply]

lemma baseL_surj (n : ℕ) (h6n : 6 ≤ n) : Function.Surjective (baseL n) := by
  intro g
  let site : Fin 4 → Fin n := fun k => ⟨if k.val < 2 then 2 * k.val else 2 * k.val - 3, by
    have := k.2
    split_ifs <;> omega⟩
  have key : ∀ j k : Fin 4, base n j (site k) = if k = j then 1 else 0 := by
    intro j k
    rw [base_apply]
    fin_cases j <;> fin_cases k <;> simp [site]
  refine ⟨∑ k, g k • Pi.single (site k) 1, ?_⟩
  funext j
  have e : ∀ k, baseL n (g k • Pi.single (site k) 1) j = if k = j then g k else 0 := by
    intro k
    rw [map_smul, Pi.smul_apply, baseL_apply, dot_single, key, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
  rw [map_sum, Finset.sum_apply, Finset.sum_congr rfl (fun k _ => e k)]
  simp

lemma mix_surj (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (x : Fin n → ZMod 2)
    (hx : ∀ j, dot n (base n j) x = 0) : ∃ w, mix n hn w = x := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  have hle : LinearMap.range (mixL n hn) ≤ LinearMap.ker (baseL n) := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    funext j
    rw [baseL_apply]
    exact base_dot_mix n hn h6 j w
  have h1 := LinearMap.finrank_range_add_finrank_ker (mixL n hn)
  have h2 := LinearMap.finrank_range_add_finrank_ker (baseL n)
  rw [LinearMap.range_eq_top.mpr (baseL_surj n h6n), finrank_top, Module.finrank_fin_fun] at h2
  rw [Module.finrank_fin_fun] at h1 h2
  have hc : Nat.card (LinearMap.ker (mixL n hn)) ≤ 16 := ker_mix_card n hn h6
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have h3 : Module.finrank (ZMod 2) (LinearMap.ker (mixL n hn)) ≤ 4 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp (hc.trans_eq (by norm_num))
  have hx' : x ∈ LinearMap.ker (baseL n) := by
    rw [LinearMap.mem_ker]
    funext j
    rw [baseL_apply]
    exact hx j
  rw [← Submodule.eq_of_le_of_finrank_le hle (by omega)] at hx'
  exact hx'

def lam (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) (i : Fin h) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun x => ∑ s, v i s * x (ix n hn (2*s.val))
    map_add' := fun x y => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := fun r x => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring) }

lemma lam_apply (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) (i : Fin h)
    (x : Fin n → ZMod 2) : lam n hn v i x = ∑ s, v i s * x (ix n hn (2*s.val)) := rfl

lemma lam_even (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (i : Fin h) (x : Fin n → ZMod 2) : lam n hn v i (even n x) = lam n hn v i x := by
  rw [lam_apply, lam_apply]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [even_apply_even n x _ (by rw [ix_val, Nat.mod_mod_of_dvd _ h2, Nat.mul_mod_right])]

def InX (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) (x : Fin n → ZMod 2) :
    Prop :=
  (∀ j, dot n (base n j) x = 0) ∧ ∀ i, lam n hn v i x = 0

lemma base_even (n : ℕ) (x : Fin n → ZMod 2) (hx : ∀ j, dot n (base n j) x = 0) (j : Fin 4) :
    dot n (base n j) (even n x) = 0 := by
  rw [← dot_even]
  rcases even_base n j with h | h
  · rw [h, hx j]
  · rw [h, dot_zero_left]

def phi (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) (i : Fin h) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (lam n hn v i).comp (mixL n hn)

def Kq (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (LinearMap.pi (phi n hn v))

lemma mem_Kq (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (w : Fin n → ZMod 2) : w ∈ Kq n hn v ↔ ∀ i, lam n hn v i (mix n hn w) = 0 := by
  unfold Kq
  rw [LinearMap.mem_ker]
  exact funext_iff

lemma mixK_range (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (x : Fin n → ZMod 2) :
    (∃ u : Kq n hn v, ((mixL n hn).comp (Kq n hn v).subtype) u = x) ↔ InX n hn v x := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fun j => base_dot_mix n hn h6 j _, (mem_Kq n hn v _).1 u.2⟩
  · rintro ⟨hb, hl⟩
    obtain ⟨w, rfl⟩ := mix_surj n hn h6 x hb
    exact ⟨⟨w, (mem_Kq n hn v w).2 hl⟩, rfl⟩

lemma tau_range (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (x : Fin n → ZMod 2) :
    (∃ u, tau n hn (Kq n hn v) u = x) ↔ InX n hn v x := by
  have h2 : 2 ∣ n := Dvd.dvd.trans (by norm_num) h6
  constructor
  · rintro ⟨u, rfl⟩
    rw [tau_apply]
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [dot_add_right, base_even n _ (fun j => base_dot_mix n hn h6 j _) j,
        base_dot_mix n hn h6, add_zero]
    · rw [map_add, lam_even n hn h2, (mem_Kq n hn v _).1 u.1.2 i, zero_add,
        ← lam_even n hn h2, even_mix_oddKer, map_zero]
  · rintro ⟨hb, hl⟩
    obtain ⟨w, rfl⟩ := mix_surj n hn h6 x hb
    obtain ⟨κ, hκ⟩ := mix_surj n hn h6 (mix n hn w + even n (mix n hn w)) (fun j => by
      rw [dot_add_right, hb j, base_even n _ hb j, add_zero])
    have he : even n (mix n hn κ) = 0 := by
      rw [hκ, even_add, even_even, fn_add_self]
    have hκK : κ ∈ Kq n hn v := (mem_Kq n hn v κ).2 (fun i => by
      rw [← lam_even n hn h2, he, map_zero])
    refine ⟨(⟨w, (mem_Kq n hn v w).2 hl⟩, ⟨κ, (mem_oddKer n hn _ κ).2 ⟨hκK, he⟩⟩), ?_⟩
    rw [tau_apply]
    show even n (mix n hn w) + mix n hn κ = mix n hn w
    rw [hκ, add_comm (mix n hn w), ← add_assoc, fn_add_self, zero_add]

lemma sum_cells (n : ℕ) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (P : (Fin n → ZMod 2) → Prop) :
    Nat.card K * Nat.card {w // P w} =
      ∑ w0 : Fin n → ZMod 2, Nat.card {k : K // P (w0 + (k : Fin n → ZMod 2))} := by
  rw [← Nat.card_sigma, ← Nat.card_prod]
  refine Nat.card_congr ((Equiv.trans ?_
    (Equiv.subtypeProdEquivSigmaSubtype (fun (w0 : Fin n → ZMod 2) (k : K) =>
      P (w0 + (k : Fin n → ZMod 2))))))
  exact
    { toFun := fun y => ⟨(y.2.1 - (y.1 : Fin n → ZMod 2), y.1), by
        show P (y.2.1 - (y.1 : Fin n → ZMod 2) + (y.1 : Fin n → ZMod 2))
        rw [sub_add_cancel]
        exact y.2.2⟩
      invFun := fun p => (p.1.2, ⟨p.1.1 + (p.1.2 : Fin n → ZMod 2), p.2⟩)
      left_inv := fun y => Prod.ext rfl (Subtype.ext (sub_add_cancel _ _))
      right_inv := fun p => Subtype.ext (Prod.ext (add_sub_cancel_right _ _) rfl) }

lemma cell_bound (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (name c w0 : Fin n → ZMod 2) (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : Fin n → ZMod 2) :
    Nat.card {k : Kq n hn v // out n hn name c (w0 + (k : Fin n → ZMod 2)) =
        A (w0 + (k : Fin n → ZMod 2)) + b} * Nat.card {x // InX n hn v x} ≤
      Nat.card (Kq n hn v) * Nat.card {x // InX n hn v x ∧ adm n hn x} := by
  have h2 : 2 ∣ n := Dvd.dvd.trans (by norm_num) h6
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  have e1 : Nat.card {k : Kq n hn v // out n hn name c (w0 + (k : Fin n → ZMod 2)) =
        A (w0 + (k : Fin n → ZMod 2)) + b} =
      Nat.card {k : Kq n hn v // ∀ i, out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
        (A (w0 + (k : Fin n → ZMod 2)) + b) i} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun k => funext_iff))
  have hp := pairs_bound n hn h2 (Kq n hn v) (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A)
  have f1 := fib (tau n hn (Kq n hn v)) (adm n hn)
  have f2 := fib (tau n hn (Kq n hn v)) (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
    and_congr_left (fun _ => tau_range n hn h6 v x)))] at f1
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_prod,
    Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
      (iff_of_eq (and_true _)).trans (tau_range n hn h6 v x)))] at f2
  rw [e1, hit_card n hn name c _ w0 A L b c0 hL]
  rw [f1] at hp
  have hpos : 0 < Nat.card (oddKer n hn (Kq n hn v)) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card (oddKer n hn (Kq n hn v)) * (Nat.card {k : Kq n hn v //
          Hit n hn _ (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} *
          Nat.card {x // InX n hn v x})
      ≤ Nat.card {x // InX n hn v x ∧ adm n hn x} *
          Nat.card (LinearMap.ker (tau n hn (Kq n hn v))) * Nat.card {x // InX n hn v x} := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_right _ hp
    _ = Nat.card (oddKer n hn (Kq n hn v)) * (Nat.card (Kq n hn v) *
          Nat.card {x // InX n hn v x ∧ adm n hn x}) := by
        rw [mul_assoc, mul_comm (Nat.card (LinearMap.ker _)), ← f2]
        ring

noncomputable def runq (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (w : Fin n → ZMod 2) : ℕ :=
  run n h (fun i _ => phi n hn v i) w

lemma runq_add (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (w0 : Fin n → ZMod 2) (k : Kq n hn v) :
    runq n hn v (w0 + (k : Fin n → ZMod 2)) = runq n hn v w0 := by
  obtain ⟨p, hp⟩ := run_eq_iff n h (fun i _ => phi n hn v i) w0
  refine (hp _).2 (fun i => ?_)
  rw [add_sub_cancel_left]
  exact (mem_Kq n hn v _).1 k.2 i

lemma upper_X (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (name c : Fin n → ZMod 2) (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : ℕ → (Fin n → ZMod 2)) :
    Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (runq n hn v w) w + b (runq n hn v w)} * Nat.card {x // InX n hn v x} ≤
      2^n * Nat.card {x // InX n hn v x ∧ adm n hn x} := by
  have hpos : 0 < Nat.card (Kq n hn v) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  rw [← mul_assoc, sum_cells, Finset.sum_mul]
  have hW : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2^n := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  calc ∑ w0 : Fin n → ZMod 2, Nat.card {k : Kq n hn v //
          out n hn name c (w0 + (k : Fin n → ZMod 2)) =
            A (runq n hn v (w0 + (k : Fin n → ZMod 2))) (w0 + (k : Fin n → ZMod 2)) +
              b (runq n hn v (w0 + (k : Fin n → ZMod 2)))} * Nat.card {x // InX n hn v x}
      ≤ ∑ _w0 : Fin n → ZMod 2,
          Nat.card (Kq n hn v) * Nat.card {x // InX n hn v x ∧ adm n hn x} := by
        refine Finset.sum_le_sum (fun w0 _ => ?_)
        simp only [runq_add]
        exact cell_bound n hn h6 v name c w0 _ _
    _ = Nat.card (Kq n hn v) * (2^n * Nat.card {x // InX n hn v x ∧ adm n hn x}) := by
        rw [Finset.sum_const, hW, smul_eq_mul]
        ring

lemma lower_X (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2)
    (name c : Fin n → ZMod 2) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (runq n hn v w) w + b (runq n hn v w)} * Nat.card {x // InX n hn v x} =
      2^n * Nat.card {x // InX n hn v x ∧ adm n hn x} := by
  obtain ⟨A, b, hAb⟩ := nonadaptive_count n hn h name c (phi n hn v)
  refine ⟨A, b, ?_⟩
  have f1 := fib ((mixL n hn).comp (Kq n hn v).subtype) (adm n hn)
  have f2 := fib ((mixL n hn).comp (Kq n hn v).subtype) (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
    and_congr_left (fun _ => mixK_range n hn h6 v x)))] at f1
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
    Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
      (iff_of_eq (and_true _)).trans (mixK_range n hn h6 v x)))] at f2
  have e1 : Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (runq n hn v w) w + b (runq n hn v w)} =
      Nat.card {w : Fin n → ZMod 2 // ∀ i, out n hn name c w i =
        (A (run n h (fun j _ => phi n hn v j) w) w +
          b (run n h (fun j _ => phi n hn v j) w)) i} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun w => funext_iff))
  have hAb' : Nat.card (Kq n hn v) * Nat.card {w : Fin n → ZMod 2 // ∀ i,
      out n hn name c w i = (A (run n h (fun j _ => phi n hn v j) w) w +
        b (run n h (fun j _ => phi n hn v j) w)) i} =
      2^n * Nat.card {u : Kq n hn v // adm n hn (mix n hn (u : Fin n → ZMod 2))} := hAb
  have f1' : Nat.card {u : Kq n hn v // adm n hn (mix n hn (u : Fin n → ZMod 2))} =
      Nat.card {x // InX n hn v x ∧ adm n hn x} *
        Nat.card (LinearMap.ker ((mixL n hn).comp (Kq n hn v).subtype)) := f1
  have hpos : 0 < Nat.card (LinearMap.ker ((mixL n hn).comp (Kq n hn v).subtype)) :=
    Nat.card_pos
  rw [e1]
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc Nat.card (LinearMap.ker ((mixL n hn).comp (Kq n hn v).subtype)) *
        (Nat.card {w : Fin n → ZMod 2 // ∀ i, out n hn name c w i =
          (A (run n h (fun j _ => phi n hn v j) w) w +
            b (run n h (fun j _ => phi n hn v j) w)) i} * Nat.card {x // InX n hn v x})
      = Nat.card (Kq n hn v) * Nat.card {w : Fin n → ZMod 2 // ∀ i, out n hn name c w i =
          (A (run n h (fun j _ => phi n hn v j) w) w +
            b (run n h (fun j _ => phi n hn v j) w)) i} := by
        rw [f2]
        ring
    _ = Nat.card (LinearMap.ker ((mixL n hn).comp (Kq n hn v).subtype)) *
        (2^n * Nat.card {x // InX n hn v x ∧ adm n hn x}) := by
        rw [hAb', f1']
        ring

def nxt (a : ℕ) (ha : 0 < a) (i : Fin a) : Fin a := ⟨(i.val+1) % a, Nat.mod_lt _ ha⟩

def cs (a r : ℕ) (e : Fin a → ZMod 2) : ZMod 2 := ∑ s : Fin a, if s.val % 3 = r then e s else 0

def bal (a : ℕ) (e : Fin a → ZMod 2) : Prop := cs a 0 e + cs a 2 e = 0 ∧ cs a 1 e + cs a 2 e = 0

def blocked (a : ℕ) (ha : 0 < a) (e : Fin a → ZMod 2) : Finset (Fin a) :=
  Finset.univ.filter (fun p => e p ≠ 0 ∨ e (nxt a ha p) ≠ 0)

def wt {ι : Type} [Fintype ι] (e : ι → ZMod 2) : ℕ := (Finset.univ.filter (fun s => e s ≠ 0)).card

def qker (a h : ℕ) (v : Fin h → Fin a → ZMod 2) (e : Fin a → ZMod 2) : Prop :=
  bal a e ∧ ∀ i, ∑ s, v i s * e s = 0

lemma nxt_val (a : ℕ) (ha : 0 < a) (i : Fin a) :
    (nxt a ha i).val = if i.val + 1 = a then 0 else i.val + 1 := by
  have := i.2
  unfold nxt
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

lemma nxt_bijective (a : ℕ) (ha : 0 < a) : Function.Bijective (nxt a ha) := by
  refine Finite.injective_iff_bijective.mp (fun i i' h => ?_)
  have h1 := congrArg Fin.val h
  rw [nxt_val, nxt_val] at h1
  have := i.2
  have := i'.2
  ext
  split_ifs at h1 <;> omega

def idx (t : ℕ) : Fin (3*t) ⊕ Fin (3*t) ≃ Fin (6*t) where
  toFun := Sum.elim (fun s => ⟨2*s.val, by have := s.2; omega⟩)
    (fun s => ⟨2*s.val+1, by have := s.2; omega⟩)
  invFun i := if i.val % 2 = 0 then Sum.inl ⟨i.val/2, by have := i.2; omega⟩
    else Sum.inr ⟨i.val/2, by have := i.2; omega⟩
  left_inv := by
    rintro (s | s)
    · have h : 2 * s.val % 2 = 0 := by omega
      have h' : 2 * s.val / 2 = s.val := by omega
      simp [h, h']
    · have h : (2 * s.val + 1) % 2 = 1 := by omega
      have h' : (2 * s.val + 1) / 2 = s.val := by omega
      simp [h, h']
  right_inv := by
    intro i
    by_cases h : i.val % 2 = 0
    · simp only [h, ↓reduceIte, Sum.elim_inl]
      ext
      show 2*(i.val/2) = i.val
      omega
    · simp only [h, ↓reduceIte, Sum.elim_inr]
      ext
      show 2*(i.val/2)+1 = i.val
      omega

def evens (t : ℕ) (x : Fin (6*t) → ZMod 2) (s : Fin (3*t)) : ZMod 2 := x (idx t (Sum.inl s))

def odds (t : ℕ) (x : Fin (6*t) → ZMod 2) (s : Fin (3*t)) : ZMod 2 := x (idx t (Sum.inr s))

def split (t : ℕ) :
    (Fin (6*t) → ZMod 2) ≃ (Fin (3*t) → ZMod 2) × (Fin (3*t) → ZMod 2) :=
  ((idx t).symm.arrowCongr (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

lemma split_apply (t : ℕ) (x : Fin (6*t) → ZMod 2) : split t x = (evens t x, odds t x) := rfl

lemma sum_split (t : ℕ) (f : Fin (6*t) → ZMod 2) :
    ∑ i, f i = ∑ s, f (idx t (Sum.inl s)) + ∑ s, f (idx t (Sum.inr s)) := by
  rw [← Fintype.sum_sum_type (fun y => f (idx t y))]
  exact (Equiv.sum_comp (idx t) f).symm

lemma ix_even (t : ℕ) (hn : 0 < 6*t) (s : Fin (3*t)) :
    ix (6*t) hn (2*s.val) = idx t (Sum.inl s) := by
  have := s.2
  ext
  exact Nat.mod_eq_of_lt (by omega)

lemma ix_odd (t : ℕ) (hn : 0 < 6*t) (s : Fin (3*t)) :
    ix (6*t) hn (2*s.val+1) = idx t (Sum.inr s) := by
  have := s.2
  ext
  exact Nat.mod_eq_of_lt (by omega)

lemma ix_even_succ (t : ℕ) (hn : 0 < 6*t) (ha : 0 < 3*t) (s : Fin (3*t)) :
    ix (6*t) hn (2*s.val+2) = idx t (Sum.inl (nxt (3*t) ha s)) := by
  ext
  show (2*s.val+2) % (6*t) = 2*((s.val+1) % (3*t))
  rw [show 6*t = 2*(3*t) by ring, show 2*s.val+2 = 2*(s.val+1) by ring, Nat.mul_mod_mul_left]

lemma cs_add (a r : ℕ) (e e' : Fin a → ZMod 2) : cs a r (e + e') = cs a r e + cs a r e' := by
  unfold cs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs
  · rfl
  · rw [add_zero]

lemma cs_single (a r : ℕ) (p : Fin a) (z : ZMod 2) :
    cs a r (Pi.single p z) = if p.val % 3 = r then z else 0 := by
  unfold cs
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro s _ hs
    rw [Pi.single_eq_of_ne hs, ite_self]
  · intro h
    exact absurd (Finset.mem_univ p) h

lemma bal_zero (a : ℕ) : bal a 0 := by
  unfold bal cs
  simp

lemma bal_add (a : ℕ) (e e' : Fin a → ZMod 2) (h : bal a e) (h' : bal a e') : bal a (e + e') := by
  unfold bal at *
  rw [cs_add, cs_add, cs_add]
  constructor
  · linear_combination h.1 + h'.1
  · linear_combination h.2 + h'.2

lemma base_iff_bal (t : ℕ) (x : Fin (6*t) → ZMod 2) :
    (∀ j, dot (6*t) (base (6*t) j) x = 0) ↔ bal (3*t) (evens t x) ∧ bal (3*t) (odds t x) := by
  have key : ∀ j : Fin 4, dot (6*t) (base (6*t) j) x =
      if j.val / 2 = 0 then cs (3*t) (j.val % 2) (evens t x) + cs (3*t) 2 (evens t x)
      else cs (3*t) (j.val % 2) (odds t x) + cs (3*t) 2 (odds t x) := by
    intro j
    unfold dot
    rw [sum_split]
    have hl : ∀ s : Fin (3*t), base (6*t) j (idx t (Sum.inl s)) * x (idx t (Sum.inl s)) =
        if j.val / 2 = 0 then (if s.val % 3 = j.val % 2 then evens t x s else 0) +
          (if s.val % 3 = 2 then evens t x s else 0) else 0 := by
      intro s
      rw [base_apply]
      have e1 : (idx t (Sum.inl s)).val = 2*s.val := rfl
      have e2 : 2*s.val % 2 = 0 := by omega
      have e3 : 2*s.val / 2 = s.val := by omega
      have hj : j.val % 2 < 2 := by omega
      rw [e1, e2, e3]
      unfold evens
      split_ifs <;> first | omega | simp
    have hr : ∀ s : Fin (3*t), base (6*t) j (idx t (Sum.inr s)) * x (idx t (Sum.inr s)) =
        if j.val / 2 = 0 then 0 else (if s.val % 3 = j.val % 2 then odds t x s else 0) +
          (if s.val % 3 = 2 then odds t x s else 0) := by
      intro s
      rw [base_apply]
      have e1 : (idx t (Sum.inr s)).val = 2*s.val+1 := rfl
      have e2 : (2*s.val+1) % 2 = 1 := by omega
      have e3 : (2*s.val+1) / 2 = s.val := by omega
      have hj : j.val % 2 < 2 := by omega
      have hj2 : j.val / 2 < 2 := by omega
      rw [e1, e2, e3]
      unfold odds
      split_ifs <;> first | omega | simp
    rw [Finset.sum_congr rfl (fun s _ => hl s), Finset.sum_congr rfl (fun s _ => hr s)]
    unfold cs
    split_ifs
    · rw [Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
    · rw [Finset.sum_const_zero, zero_add, Finset.sum_add_distrib]
  rw [Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one,
    key, key, key, key]
  unfold bal
  simp only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    ite_true, one_ne_zero, ite_false]
  tauto

def compat (a : ℕ) (ha : 0 < a) (e o : Fin a → ZMod 2) : Prop :=
  ∀ q ∈ blocked a ha e, o q = 0

lemma adm_iff_compat (t : ℕ) (hn : 0 < 6*t) (ha : 0 < 3*t) (x : Fin (6*t) → ZMod 2) :
    adm (6*t) hn x ↔ compat (3*t) ha (evens t x) (odds t x) := by
  have hz : ∀ u w : ZMod 2, u * w = 0 ↔ (u ≠ 0 → w = 0) := by decide
  have hz' : ∀ u w : ZMod 2, w * u = 0 ↔ (u ≠ 0 → w = 0) := by decide
  unfold compat blocked
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h q hq
    rcases hq with hq | hq
    · have h1 := h (ix (6*t) hn (2*q.val + (6*t-1)))
      rw [ix_val_add, ix_val_add, show 2*q.val + (6*t-1) + 1 = 2*q.val + 6*t by omega,
        show 2*q.val + (6*t-1) + 2 = 2*q.val + 1 + 6*t by omega, ix_add_n, ix_add_n,
        ix_even, ix_odd] at h1
      exact (hz _ _).1 h1 hq
    · have h1 := h (idx t (Sum.inl q))
      rw [show (idx t (Sum.inl q)).val = 2*q.val from rfl, ix_odd, ix_even_succ t hn ha] at h1
      exact (hz' _ _).1 h1 hq
  · intro h i
    obtain ⟨y, rfl⟩ := (idx t).surjective i
    rcases y with s | s
    · rw [show (idx t (Sum.inl s)).val = 2*s.val from rfl, ix_odd, ix_even_succ t hn ha]
      exact (hz' _ _).2 (fun hs => h s (Or.inr hs))
    · have hs := h (nxt (3*t) ha s)
      rw [show (idx t (Sum.inr s)).val + 1 = 2*s.val+2 from rfl, ix_even_succ t hn ha,
        show (idx t (Sum.inr s)).val + 2 = 2*s.val+2+1 from rfl]
      have e : ix (6*t) hn (2*s.val+2+1) = idx t (Sum.inr (nxt (3*t) ha s)) := by
        rw [← ix_odd t hn, ← ix_val_add, ix_even_succ t hn ha]
        rfl
      rw [e]
      exact (hz _ _).2 (fun hs' => hs (Or.inl hs'))

lemma zero_count (a : ℕ) (T : Finset (Fin a)) :
    Nat.card {o : Fin a → ZMod 2 // ∀ q ∈ T, o q = 0} * 2^T.card = 2^a := by
  classical
  have e : {o : Fin a → ZMod 2 // ∀ q ∈ T, o q = 0} ≃ ({q : Fin a // q ∉ T} → ZMod 2) :=
    { toFun := fun o q => o.1 q.1
      invFun := fun g => ⟨fun q => if h : q ∈ T then 0 else g ⟨q, h⟩, fun q hq => by simp [hq]⟩
      left_inv := fun o => by
        ext q
        by_cases h : q ∈ T
        · simp [h, o.2 q h]
        · simp [h]
      right_inv := fun g => by
        funext q
        simp [q.2] }
  have hc : Nat.card {q : Fin a // q ∉ T} = a - T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hT : T.card ≤ a := (Finset.card_le_univ T).trans_eq (Fintype.card_fin a)
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, hc, ← pow_add, Nat.sub_add_cancel hT]

lemma bal_count (a : ℕ) (T : Finset (Fin a)) (p p' : Fin a) (hp : p ∉ T) (hp' : p' ∉ T)
    (h0 : p.val % 3 = 0) (h1 : p'.val % 3 = 1) :
    Nat.card {o : Fin a → ZMod 2 // bal a o ∧ ∀ q ∈ T, o q = 0} * 2^(T.card + 2) = 2^a := by
  have hα : ∀ (o : Fin a → ZMod 2) (z z' : ZMod 2),
      cs a 0 (o + Pi.single p z + Pi.single p' z') + cs a 2 (o + Pi.single p z + Pi.single p' z')
        = cs a 0 o + cs a 2 o + z := by
    intro o z z'
    simp only [cs_add, cs_single, h0, h1]
    norm_num
    ring
  have hβ : ∀ (o : Fin a → ZMod 2) (z z' : ZMod 2),
      cs a 1 (o + Pi.single p z + Pi.single p' z') + cs a 2 (o + Pi.single p z + Pi.single p' z')
        = cs a 1 o + cs a 2 o + z' := by
    intro o z z'
    simp only [cs_add, cs_single, h0, h1]
    norm_num
    ring
  have hT : ∀ (o : Fin a → ZMod 2) (z z' : ZMod 2), (∀ q ∈ T, o q = 0) →
      ∀ q ∈ T, (o + Pi.single p z + Pi.single p' z' : Fin a → ZMod 2) q = 0 := by
    intro o z z' ho q hq
    have h1 : q ≠ p := fun h => hp (h ▸ hq)
    have h2 : q ≠ p' := fun h => hp' (h ▸ hq)
    simp [ho q hq, h1, h2]
  have hcancel : ∀ (o : Fin a → ZMod 2) (z z' : ZMod 2),
      o + Pi.single p z + Pi.single p' z' + Pi.single p z + Pi.single p' z' = o := by
    intro o z z'
    calc o + Pi.single p z + Pi.single p' z' + Pi.single p z + Pi.single p' z'
        = o + (Pi.single p z + Pi.single p z) + (Pi.single p' z' + Pi.single p' z') := by abel
      _ = o := by rw [fn_add_self, fn_add_self, add_zero, add_zero]
  have key : Nat.card {o : Fin a → ZMod 2 // ∀ q ∈ T, o q = 0} =
      Nat.card {o : Fin a → ZMod 2 // bal a o ∧ ∀ q ∈ T, o q = 0} * 4 := by
    have h4 : Nat.card (ZMod 2 × ZMod 2) = 4 := by
      rw [Nat.card_prod, Nat.card_zmod]
    rw [← h4, ← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun o => (⟨o.1 + Pi.single p (cs a 0 o.1 + cs a 2 o.1) +
            Pi.single p' (cs a 1 o.1 + cs a 2 o.1),
          ⟨by rw [hα, z2_add_self], by rw [hβ, z2_add_self]⟩, hT _ _ _ o.2⟩,
          (cs a 0 o.1 + cs a 2 o.1, cs a 1 o.1 + cs a 2 o.1))
        invFun := fun y => ⟨y.1.1 + Pi.single p y.2.1 + Pi.single p' y.2.2, hT _ _ _ y.1.2.2⟩
        left_inv := fun o => Subtype.ext (hcancel _ _ _)
        right_inv := fun y => by
          have e1 : cs a 0 (y.1.1 + Pi.single p y.2.1 + Pi.single p' y.2.2) +
              cs a 2 (y.1.1 + Pi.single p y.2.1 + Pi.single p' y.2.2) = y.2.1 := by
            rw [hα, y.1.2.1.1, zero_add]
          have e2 : cs a 1 (y.1.1 + Pi.single p y.2.1 + Pi.single p' y.2.2) +
              cs a 2 (y.1.1 + Pi.single p y.2.1 + Pi.single p' y.2.2) = y.2.2 := by
            rw [hβ, y.1.2.1.2, zero_add]
          refine Prod.ext (Subtype.ext ?_) (Prod.ext e1 e2)
          show y.1.1 + Pi.single p y.2.1 + Pi.single p' y.2.2 + Pi.single p _ + Pi.single p' _
            = y.1.1
          rw [e1, e2, hcancel] }
  rw [← zero_count a T, key]
  ring

noncomputable def cnt (a : ℕ) (ha : 0 < a) (e : Fin a → ZMod 2) : ℕ :=
  Nat.card {o : Fin a → ZMod 2 // bal a o ∧ compat a ha e o}

lemma cnt_le (a : ℕ) (ha : 0 < a) (e : Fin a → ZMod 2) :
    cnt a ha e * 2^(blocked a ha e).card ≤ 2^a := by
  rw [← zero_count a (blocked a ha e)]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective
    (fun o : {o : Fin a → ZMod 2 // bal a o ∧ compat a ha e o} =>
      (⟨o.1, o.2.2⟩ : {o : Fin a → ZMod 2 // ∀ q ∈ blocked a ha e, o q = 0}))
    (fun o o' h => Subtype.ext (congrArg
      (fun y : {o : Fin a → ZMod 2 // ∀ q ∈ blocked a ha e, o q = 0} => y.1) h)))

lemma free_lanes (t : ℕ) (ha : 0 < 3*t) (e : Fin (3*t) → ZMod 2) (hw : wt e < t) :
    ∃ p p' : Fin (3*t), p ∉ blocked (3*t) ha e ∧ p' ∉ blocked (3*t) ha e ∧
      p.val % 3 = 0 ∧ p'.val % 3 = 1 := by
  have hdead : ∃ i0 : Fin t, ∀ s : Fin (3*t), e s ≠ 0 → s.val / 3 ≠ i0.val := by
    by_contra hcon
    have hall : ∀ i0 : Fin t, ∃ s : Fin (3*t), e s ≠ 0 ∧ s.val / 3 = i0.val := fun i0 => by
      by_contra h
      exact hcon ⟨i0, fun s hs hs' => h ⟨s, hs, hs'⟩⟩
    choose f hf using hall
    have hinj : Function.Injective f := fun i i' h => by
      ext
      rw [← (hf i).2, ← (hf i').2, h]
    have hle := Finset.card_le_card_of_injOn (s := Finset.univ)
      (t := Finset.univ.filter (fun s => e s ≠ 0)) f
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf i).1⟩) hinj.injOn
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact absurd hw (not_lt.mpr hle)
  obtain ⟨i0, hi0⟩ := hdead
  have h3 := i0.2
  have hb : ∀ p : Fin (3*t), p.val / 3 = i0.val → p.val % 3 ≠ 2 → p ∉ blocked (3*t) ha e := by
    intro p hp1 hp2 hp
    rcases (Finset.mem_filter.mp hp).2 with h | h
    · exact hi0 p h hp1
    · refine hi0 _ h ?_
      rw [nxt_val]
      have := p.2
      split_ifs <;> omega
  exact ⟨⟨3*i0.val, by omega⟩, ⟨3*i0.val+1, by omega⟩,
    hb _ (by show 3*i0.val/3 = _; omega) (by show 3*i0.val % 3 ≠ 2; omega),
    hb _ (by show (3*i0.val+1)/3 = _; omega) (by show (3*i0.val+1) % 3 ≠ 2; omega),
    by show 3*i0.val % 3 = 0; omega, by show (3*i0.val+1) % 3 = 1; omega⟩

lemma blocked_card (a : ℕ) (ha : 0 < a) (e : Fin a → ZMod 2)
    (hs : ∀ s, e s ≠ 0 → e (nxt a ha s) = 0) : (blocked a ha e).card = 2 * wt e := by
  have hd : Disjoint (Finset.univ.filter (fun p => e p ≠ 0))
      (Finset.univ.filter (fun p => e (nxt a ha p) ≠ 0)) := by
    rw [Finset.disjoint_filter]
    exact fun p _ h1 h2 => h2 (hs p h1)
  have h2 : (Finset.univ.filter (fun p => e (nxt a ha p) ≠ 0)).card = wt e :=
    Finset.card_bij (fun p _ => nxt a ha p)
      (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
      (fun p _ p' _ h => (nxt_bijective a ha).1 h)
      (fun s hs => by
        obtain ⟨p, rfl⟩ := (nxt_bijective a ha).2 s
        exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩, rfl⟩)
  unfold blocked
  rw [Finset.filter_or, Finset.card_union_of_disjoint hd, h2]
  unfold wt
  ring

lemma cnt_light (t : ℕ) (ha : 0 < 3*t) (e : Fin (3*t) → ZMod 2)
    (hs : ∀ s, e s ≠ 0 → e (nxt (3*t) ha s) = 0) (hw : wt e < t) :
    cnt (3*t) ha e * 4^(wt e) = 2^(3*t-2) := by
  obtain ⟨p, p', hp, hp', h0, h1⟩ := free_lanes t ha e hw
  have h := bal_count (3*t) (blocked (3*t) ha e) p p' hp hp' h0 h1
  rw [blocked_card (3*t) ha e hs, pow_add, pow_mul] at h
  have h2 : (2:ℕ)^(3*t) = 2^(3*t-2) * 2^2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [h2, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

lemma cnt_spaced (t j : ℕ) (hjt : j+3 ≤ t) (ha : 0 < 3*t) (e : Fin (3*t) → ZMod 2)
    (hs : ∀ s, e s ≠ 0 → e (nxt (3*t) ha s) = 0) :
    cnt (3*t) ha e * 4^(min (wt e) (j+2)) ≤ 2^(3*t-2) := by
  rcases Nat.lt_or_ge (wt e) (j+3) with hw | hw
  · rw [Nat.min_eq_left (by omega)]
    exact (cnt_light t ha e hs (by omega)).le
  · rw [Nat.min_eq_right (by omega)]
    have h := cnt_le (3*t) ha e
    rw [blocked_card (3*t) ha e hs, pow_mul] at h
    have h2 : (2:ℕ)^(3*t) = 2^(3*t-2) * 4 := by
      rw [show (4:ℕ) = 2^2 by norm_num, ← pow_add]
      congr 1
      omega
    have h3 : (4:ℕ)^(j+2) * 4 ≤ (2^2)^(wt e) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hw
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 4 by norm_num)
    calc cnt (3*t) ha e * 4^(j+2) * 4 ≤ cnt (3*t) ha e * (2^2)^(wt e) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left _ h3
      _ ≤ 2^(3*t-2) * 4 := h.trans_eq h2

lemma wt_eq_sum {ι : Type} [Fintype ι] (e : ι → ZMod 2) : wt e = ∑ t, (e t).val := by
  rw [wt, Finset.card_filter]
  exact Finset.sum_congr rfl fun t _ =>
    (by decide : ∀ z : ZMod 2, (if z ≠ 0 then 1 else 0) = z.val) (e t)

lemma sum_pow_sub_le {α : Type*} (A : Finset α) (c : ℕ) (w : α → ℕ) :
    ∑ e ∈ A, 4^(c - w e) ≤ A.card * 4^c := by
  simpa using Finset.sum_le_card_nsmul A _ _ fun e _ =>
    Nat.pow_le_pow_right (by norm_num : 0 < 4) (Nat.sub_le c (w e))

lemma sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ z, f z = f 0 + f 1 :=
  Fin.sum_univ_two f

lemma two_mul_card_slice {ι : Type} {A : Finset (ι → ZMod 2)}
    (hA : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z ∈ A) {a b : ι → ZMod 2} (ha : a ∈ A) (hb : b ∈ A)
    {s : ι} (hs : a s ≠ b s) (z : ZMod 2) : 2 * (A.filter (fun e => e s = z)).card = A.card := by
  have hab : a s + b s = 1 := (by decide : ∀ p q : ZMod 2, p ≠ q → p + q = 1) _ _ hs
  have key : ∀ z : ZMod 2,
      (A.filter (fun e => e s = z)).card ≤ (A.filter (fun e => e s = z + 1)).card := fun z =>
    Finset.card_le_card_of_injOn (· + a + b)
      (fun e he => by
        obtain ⟨heA, rfl⟩ := Finset.mem_filter.1 he
        exact Finset.mem_filter.2 ⟨hA e heA a ha b hb, by simp [add_assoc, hab]⟩)
      (fun x _ y _ h => add_right_cancel (add_right_cancel h))
  have heq : (A.filter (fun e => e s = 0)).card = (A.filter (fun e => e s = 1)).card :=
    le_antisymm (key 0) (key 1)
  have h := Finset.card_eq_sum_card_fiberwise (s := A) (t := Finset.univ) (f := fun e => e s)
    fun _ _ => Finset.mem_univ _
  rw [sum_zmod_two] at h
  rcases z2_cases z with rfl | rfl <;> omega

theorem coset_bound {ι : Type} (S : Finset ι) (A : Finset (ι → ZMod 2))
    (hA : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z ∈ A)
    (hS : ∀ x ∈ A, ∀ y ∈ A, (∀ t ∈ S, x t = y t) → x = y)
    (d c : ℕ) (hd : 2^d ≤ A.card) (hc : d ≤ c) :
    8^d * ∑ e ∈ A, 4^(c - ∑ t ∈ S, (e t).val) ≤ A.card * 4^c * 5^d := by
  induction d generalizing S A c with
  | zero => simpa using sum_pow_sub_le A c _
  | succ d ih =>
    classical
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le (by simp) hd)
    obtain ⟨s, hs, hsab⟩ : ∃ s ∈ S, a s ≠ b s := by
      by_contra! h
      exact hab (hS a ha b hb h)
    have hcard := two_mul_card_slice hA ha hb hsab
    have slice : ∀ z : ZMod 2, 2 * (8^d * ∑ e ∈ A with e s = z, 4^(c - ∑ t ∈ S, (e t).val))
        ≤ A.card * 4^(c - z.val) * 5^d := fun z => by
      have hz := ZMod.val_lt z
      have hsum : ∑ e ∈ A with e s = z, 4^(c - ∑ t ∈ S, (e t).val)
          = ∑ e ∈ A with e s = z, 4^(c - z.val - ∑ t ∈ S.erase s, (e t).val) :=
        Finset.sum_congr rfl fun e he => by
          rw [← Finset.add_sum_erase _ _ hs, (Finset.mem_filter.1 he).2, Nat.sub_add_eq]
      have := ih (S.erase s) (A.filter (fun e => e s = z))
        (fun x hx y hy w hw => by
          simp only [Finset.mem_filter] at hx hy hw ⊢
          exact ⟨hA x hx.1 y hy.1 w hw.1, by simp [hx.2, hy.2, hw.2, CharTwo.add_self_eq_zero]⟩)
        (fun x hx y hy h => by
          simp only [Finset.mem_filter] at hx hy
          refine hS x hx.1 y hy.1 fun t ht => ?_
          by_cases hts : t = s
          · rw [hts, hx.2, hy.2]
          · exact h t (Finset.mem_erase.2 ⟨hts, ht⟩))
        (c - z.val) (by have := hcard z; rw [pow_succ] at hd; omega) (by omega)
      rw [hsum, ← hcard z]
      linarith
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    have h0 := slice 0
    have h1 := slice 1
    rw [← Finset.sum_fiberwise A (fun e => e s), sum_zmod_two]
    simp only [ZMod.val_zero, ZMod.val_one, Nat.sub_zero, Nat.add_sub_cancel, pow_succ] at h0 h1 ⊢
    linarith

theorem enum_bound {ι : Type} [Fintype ι] (V : Finset (ι → ZMod 2)) (h0 : (0 : ι → ZMod 2) ∈ V)
    (hadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (h1 : ∀ e ∈ V, e ≠ 0 → 2 ≤ wt e)
    (d c : ℕ) (hd : 2^d ≤ V.card) (hc : d + 1 ≤ c) :
    8^(d+1) * ∑ e ∈ V, 4^(c - min (wt e) c) ≤ V.card * 4^c * (5^(d+1) + 3^(d+1)) := by
  simp only [min_comm (wt _) c, tsub_min]
  induction d generalizing V c with
  | zero => norm_num; linarith [sum_pow_sub_le V c wt]
  | succ d ih =>
    classical
    obtain ⟨g, hg, hg0⟩ := Finset.exists_mem_ne (lt_of_lt_of_le (by simp) hd) 0
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hg0
    have hA : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, x + y + z ∈ V := fun x hx y hy z hz =>
      hadd _ (hadd x hx y hy) z hz
    have hcard := two_mul_card_slice hA hg h0 hs 0
    have hinj : ∀ x ∈ V, ∀ y ∈ V, (∀ t ∈ Finset.univ.erase s, x t = y t) → x = y := by
      intro x hx y hy h
      by_contra hxy
      have h2 := h1 (x + y) (hadd x hx y hy) fun h0 =>
        hxy (funext fun t => CharTwo.add_eq_zero.1 (congr_fun h0 t))
      rw [wt_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ s), Finset.sum_eq_zero
        fun t ht => by simp [h t ht, CharTwo.add_self_eq_zero]] at h2
      have := ZMod.val_lt ((x + y) s)
      omega
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    have hQ := coset_bound (Finset.univ.erase s) V hA hinj (d + 1) k hd (by omega)
    have hI := ih (V.filter (fun e => e s = 0)) (by simp [h0])
      (fun x hx y hy => by
        simp only [Finset.mem_filter] at hx hy ⊢
        exact ⟨hadd x hx.1 y hy.1, by simp [hx.2, hy.2]⟩)
      (fun e he => h1 e (Finset.mem_filter.1 he).1) (k + 1) (by rw [pow_succ] at hd; omega)
      (by omega)
    have key : 8 * ∑ e ∈ V, 4^(k + 1 - wt e)
        ≤ 8 * ∑ e ∈ V, 4^(k - ∑ t ∈ Finset.univ.erase s, (e t).val)
          + 6 * ∑ e ∈ V with e s = 0, 4^(k + 1 - wt e) := by
      rw [Finset.sum_filter]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun e _ => ?_
      rw [wt_eq_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
      generalize ∑ t ∈ Finset.univ.erase s, (e t).val = w
      rcases z2_cases (e s) with h | h
      · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) (by omega : k + 1 - w ≤ k - w + 1)
        rw [h, ZMod.val_zero, add_zero, ite_eq_left rfl]
        omega
      · rw [h, ZMod.val_one, Nat.add_sub_add_right, ite_eq_right one_ne_zero]
        omega
    have := Nat.mul_le_mul_left (8^(d+1)) key
    rw [← hcard] at hQ ⊢
    simp only [pow_succ] at hQ hI this ⊢
    linarith

def live (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) (s : Fin a) : Prop :=
  ∃ w : Fin n → ZMod 2, (∀ i, lam n hn v i (mix n hn w) = 0) ∧ mix n hn w (ix n hn (2*s.val)) ≠ 0

lemma InX_iff (t : ℕ) (hn : 0 < 6*t) {h : ℕ} (v : Fin h → Fin (3*t) → ZMod 2)
    (x : Fin (6*t) → ZMod 2) :
    InX (6*t) hn v x ↔ qker (3*t) h v (evens t x) ∧ bal (3*t) (odds t x) := by
  have hl : ∀ i, lam (6*t) hn v i x = ∑ s, v i s * evens t x s := fun i => by
    rw [lam_apply]
    exact Finset.sum_congr rfl (fun s _ => by rw [ix_even]; rfl)
  unfold InX qker
  rw [base_iff_bal]
  simp only [hl]
  tauto

lemma card_bal (t : ℕ) (ht : 0 < t) :
    Nat.card {o : Fin (3*t) → ZMod 2 // bal (3*t) o} = 2^(3*t-2) := by
  have h := bal_count (3*t) ∅ ⟨0, by omega⟩ ⟨1, by omega⟩ (Finset.notMem_empty _)
    (Finset.notMem_empty _) rfl rfl
  have e : Nat.card {o : Fin (3*t) → ZMod 2 // bal (3*t) o ∧
      ∀ q ∈ (∅ : Finset (Fin (3*t))), o q = 0} = Nat.card {o : Fin (3*t) → ZMod 2 // bal (3*t) o} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun o => by simp))
  rw [e, Finset.card_empty,
    show (2:ℕ)^(3*t) = 2^(3*t-2) * 2^(0+2) by rw [← pow_add]; congr 1; omega] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

lemma card_X (t : ℕ) (ht : 0 < t) (hn : 0 < 6*t) {h : ℕ} (v : Fin h → Fin (3*t) → ZMod 2) :
    Nat.card {x // InX (6*t) hn v x} = Nat.card {e // qker (3*t) h v e} * 2^(3*t-2) := by
  rw [← card_bal t ht, ← Nat.card_prod]
  exact Nat.card_congr (((split t).subtypeEquiv (fun x => by
    rw [InX_iff, split_apply])).trans Equiv.subtypeProdEquivProd)

open Classical in
lemma card_adm (t : ℕ) (hn : 0 < 6*t) (ha : 0 < 3*t) {h : ℕ} (v : Fin h → Fin (3*t) → ZMod 2) :
    Nat.card {x // InX (6*t) hn v x ∧ adm (6*t) hn x} =
      ∑ e : Fin (3*t) → ZMod 2, if qker (3*t) h v e then cnt (3*t) ha e else 0 := by
  have e1 : Nat.card {x // InX (6*t) hn v x ∧ adm (6*t) hn x} =
      Nat.card {p : (Fin (3*t) → ZMod 2) × (Fin (3*t) → ZMod 2) //
        qker (3*t) h v p.1 ∧ bal (3*t) p.2 ∧ compat (3*t) ha p.1 p.2} :=
    Nat.card_congr ((split t).subtypeEquiv (fun x => by
      rw [InX_iff, adm_iff_compat t hn ha, split_apply, and_assoc]))
  rw [e1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun e o => qker (3*t) h v e ∧ bal (3*t) o ∧ compat (3*t) ha e o)), Nat.card_sigma]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs with hq
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun o => and_iff_right hq))
  · rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun o => hq o.2.1⟩

lemma card_InX_ge (n : ℕ) (hn : 0 < n) {a h : ℕ} (v : Fin h → Fin a → ZMod 2) :
    2^n ≤ Nat.card {x // InX n hn v x} * 2^(h+4) := by
  let L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin 4 ⊕ Fin h → ZMod 2) :=
    LinearMap.pi (Sum.elim (fun j => dotL n (base n j)) (lam n hn v))
  have e : Nat.card {x // InX n hn v x} = Nat.card (LinearMap.ker L) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      rw [LinearMap.mem_ker, funext_iff, Sum.forall]
      exact and_congr (forall_congr' (fun j => by rw [dot_comm]; rfl)) Iff.rfl))
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin] at h2
  rw [Module.finrank_fin_fun] at h1
  rw [e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma exists_mix_of_bal (t : ℕ) (hn : 0 < 6*t) (e : Fin (3*t) → ZMod 2) (he : bal (3*t) e) :
    ∃ w, evens t (mix (6*t) hn w) = e ∧ odds t (mix (6*t) hn w) = 0 := by
  have hx : split t ((split t).symm (e, 0)) = (e, 0) := (split t).apply_symm_apply _
  rw [split_apply, Prod.mk.injEq] at hx
  obtain ⟨w, hw⟩ := mix_surj (6*t) hn (Dvd.intro t rfl) ((split t).symm (e, 0))
    ((base_iff_bal t _).2 (by rw [hx.1, hx.2]; exact ⟨he, bal_zero _⟩))
  exact ⟨w, by rw [hw]; exact hx.1, by rw [hw]; exact hx.2⟩

lemma live_of_qker (t : ℕ) (hn : 0 < 6*t) {h : ℕ} (v : Fin h → Fin (3*t) → ZMod 2)
    (e : Fin (3*t) → ZMod 2) (he : qker (3*t) h v e) (s : Fin (3*t)) (hs : e s ≠ 0) :
    live (6*t) hn v s := by
  obtain ⟨w, hw, hw0⟩ := exists_mix_of_bal t hn e he.1
  refine ⟨w, ((InX_iff t hn v _).2 ⟨by rw [hw]; exact he, by rw [hw0]; exact bal_zero _⟩).2, ?_⟩
  rw [ix_even]
  show evens t (mix (6*t) hn w) s ≠ 0
  rw [hw]
  exact hs

lemma qker_of_live (t : ℕ) (hn : 0 < 6*t) {h : ℕ} (v : Fin h → Fin (3*t) → ZMod 2)
    (s : Fin (3*t)) (hl : live (6*t) hn v s) : ∃ e, qker (3*t) h v e ∧ e s ≠ 0 := by
  obtain ⟨w, hw, hs⟩ := hl
  refine ⟨evens t (mix (6*t) hn w), ((InX_iff t hn v _).1
    ⟨fun j => base_dot_mix (6*t) hn (Dvd.intro t rfl) j w, hw⟩).1, ?_⟩
  rw [ix_even] at hs
  exact hs

lemma bal_wt (a : ℕ) (e : Fin a → ZMod 2) (hb : bal a e) (he : e ≠ 0) : 2 ≤ wt e := by
  by_contra hlt
  have h0 : wt e ≠ 0 := by
    intro h0
    refine he (funext (fun s => by_contra (fun hs => ?_)))
    unfold wt at h0
    rw [Finset.card_eq_zero] at h0
    exact Finset.notMem_empty s (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)
  obtain ⟨s0, hs0⟩ := Finset.card_eq_one.mp (show wt e = 1 by omega)
  have hmem : ∀ s, e s ≠ 0 ↔ s = s0 := fun s => by
    rw [← Finset.mem_singleton, ← hs0, Finset.mem_filter]
    exact (and_iff_right (Finset.mem_univ s)).symm
  have hes : e = Pi.single s0 1 := by
    funext s
    by_cases h : s = s0
    · rw [h, Pi.single_eq_same]
      exact (z2_cases (e s0)).resolve_left ((hmem s0).2 rfl)
    · rw [Pi.single_eq_of_ne h]
      exact not_not.mp (fun hne => h ((hmem s).1 hne))
  unfold bal at hb
  rw [hes, cs_single, cs_single, cs_single] at hb
  have h3 : s0.val % 3 = 0 ∨ s0.val % 3 = 1 ∨ s0.val % 3 = 2 := by omega
  rcases h3 with h | h | h <;> simp [h] at hb

lemma scale_le (N X Y D P M : ℕ) (hX : 0 < X) (h : N * X ≤ M * Y) (hs : Y * D ≤ X * P) :
    N * D ≤ M * P := by
  refine Nat.le_of_mul_le_mul_right ?_ hX
  calc N * D * X = N * X * D := by ring
    _ ≤ M * Y * D := Nat.mul_le_mul_right _ h
    _ = M * (Y * D) := mul_assoc _ _ _
    _ ≤ M * (X * P) := Nat.mul_le_mul_left _ hs
    _ = M * P * X := by ring

lemma scale_eq (N X Y D P M : ℕ) (hX : 0 < X) (h : N * X = M * Y) (hs : Y * D = X * P) :
    N * D = M * P := by
  refine Nat.eq_of_mul_eq_mul_right hX ?_
  calc N * D * X = N * X * D := by ring
    _ = M * Y * D := by rw [h]
    _ = M * P * X := by rw [mul_assoc, hs]; ring

open Classical in
lemma spaced_price (t : ℕ) (ht : 0 < t) (j : ℕ) (hj3 : j+3 ≤ t) (hn : 0 < 6*t) (ha : 0 < 3*t)
    (v : Fin (3*t-2-j) → Fin (3*t) → ZMod 2)
    (hsp : ∀ s, ¬ (live (6*t) hn v s ∧ live (6*t) hn v (nxt (3*t) ha s))) :
    2^j * 2^(3*t-2) ≤ Nat.card {x // InX (6*t) hn v x} ∧
    Nat.card {x // InX (6*t) hn v x ∧ adm (6*t) hn x} * 8^(j+1) ≤
      Nat.card {x // InX (6*t) hn v x} * (5^(j+1)+3^(j+1)) := by
  have hspaced : ∀ e, qker (3*t) (3*t-2-j) v e → ∀ s, e s ≠ 0 → e (nxt (3*t) ha s) = 0 :=
    fun e he s hs => not_not.mp (fun h' =>
      hsp s ⟨live_of_qker t hn v e he s hs, live_of_qker t hn v e he _ h'⟩)
  have hG := card_InX_ge (6*t) hn v
  have hcard : Nat.card {e // qker (3*t) (3*t-2-j) v e} =
      (Finset.univ.filter (fun e => qker (3*t) (3*t-2-j) v e)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [card_X t ht hn, hcard] at hG ⊢
  rw [card_adm t hn ha, ← Finset.sum_filter]
  set V := Finset.univ.filter (fun e => qker (3*t) (3*t-2-j) v e) with hV
  have hmem : ∀ e, e ∈ V → qker (3*t) (3*t-2-j) v e := fun e he => (Finset.mem_filter.mp he).2
  have hd : 2^j ≤ V.card := by
    have h2 : (2:ℕ)^(6*t) = 2^j * (2^(3*t-2) * 2^(3*t-2-j+4)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [h2, mul_assoc] at hG
    exact Nat.le_of_mul_le_mul_right hG (by positivity)
  refine ⟨Nat.mul_le_mul_right _ hd, ?_⟩
  have hE := enum_bound V
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, bal_zero _, fun i => by simp⟩)
    (fun x hx y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      bal_add _ x y (hmem x hx).1 (hmem y hy).1, fun i => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, (hmem x hx).2 i,
          (hmem y hy).2 i, add_zero]⟩)
    (fun e he => bal_wt _ e (hmem e he).1) j (j+2) hd (by omega)
  have hS : (∑ e ∈ V, cnt (3*t) ha e) * 4^(j+2) ≤
      2^(3*t-2) * ∑ e ∈ V, 4^(j+2 - min (wt e) (j+2)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum (fun e he => ?_)
    calc cnt (3*t) ha e * 4^(j+2)
        = cnt (3*t) ha e * 4^(min (wt e) (j+2)) * 4^(j+2 - min (wt e) (j+2)) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Nat.min_le_right _ _)]
      _ ≤ 2^(3*t-2) * 4^(j+2 - min (wt e) (j+2)) :=
          Nat.mul_le_mul_right _ (cnt_spaced t j hj3 ha e (hspaced e (hmem e he)))
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 4^(j+2) by positivity)
  calc (∑ e ∈ V, cnt (3*t) ha e) * 8^(j+1) * 4^(j+2)
      = 8^(j+1) * ((∑ e ∈ V, cnt (3*t) ha e) * 4^(j+2)) := by ring
    _ ≤ 8^(j+1) * (2^(3*t-2) * ∑ e ∈ V, 4^(j+2 - min (wt e) (j+2))) :=
        Nat.mul_le_mul_left _ hS
    _ = 2^(3*t-2) * (8^(j+1) * ∑ e ∈ V, 4^(j+2 - min (wt e) (j+2))) := by ring
    _ ≤ 2^(3*t-2) * (V.card * 4^(j+2) * (5^(j+1)+3^(j+1))) := Nat.mul_le_mul_left _ hE
    _ = V.card * 2^(3*t-2) * (5^(j+1)+3^(j+1)) * 4^(j+2) := by ring

def pinned (a h : ℕ) (e : Fin a → ZMod 2) : Prop := ∀ s : Fin a, s.val < h → e s = 0

def par (a : ℕ) (e : Fin a → ZMod 2) : ZMod 2 × ZMod 2 := (cs a 0 e + cs a 2 e, cs a 1 e + cs a 2 e)

def dl (c : ℕ) : ZMod 2 × ZMod 2 := (if c % 3 = 1 then 0 else 1, if c % 3 = 0 then 0 else 1)

def fr (a : ℕ) (ha : 0 < a) (h : ℕ) (e : Fin a → ZMod 2) : ℕ :=
  (Finset.univ.filter fun p : Fin a => h ≤ p.val ∧ e p = 0 ∧ e (nxt a ha p) = 0).card

def D (q : ℕ) : ℕ → ZMod 2 → ZMod 2 × ZMod 2 → ℕ
  | 0, b, r => if r = 0 then (if b = 0 then q else 1) else 0
  | k+1, b, r => (if b = 0 then q else 1) * D q k 0 r + D q k 1 (r + dl (2*k+2))

def consI (j : ℕ) : ℕ := D 2 (j+2) 0 0

lemma cs_update {a : ℕ} (r : ℕ) {e : Fin a → ZMod 2} {i : Fin a} (hi : e i = 0) (b : ZMod 2) :
    cs a r (Function.update e i b) = cs a r e + if i.val % 3 = r then b else 0 := by
  have h : ∀ s : Fin a, (if s.val % 3 = r then Function.update e i b s else 0)
      = (if s.val % 3 = r then e s else 0) + if s = i then (if i.val % 3 = r then b else 0) else 0 := by
    intro s
    by_cases hs : s = i
    · subst hs; simp [hi]
    · simp [hs]
  simp only [cs, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma par_update {a : ℕ} {e : Fin a → ZMod 2} {i : Fin a} (hi : e i = 0) (b : ZMod 2) :
    par a (Function.update e i b) = par a e + b • dl i := by
  rcases (by omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h <;>
    ext <;> simp [par, dl, cs_update _ hi, h] <;> ring

lemma nxt_ne {a : ℕ} (ha : 0 < a) {i p : Fin a} (hi : 1 ≤ i.val) (hp : i.val ≤ p.val) :
    nxt a ha p ≠ i := by
  intro h
  have h' : (p.val + 1) % a = i.val := congrArg Fin.val h
  rcases (Nat.succ_le_of_lt p.isLt).eq_or_lt with h1 | h1
  · rw [show p.val + 1 = a from h1, Nat.mod_self] at h'; omega
  · rw [Nat.mod_eq_of_lt h1] at h'; omega

lemma fr_update {a : ℕ} (ha : 0 < a) {i : Fin a} (hi : 1 ≤ i.val) (e : Fin a → ZMod 2) (b : ZMod 2) :
    fr a ha i (Function.update e i b)
      = fr a ha (i+1) e + if b = 0 ∧ e (nxt a ha i) = 0 then 1 else 0 := by
  have h : ∀ p : Fin a, (if i.val ≤ p.val ∧ Function.update e i b p = 0
        ∧ Function.update e i b (nxt a ha p) = 0 then 1 else 0)
      = (if i.val + 1 ≤ p.val ∧ e p = 0 ∧ e (nxt a ha p) = 0 then 1 else 0)
        + if p = i then (if b = 0 ∧ e (nxt a ha i) = 0 then 1 else 0) else 0 := by
    intro p
    rcases lt_trichotomy p i with hp | rfl | hp
    · simp [not_le_of_gt hp, lt_asymm hp, ne_of_lt hp]
    · simp [Function.update_of_ne (nxt_ne ha hi le_rfl)]
    · simp [le_of_lt hp, hp, ne_of_gt hp, Function.update_of_ne (nxt_ne ha hi (le_of_lt hp))]
  simp only [fr, Finset.card_filter, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

lemma pinned_succ {a : ℕ} (i : Fin a) (e : Fin a → ZMod 2) :
    pinned a (i+1) e ↔ pinned a i e ∧ e i = 0 := by
  refine ⟨fun h => ⟨fun s hs => h s (Nat.lt_succ_of_lt hs), h i (Nat.lt_succ_self _)⟩, fun h s hs => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
  · exact h.1 s hs
  · rw [Fin.ext hs]; exact h.2

lemma pinned_update {a : ℕ} (i : Fin a) (e : Fin a → ZMod 2) (b : ZMod 2) :
    pinned a i (Function.update e i b) ↔ pinned a i e :=
  forall₂_congr fun s hs => by rw [Function.update_of_ne (Fin.ne_of_val_ne hs.ne)]

open Classical in
lemma sum_pinned_succ {a : ℕ} (i : Fin a) (f : (Fin a → ZMod 2) → ℕ) :
    ∑ e with pinned a i e, f e
      = ∑ b : ZMod 2, ∑ e with pinned a (i+1) e, f (Function.update e i b) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij' (fun x : ZMod 2 × (Fin a → ZMod 2) => Function.update x.2 i x.1)
    (fun e : Fin a → ZMod 2 => (e i, Function.update e i 0)) ?_ ?_ ?_ ?_ fun _ _ => rfl).symm <;>
    intro x hx <;>
    simp_all [pinned_succ, pinned_update, Prod.ext_iff, Function.update_eq_self_iff]

open Classical in
theorem sum_pinned (q t : ℕ) (ha : 0 < 3*t) : ∀ (k : ℕ) (i : Fin (3*t)), i.val + k + 1 = 3*t →
    1 ≤ i.val → ∀ (b : ZMod 2) (r : ZMod 2 × ZMod 2),
      ∑ e with pinned (3*t) (i+1) e,
        (if par (3*t) e = r then q ^ fr (3*t) ha i (Function.update e i b) else 0) = D q k b r := by
  intro k
  induction k with
  | zero =>
    intro i hk hi b r
    have h0 : (Finset.univ.filter fun e => pinned (3*t) (i+1) e) = {0} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => funext fun s => h s (by omega), fun h s _ => by rw [h]; rfl⟩
    have hf : fr (3*t) ha (i+1) (0 : Fin (3*t) → ZMod 2) = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ hp => by omega)
    have hp : par (3*t) 0 = 0 := by simp [par, cs]
    rw [h0, Finset.sum_singleton, fr_update ha hi, hf, hp]
    simp [D, eq_comm]
  | succ k ih =>
    intro i hk hi b r
    obtain ⟨i', hi'⟩ : ∃ i' : Fin (3*t), i'.val = i.val + 1 := ⟨⟨i+1, by omega⟩, rfl⟩
    have hn : nxt (3*t) ha i = i' := Fin.ext ((Nat.mod_eq_of_lt (by omega)).trans hi'.symm)
    have hd : dl i' = dl (2*k+2) := by unfold dl; rw [show i'.val % 3 = (2*k+2) % 3 by omega]
    have key : ∀ b' : ZMod 2, ∑ e with pinned (3*t) (i'+1) e,
        (if par (3*t) (Function.update e i' b') = r
          then q ^ fr (3*t) ha i (Function.update (Function.update e i' b') i b) else 0)
        = (if b = 0 ∧ b' = 0 then q else 1) * D q k b' (r + b' • dl i') := by
      intro b'
      rw [← ih i' (by omega) (by omega) b' (r + b' • dl i'), Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [par_update ((pinned_succ i' e).1 (Finset.mem_filter.mp he).2).2, fr_update ha hi, hn,
        Function.update_self, ← hi']
      simp only [CharTwo.add_eq_iff_eq_add (R := ZMod 2 × ZMod 2)]
      split_ifs <;> simp [pow_succ, mul_comm]
    rw [← hi', sum_pinned_succ, sum_zmod_two, key, key, D, hd]
    simp

lemma blocked_card_pinned {a : ℕ} (ha : 0 < a) (i : Fin a) {e : Fin a → ZMod 2} (hp : pinned a (i+1) e) :
    (blocked a ha e).card + fr a ha i e = a - i := by
  have hb : blocked a ha e = (Finset.Ici i).filter fun p => ¬ (e p = 0 ∧ e (nxt a ha p) = 0) := by
    ext p
    simp only [blocked, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, not_and_or,
      iff_and_self]
    intro h
    by_contra hlt
    have hlt' : p.val < i.val := not_le.mp hlt
    exact h.elim (· (hp p (by omega))) (· (hp _ (by
      show (p.val + 1) % a < i.val + 1
      rw [Nat.mod_eq_of_lt (by omega)]; omega)))
  have hf : fr a ha i e = ((Finset.Ici i).filter fun p => e p = 0 ∧ e (nxt a ha p) = 0).card := by
    rw [fr, ← Finset.filter_filter]
    exact congrArg (fun s => (Finset.filter _ s).card) Finset.filter_le_eq_Ici
  rw [hb, hf, add_comm, Finset.card_filter_add_card_filter_not, Fin.card_Ici]

open Classical in
lemma sum_bal (q t : ℕ) (ha : 0 < 3*t) (k : ℕ) (i : Fin (3*t)) (hk : i.val + k + 1 = 3*t)
    (hi : 1 ≤ i.val) :
    (∑ e : Fin (3*t) → ZMod 2, if pinned (3*t) (i+1) e ∧ bal (3*t) e
      then q ^ (k + 1 - (blocked (3*t) ha e).card) else 0) = D q k 0 0 := by
  rw [← sum_pinned q t ha k i hk hi 0 0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hp : pinned (3*t) (i+1) e
  · have hc := blocked_card_pinned ha i hp
    rw [Function.update_eq_self_iff.mpr ((pinned_succ i e).1 hp).2.symm,
      show k + 1 - (blocked (3*t) ha e).card = fr (3*t) ha i e by omega]
    simp [hp, bal, par]
  · simp [hp]

lemma D_one : ∀ (k : ℕ) (b : ZMod 2) (r : ZMod 2 × ZMod 2), D 1 (k+2) b r = 2^k
  | 0 => by decide
  | k+1 => fun b r => by rw [D, D_one k, D_one k, ite_self]; ring

lemma D_gt (j : ℕ) (hj : 10 ≤ j) : ∀ r, 5^(j+1) + 3^(j+1) < 2^j * D 2 (j+2) 0 r
    ∧ 5^(j+1) + 3^(j+1) < 2^j * (2 * D 2 (j+2) 1 r) := by
  induction j, hj using Nat.le_induction with
  | base => decide +kernel
  | succ j hj ih =>
    intro r
    have h0 := (ih r).1
    have h1 := (ih (r + dl (2*(j+2)+2))).2
    rw [show D 2 (j+1+2) 0 r = 2 * D 2 (j+2) 0 r + D 2 (j+2) 1 (r + dl (2*(j+2)+2)) from rfl,
      show D 2 (j+1+2) 1 r = 1 * D 2 (j+2) 0 r + D 2 (j+2) 1 (r + dl (2*(j+2)+2)) from rfl]
    simp only [pow_succ] at h0 h1 ⊢
    constructor <;> linarith [Nat.zero_le (3^j), Nat.zero_le (5^j)]

lemma exists_lane {t j : ℕ} (h2 : j+3 ≤ t) : ∃ i : Fin (3*t), 3*t-2-j = i.val + 1 :=
  ⟨⟨3*t-3-j, by omega⟩, by simp only []; omega⟩

theorem cons_blocked_le (t j : ℕ) (h2 : j+3 ≤ t) (ha : 0 < 3*t)
    (e : Fin (3*t) → ZMod 2) (hp : pinned (3*t) (3*t-2-j) e) :
    (blocked (3*t) ha e).card ≤ j+3 := by
  obtain ⟨i, hi⟩ := exists_lane h2
  exact (Nat.le.intro (blocked_card_pinned ha i (hi ▸ hp))).trans (by omega)

open Classical in
theorem cons_sum (t j : ℕ) (h1 : 1 ≤ j) (h2 : j+3 ≤ t) (ha : 0 < 3*t) :
    (∑ e : Fin (3*t) → ZMod 2, if pinned (3*t) (3*t-2-j) e ∧ bal (3*t) e
      then 2^(j+3 - (blocked (3*t) ha e).card) else 0) = consI j := by
  obtain ⟨i, hi⟩ := exists_lane h2
  rw [hi]
  exact sum_bal 2 t ha (j+2) i (by omega) (by omega)

theorem cons_card (t j : ℕ) (h1 : 1 ≤ j) (h2 : j+3 ≤ t) :
    Nat.card {e : Fin (3*t) → ZMod 2 // pinned (3*t) (3*t-2-j) e ∧ bal (3*t) e} = 2^j := by
  classical
  obtain ⟨i, hi⟩ := exists_lane h2
  have h := sum_bal 1 t (by omega) (j+2) i (by omega) (by omega)
  simp only [one_pow, D_one] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, hi]
  convert h

theorem consI_eq (j : ℕ) (hj : j = 1 ∨ j = 2) : 2^j * consI j = 5^(j+1)+3^(j+1) := by
  rcases hj with rfl | rfl <;> decide

theorem consI_lt (j : ℕ) (h3 : 3 ≤ j) (h8 : j ≤ 8) : 2^j * consI j < 5^(j+1)+3^(j+1) := by
  interval_cases j <;> decide +kernel

theorem consI_gt (j : ℕ) (h9 : 9 ≤ j) : 5^(j+1)+3^(j+1) < 2^j * consI j := by
  rcases h9.eq_or_lt with rfl | h
  · decide +kernel
  · exact (D_gt j h 0).1

theorem ite_ne_zero_eq_self (b : ZMod 2) : (if b ≠ 0 then 1 else 0) = b := by revert b; decide

def supp {ι : Type} [Fintype ι] [DecidableEq ι] : (ι → ZMod 2) ≃ Finset ι where
  toFun e := Finset.univ.filter (fun s => e s ≠ 0)
  invFun S s := if s ∈ S then 1 else 0
  left_inv e := funext fun s => by simpa using ite_ne_zero_eq_self (e s)
  right_inv S := by ext; simp

theorem mem_supp {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → ZMod 2} {s : ι} :
    s ∈ supp e ↔ e s ≠ 0 := by
  simp [supp]

theorem sum_eq_zero_iff_even_wt {ι : Type} [Fintype ι] (e : ι → ZMod 2) :
    ∑ s, e s = 0 ↔ Even (wt e) := by
  rw [← ZMod.natCast_eq_zero_iff_even, wt, Finset.natCast_card_filter]
  simp_rw [ite_ne_zero_eq_self]

def evenOn {ι : Type} [Fintype ι] [DecidableEq ι] (L : Finset ι) (e : ι → ZMod 2) : Prop :=
  supp e ⊆ L ∧ Even (wt e)

theorem sum_supp_subset {ι R : Type} [Fintype ι] [DecidableEq ι] [CommSemiring R] (L : Finset ι)
    (a b : R) :
    ∑ e : ι → ZMod 2, (if supp e ⊆ L then a ^ wt e * b ^ (L.card - wt e) else 0) =
      (a + b) ^ L.card := by
  rw [← Finset.sum_pow_mul_eq_add_pow, ← Finset.univ_inter L.powerset, ← Finset.sum_ite_mem,
    ← supp.sum_comp]
  simp [wt, supp]

open Classical in

theorem sum_evenOn {ι : Type} [Fintype ι] [DecidableEq ι] (L : Finset ι) (y : ℕ) :
    2 * ∑ e : ι → ZMod 2, (if evenOn L e then (y + 1) ^ (L.card - wt e) else 0) =
      (y + 2) ^ L.card + y ^ L.card := by
  have h := congrArg₂ (· + ·) (sum_supp_subset L (1 : ℤ) (y + 1))
    (sum_supp_subset L (-1 : ℤ) (y + 1))
  rw [← Finset.sum_add_distrib] at h
  zify
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun e _ => ?_).trans (h.trans (by ring))
  by_cases hs : supp e ⊆ L <;> by_cases he : Even (wt e) <;>
    simp [evenOn, hs, he, neg_one_pow_eq_ite, two_mul]

theorem cs_eq_single {a r c : ℕ} {e : Fin a → ZMod 2} {x : Fin a} (hx : x.val % 3 = c)
    (h : ∀ s, s ≠ x → s.val % 3 = r → e s = 0) : cs a r e = if c = r then e x else 0 :=
  hx ▸ Finset.sum_eq_single x (fun s _ hsx => by split_ifs with hs; exacts [h s hsx hs, rfl])
    (by simp)

theorem cs_eq_sum {a r : ℕ} {e : Fin a → ZMod 2} (h : ∀ s, e s ≠ 0 → s.val % 3 = r) :
    cs a r e = ∑ s, e s :=
  Finset.sum_congr rfl fun s _ => ite_eq_left_iff.2 fun hs => (not_not.1 (mt (h s) hs)).symm

theorem bal_iff_of_supp {a : ℕ} {L : Finset (Fin a)} {x : Fin a} {e : Fin a → ZMod 2}
    (hL : ∀ s ∈ L, s.val % 3 = 0) (hx : x.val % 3 = 1) (hz : supp e ⊆ insert x L) :
    bal a e ↔ cs a 0 e = 0 ∧ e x = 0 := by
  have c : ∀ r, r ≠ 0 → cs a r e = if 1 = r then e x else 0 := fun r hr =>
    cs_eq_single hx fun s hsx hs => by_contra fun h => hr <| hs.symm.trans <|
      hL s <| (Finset.mem_insert.1 (hz (mem_supp.2 h))).resolve_left hsx
  simp [bal, c]

theorem bal_and_supp_iff {a : ℕ} {L : Finset (Fin a)} {x : Fin a} (hL : ∀ s ∈ L, s.val % 3 = 0)
    (hx : x.val % 3 = 1) (e : Fin a → ZMod 2) :
    (bal a e ∧ supp e ⊆ insert x L) ↔ evenOn L e := by
  have h0 : supp e ⊆ L → (cs a 0 e = 0 ↔ Even (wt e)) := fun hs => by
    rw [cs_eq_sum fun s h => hL s (hs (mem_supp.2 h)), sum_eq_zero_iff_even_wt]
  constructor
  · rintro ⟨hb, hz⟩
    obtain ⟨hc, ex⟩ := (bal_iff_of_supp hL hx hz).1 hb
    have hs := (Finset.subset_insert_iff_of_notMem (mt mem_supp.1 (not_not.2 ex))).1 hz
    exact ⟨hs, (h0 hs).1 hc⟩
  · rintro ⟨hs, he⟩
    have hz := hs.trans (Finset.subset_insert x L)
    exact ⟨(bal_iff_of_supp hL hx hz).2 ⟨(h0 hs).2 he, by_contra fun h =>
      zero_ne_one ((hL x (hs (mem_supp.2 h))).symm.trans hx)⟩, hz⟩

theorem exists_pins {ι : Type} [Fintype ι] [DecidableEq ι] {h : ℕ} (F : Finset ι)
    (hF : Fᶜ.card = h) :
    ∃ v : Fin h → ι → ZMod 2, ∀ e : ι → ZMod 2, (∀ i, ∑ s, v i s * e s = 0) ↔ supp e ⊆ F :=
  ⟨fun i => Pi.single ((Fᶜ.equivFinOfCardEq hF).symm i).1 1, fun e => by
    simpa [Pi.single_apply, Finset.subset_iff, mem_supp, not_imp_comm] using
      ((Fᶜ.equivFinOfCardEq hF).forall_congr_left (p := fun s : ↥Fᶜ => e s = 0)).symm.trans
        Subtype.forall⟩

theorem exists_qker_eq_evenOn {a h : ℕ} {L : Finset (Fin a)} {x : Fin a}
    (hL : ∀ s ∈ L, s.val % 3 = 0) (hx : x.val % 3 = 1) (hh : h + L.card + 1 = a) :
    ∃ v : Fin h → Fin a → ZMod 2, qker a h v = evenOn L := by
  obtain ⟨v, hv⟩ := exists_pins (h := h) (insert x L) (by
    rw [Finset.card_compl, Finset.card_insert_of_notMem fun hxL => by simpa [hx] using hL x hxL,
      Fintype.card_fin]
    omega)
  exact ⟨v, funext fun e => propext (by simpa [qker, hv] using bal_and_supp_iff hL hx e)⟩

open Classical in

theorem spaced_witness (t j : ℕ) (h1 : 1 ≤ j) (h2 : j+3 ≤ t) :
    ∃ v : Fin (3*t-2-j) → Fin (3*t) → ZMod 2,
      (∀ e, qker (3*t) (3*t-2-j) v e → wt e ≤ j+1 ∧ ∀ s, e s ≠ 0 → s.val % 3 = 0) ∧
      Nat.card {e : Fin (3*t) → ZMod 2 // qker (3*t) (3*t-2-j) v e} = 2^j ∧
      2 * (∑ e : Fin (3*t) → ZMod 2, if qker (3*t) (3*t-2-j) v e then 4^(j+1 - wt e) else 0) =
        5^(j+1) + 3^(j+1) := by
  obtain ⟨L, hL, hL0⟩ : ∃ L : Finset (Fin (3 * t)), L.card = j + 1 ∧ ∀ s ∈ L, s.val % 3 = 0 :=
    ⟨Finset.univ.image fun q : Fin (j + 1) => ⟨3 * q, by omega⟩,
      (Finset.card_image_of_injective _ fun p q h => by simpa [Fin.ext_iff] using h).trans
        (Finset.card_fin _), by simp⟩
  obtain ⟨v, hv⟩ := exists_qker_eq_evenOn (h := 3 * t - 2 - j) (x := ⟨1, by omega⟩) hL0 rfl
    (by omega)
  refine ⟨v, ?_⟩
  rw [hv]
  refine ⟨fun e he => ⟨hL ▸ Finset.card_le_card he.1, fun s hs => hL0 s (he.1 (mem_supp.2 hs))⟩,
    ?_, ?_⟩
  · simpa [hL, Nat.card_eq_fintype_card, Fintype.card_subtype, pow_succ'] using sum_evenOn L 0
  · simpa [hL] using sum_evenOn L 3

lemma qker_cons (t : ℕ) (hn : 0 < 6*t) (j : ℕ) (v : Fin (3*t-2-j) → Fin (3*t) → ZMod 2)
    (hv : ∀ i w, lam (6*t) hn v i (mix (6*t) hn w) = mix (6*t) hn w (ix (6*t) hn (2*i.val)))
    (e : Fin (3*t) → ZMod 2) :
    qker (3*t) (3*t-2-j) v e ↔ pinned (3*t) (3*t-2-j) e ∧ bal (3*t) e := by
  unfold qker
  rw [and_comm]
  refine and_congr_left (fun hb => ?_)
  obtain ⟨w, hw, -⟩ := exists_mix_of_bal t hn e hb
  have key : ∀ i : Fin (3*t-2-j), ∑ s, v i s * e s = e ⟨i.val, by have := i.2; omega⟩ := by
    intro i
    have h1 := hv i w
    rw [lam_apply, ix_even t hn ⟨i.val, by have := i.2; omega⟩] at h1
    rw [← hw]
    refine Eq.trans (Finset.sum_congr rfl (fun s _ => ?_)) h1
    rw [ix_even]
    rfl
  simp only [key]
  exact ⟨fun h s hs => h ⟨s.val, hs⟩, fun h i => h _ i.2⟩

lemma cons_cnt (t j : ℕ) (hj3 : j+3 ≤ t) (ha : 0 < 3*t) (e : Fin (3*t) → ZMod 2)
    (hp : pinned (3*t) (3*t-2-j) e) :
    cnt (3*t) ha e * 2^(j+5) = 2^(3*t) * 2^(j+3 - (blocked (3*t) ha e).card) := by
  have hb : ∀ p : Fin (3*t), p.val < 2 → p ∉ blocked (3*t) ha e := by
    intro p hp2 hmem
    rcases (Finset.mem_filter.mp hmem).2 with h | h
    · exact h (hp p (by omega))
    · refine h (hp _ ?_)
      rw [nxt_val]
      split_ifs <;> omega
  have h := bal_count (3*t) (blocked (3*t) ha e) ⟨0, by omega⟩ ⟨1, by omega⟩
    (hb _ (by norm_num)) (hb _ (by norm_num)) rfl rfl
  have hle := cons_blocked_le t j hj3 ha e hp
  rw [← h, mul_assoc, ← pow_add]
  congr 2
  omega

open Classical in
lemma cons_scale (t : ℕ) (ht : 0 < t) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j+3 ≤ t)
    (hn : 0 < 6*t) (v : Fin (3*t-2-j) → Fin (3*t) → ZMod 2)
    (hv : ∀ i w, lam (6*t) hn v i (mix (6*t) hn w) = mix (6*t) hn w (ix (6*t) hn (2*i.val))) :
    Nat.card {x // InX (6*t) hn v x} = 2^j * 2^(3*t-2) ∧
    Nat.card {x // InX (6*t) hn v x ∧ adm (6*t) hn x} * 2^(2*j+3) =
      2^j * 2^(3*t-2) * consI j := by
  have ha : 0 < 3*t := by omega
  have hX : Nat.card {x // InX (6*t) hn v x} = 2^j * 2^(3*t-2) := by
    rw [card_X t ht hn, Nat.card_congr (Equiv.subtypeEquivRight (qker_cons t hn j v hv)),
      cons_card t j hj1 hj3]
  refine ⟨hX, ?_⟩
  have hA : (∑ e : Fin (3*t) → ZMod 2, if qker (3*t) (3*t-2-j) v e then cnt (3*t) ha e else 0) *
      2^(j+5) = 2^(3*t) * consI j := by
    rw [← cons_sum t j hj1 hj3 ha, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hq := qker_cons t hn j v hv e
    split_ifs with h1 h2 h2
    · exact cons_cnt t j hj3 ha e h2.1
    · exact absurd (hq.1 h1) h2
    · exact absurd (hq.2 h2) h1
    · rw [zero_mul, mul_zero]
  rw [card_adm t hn ha]
  refine Nat.eq_of_mul_eq_mul_right (show 0 < 4 by norm_num) ?_
  calc (∑ e : Fin (3*t) → ZMod 2, if qker (3*t) (3*t-2-j) v e then cnt (3*t) ha e else 0) *
        2^(2*j+3) * 4
      = (∑ e : Fin (3*t) → ZMod 2, if qker (3*t) (3*t-2-j) v e then cnt (3*t) ha e else 0) *
        2^(j+5) * 2^j := by
        rw [mul_assoc, mul_assoc, show (4:ℕ) = 2^2 by norm_num, ← pow_add, ← pow_add]
        congr 2
        omega
    _ = 2^(3*t-2) * 2^2 * consI j * 2^j := by
        rw [hA, ← pow_add, show 3*t-2+2 = 3*t by omega]
    _ = 2^j * 2^(3*t-2) * consI j * 4 := by ring

def win (t : ℕ) (ht : 0 < t) (j : ℕ) (name c : Fin (6*t) → ZMod 2) (spaced : Bool) (k : ℕ) :
    Prop :=
  ∃ (v : Fin (3*t-2-j) → Fin (3*t) → ZMod 2)
    (A : ℕ → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] (Fin (6*t) → ZMod 2)) (b : ℕ → (Fin (6*t) → ZMod 2)),
    (spaced = true → ∀ s, ¬ (live (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) v s ∧
      live (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) v
        (nxt (3*t) (Nat.mul_pos (Nat.succ_pos 2) ht) s))) ∧
    (spaced = false → ∀ i w, lam (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) v i
        (mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w) =
      mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
        (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) (2*i.val))) ∧
    k ≤ Nat.card {w : Fin (6*t) → ZMod 2 //
      out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w =
        A (runq (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) v w) w +
          b (runq (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) v w)}

theorem cons_iff (t : ℕ) (ht : 0 < t) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j+3 ≤ t)
    (name c : Fin (6*t) → ZMod 2) (k : ℕ) :
    win t ht j name c false k ↔ 2^(2*j+3)*k ≤ consI j * 2^(6*t) := by
  have hn : 0 < 6*t := Nat.mul_pos (Nat.zero_lt_succ 5) ht
  have h6 : 6 ∣ 6*t := Dvd.intro t rfl
  constructor
  · rintro ⟨v, A, b, -, hv, hk⟩
    obtain ⟨hX, hs⟩ := cons_scale t ht j hj1 hj3 hn v (hv rfl)
    have hU := upper_X (6*t) hn h6 v name c A b
    rw [hX] at hU
    have h1 := scale_le _ _ _ _ _ _ (by positivity) hU hs.le
    calc 2^(2*j+3)*k ≤ 2^(2*j+3) * Nat.card {w : Fin (6*t) → ZMod 2 //
          out (6*t) hn name c w = A (runq (6*t) hn v w) w + b (runq (6*t) hn v w)} :=
          Nat.mul_le_mul_left _ hk
      _ ≤ consI j * 2^(6*t) := by rw [mul_comm, mul_comm (consI j)]; exact h1
  · intro hk
    let v : Fin (3*t-2-j) → Fin (3*t) → ZMod 2 :=
      fun i => Pi.single ⟨i.val, by have := i.2; omega⟩ 1
    have hv : ∀ i w, lam (6*t) hn v i (mix (6*t) hn w) =
        mix (6*t) hn w (ix (6*t) hn (2*i.val)) := by
      intro i w
      rw [lam_apply, Finset.sum_eq_single ⟨i.val, by have := i.2; omega⟩]
      · simp [v]
      · intro s _ hs
        simp [v, Pi.single_eq_of_ne hs]
      · intro h
        exact absurd (Finset.mem_univ _) h
    obtain ⟨hX, hs⟩ := cons_scale t ht j hj1 hj3 hn v hv
    obtain ⟨A, b, hL⟩ := lower_X (6*t) hn h6 v name c
    rw [hX] at hL
    have h1 := scale_eq _ _ _ _ _ _ (by positivity) hL hs
    refine ⟨v, A, b, fun h => absurd h (by decide), fun _ => hv, ?_⟩
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2^(2*j+3) by positivity)
    rw [mul_comm _ (Nat.card _), h1, mul_comm (2^(6*t))]
    exact hk

open Classical in
theorem spaced_iff (t : ℕ) (ht : 0 < t) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j+3 ≤ t)
    (name c : Fin (6*t) → ZMod 2) (k : ℕ) :
    win t ht j name c true k ↔ 8^(j+1)*k ≤ (5^(j+1)+3^(j+1))*2^(6*t) := by
  have hn : 0 < 6*t := Nat.mul_pos (Nat.zero_lt_succ 5) ht
  have ha : 0 < 3*t := Nat.mul_pos (Nat.succ_pos 2) ht
  have h6 : 6 ∣ 6*t := Dvd.intro t rfl
  constructor
  · rintro ⟨v, A, b, hsp, -, hk⟩
    obtain ⟨hX, hs⟩ := spaced_price t ht j hj3 hn ha v (hsp rfl)
    have h1 := scale_le _ _ _ _ _ _ (lt_of_lt_of_le (by positivity) hX)
      (upper_X (6*t) hn h6 v name c A b) hs
    calc 8^(j+1)*k ≤ 8^(j+1) * Nat.card {w : Fin (6*t) → ZMod 2 //
          out (6*t) hn name c w = A (runq (6*t) hn v w) w + b (runq (6*t) hn v w)} :=
          Nat.mul_le_mul_left _ hk
      _ ≤ (5^(j+1)+3^(j+1)) * 2^(6*t) := by
          rw [mul_comm, mul_comm (5^(j+1)+3^(j+1))]
          exact h1
  · intro hk
    obtain ⟨v, hW1, hW2, hW3⟩ := spaced_witness t j hj1 hj3
    have hcls : ∀ s : Fin (3*t), s.val % 3 = 0 → (nxt (3*t) ha s).val % 3 ≠ 0 := by
      intro s hs
      have := s.2
      rw [nxt_val]
      split_ifs <;> omega
    have hX : Nat.card {x // InX (6*t) hn v x} = 2^j * 2^(3*t-2) := by
      rw [card_X t ht hn, hW2]
    have hs : Nat.card {x // InX (6*t) hn v x ∧ adm (6*t) hn x} * 8^(j+1) =
        2^j * 2^(3*t-2) * (5^(j+1)+3^(j+1)) := by
      rw [card_adm t hn ha, ← hW3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      split_ifs with he
      · obtain ⟨hw, hsupp⟩ := hW1 e he
        have hlight := cnt_light t ha e (fun s hs => not_not.mp (fun h' =>
          hcls s (hsupp s hs) (hsupp _ h'))) (by omega)
        calc cnt (3*t) ha e * 8^(j+1)
            = cnt (3*t) ha e * 4^(wt e) * 4^(j+1 - wt e) * 2^(j+1) := by
              rw [mul_assoc (cnt (3*t) ha e), ← pow_add, Nat.add_sub_cancel' hw, mul_assoc,
                ← mul_pow]
              norm_num
          _ = 2^j * 2^(3*t-2) * (2 * 4^(j+1 - wt e)) := by
              rw [hlight, pow_succ]
              ring
      · simp
    obtain ⟨A, b, hL⟩ := lower_X (6*t) hn h6 v name c
    rw [hX] at hL
    have h1 := scale_eq _ _ _ _ _ _ (by positivity) hL hs
    refine ⟨v, A, b, fun _ s hl => ?_, fun h => absurd h (by decide), ?_⟩
    · obtain ⟨e, he, hes⟩ := qker_of_live t hn v s hl.1
      obtain ⟨e', he', hes'⟩ := qker_of_live t hn v _ hl.2
      exact hcls s ((hW1 e he).2 s hes) ((hW1 e' he').2 _ hes')
    · refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 8^(j+1) by positivity)
      rw [mul_comm _ (Nat.card _), h1, mul_comm (2^(6*t))]
      exact hk

theorem final (t : ℕ) (ht : 0 < t) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j+3 ≤ t)
    (name c : Fin (6*t) → ZMod 2) :
    (∀ k, win t ht j name c true k ↔ 8^(j+1)*k ≤ (5^(j+1)+3^(j+1))*2^(6*t)) ∧
      ((∃ k, win t ht j name c true k ∧ ¬ win t ht j name c false k) ↔ 3 ≤ j ∧ j ≤ 8) ∧
      ((∃ k, win t ht j name c false k ∧ ¬ win t ht j name c true k) ↔ 9 ≤ j) := by
  obtain ⟨N, hN⟩ : ∃ N, 2^(6*t) = 8^(j+1) * N ∧ 0 < N := ⟨2^(6*t-3*(j+1)), by
    rw [show (8:ℕ) = 2^3 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega, by positivity⟩
  have hS : ∀ k, win t ht j name c true k ↔ k ≤ (5^(j+1)+3^(j+1)) * N := by
    intro k
    rw [spaced_iff t ht j hj1 hj3, hN.1, mul_left_comm]
    exact Nat.mul_le_mul_left_iff (by positivity)
  have hC : ∀ k, win t ht j name c false k ↔ k ≤ 2^j * consI j * N := by
    intro k
    rw [cons_iff t ht j hj1 hj3, hN.1,
      show consI j * (8^(j+1) * N) = 2^(2*j+3) * (2^j * consI j * N) by
        rw [show (8:ℕ) = 2^3 by norm_num, ← pow_mul, show 3*(j+1) = (2*j+3) + j by ring, pow_add]
        ring]
    exact Nat.mul_le_mul_left_iff (by positivity)
  refine ⟨spaced_iff t ht j hj1 hj3 name c, ?_, ?_⟩
  · constructor
    · rintro ⟨k, h1, h2⟩
      rw [hS] at h1
      rw [hC, not_le] at h2
      have h3 : 2^j * consI j < 5^(j+1)+3^(j+1) :=
        lt_of_mul_lt_mul_right (lt_of_lt_of_le h2 h1) (Nat.zero_le N)
      by_contra hcon
      rcases Nat.lt_or_ge j 3 with h | h
      · have := consI_eq j (by omega)
        omega
      · have := consI_gt j (by omega)
        omega
    · rintro ⟨h3, h8⟩
      refine ⟨(5^(j+1)+3^(j+1)) * N, (hS _).2 le_rfl, ?_⟩
      rw [hC, not_le]
      exact Nat.mul_lt_mul_of_pos_right (consI_lt j h3 h8) hN.2
  · constructor
    · rintro ⟨k, h1, h2⟩
      rw [hC] at h1
      rw [hS, not_le] at h2
      have h3 : 5^(j+1)+3^(j+1) < 2^j * consI j :=
        lt_of_mul_lt_mul_right (lt_of_lt_of_le h2 h1) (Nat.zero_le N)
      by_contra hcon
      rcases Nat.lt_or_ge j 3 with h | h
      · have := consI_eq j (by omega)
        omega
      · have := consI_lt j h (by omega)
        omega
    · intro h9
      refine ⟨2^j * consI j * N, (hC _).2 le_rfl, ?_⟩
      rw [hS, not_le]
      exact Nat.mul_lt_mul_of_pos_right (consI_gt j h9) hN.2

end PEqualNP.Outside.L_meta_33665

theorem PEqualNP.Outside.L_meta_33665 :
(
∀ (t : ℕ) (ht : 0 < t) (j : ℕ), 1 ≤ j → j+3 ≤ t →
  let h := 3*t-2-j
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let a := 3*t
  let evenBit := fun (w : W) (i : Fin a) => mix w (ix (2*i.val))
  let next := fun (i : Fin a) => (⟨(i.val+1) % a, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin a)
  ∀ name c : W,
    let win := fun (spaced : Bool) (k : ℕ) =>
      ∃ (v : Fin h → Fin a → F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
        let q := fun (i : Fin h) (w : W) => ∑ s, v i s * evenBit w s
        let live := fun (s : Fin a) => ∃ w : W, (∀ i, q i w = 0) ∧ evenBit w s ≠ 0
        let run := fun w : W =>
          (List.finRange h).foldl (fun u i => 2*u + (if q i w = 0 then 0 else 1)) (0 : ℕ)
        (spaced = true → ∀ s, ¬ (live s ∧ live (next s))) ∧
        (spaced = false → ∀ i w, q i w = mix w (ix (2*i.val))) ∧
        k ≤ Nat.card {w : W // out name c w = A (run w) w + b (run w)}
    (∀ k, win true k ↔ 8^(j+1)*k ≤ (5^(j+1)+3^(j+1))*2^n) ∧
      ((∃ k, win true k ∧ ¬ win false k) ↔ 3 ≤ j ∧ j ≤ 8) ∧
      ((∃ k, win false k ∧ ¬ win true k) ↔ 9 ≤ j)
) := by
  intro t ht j hj1 hj3
  exact fun name c => PEqualNP.Outside.L_meta_33665.final t ht j hj1 hj3 name c

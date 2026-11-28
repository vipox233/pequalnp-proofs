import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_935_aux

open Finset

def sg (s : ZMod 2) : ℤ := if s = 0 then 1 else -1

lemma z2 (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s; decide

lemma sg_add (s t : ZMod 2) : sg (s + t) = sg s * sg t := by
  revert s t; decide

lemma sg_one : sg 1 = -1 := by decide

lemma sg_sum {κ : Type*} (S : Finset κ) (f : κ → ZMod 2) :
    sg (∑ k ∈ S, f k) = ∏ k ∈ S, sg (f k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sg]
  | insert k S hk ih => rw [sum_insert hk, prod_insert hk, sg_add, ih]

lemma sum_z2 (f : ZMod 2 → ℤ) : ∑ t, f t = f 0 + f 1 := Fin.sum_univ_two f

lemma neg_v {κ : Type*} (v : κ → ZMod 2) : -v = v :=
  funext fun k => ZMod.neg_eq_self_mod_two _

lemma add_eq_zero_iff_v {κ : Type*} (u v : κ → ZMod 2) : u + v = 0 ↔ u = v := by
  rw [add_eq_zero_iff_eq_neg, neg_v]

lemma add_add_v {κ : Type*} (u v : κ → ZMod 2) : u + v + v = u := by
  rw [add_assoc, (add_eq_zero_iff_v v v).2 rfl, add_zero]

lemma card_fun2 {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Fintype.card (κ → ZMod 2) = 2 ^ Fintype.card κ := by
  simp [Fintype.card_fun, ZMod.card]

lemma orth {κ : Type*} [Fintype κ] [DecidableEq κ] (v : κ → ZMod 2) :
    ∑ y : κ → ZMod 2, sg (dotProduct v y) = if v = 0 then (2:ℤ) ^ Fintype.card κ else 0 := by
  split_ifs with hv
  · subst hv
    simp [sg, card_fun2]
  · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      exact hv (funext fun k => by_contra fun hk => h ⟨k, hk⟩)
    have hk1 : v k = 1 := (z2 _).resolve_left hk
    have key : ∑ y : κ → ZMod 2, sg (dotProduct v y) =
        ∑ y : κ → ZMod 2, sg (dotProduct v (y + Pi.single k 1)) :=
      (Fintype.sum_equiv (Equiv.addRight (Pi.single k 1)) _ _ (fun _ => rfl)).symm
    have h2 : ∀ y : κ → ZMod 2, sg (dotProduct v (y + Pi.single k 1)) = - sg (dotProduct v y) := by
      intro y
      rw [dotProduct_add, dotProduct_single, hk1, mul_one, sg_add, sg_one, mul_neg_one]
    simp only [h2, Finset.sum_neg_distrib] at key
    linarith

variable {n : ℕ}

def chi (v x : Fin n → ZMod 2) : ℤ := sg (dotProduct v x)

def dl (v : Fin n → ZMod 2) : ℤ := if v = 0 then 1 else 0

lemma sum_chi (v : Fin n → ZMod 2) : ∑ x, chi v x = 2 ^ n * dl v := by
  have := orth v
  simp only [Fintype.card_fin] at this
  unfold chi dl
  rw [this]
  split_ifs <;> simp

lemma chi_add (u v x : Fin n → ZMod 2) : chi (u + v) x = chi u x * chi v x := by
  simp only [chi, add_dotProduct, sg_add]

lemma err_id (p a b x : Fin n → ZMod 2) (c : ZMod 2) :
    4 * (if dotProduct p x + c ≠ dotProduct a x * dotProduct b x then (1:ℤ) else 0) =
      2 - sg c * (chi p x + chi (p + a) x + chi (p + b) x - chi (p + a + b) x) := by
  have key : ∀ P A B c : ZMod 2, 4 * (if P + c ≠ A * B then (1:ℤ) else 0) =
      2 - sg c * (sg P + sg P * sg A + sg P * sg B - sg P * sg A * sg B) := by decide
  simp only [chi_add]
  exact key _ _ _ _

def Kv (p a b : Fin n → ZMod 2) (c : ZMod 2) : ℤ :=
  sg c * (dl p + dl (p + a) + dl (p + b) - dl (p + a + b))

lemma card_V : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  rw [card_fun2, Fintype.card_fin]

lemma sum_err (p a b : Fin n → ZMod 2) (c : ZMod 2) :
    ∑ x, 4 * (if dotProduct p x + c ≠ dotProduct a x * dotProduct b x then (1:ℤ) else 0) =
      2 ^ n * (2 - Kv p a b c) := by
  rw [Finset.sum_congr rfl (fun x _ => err_id p a b x c)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_chi, sum_chi, sum_chi, sum_chi]
  simp only [Finset.sum_const, Finset.card_univ, card_V, nsmul_eq_mul, Kv]
  push_cast
  ring

def phi (a b : Fin n → ZMod 2) (t : ZMod 2 × ZMod 2) : (Fin n → ZMod 2) × ZMod 2 :=
  (t.2 • a + t.1 • b, t.1 * t.2)

lemma Kv_le (p a b : Fin n → ZMod 2) (c : ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Kv p a b c ≤ 1 ∧ (Kv p a b c = 1 → ∃ t, phi a b t = (p, c)) := by
  have hab' : a + b ≠ 0 := by rw [Ne, add_eq_zero_iff_v]; exact hab
  simp only [Kv, dl, add_assoc, add_eq_zero_iff_v]
  by_cases h0 : p = 0
  · subst h0
    have h1 : ¬ (0 : Fin n → ZMod 2) = a := fun h => ha h.symm
    have h2 : ¬ (0 : Fin n → ZMod 2) = b := fun h => hb h.symm
    have h3 : ¬ (0 : Fin n → ZMod 2) = a + b := fun h => hab' h.symm
    simp only [h1, h2, h3, ite_true, ite_false]
    rcases z2 c with rfl | rfl
    · exact ⟨by decide, fun _ => ⟨(0, 0), by simp [phi]⟩⟩
    · exact ⟨by decide, fun h => absurd h (by decide)⟩
  by_cases h1 : p = a
  · subst h1
    have h2 : ¬ p = b := hab
    have h3 : ¬ p = p + b := by
      intro h; apply hb
      have := congrArg (fun z => z + p) h
      rw [add_comm p b, add_add_v] at this
      rw [← this, (add_eq_zero_iff_v p p).2 rfl]
    simp only [h0, h2, h3, ite_true, ite_false]
    rcases z2 c with rfl | rfl
    · exact ⟨by decide, fun _ => ⟨(0, 1), by simp [phi]⟩⟩
    · exact ⟨by decide, fun h => absurd h (by decide)⟩
  by_cases h2 : p = b
  · subst h2
    have h3 : ¬ p = a + p := by
      intro h; apply ha
      have := congrArg (fun z => z + p) h
      rw [add_add_v] at this
      rw [← this, (add_eq_zero_iff_v p p).2 rfl]
    simp only [h0, h1, h3, ite_true, ite_false]
    rcases z2 c with rfl | rfl
    · exact ⟨by decide, fun _ => ⟨(1, 0), by simp [phi]⟩⟩
    · exact ⟨by decide, fun h => absurd h (by decide)⟩
  by_cases h3 : p = a + b
  · subst h3
    simp only [h0, h1, h2, ite_true, ite_false]
    rcases z2 c with rfl | rfl
    · exact ⟨by decide, fun h => absurd h (by decide)⟩
    · exact ⟨by decide, fun _ => ⟨(1, 1), by simp [phi]⟩⟩
  simp only [h0, h1, h2, h3, ite_false]
  exact ⟨by simp, fun h => absurd h (by simp)⟩

lemma state_id (a b x : Fin n → ZMod 2) (t : ZMod 2 × ZMod 2) :
    4 * (if dotProduct (phi a b t).1 x + (phi a b t).2 ≠ dotProduct a x * dotProduct b x
      then (1:ℤ) else 0) =
      1 - (sg t.1 * chi a x + sg t.2 * chi b x + sg (t.1 + t.2 + 1) * chi (a + b) x) := by
  have key : ∀ α β A B : ZMod 2, 4 * (if β * A + α * B + α * β ≠ A * B then (1:ℤ) else 0) =
      1 - (sg α * sg A + sg β * sg B + sg (α + β + 1) * sg (A + B)) := by decide
  simp only [phi, chi, add_dotProduct, smul_dotProduct, smul_eq_mul]
  exact key _ _ _ _

def bit (a b : Fin n → ZMod 2) (t : ZMod 2 × ZMod 2) (w : Fin n → ZMod 2) : ZMod 2 :=
  (if w = a then t.1 else 0) + (if w = b then t.2 else 0) +
    (if w = a + b then t.1 + t.2 + 1 else 0)

def fr (a b : Fin n → ZMod 2) : Finset (Fin n → ZMod 2) := {a, b, a + b}

section dist
variable {a b : Fin n → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
include ha hb hab

lemma ne_ab1 : a ≠ a + b := by
  intro h; apply hb
  have := congrArg (fun z => z + a) h
  rw [add_comm a b, add_add_v] at this
  rw [← this, (add_eq_zero_iff_v a a).2 rfl]

lemma ne_ab2 : b ≠ a + b := by
  intro h; apply ha
  have := congrArg (fun z => z + b) h
  rw [add_add_v] at this
  rw [← this, (add_eq_zero_iff_v b b).2 rfl]

lemma bit_a (t) : bit a b t a = t.1 := by
  simp [bit, hab, ne_ab1 ha hb hab]

lemma bit_b (t) : bit a b t b = t.2 := by
  simp [bit, Ne.symm hab, ne_ab2 ha hb hab]

lemma bit_ab (t) : bit a b t (a + b) = t.1 + t.2 + 1 := by
  simp [bit, (ne_ab1 ha hb hab).symm, (ne_ab2 ha hb hab).symm]

lemma T_eq (t : ZMod 2 × ZMod 2) (x : Fin n → ZMod 2) :
    ∑ w ∈ fr a b, sg (bit a b t w) * chi w x =
      sg t.1 * chi a x + sg t.2 * chi b x + sg (t.1 + t.2 + 1) * chi (a + b) x := by
  have h1 : a ∉ ({b, a + b} : Finset (Fin n → ZMod 2)) := by
    simp [hab, ne_ab1 ha hb hab]
  have h2 : b ∉ ({a + b} : Finset (Fin n → ZMod 2)) := by
    simp [ne_ab2 ha hb hab]
  rw [fr, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton,
    bit_a ha hb hab, bit_b ha hb hab, bit_ab ha hb hab]
  ring

lemma phi_inj (t t' : ZMod 2 × ZMod 2) (h : (phi a b t).1 = (phi a b t').1) : t = t' := by
  obtain ⟨t1, t2⟩ := t
  obtain ⟨u1, u2⟩ := t'
  have e1 := ne_ab1 ha hb hab
  have e2 := ne_ab2 ha hb hab
  have hab' : a + b ≠ 0 := by rw [Ne, add_eq_zero_iff_v]; exact hab
  simp only [phi] at h
  rcases z2 t1 with rfl | rfl <;> rcases z2 t2 with rfl | rfl <;>
    rcases z2 u1 with rfl | rfl <;> rcases z2 u2 with rfl | rfl <;>
    simp only [zero_smul, one_smul, add_zero, zero_add] at h <;>
    first
    | rfl
    | exact absurd h ha.symm
    | exact absurd h hb.symm
    | exact absurd h hab'.symm
    | exact absurd h ha
    | exact absurd h hb
    | exact absurd h hab'
    | exact absurd h hab
    | exact absurd h hab.symm
    | exact absurd h e1
    | exact absurd h e2
    | exact absurd h e1.symm
    | exact absurd h e2.symm

end dist


section glob
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowsF (a b : ι → Fin n → ZMod 2) (w : Fin n → ZMod 2) : Finset ι :=
  univ.filter (fun k => w ∈ fr (a k) (b k))

def sig (a b : ι → Fin n → ZMod 2) (s : ι → ZMod 2 × ZMod 2) (w : Fin n → ZMod 2) : ℤ :=
  ∑ k ∈ rowsF a b w, sg (bit (a k) (b k) (s k) w)

lemma regroup (a b : ι → Fin n → ZMod 2) (f : ι → (Fin n → ZMod 2) → ℤ) :
    ∑ k, ∑ w ∈ fr (a k) (b k), f k w = ∑ w, ∑ k ∈ rowsF a b w, f k w := by
  apply Finset.sum_comm'
  intro k w
  simp [rowsF]

lemma state_sum (a b : ι → Fin n → ZMod 2) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (s : ι → ZMod 2 × ZMod 2) (x : Fin n → ZMod 2) :
    ∑ k, 4 * (if dotProduct (phi (a k) (b k) (s k)).1 x + (phi (a k) (b k) (s k)).2 ≠
        dotProduct (a k) x * dotProduct (b k) x then (1:ℤ) else 0) =
      (Fintype.card ι : ℤ) - ∑ w, sig a b s w * chi w x := by
  simp only [state_id]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  have h1 : ∀ k, sg (s k).1 * chi (a k) x + sg (s k).2 * chi (b k) x +
      sg ((s k).1 + (s k).2 + 1) * chi (a k + b k) x =
      ∑ w ∈ fr (a k) (b k), sg (bit (a k) (b k) (s k) w) * chi w x := fun k =>
    (T_eq (hab k).1 (hab k).2.1 (hab k).2.2 (s k) x).symm
  simp only [h1]
  rw [regroup]
  simp only [sig, Finset.sum_mul]

lemma fourier_inv (f : (Fin n → ZMod 2) → ℤ) (h : ∀ x, ∑ w, f w * chi w x = 0)
    (w0 : Fin n → ZMod 2) : f w0 = 0 := by
  have key : ∑ x, (∑ w, f w * chi w x) * chi w0 x = ∑ w, f w * (2 ^ n * dl (w + w0)) := by
    simp only [Finset.sum_mul, mul_assoc, ← chi_add]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_chi]
  have key2 : ∑ w, f w * (2 ^ n * dl (w + w0)) = f w0 * 2 ^ n := by
    simp only [dl, add_eq_zero_iff_v, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [key2] at key
  simp only [h, zero_mul, Finset.sum_const_zero] at key
  have : (2:ℤ) ^ n ≠ 0 := by positivity
  rcases mul_eq_zero.1 key.symm with h1 | h1
  · exact h1
  · exact absurd h1 this

lemma good_card {e : ℕ} (hcard : Fintype.card ι = 4 * e) (a b : ι → Fin n → ZMod 2)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (good : Finset ((ι → Fin n → ZMod 2) × (ι → ZMod 2)))
    (hgood : ∀ p, p ∈ good ↔ ∀ x : Fin n → ZMod 2, ((Finset.univ : Finset ι).filter (fun i =>
        dotProduct (p.1 i) x + p.2 i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ e) :
    good.card =
      (Finset.univ.filter (fun s : ι → ZMod 2 × ZMod 2 => ∀ w, sig a b s w = 0)).card := by
  have hcnt : ∀ (p : (ι → Fin n → ZMod 2) × (ι → ZMod 2)) x,
      (((Finset.univ : Finset ι).filter (fun i =>
        dotProduct (p.1 i) x + p.2 i ≠ dotProduct (a i) x * dotProduct (b i) x)).card : ℤ) =
      ∑ k, (if dotProduct (p.1 k) x + p.2 k ≠ dotProduct (a k) x * dotProduct (b k) x
        then (1:ℤ) else 0) := by
    intro p x
    rw [Finset.natCast_card_filter]
  symm
  apply Finset.card_bij (fun s _ =>
    ((fun k => (phi (a k) (b k) (s k)).1, fun k => (phi (a k) (b k) (s k)).2) :
      (ι → Fin n → ZMod 2) × (ι → ZMod 2)))
  · intro s hs
    rw [Finset.mem_filter] at hs
    rw [hgood]
    intro x
    have h4 := state_sum a b hab s x
    simp only [hs.2, zero_mul, Finset.sum_const_zero, sub_zero, hcard] at h4
    have h5 := hcnt ((fun k => (phi (a k) (b k) (s k)).1, fun k => (phi (a k) (b k) (s k)).2) :
      (ι → Fin n → ZMod 2) × (ι → ZMod 2)) x
    simp only at h5
    rw [← Finset.mul_sum, ← h5] at h4
    push_cast at h4
    have : ((((Finset.univ : Finset ι).filter (fun i =>
        dotProduct ((phi (a i) (b i) (s i)).1) x + (phi (a i) (b i) (s i)).2 ≠
          dotProduct (a i) x * dotProduct (b i) x)).card : ℤ)) ≤ e := by linarith
    exact_mod_cast this
  · intro s1 _ s2 _ h
    funext k
    have := congrArg (fun p => p.1 k) h
    exact phi_inj (hab k).1 (hab k).2.1 (hab k).2.2 _ _ this
  · intro p hp
    rw [hgood] at hp
    set cZ : (Fin n → ZMod 2) → ℤ := fun x => ∑ k, (if dotProduct (p.1 k) x + p.2 k ≠
        dotProduct (a k) x * dotProduct (b k) x then (1:ℤ) else 0) with hcZ
    have hle : ∀ x, 4 * cZ x ≤ 4 * e := by
      intro x
      have h1 := hcnt p x
      have h2 : ((((Finset.univ : Finset ι).filter (fun i =>
        dotProduct (p.1 i) x + p.2 i ≠ dotProduct (a i) x * dotProduct (b i) x)).card : ℤ)) ≤ e := by
        exact_mod_cast hp x
      rw [h1] at h2
      linarith
    have htot : ∑ x, 4 * cZ x = ∑ k, 2 ^ n * (2 - Kv (p.1 k) (a k) (b k) (p.2 k)) := by
      simp only [hcZ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => sum_err _ _ _ _)
    have hK : ∀ k, Kv (p.1 k) (a k) (b k) (p.2 k) ≤ 1 := fun k =>
      (Kv_le _ _ _ _ (hab k).1 (hab k).2.1 (hab k).2.2).1
    have hA : ∑ x : Fin n → ZMod 2, 4 * cZ x ≤ ∑ x : Fin n → ZMod 2, 4 * (e : ℤ) :=
      Finset.sum_le_sum (fun x _ => hle x)
    have hB : ∑ x : Fin n → ZMod 2, 4 * (e : ℤ) = ∑ k : ι, (2:ℤ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, card_V, hcard, nsmul_eq_mul]
      push_cast; ring
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ (2:ℤ) ^ n * (1 - Kv (p.1 k) (a k) (b k) (p.2 k)) := by
      intro k _
      have := hK k
      have : (0:ℤ) ≤ 2 ^ n := by positivity
      nlinarith
    have hsum0 : ∑ k, (2:ℤ) ^ n * (1 - Kv (p.1 k) (a k) (b k) (p.2 k)) = 0 := by
      have e1 : ∑ k, (2:ℤ) ^ n * (1 - Kv (p.1 k) (a k) (b k) (p.2 k)) =
          ∑ k, 2 ^ n * (2 - Kv (p.1 k) (a k) (b k) (p.2 k)) - ∑ k : ι, (2:ℤ) ^ n := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      have e2 := Finset.sum_nonneg hnn
      linarith
    have hK1 : ∀ k, Kv (p.1 k) (a k) (b k) (p.2 k) = 1 := by
      intro k
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 k (Finset.mem_univ _)
      have h2 : (2:ℤ) ^ n ≠ 0 := by positivity
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h2
      · linarith
    choose s hs using fun k => (Kv_le _ _ _ _ (hab k).1 (hab k).2.1 (hab k).2.2).2 (hK1 k)
    have hall : ∀ x, 4 * cZ x = 4 * e := by
      have heq : ∑ x : Fin n → ZMod 2, 4 * cZ x = ∑ x : Fin n → ZMod 2, 4 * (e : ℤ) := by
        rw [htot, hB]
        have : ∀ k, (2:ℤ) ^ n * (2 - Kv (p.1 k) (a k) (b k) (p.2 k)) = 2 ^ n := by
          intro k; rw [hK1 k]; ring
        simp only [this]
      intro x
      exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).1 heq x (Finset.mem_univ _)
    refine ⟨s, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply fourier_inv
      intro x
      have h4 := state_sum a b hab s x
      have h5 : ∀ k, phi (a k) (b k) (s k) = (p.1 k, p.2 k) := hs
      simp only [h5] at h4
      have h6 := hall x
      simp only [hcZ] at h6
      rw [← Finset.mul_sum] at h4
      rw [hcard] at h4
      push_cast at h4
      linarith
    · ext k
      · simp only [hs k]
      · simp only [hs k]

end glob

section count
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def EF (a b : ι → Fin n → ZMod 2) : Finset (Fin n → ZMod 2) :=
  univ.filter (fun w => ∃ k, w ∈ fr (a k) (b k))

def adjF (a b : ι → Fin n → ZMod 2) (i j : ι) : Prop :=
  ∃ v ∈ fr (a i) (b i), v ∈ fr (a j) (b j)

lemma bit_out {a b : Fin n → ZMod 2} (t : ZMod 2 × ZMod 2) (w : Fin n → ZMod 2)
    (hw : w ∉ fr a b) : bit a b t w = 0 := by
  simp only [fr, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  simp [bit, hw.1, hw.2.1, hw.2.2]

lemma sig_iff (a b : ι → Fin n → ZMod 2)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2)
    (s : ι → ZMod 2 × ZMod 2) (w : Fin n → ZMod 2) :
    sig a b s w = 0 ↔ (w ∈ EF a b → ∑ k, bit (a k) (b k) (s k) w + 1 = 0) := by
  by_cases hw : w ∈ EF a b
  · simp only [hw, true_implies]
    obtain ⟨k0, hk0⟩ := (Finset.mem_filter.1 hw).2
    have hc := hrows k0 w hk0
    obtain ⟨k1, k2, hne, heq⟩ := Finset.card_eq_two.1 hc
    have hsum : ∑ k, bit (a k) (b k) (s k) w = ∑ k ∈ rowsF a b w, bit (a k) (b k) (s k) w := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      apply bit_out
      simpa [rowsF] using hk
    rw [hsum, sig, heq, Finset.sum_pair hne, Finset.sum_pair hne]
    have key : ∀ u v : ZMod 2, sg u + sg v = 0 ↔ u + v + 1 = 0 := by decide
    exact key _ _
  · simp only [hw, false_implies, iff_true]
    apply Finset.sum_eq_zero
    intro k hk
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨k, (Finset.mem_filter.1 hk).2⟩⟩) hw

lemma orthE {κ : Type*} [Fintype κ] [DecidableEq κ] (E : Finset κ) (v : κ → ZMod 2) :
    ∑ y ∈ Fintype.piFinset (fun w => if w ∈ E then (univ : Finset (ZMod 2)) else {0}),
      sg (dotProduct y v) = if (∀ w ∈ E, v w = 0) then (2:ℤ) ^ E.card else 0 := by
  split_ifs with hv
  · have h1 : ∀ y ∈ Fintype.piFinset (fun w => if w ∈ E then (univ : Finset (ZMod 2)) else {0}),
        sg (dotProduct y v) = 1 := by
      intro y hy
      rw [Fintype.mem_piFinset] at hy
      have : dotProduct y v = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        by_cases hw : w ∈ E
        · rw [hv w hw, mul_zero]
        · have := hy w
          rw [if_neg hw, Finset.mem_singleton] at this
          rw [this, zero_mul]
      rw [this]; rfl
    have hc : (Fintype.piFinset (fun w => if w ∈ E then (univ : Finset (ZMod 2)) else {0})).card
        = 2 ^ E.card := by
      rw [Fintype.card_piFinset]
      have : ∀ w, (if w ∈ E then (univ : Finset (ZMod 2)) else {0}).card =
          if w ∈ E then 2 else 1 := by
        intro w; split_ifs <;> simp [ZMod.card]
      simp only [this]
      rw [Finset.prod_ite_mem univ E (fun _ => 2), Finset.univ_inter, Finset.prod_const]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, hc]
    simp
  · obtain ⟨k, hkE, hk⟩ : ∃ k ∈ E, v k ≠ 0 := by
      by_contra h
      apply hv
      intro w hw
      by_contra hw'
      exact h ⟨w, hw, hw'⟩
    have hk1 : v k = 1 := (z2 _).resolve_left hk
    set S := Fintype.piFinset (fun w => if w ∈ E then (univ : Finset (ZMod 2)) else {0}) with hS
    have hmem : ∀ y ∈ S, y + Pi.single k 1 ∈ S := by
      intro y hy
      rw [hS, Fintype.mem_piFinset] at hy ⊢
      intro w
      by_cases hw : w = k
      · subst hw; rw [if_pos hkE]; exact Finset.mem_univ _
      · rw [Pi.add_apply, Pi.single_eq_of_ne hw, add_zero]; exact hy w
    have key : ∑ y ∈ S, sg (dotProduct y v) = ∑ y ∈ S, -sg (dotProduct y v) := by
      apply Finset.sum_nbij' (fun y => y + Pi.single k 1) (fun y => y + Pi.single k 1) hmem hmem
        (fun y _ => add_add_v _ _) (fun y _ => add_add_v _ _)
      intro y _
      rw [add_dotProduct, single_dotProduct, hk1, mul_one, sg_add, sg_one, mul_neg_one, neg_neg]
    rw [Finset.sum_neg_distrib] at key
    linarith

lemma inner_bit (a b : Fin n → ZMod 2) (y : (Fin n → ZMod 2) → ZMod 2) (t : ZMod 2 × ZMod 2) :
    ∑ w, y w * bit a b t w = y a * t.1 + y b * t.2 + y (a + b) * (t.1 + t.2 + 1) := by
  simp only [bit, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma dot_vS (a b : ι → Fin n → ZMod 2) (y : (Fin n → ZMod 2) → ZMod 2)
    (s : ι → ZMod 2 × ZMod 2) :
    dotProduct y (fun w => ∑ k, bit (a k) (b k) (s k) w + 1) =
      ∑ k, (y (a k) * (s k).1 + y (b k) * (s k).2 + y (a k + b k) * ((s k).1 + (s k).2 + 1)) +
        ∑ w, y w := by
  simp only [dotProduct]
  have h1 : ∀ w, y w * (∑ k, bit (a k) (b k) (s k) w + 1) =
      ∑ k, y w * bit (a k) (b k) (s k) w + y w := by
    intro w; rw [mul_add, mul_one, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => inner_bit (a k) (b k) y (s k))

lemma sum_t (Y1 Y2 Y3 : ZMod 2) :
    ∑ t : ZMod 2 × ZMod 2, sg (Y1 * t.1 + Y2 * t.2 + Y3 * (t.1 + t.2 + 1)) =
      if Y1 = Y3 ∧ Y2 = Y3 then 4 * sg Y3 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_z2]
  revert Y1 Y2 Y3; decide

lemma sum_s (a b : ι → Fin n → ZMod 2) (y : (Fin n → ZMod 2) → ZMod 2) :
    ∑ s : ι → ZMod 2 × ZMod 2, sg (dotProduct y (fun w => ∑ k, bit (a k) (b k) (s k) w + 1)) =
      if (∀ k, y (a k) = y (a k + b k) ∧ y (b k) = y (a k + b k)) then
        4 ^ Fintype.card ι * sg (∑ k, y (a k + b k) + ∑ w, y w) else 0 := by
  have h1 : ∀ s : ι → ZMod 2 × ZMod 2,
      sg (dotProduct y (fun w => ∑ k, bit (a k) (b k) (s k) w + 1)) =
      (∏ k, sg (y (a k) * (s k).1 + y (b k) * (s k).2 + y (a k + b k) * ((s k).1 + (s k).2 + 1)))
        * sg (∑ w, y w) := by
    intro s; rw [dot_vS, sg_add, sg_sum]
  simp only [h1]
  rw [← Finset.sum_mul]
  have := Fintype.prod_sum (fun k (t : ZMod 2 × ZMod 2) =>
    sg (y (a k) * t.1 + y (b k) * t.2 + y (a k + b k) * (t.1 + t.2 + 1)))
  rw [← this]
  simp only [sum_t]
  rw [Fintype.prod_ite_zero]
  split_ifs
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, sg_add,
      sg_sum univ (fun k => y (a k + b k))]
    ring
  · simp

end count

section final
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Gm (a b : ι → Fin n → ZMod 2) (g : ι → ZMod 2) (w : Fin n → ZMod 2) : ZMod 2 :=
  if ∃ k, w ∈ fr (a k) (b k) ∧ g k = 1 then 1 else 0

open Classical in
noncomputable def G0 (a b : ι → Fin n → ZMod 2) : Finset (ι → ZMod 2) :=
  univ.filter (fun g => ∀ i j, adjF a b i j → g i = g j)

lemma mem_G0 {a b : ι → Fin n → ZMod 2} {g : ι → ZMod 2} :
    g ∈ G0 a b ↔ ∀ i j, adjF a b i j → g i = g j := by
  simp [G0]

lemma Gm_eq {a b : ι → Fin n → ZMod 2} {g : ι → ZMod 2} (hg : g ∈ G0 a b) (k : ι)
    (w : Fin n → ZMod 2) (hw : w ∈ fr (a k) (b k)) : Gm a b g w = g k := by
  have hg' := mem_G0.1 hg
  unfold Gm
  rcases z2 (g k) with h | h
  · rw [h, if_neg]
    rintro ⟨k', hk', hgk'⟩
    have := hg' k k' ⟨w, hw, hk'⟩
    rw [h, hgk'] at this
    exact zero_ne_one this
  · rw [h, if_pos ⟨k, hw, h⟩]

lemma Gm_out {a b : ι → Fin n → ZMod 2} {g : ι → ZMod 2} (w : Fin n → ZMod 2)
    (hw : w ∉ EF a b) : Gm a b g w = 0 := by
  unfold Gm
  rw [if_neg]
  rintro ⟨k, hk, _⟩
  exact hw (Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hk⟩)

lemma Y0_eq {a b : ι → Fin n → ZMod 2} {y : (Fin n → ZMod 2) → ZMod 2}
    (hy : ∀ k, y (a k) = y (a k + b k) ∧ y (b k) = y (a k + b k)) (k : ι)
    (w : Fin n → ZMod 2) (hw : w ∈ fr (a k) (b k)) : y w = y (a k) := by
  simp only [fr, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · rfl
  · rw [(hy k).2, (hy k).1]
  · rw [(hy k).1]

lemma comp_mem_G0 {a b : ι → Fin n → ZMod 2} {y : (Fin n → ZMod 2) → ZMod 2}
    (hy : ∀ k, y (a k) = y (a k + b k) ∧ y (b k) = y (a k + b k)) :
    (fun k => y (a k)) ∈ G0 a b := by
  refine mem_G0.2 ?_
  rintro i j ⟨v, hvi, hvj⟩
  rw [← Y0_eq hy i v hvi, ← Y0_eq hy j v hvj]

lemma Gm_comp {a b : ι → Fin n → ZMod 2} {y : (Fin n → ZMod 2) → ZMod 2}
    (hy : y ∈ (Fintype.piFinset (fun w => if w ∈ EF a b then (univ : Finset (ZMod 2))
      else {0})).filter (fun y => ∀ k, y (a k) = y (a k + b k) ∧ y (b k) = y (a k + b k))) :
    Gm a b (fun k => y (a k)) = y := by
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hy
  have hyG := comp_mem_G0 hy.2
  funext w
  by_cases hw : w ∈ EF a b
  · obtain ⟨k0, hk0⟩ := (Finset.mem_filter.1 hw).2
    rw [Gm_eq hyG k0 w hk0, Y0_eq hy.2 k0 w hk0]
  · rw [Gm_out w hw]
    have := hy.1 w
    rw [if_neg hw, Finset.mem_singleton] at this
    exact this.symm

lemma sum_Y_G (a b : ι → Fin n → ZMod 2) :
    ∑ y ∈ (Fintype.piFinset (fun w => if w ∈ EF a b then (univ : Finset (ZMod 2))
      else {0})).filter (fun y => ∀ k, y (a k) = y (a k + b k) ∧ y (b k) = y (a k + b k)),
      sg (∑ k, y (a k + b k) + ∑ w, y w) =
    ∑ g ∈ G0 a b, sg (∑ k, g k + ∑ w, Gm a b g w) := by
  apply Finset.sum_nbij' (fun y => fun k => y (a k)) (fun g => Gm a b g)
  · intro y hy
    exact comp_mem_G0 (Finset.mem_filter.1 hy).2
  · intro g hg
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun w => ?_, fun k => ?_⟩
    · split_ifs with hw
      · exact Finset.mem_univ _
      · rw [Gm_out w hw]; exact Finset.mem_singleton_self _
    · have h1 : a k ∈ fr (a k) (b k) := by simp [fr]
      have h2 : b k ∈ fr (a k) (b k) := by simp [fr]
      have h3 : a k + b k ∈ fr (a k) (b k) := by simp [fr]
      rw [Gm_eq hg k _ h1, Gm_eq hg k _ h2, Gm_eq hg k _ h3]
      exact ⟨rfl, rfl⟩
  · intro y hy
    exact Gm_comp hy
  · intro g hg
    funext k
    have h1 : a k ∈ fr (a k) (b k) := by simp [fr]
    exact Gm_eq hg k _ h1
  · intro y hy
    have hc := Gm_comp hy
    have hy2 := (Finset.mem_filter.1 hy).2
    simp only [hc]
    congr 2
    exact Finset.sum_congr rfl (fun k _ => (hy2 k).1.symm)

lemma card_fr {a b : Fin n → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (fr a b).card = 3 :=
  Finset.card_eq_three.2 ⟨a, b, a + b, hab, ne_ab1 ha hb hab, ne_ab2 ha hb hab, rfl⟩

lemma dcount (a b : ι → Fin n → ZMod 2) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2)
    (g : ι → ZMod 2) (hg : g ∈ G0 a b) :
    2 * (univ.filter (fun w => ∃ k, w ∈ fr (a k) (b k) ∧ g k = 1)).card =
      3 * (univ.filter (fun k => g k = 1)).card := by
  set S := univ.filter (fun k : ι => g k = 1) with hS
  have h1 : ∑ k ∈ S, (fr (a k) (b k)).card = 3 * S.card := by
    rw [Finset.sum_congr rfl (fun k _ => card_fr (hab k).1 (hab k).2.1 (hab k).2.2),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have h2 : ∑ k ∈ S, (fr (a k) (b k)).card =
      ∑ w, (S.filter (fun k => w ∈ fr (a k) (b k))).card := by
    simp only [Finset.card_eq_sum_ones]
    apply Finset.sum_comm'
    intro k w
    simp
  have h3 : ∀ w, (S.filter (fun k => w ∈ fr (a k) (b k))).card =
      if (∃ k, w ∈ fr (a k) (b k) ∧ g k = 1) then 2 else 0 := by
    intro w
    split_ifs with hw
    · obtain ⟨k0, hk0, hg0⟩ := hw
      have : S.filter (fun k => w ∈ fr (a k) (b k)) = rowsF a b w := by
        ext k
        simp only [hS, rowsF, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          rw [← Gm_eq hg k w h, Gm_eq hg k0 w hk0, hg0]
      rw [this, hrows k0 w hk0]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk h
      exact hw ⟨k, h, (Finset.mem_filter.1 hk).2⟩
  rw [h2, Finset.sum_congr rfl (fun w _ => h3 w), ← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul] at h1
  omega

lemma eqv_const {a b : ι → Fin n → ZMod 2} {g : ι → ZMod 2} (hg : g ∈ G0 a b) {i j : ι}
    (h : Relation.EqvGen (adjF a b) i j) : g i = g j := by
  induction h with
  | rel x y hxy => exact mem_G0.1 hg x y hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

lemma sg_nat (m : ℕ) : sg (m : ZMod 2) = (-1) ^ m := by
  induction m with
  | zero => simp [sg]
  | succ m ih => rw [Nat.cast_succ, sg_add, ih, sg_one, pow_succ]

lemma sg_G (a b : ι → Fin n → ZMod 2) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2)
    (g : ι → ZMod 2) (hg : g ∈ G0 a b) :
    sg (∑ k, g k + ∑ w, Gm a b g w) = (-1) ^ ((univ.filter (fun k => g k = 1)).card / 2) := by
  have h1 : ∑ k, g k = ((univ.filter (fun k => g k = 1)).card : ZMod 2) := by
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro k _
    rcases z2 (g k) with h | h <;> simp [h]
  have h2 : ∑ w, Gm a b g w =
      ((univ.filter (fun w => ∃ k, w ∈ fr (a k) (b k) ∧ g k = 1)).card : ZMod 2) := by
    rw [Finset.natCast_card_filter]
    rfl
  have hd := dcount a b hab hrows g hg
  rw [h1, h2, ← Nat.cast_add, sg_nat]
  rw [show (univ.filter (fun k => g k = 1)).card +
      (univ.filter (fun w => ∃ k, w ∈ fr (a k) (b k) ∧ g k = 1)).card =
      (univ.filter (fun k => g k = 1)).card / 2 +
        2 * (2 * ((univ.filter (fun k => g k = 1)).card / 2)) by omega, pow_add, pow_mul]
  norm_num

section comps
variable (a b : ι → Fin n → ZMod 2) (comp : ι → Finset ι)
  (hcomp : ∀ i j, j ∈ comp i ↔ Relation.EqvGen (adjF a b) i j)
include hcomp

lemma comp_eq_iff (i j : ι) : comp i = comp j ↔ Relation.EqvGen (adjF a b) i j := by
  constructor
  · intro h
    have : j ∈ comp i := by rw [h, hcomp]; exact Relation.EqvGen.refl j
    exact (hcomp i j).1 this
  · intro h
    ext k
    rw [hcomp, hcomp]
    constructor
    · intro hik; exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hik
    · intro hjk; exact Relation.EqvGen.trans _ _ _ h hjk

lemma mem_comp_self (i : ι) : i ∈ comp i := (hcomp i i).2 (Relation.EqvGen.refl i)

lemma mem_comp_iff (i k : ι) : k ∈ comp i ↔ comp k = comp i := by
  rw [hcomp, comp_eq_iff a b comp hcomp]
  exact ⟨fun h => Relation.EqvGen.symm _ _ h, fun h => Relation.EqvGen.symm _ _ h⟩

lemma gT_mem (T : Finset (Finset ι)) :
    (fun k => if comp k ∈ T then (1 : ZMod 2) else 0) ∈ G0 a b := by
  refine mem_G0.2 (fun i j hij => ?_)
  have : comp i = comp j := (comp_eq_iff a b comp hcomp i j).2 (Relation.EqvGen.rel _ _ hij)
  simp only [this]

lemma gT_T (g : ι → ZMod 2) (hg : g ∈ G0 a b) :
    (fun k => if comp k ∈ (univ.image comp).filter (fun C => ∃ k' ∈ C, g k' = 1)
      then (1 : ZMod 2) else 0) = g := by
  funext k
  have hk : (∃ k' ∈ comp k, g k' = 1) ↔ g k = 1 := by
    constructor
    · rintro ⟨k', hk', h1⟩
      rw [eqv_const hg ((hcomp k k').1 hk'), h1]
    · intro h1; exact ⟨k, mem_comp_self a b comp hcomp k, h1⟩
  have hmem : comp k ∈ univ.image comp := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rcases z2 (g k) with h0 | h1
  · have : comp k ∉ (univ.image comp).filter (fun C => ∃ k' ∈ C, g k' = 1) := by
      rw [Finset.mem_filter]
      rintro ⟨_, hk'⟩
      rw [hk, h0] at hk'
      exact zero_ne_one hk'
    rw [if_neg this, h0]
  · have : comp k ∈ (univ.image comp).filter (fun C => ∃ k' ∈ C, g k' = 1) := by
      rw [Finset.mem_filter]
      exact ⟨hmem, hk.2 h1⟩
    rw [if_pos this, h1]

lemma sum_G_T (h : (ι → ZMod 2) → ℤ) :
    ∑ g ∈ G0 a b, h g =
      ∑ T ∈ (univ.image comp).powerset,
        h (fun k => if comp k ∈ T then (1 : ZMod 2) else 0) := by
  apply Finset.sum_nbij' (fun g => (univ.image comp).filter (fun C => ∃ k ∈ C, g k = 1))
    (fun T => fun k => if comp k ∈ T then (1 : ZMod 2) else 0)
  · intro g _
    exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · intro T _
    exact gT_mem a b comp hcomp T
  · intro g hg
    exact gT_T a b comp hcomp g hg
  · intro T hT
    rw [Finset.mem_powerset] at hT
    ext C
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hC, k, hk, h1⟩
      obtain ⟨k0, _, rfl⟩ := Finset.mem_image.1 hC
      have : comp k = comp k0 := (mem_comp_iff a b comp hcomp k0 k).1 hk
      split_ifs at h1 with hkT
      · rw [← this]; exact hkT
      · exact absurd h1 zero_ne_one
    · intro hC
      refine ⟨hT hC, ?_⟩
      obtain ⟨k0, _, rfl⟩ := Finset.mem_image.1 (hT hC)
      exact ⟨k0, mem_comp_self a b comp hcomp k0, by rw [if_pos hC]⟩
  · intro g hg
    rw [gT_T a b comp hcomp g hg]

lemma card_supp_gT (T : Finset (Finset ι)) (hT : T ⊆ univ.image comp) :
    (univ.filter (fun k => (if comp k ∈ T then (1 : ZMod 2) else 0) = 1)).card =
      ∑ C ∈ T, C.card := by
  have e1 : univ.filter (fun k => (if comp k ∈ T then (1 : ZMod 2) else 0) = 1) =
      univ.filter (fun k => comp k ∈ T) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h <;> simp [h]
  rw [e1, Finset.card_eq_sum_card_fiberwise (f := comp) (s := univ.filter (fun k => comp k ∈ T))
    (t := T) (fun k hk => (Finset.mem_filter.1 hk).2)]
  apply Finset.sum_congr rfl
  intro C hC
  obtain ⟨k0, _, rfl⟩ := Finset.mem_image.1 (hT hC)
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_comp_iff a b comp hcomp k0 k]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hC, h⟩

lemma comp_even (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2)
    (C : Finset ι) (hC : C ∈ univ.image comp) : 2 ∣ C.card := by
  have hg := gT_mem a b comp hcomp {C}
  have h := dcount a b hab hrows _ hg
  rw [card_supp_gT a b comp hcomp {C} (by simpa using hC), Finset.sum_singleton] at h
  omega

lemma sum_T (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2) :
    ∑ T ∈ (univ.image comp).powerset,
      ((-1 : ℤ) ^ ((univ.filter (fun k => (if comp k ∈ T then (1 : ZMod 2) else 0) = 1)).card
        / 2)) =
      if ∀ C ∈ univ.image comp, 4 ∣ C.card then 2 ^ (univ.image comp).card else 0 := by
  have hev : ∀ C ∈ univ.image comp, C.card = 2 * (C.card / 2) := fun C hC => by
    have := comp_even a b comp hcomp hab hrows C hC
    omega
  have h1 : ∀ T ∈ (univ.image comp).powerset,
      ((-1 : ℤ) ^ ((univ.filter (fun k => (if comp k ∈ T then (1 : ZMod 2) else 0) = 1)).card
        / 2)) = ∏ C ∈ T, (-1 : ℤ) ^ (C.card / 2) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [card_supp_gT a b comp hcomp T hT, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun C hC => hev C (hT hC)), ← Finset.mul_sum]
    omega
  rw [Finset.sum_congr rfl h1, ← Finset.prod_one_add]
  split_ifs with h4
  · rw [Finset.prod_congr rfl (fun C hC => show (1 : ℤ) + (-1) ^ (C.card / 2) = 2 from by
        have h5 := h4 C hC
        have h6 := hev C hC
        rw [Even.neg_one_pow ⟨C.card / 4, by omega⟩]
        norm_num), Finset.prod_const]
  · obtain ⟨C, hC, hC4⟩ : ∃ C ∈ univ.image comp, ¬ 4 ∣ C.card := by
      by_contra hh
      exact h4 (fun C hC => by
        by_contra h5
        exact hh ⟨C, hC, h5⟩)
    apply Finset.prod_eq_zero hC
    have h6 := hev C hC
    rw [Odd.neg_one_pow ⟨C.card / 4, by omega⟩]
    norm_num

end comps

lemma card_E (a b : ι → Fin n → ZMod 2) (e : ℕ) (hcard : Fintype.card ι = 4 * e)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2) :
    (EF a b).card = 6 * e := by
  have hg : (fun _ => (1 : ZMod 2)) ∈ G0 a b := mem_G0.2 (fun _ _ _ => rfl)
  have h := dcount a b hab hrows (fun _ => 1) hg
  have h2 : (univ.filter (fun w => ∃ k, w ∈ fr (a k) (b k) ∧ (1 : ZMod 2) = 1)) = EF a b := by
    ext w; simp [EF]
  have h3 : (univ.filter (fun k : ι => (1 : ZMod 2) = 1)) = univ := by
    ext k; simp
  rw [h2, h3, Finset.card_univ, hcard] at h
  omega

lemma sol_card (a b : ι → Fin n → ZMod 2) (comp : ι → Finset ι)
    (hcomp : ∀ i j, j ∈ comp i ↔ Relation.EqvGen (adjF a b) i j)
    (e : ℕ) (hcard : Fintype.card ι = 4 * e) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hrows : ∀ k, ∀ v ∈ fr (a k) (b k), (rowsF a b v).card = 2) :
    ((univ.filter (fun s : ι → ZMod 2 × ZMod 2 => ∀ w, sig a b s w = 0)).card : ℤ) =
      if ∀ C ∈ univ.image comp, 4 ∣ C.card then 2 ^ (2 * e + (univ.image comp).card)
      else 0 := by
  have step1 : (2:ℤ) ^ (EF a b).card *
      ((univ.filter (fun s : ι → ZMod 2 × ZMod 2 => ∀ w, sig a b s w = 0)).card : ℤ) =
      ∑ s : ι → ZMod 2 × ZMod 2,
        ∑ y ∈ Fintype.piFinset (fun w => if w ∈ EF a b then (univ : Finset (ZMod 2)) else {0}),
          sg (dotProduct y (fun w => ∑ k, bit (a k) (b k) (s k) w + 1)) := by
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [orthE]
    have hiff : (∀ w, sig a b s w = 0) ↔
        (∀ w ∈ EF a b, (∑ k, bit (a k) (b k) (s k) w + 1) = 0) :=
      forall_congr' (fun w => sig_iff a b hrows s w)
    by_cases h : ∀ w, sig a b s w = 0
    · rw [if_pos h, if_pos (hiff.1 h), mul_one]
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h')), mul_zero]
  have step2 : ∑ s : ι → ZMod 2 × ZMod 2,
        ∑ y ∈ Fintype.piFinset (fun w => if w ∈ EF a b then (univ : Finset (ZMod 2)) else {0}),
          sg (dotProduct y (fun w => ∑ k, bit (a k) (b k) (s k) w + 1)) =
      4 ^ Fintype.card ι * ∑ g ∈ G0 a b, sg (∑ k, g k + ∑ w, Gm a b g w) := by
    rw [Finset.sum_comm]
    simp only [sum_s]
    rw [← Finset.sum_filter, ← Finset.mul_sum, sum_Y_G]
  have step3 : ∑ g ∈ G0 a b, sg (∑ k, g k + ∑ w, Gm a b g w) =
      if ∀ C ∈ univ.image comp, 4 ∣ C.card then 2 ^ (univ.image comp).card else 0 := by
    rw [Finset.sum_congr rfl (fun g hg => sg_G a b hab hrows g hg)]
    rw [sum_G_T a b comp hcomp]
    exact sum_T a b comp hcomp hab hrows
  rw [step2, step3, card_E a b e hcard hab hrows, hcard] at step1
  have h4 : (4:ℤ) ^ (4 * e) = 2 ^ (6 * e) * 2 ^ (2 * e) := by
    rw [← pow_add, show (4:ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  rw [h4, mul_assoc] at step1
  have h5 := mul_left_cancel₀ (by positivity : (2:ℤ) ^ (6 * e) ≠ 0) step1
  rw [h5]
  split_ifs <;> simp [pow_add]

end final

end PEqualNP.Outside.L_lib_935_aux

theorem PEqualNP.Outside.L_lib_935 : ∀ (n e : Nat),
  let F := ZMod 2
  let W := Fin n → F
  let I := Fin (4*e)
  ∀ a b : I → W,
    (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let freq := fun (i : I) => ({a i, b i, a i+b i} : Finset W)
    let rows := fun v : W => (Finset.univ : Finset I).filter (fun i => v ∈ freq i)
    (∀ i, ∀ v ∈ freq i, (rows v).card = 2) →
    let adj := fun (i j : I) => ∃ v ∈ freq i, v ∈ freq j
    let comp := fun i : I => (Finset.univ : Finset I).filter
      (fun j => @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true)
    let comps := (Finset.univ : Finset I).image comp
    let good := (Finset.univ : Finset ((I → W) × (I → F))).filter (fun p =>
      ∀ x : W, ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (p.1 i) x+p.2 i ≠ dotProduct (a i) x*dotProduct (b i) x)).card ≤ e)
    good.card = if ∀ C ∈ comps, 4 ∣ C.card then 2^(2*e+comps.card) else 0 := by
  intro n e F W I a b hab freq rows hrows adj comp comps good
  have hrows' : ∀ k, ∀ v ∈ PEqualNP.Outside.L_lib_935_aux.fr (a k) (b k),
      (PEqualNP.Outside.L_lib_935_aux.rowsF (ι := Fin (4*e)) a b v).card = 2 := hrows
  have hcomp : ∀ i j, j ∈ comp i ↔
      Relation.EqvGen (PEqualNP.Outside.L_lib_935_aux.adjF (ι := Fin (4*e)) a b) i j := by
    intro i j
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact Iff.rfl
  have hgood : ∀ p, p ∈ good ↔ ∀ x : Fin n → ZMod 2,
      ((Finset.univ : Finset (Fin (4*e))).filter (fun i =>
        dotProduct (p.1 i) x + p.2 i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ e := by
    intro p
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hcard : Fintype.card (Fin (4*e)) = 4 * e := Fintype.card_fin _
  show good.card = (if ∀ C ∈ (Finset.univ : Finset (Fin (4*e))).image comp, 4 ∣ C.card then
    2^(2*e+((Finset.univ : Finset (Fin (4*e))).image comp).card) else 0)
  rw [PEqualNP.Outside.L_lib_935_aux.good_card (ι := Fin (4*e)) hcard a b hab good hgood]
  have := PEqualNP.Outside.L_lib_935_aux.sol_card (ι := Fin (4*e)) a b comp hcomp e hcard hab
    hrows'
  exact_mod_cast this

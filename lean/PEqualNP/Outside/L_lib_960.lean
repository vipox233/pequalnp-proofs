import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_960

open Finset

theorem decomp {F : Type} [Field F] {n m : ℕ} (A : Matrix (Fin n) (Fin m) F) :
    ∃ r, A.rank = r ∧ ∃ (U : Matrix (Fin n) (Fin r) F) (V : Matrix (Fin r) (Fin m) F),
      A = U * V := by
  let W := LinearMap.range A.mulVecLin
  let bs := Module.finBasisOfFinrankEq F W (rfl : Module.finrank F W = A.rank)
  let w : Fin m → W := fun j => ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨_, rfl, Matrix.of fun i k => (bs k : Fin n → F) i, Matrix.of fun k j => bs.repr (w j) k, ?_⟩
  ext i j
  have h := congrArg (fun x : W => (x : Fin n → F) i) (bs.sum_repr (w j))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  have hw : (w j : Fin n → F) i = A i j := by simp [w, Matrix.mulVec_single]
  rw [← hw, ← h, Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_comm]
  rfl

theorem pad {K : Type} [Field K] {ι : Type} [Fintype ι] {α β : Type} (d : ℕ)
    (hd : Fintype.card ι ≤ d) (a : α → ι → K) (b : β → ι → K) :
    ∃ (A : α → Fin d → K) (B : β → Fin d → K),
      ∀ p q, ∑ σ, a p σ * b q σ = ∑ j : Fin d, A p j * B q j := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin d) (by simpa using hd)
  refine ⟨fun p => Function.extend e (a p) 0, fun q => Function.extend e (b q) 0, fun p q => ?_⟩
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    have hj' : ¬∃ x, e x = j := by simpa [Set.mem_range] using hj
    dsimp only
    rw [Function.extend_apply' _ _ _ hj']
    simp
  · intro σ
    simp [e.injective.extend_apply]

/-- the parity identity over the integers -/
theorem parity_int (t : ℕ) :
    ((t % 2 : ℕ) : ℤ) = ∑ k ∈ range t, (t.choose (k+1) : ℤ) * (-2) ^ k := by
  have h1 := add_pow (-2 : ℤ) 1 t
  rw [sum_range_succ'] at h1
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one] at h1
  have h2 : (-2 : ℤ) * ∑ k ∈ range t, (t.choose (k+1) : ℤ) * (-2) ^ k
      = ∑ k ∈ range t, (-2) ^ (k+1) * (t.choose (k+1) : ℤ) := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => by ring
  have h3 : (-2 : ℤ) * ((t % 2 : ℕ) : ℤ) = (-2 + 1) ^ t - 1 := by
    rcases Nat.even_or_odd t with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have : (k + k) % 2 = 0 := by omega
      rw [this, show k + k = 2 * k by ring, pow_mul]; norm_num
    · have : (2 * k + 1) % 2 = 1 := by omega
      rw [this, pow_succ, pow_mul]; norm_num
  have h4 : (-2 : ℤ) * ((t % 2 : ℕ) : ℤ) = (-2) * ∑ k ∈ range t, (t.choose (k+1) : ℤ) * (-2) ^ k := by
    rw [h3, h2, h1]; ring
  exact mul_left_cancel₀ (by norm_num) h4

/-- the diagonal weight of a subset of size k -/
def dd (k : ℕ) : ℤ := if k = 0 then 0 else (-2) ^ (k - 1)

theorem parity_sub {α : Type} [DecidableEq α] (U : Finset α) :
    ((U.card % 2 : ℕ) : ℤ) = ∑ S ∈ U.powerset, dd S.card := by
  rw [sum_powerset_apply_card, sum_range_succ', parity_int]
  simp [dd]

theorem inj_tri {α R : Type} [Fintype α] [DecidableEq α] [AddCommGroup R]
    (rel : α → α → Prop) [DecidableRel rel] (wf : WellFounded (fun a b => rel a b ∧ a ≠ b))
    (hrefl : ∀ a, rel a a) (x y : α → R)
    (h : ∀ I, ∑ S, (if rel S I then x S else 0) = ∑ S, (if rel S I then y S else 0)) : x = y := by
  funext I
  induction I using wf.induction with
  | _ I ih =>
    have hI := h I
    rw [← add_sum_erase _ _ (mem_univ I), ← add_sum_erase _ _ (mem_univ I)] at hI
    have he : ∑ S ∈ univ.erase I, (if rel S I then x S else 0)
        = ∑ S ∈ univ.erase I, (if rel S I then y S else 0) := by
      refine sum_congr rfl fun S hS => ?_
      by_cases hr : rel S I
      · rw [if_pos hr, if_pos hr, ih S ⟨hr, ne_of_mem_erase hS⟩]
      · rw [if_neg hr, if_neg hr]
    rw [he, if_pos (hrefl I), if_pos (hrefl I)] at hI
    exact add_right_cancel hI

theorem mulcard (h e : ℕ) :
    (univ.image (fun a : ZMod (2^h) => (2 : ZMod (2^h)) ^ e * a)).card = 2 ^ (h - e) := by
  rcases le_or_gt h e with hle | hlt
  · have h0 : (2 : ZMod (2^h)) ^ e = 0 := by
      have : ((2^e : ℕ) : ZMod (2^h)) = 0 := by
        obtain ⟨c, hc⟩ := pow_dvd_pow 2 hle
        rw [hc, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      exact_mod_cast this
    simp only [h0, zero_mul, Nat.sub_eq_zero_of_le hle, pow_zero]
    rw [image_const univ_nonempty, card_singleton]
  · obtain ⟨f, rfl⟩ : ∃ f, h = e + f := ⟨h - e, by omega⟩
    have key : ∀ v : ℕ, 2^e * (v % 2^f) % 2^(e+f) = 2^e * v % 2^(e+f) := by
      intro v; rw [pow_add, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
    have hs : univ.image (fun a : ZMod (2^(e+f)) => (2 : ZMod (2^(e+f))) ^ e * a)
        = univ.image (fun t : Fin (2^f) => (((2^e * t.val : ℕ)) : ZMod (2^(e+f)))) := by
      ext z
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩
        refine ⟨⟨a.val % 2^f, Nat.mod_lt _ (by positivity)⟩, ?_⟩
        calc ((2^e * (a.val % 2^f) : ℕ) : ZMod (2^(e+f))) = ((2^e * a.val : ℕ) : ZMod (2^(e+f))) :=
              (ZMod.natCast_eq_natCast_iff' _ _ _).2 (key a.val)
          _ = 2^e * a := by push_cast; rw [ZMod.natCast_zmod_val]
      · rintro ⟨t, rfl⟩
        exact ⟨(t.val : ZMod _), by push_cast; ring⟩
    have hlt2 : ∀ t : Fin (2^f), 2^e * t.val < 2^(e+f) := by
      intro t; rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left t.isLt (by positivity)
    rw [hs, card_image_of_injective, card_univ, Fintype.card_fin, Nat.add_sub_cancel_left]
    intro t1 t2 ht
    have := congrArg ZMod.val ht
    simp only at this
    rw [ZMod.val_natCast_of_lt (hlt2 t1), ZMod.val_natCast_of_lt (hlt2 t2)] at this
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (by positivity) this)

theorem mulcard_neg (h e : ℕ) :
    (univ.image (fun a : ZMod (2^h) => (-2 : ZMod (2^h)) ^ e * a)).card = 2 ^ (h - e) := by
  rw [← mulcard h e]
  congr 1
  ext z
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(-1)^e * a, by show 2^e * ((-1)^e * a) = (-2)^e * a; rw [neg_pow (2 : ZMod (2^h))]; ring⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(-1)^e * a, ?_⟩
    rw [neg_pow (2 : ZMod (2^h)), show ((-1 : ZMod (2^h))^e * 2^e * ((-1)^e * a)) = ((-1)^e * (-1)^e) * (2^e * a) by ring,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

def PP (r h : ℕ) : Matrix (Finset (Fin r)) (Finset (Fin r)) (ZMod (2^h)) :=
  fun I J => (((I ∩ J).card % 2 : ℕ) : ZMod (2^h))

theorem part1 (r h : ℕ) :
    (univ.image (fun x : Finset (Fin r) → ZMod (2^h) => (PP r h).mulVec x)).card
      = 2 ^ ((Finset.range h).sum (fun k => (h-k) * Nat.choose r (k+1))) := by
  let P := PP r h
  let dR : Finset (Fin r) → ZMod (2^h) := fun S => ((dd S.card : ℤ) : ZMod (2^h))
  let Z : Matrix (Finset (Fin r)) (Finset (Fin r)) (ZMod (2^h)) := fun I S => if S ⊆ I then 1 else 0
  have hent : ∀ I J, P I J = ∑ S, Z I S * dR S * Z J S := by
    intro I J
    have e1 : ∑ S, Z I S * dR S * Z J S = ∑ S ∈ (I ∩ J).powerset, dR S := by
      have : (I ∩ J).powerset = univ.filter (fun S => S ⊆ I ∩ J) := by ext S; simp
      rw [this, sum_filter]
      refine sum_congr rfl fun S _ => ?_
      simp only [Z, subset_inter_iff]
      split_ifs <;> simp_all
    rw [e1]
    simp only [P, PP, dR]
    rw [← Int.cast_sum, ← parity_sub, Int.cast_natCast]
  have hP : ∀ x, P.mulVec x = Z.mulVec (fun S => dR S * (Z.transpose.mulVec x) S) := by
    intro x
    funext I
    show ∑ J, P I J * x J = ∑ S, Z I S * (dR S * ∑ J, Z J S * x J)
    simp_rw [hent, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun S _ => sum_congr rfl fun J _ => by ring
  have hZ : Function.Injective Z.mulVec := by
    intro x y hxy
    refine inj_tri (fun S I => S ⊆ I)
      ((wellFounded_lt (α := Finset (Fin r))).mono
        (fun a b hab => Finset.lt_iff_ssubset.2 (Finset.ssubset_iff_subset_ne.2 hab)))
      (fun a => subset_refl a) x y (fun I => ?_)
    have := congrFun hxy I
    simpa [Matrix.mulVec, dotProduct, Z] using this
  have hZt : Function.Surjective Z.transpose.mulVec := by
    apply Finite.injective_iff_surjective.1
    intro x y hxy
    refine inj_tri (fun J S => S ⊆ J)
      ((wellFounded_gt (α := Finset (Fin r))).mono
        (fun a b hab => Finset.lt_iff_ssubset.2 (Finset.ssubset_iff_subset_ne.2 ⟨hab.1, hab.2.symm⟩)))
      (fun a => subset_refl a) x y (fun I => ?_)
    have e : ∀ x : Finset (Fin r) → ZMod (2^h),
        Z.transpose.mulVec x I = ∑ S, (if I ⊆ S then x S else 0) := fun x => by
      show ∑ S, Z S I * x S = _
      simp [Z]
    rw [← e, ← e]
    exact congrFun hxy I
  have himg : univ.image P.mulVec
      = (univ.image (fun y : Finset (Fin r) → ZMod (2^h) => fun S => dR S * y S)).image Z.mulVec := by
    rw [image_image]
    ext z
    simp only [mem_image, mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Z.transpose.mulVec x, (hP x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hZt y
      exact ⟨x, hP x⟩
  show (univ.image P.mulVec).card = _
  rw [himg, card_image_of_injective _ hZ]
  have hpi : univ.image (fun y : Finset (Fin r) → ZMod (2^h) => fun S => dR S * y S)
      = Fintype.piFinset (fun S => univ.image (fun a : ZMod (2^h) => dR S * a)) := by
    ext z
    simp only [mem_image, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨y, rfl⟩ S
      exact ⟨y S, rfl⟩
    · intro hz
      exact ⟨fun S => (hz S).choose, funext fun S => (hz S).choose_spec⟩
  rw [hpi, Fintype.card_piFinset]
  have hcard : ∀ S : Finset (Fin r), (univ.image (fun a : ZMod (2^h) => dR S * a)).card
      = 2 ^ (if S.card = 0 then 0 else h - (S.card - 1)) := by
    intro S
    by_cases hS : S.card = 0
    · obtain rfl : S = ∅ := card_eq_zero.1 hS
      simp only [dR, dd, card_empty, if_true, Int.cast_zero, zero_mul]
      rw [image_const univ_nonempty, card_singleton, pow_zero]
    · have hS' : S ≠ ∅ := fun h0 => hS (by simp [h0])
      rw [if_neg hS, ← mulcard_neg h (S.card - 1)]
      simp [dR, dd, hS']
  rw [prod_congr rfl (fun S _ => hcard S), prod_pow_eq_pow_sum]
  congr 1
  rw [← powerset_univ, sum_powerset_apply_card (f := fun k => if k = 0 then 0 else h - (k-1)), card_univ, Fintype.card_fin, sum_range_succ']
  simp only [smul_eq_mul, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true,
    Nat.add_sub_cancel, mul_zero, add_zero]
  calc ∑ k ∈ range r, r.choose (k+1) * (h - k)
      = ∑ k ∈ range (max r h), r.choose (k+1) * (h - k) := by
        refine sum_subset (range_mono (le_max_left r h)) (fun k _ hk => ?_)
        simp only [mem_range, not_lt] at hk
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    _ = ∑ k ∈ range (max r h), (h - k) * r.choose (k+1) := sum_congr rfl fun _ _ => mul_comm _ _
    _ = ∑ k ∈ range h, (h - k) * r.choose (k+1) := by
        refine (sum_subset (range_mono (le_max_right r h)) (fun k _ hk => ?_)).symm
        simp only [mem_range, not_lt] at hk
        rw [Nat.sub_eq_zero_of_le hk]; simp

theorem part2 (r h n m : ℕ) (H : Fin n → Fin m → Bool) (B : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin n) (Fin m) (ZMod (2^h)))
    (hB : ∀ i j, B i j = ((H i j).toNat : ZMod 2)) (hA : ∀ i j, A i j = ((H i j).toNat : ZMod (2^h)))
    (hr : Matrix.rank B ≤ r) :
    (univ.image (fun x : Fin m → ZMod (2^h) => A.mulVec x)).card
      ≤ (univ.image (fun x : Finset (Fin r) → ZMod (2^h) => (PP r h).mulVec x)).card := by
  obtain ⟨d, hd, U, V, hUV⟩ := decomp B
  have hdr : d ≤ r := hd ▸ hr
  obtain ⟨u, v, huv⟩ := pad (K := ZMod 2) (ι := Fin d) r (by simpa using hdr)
    (fun i k => U i k) (fun j k => V k j)
  let I : Fin n → Finset (Fin r) := fun i => univ.filter (fun k => u i k = 1)
  let J : Fin m → Finset (Fin r) := fun j => univ.filter (fun k => v j k = 1)
  have hent : ∀ i j, ((H i j).toNat : ZMod (2^h)) = PP r h (I i) (J j) := by
    intro i j
    have h1 : ((H i j).toNat : ZMod 2) = (((I i ∩ J j).card : ℕ) : ZMod 2) := by
      have hb : B i j = ∑ k, u i k * v j k := by rw [hUV, Matrix.mul_apply, huv]
      rw [← hB i j, hb]
      have hab : ∀ a b : ZMod 2, a * b = if a = 1 ∧ b = 1 then 1 else 0 := by decide
      simp_rw [hab]
      rw [sum_boole, filter_and]
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
    have h3 : (H i j).toNat % 2 = (H i j).toNat := by cases H i j <;> rfl
    simp only [PP]
    rw [← h2, h3]
  have hsub : univ.image (fun x : Fin m → ZMod (2^h) => A.mulVec x)
      ⊆ (univ.image (fun x : Finset (Fin r) → ZMod (2^h) => (PP r h).mulVec x)).image
        (fun z i => z (I i)) := by
    intro w hw
    simp only [mem_image, mem_univ, true_and] at hw ⊢
    obtain ⟨x, rfl⟩ := hw
    refine ⟨(PP r h).mulVec (fun S => ∑ j, if J j = S then x j else 0), ⟨_, rfl⟩, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    simp [sum_ite_eq, hA, hent]
  exact (card_le_card hsub).trans card_image_le

end PEqualNP.Outside.L_lib_960

open PEqualNP.Outside.L_lib_960 in
theorem PEqualNP.Outside.L_lib_960 : ∀ (r h : ℕ),
  let F := (Finset.range h).sum (fun k => (h-k) * Nat.choose r (k+1))
  let P : Matrix (Finset (Fin r)) (Finset (Fin r)) (ZMod (2^h)) :=
    fun I J => (((I ∩ J).card % 2 : ℕ) : ZMod (2^h))
  (Finset.univ.image (fun x : Finset (Fin r) → ZMod (2^h) => P.mulVec x)).card = 2^F ∧
  ∀ (n m : ℕ) (H : Fin n → Fin m → Bool),
    let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => ((H i j).toNat : ZMod 2)
    let A : Matrix (Fin n) (Fin m) (ZMod (2^h)) := fun i j => ((H i j).toNat : ZMod (2^h))
    Matrix.rank B ≤ r →
      (Finset.univ.image (fun x : Fin m → ZMod (2^h) => A.mulVec x)).card ≤ 2^F := by
  intro r h F P
  refine ⟨part1 r h, ?_⟩
  intro n m H B A hr
  exact (part2 r h n m H B A (fun _ _ => rfl) (fun _ _ => rfl) hr).trans (part1 r h).le

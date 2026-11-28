import Mathlib

namespace PEqualNP.Outside.L_meta_33656_aux

-- The lane reduction, quadratic decomposition, and transcript-coset argument
-- come from lean/PEqualNP/Outside/L_meta_33654.lean at
-- 89d2fd4116d94c448b241700eb4b4b27f657d92a. The rank and count cutoffs change here.

abbrev F := ZMod 2

lemma z2_add_self (x : F) : x + x = 0 := by
  revert x; decide

lemma z2_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma z2_eq_iff_zero (x y : F) : (x = 0 ↔ y = 0) ↔ x = y := by
  revert x y; decide

lemma z2_out_expand (a0 a1 a2 b0 b1 b2 : F) :
    (a0 + b0) + (1 + (a1 + b1)) * (a2 + b2) =
      a1 * a2 + (a0 + a2 + a1 * b2 + b1 * a2) + (b0 + b2 + b1 * b2) := by
  revert a0 a1 a2 b0 b1 b2; decide

lemma z2_two : (2 : F) = 0 := by decide

lemma z3_cases (r y : ZMod 3) : y = r ∨ y = r + 1 ∨ y = r - 1 := by
  revert r y; decide

lemma z3_elems (r : ZMod 3) : r = 0 ∨ r = 1 ∨ r = 2 := by
  revert r; decide

lemma z3_ne_add_one (r : ZMod 3) : r ≠ r + 1 := by
  revert r; decide

lemma z3_ne_sub_one (r : ZMod 3) : r ≠ r - 1 := by
  revert r; decide

lemma z3_add_one_ne_sub_one (r : ZMod 3) : r + 1 ≠ r - 1 := by
  revert r; decide

lemma z3_third_ne (r0 r1 : ZMod 3) (h : r0 ≠ r1) :
    r0 ≠ -(r0 + r1) ∧ r1 ≠ -(r0 + r1) := by
  revert r0 r1 h; decide

lemma z3_zero_ne_two : (0 : ZMod 3) ≠ 2 := by decide
lemma z3_one_ne_two : (1 : ZMod 3) ≠ 2 := by decide
lemma z3_three_zero : (3 : ZMod 3) = 0 := by decide

lemma two_mul_add_bit_eq (a b : ℕ) (p q : Prop) [Decidable p] [Decidable q] :
    (2 * a + (if p then 0 else 1) = 2 * b + (if q then 0 else 1)) ↔ (a = b ∧ (p ↔ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> omega

lemma vec_add_self {ι : Type*} (x : ι → F) : x + x = 0 := by
  funext i; exact z2_add_self (x i)

lemma card_filter_add_not {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card + (Finset.univ.filter (fun x => ¬ p x)).card = Fintype.card α := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h hn => hn h))]
  have h : Finset.univ.filter p ∪ Finset.univ.filter (fun x => ¬ p x) = Finset.univ := by
    ext x; simp [em]
  rw [h, Finset.card_univ]

lemma card_eq_two_pow_finrank {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    Nat.card V = 2 ^ Module.finrank F V := by
  have e := (Module.finBasis F V).equivFun.toEquiv
  rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma card_preimage_linear {X Y : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] (f : X →ₗ[F] Y) (p : Y → Prop) :
    Nat.card {x : X // p (f x)} =
      Nat.card (LinearMap.ker f) * Nat.card {y : f.range // p y.1} := by
  classical
  let sec : f.range → X := fun y => Classical.choose y.2
  have hsec : ∀ y : f.range, f (sec y) = y.1 := fun y => Classical.choose_spec y.2
  have e : {x : X // p (f x)} ≃ LinearMap.ker f × {y : f.range // p y.1} :=
    { toFun := fun x =>
        (⟨x.1 - sec ⟨f x.1, LinearMap.mem_range_self f x.1⟩, by
          rw [LinearMap.mem_ker, map_sub, hsec, sub_self]⟩,
         ⟨⟨f x.1, LinearMap.mem_range_self f x.1⟩, x.2⟩)
      invFun := fun q =>
        ⟨q.1.1 + sec q.2.1, by
          have hf : f (q.1.1 + sec q.2.1) = q.2.1.1 := by
            rw [map_add, LinearMap.mem_ker.mp q.1.2, zero_add, hsec]
          rw [hf]; exact q.2.2⟩
      left_inv := fun x => by
        apply Subtype.ext; dsimp only; exact sub_add_cancel _ _
      right_inv := fun q => by
        rcases q with ⟨⟨k, hk⟩, ⟨⟨y, hy⟩, hpy⟩⟩
        have hf : f (k + sec ⟨y, hy⟩) = y := by
          rw [map_add, LinearMap.mem_ker.mp hk, zero_add, hsec]
        apply Prod.ext
        · apply Subtype.ext; dsimp only
          have hpair : (⟨f (k + sec ⟨y, hy⟩), LinearMap.mem_range_self f _⟩ : f.range) = ⟨y, hy⟩ :=
            Subtype.ext hf
          rw [hpair, add_sub_cancel_right]
        · apply Subtype.ext; apply Subtype.ext; exact hf }
  rw [Nat.card_congr e, Nat.card_prod]

abbrev Lane (m : ℕ) := ZMod m → F

def tri {m : ℕ} : Lane m →ₗ[F] Lane m where
  toFun x a := x a + x (a + 1) + x (a - 1)
  map_add' x y := by funext a; simp only [Pi.add_apply]; abel
  map_smul' c x := by funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def res3 (t : ℕ) : ZMod (3 * t) →+* ZMod 3 :=
  ZMod.castHom (dvd_mul_right 3 t) (ZMod 3)

lemma res3_one_id (x : ZMod 3) : res3 1 x = x := by
  revert x; decide

lemma z6_elems (a : ZMod 6) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
  revert a; decide

lemma z6_filter_0 : Finset.univ.filter (fun x : ZMod 6 => res3 2 x = 0) = {0, 3} := by decide
lemma z6_filter_1 : Finset.univ.filter (fun x : ZMod 6 => res3 2 x = 1) = {1, 4} := by decide
lemma z6_filter_2 : Finset.univ.filter (fun x : ZMod 6 => res3 2 x = 2) = {2, 5} := by decide
lemma z6_0_ne_3 : (0 : ZMod 6) ≠ 3 := by decide
lemma z6_1_ne_4 : (1 : ZMod 6) ≠ 4 := by decide
lemma z6_2_ne_5 : (2 : ZMod 6) ≠ 5 := by decide

def parSum (t : ℕ) [NeZero (3 * t)] (r : ZMod 3) : Lane (3 * t) →ₗ[F] F where
  toFun u := ∑ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r), u a
  map_add' u v := Finset.sum_add_distrib
  map_smul' c u := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

lemma parSum_apply (t : ℕ) [NeZero (3 * t)] (r : ZMod 3) (u : Lane (3 * t)) :
    parSum t r u = ∑ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r), u a := rfl

def imSub (t : ℕ) [NeZero (3 * t)] : Submodule F (Lane (3 * t)) :=
  LinearMap.ker (parSum t 0 + parSum t 2) ⊓ LinearMap.ker (parSum t 1 + parSum t 2)

lemma mem_imSub_iff (t : ℕ) [NeZero (3 * t)] (u : Lane (3 * t)) :
    u ∈ imSub t ↔ parSum t 0 u = parSum t 2 u ∧ parSum t 1 u = parSum t 2 u := by
  simp only [imSub, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · calc parSum t 0 u = parSum t 0 u + (parSum t 2 u + parSum t 2 u) := by
              rw [z2_add_self, add_zero]
        _ = (parSum t 0 u + parSum t 2 u) + parSum t 2 u := by rw [add_assoc]
        _ = parSum t 2 u := by rw [h0, zero_add]
    · calc parSum t 1 u = parSum t 1 u + (parSum t 2 u + parSum t 2 u) := by
              rw [z2_add_self, add_zero]
        _ = (parSum t 1 u + parSum t 2 u) + parSum t 2 u := by rw [add_assoc]
        _ = parSum t 2 u := by rw [h1, zero_add]
  · rintro ⟨h0, h1⟩
    exact ⟨by rw [h0, z2_add_self], by rw [h1, z2_add_self]⟩

lemma parSum_eq_of_mem_imSub (t : ℕ) [NeZero (3 * t)] {u : Lane (3 * t)}
    (hu : u ∈ imSub t) (r1 r2 : ZMod 3) : parSum t r1 u = parSum t r2 u := by
  rcases (mem_imSub_iff t u).mp hu with ⟨h0, h1⟩
  have hr : ∀ r : ZMod 3, parSum t r u = parSum t 2 u := by
    intro r
    rcases z3_elems r with rfl | rfl | rfl
    · exact h0
    · exact h1
    · rfl
  rw [hr r1, hr r2]

lemma parSum_shift_add (t : ℕ) [NeZero (3 * t)] (r : ZMod 3) (x : Lane (3 * t))
    (s : ZMod (3 * t)) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r), x (a + s) =
      parSum t (r + res3 t s) x := by
  rw [parSum_apply]
  refine Finset.sum_nbij (fun a => a + s) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    have hfa := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [map_add, hfa]⟩
  · intro a1 _ a2 _ h; exact add_right_cancel h
  · intro b hb
    have hfb := (Finset.mem_filter.mp hb).2
    refine ⟨b - s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, sub_add_cancel b s⟩
    rw [map_sub, hfb, add_sub_cancel_right]

lemma parSum_tri (t : ℕ) [NeZero (3 * t)] (r : ZMod 3) (x : Lane (3 * t)) :
    parSum t r (tri x) = ∑ a : ZMod (3 * t), x a := by
  have h1 : parSum t r (tri x) =
      parSum t r x + parSum t (r + 1) x + parSum t (r - 1) x := by
    rw [parSum_apply]
    change ∑ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r),
        (x a + x (a + 1) + x (a - 1)) = _
    simp only [Finset.sum_add_distrib]
    have hs1 : ∑ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r), x (a + 1) =
        parSum t (r + 1) x := by
      simpa only [map_one] using parSum_shift_add t r x 1
    have hs2 : ∑ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r), x (a - 1) =
        parSum t (r - 1) x := by
      have := parSum_shift_add t r x (-1)
      simp only [map_neg, map_one, ← sub_eq_add_neg] at this
      exact this
    rw [hs1, hs2, ← parSum_apply]
  rw [h1]
  have hpart : (Finset.univ : Finset (ZMod (3 * t))) =
      Finset.univ.filter (fun a => res3 t a = r) ∪
        (Finset.univ.filter (fun a => res3 t a = r + 1) ∪
         Finset.univ.filter (fun a => res3 t a = r - 1)) := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact z3_cases r (res3 t a)
  have hd12 : Disjoint (Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r + 1))
      (Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r - 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact z3_add_one_ne_sub_one r ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  have hd0 : Disjoint (Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r))
      (Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r + 1) ∪
       Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r - 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h0a := (Finset.mem_filter.mp ha).2
    rcases Finset.mem_union.mp hb with h1b | h2b
    · exact z3_ne_add_one r (h0a.symm.trans (Finset.mem_filter.mp h1b).2)
    · exact z3_ne_sub_one r (h0a.symm.trans (Finset.mem_filter.mp h2b).2)
  conv_rhs => rw [hpart, Finset.sum_union hd0, Finset.sum_union hd12]
  rw [parSum_apply, parSum_apply, parSum_apply, add_assoc]

lemma range_tri_le_imSub (t : ℕ) [NeZero (3 * t)] :
    LinearMap.range (tri : Lane (3 * t) →ₗ[F] Lane (3 * t)) ≤ imSub t := by
  rintro _ ⟨x, rfl⟩
  rw [mem_imSub_iff]
  exact ⟨by rw [parSum_tri, parSum_tri], by rw [parSum_tri, parSum_tri]⟩

lemma finrank_ker_tri_le (t : ℕ) [NeZero (3 * t)] :
    Module.finrank F (LinearMap.ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t))) ≤ 2 := by
  let ev : LinearMap.ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t)) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun x i => if i.val = 0 then x.1 0 else x.1 1
      map_add' := fun x y => by funext i; dsimp only [Pi.add_apply]; split_ifs <;> rfl
      map_smul' := fun c x => by funext i; dsimp only [Pi.smul_apply]; split_ifs <;> rfl }
  have hinj : Function.Injective ev := by
    intro x y hxy
    have h0 : x.1 0 = y.1 0 := congrFun hxy 0
    have h1 : x.1 1 = y.1 1 := congrFun hxy 1
    have hdiff : ∀ k : ℕ, x.1 (k : ZMod (3 * t)) = y.1 (k : ZMod (3 * t)) := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        match k with
        | 0 => simpa using h0
        | 1 => simpa using h1
        | k + 2 =>
          have hxk := congrFun (LinearMap.mem_ker.mp x.2) ((k + 1 : ℕ) : ZMod (3 * t))
          have hyk := congrFun (LinearMap.mem_ker.mp y.2) ((k + 1 : ℕ) : ZMod (3 * t))
          dsimp only [tri, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hxk hyk
          have h1eq : x.1 ((k + 1 : ℕ) : ZMod (3 * t)) = y.1 ((k + 1 : ℕ) : ZMod (3 * t)) :=
            ih (k + 1) (by omega)
          have h0eq : x.1 ((k : ℕ) : ZMod (3 * t)) = y.1 ((k : ℕ) : ZMod (3 * t)) :=
            ih k (by omega)
          have hsub : ((k + 1 : ℕ) : ZMod (3 * t)) - 1 = (k : ZMod (3 * t)) := by
            push_cast; rw [add_sub_cancel_right]
          have hadd : ((k + 1 : ℕ) : ZMod (3 * t)) + 1 = ((k + 2 : ℕ) : ZMod (3 * t)) := by
            push_cast; rw [add_assoc]; norm_num
          rw [hsub, hadd] at hxk hyk
          rw [h1eq, h0eq] at hxk
          have hsum : y.1 ((k + 1 : ℕ) : ZMod (3 * t)) + x.1 ((k + 2 : ℕ) : ZMod (3 * t)) +
              y.1 (k : ZMod (3 * t)) =
              y.1 ((k + 1 : ℕ) : ZMod (3 * t)) + y.1 ((k + 2 : ℕ) : ZMod (3 * t)) +
              y.1 (k : ZMod (3 * t)) := hxk.trans hyk.symm
          exact add_left_cancel (add_right_cancel hsum)
    apply Subtype.ext
    funext a
    rw [← ZMod.natCast_zmod_val a]
    exact hdiff a.val
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at hle

lemma finrank_imSub_add_two (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    Module.finrank F (imSub t) + 2 = 3 * t := by
  classical
  let chk : Lane (3 * t) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun u i => if i.val = 0 then parSum t 0 u + parSum t 2 u
                          else parSum t 1 u + parSum t 2 u
      map_add' := fun u v => by
        funext i; dsimp only [Pi.add_apply]; split_ifs <;> simp only [map_add] <;> abel
      map_smul' := fun c u => by
        funext i; dsimp only [Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp only [map_smul, smul_eq_mul, mul_add] }
  have hker : LinearMap.ker chk = imSub t := by
    ext u
    simp only [LinearMap.mem_ker, imSub, Submodule.mem_inf, LinearMap.add_apply]
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i; fin_cases i
      · exact h0
      · exact h1
  have hsurj : Function.Surjective chk := by
    intro y
    have h01 : (0 : ZMod (3 * t)) ≠ 1 := by
      intro h
      have hv := congrArg ZMod.val h
      have hv1 : (1 : ZMod (3 * t)).val = 1 := by
        have := ZMod.val_natCast (3 * t) 1
        rw [Nat.cast_one, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      rw [ZMod.val_zero, hv1] at hv
      omega
    let u : Lane (3 * t) := fun a => if a = 0 then y 0 else if a = 1 then y 1 else 0
    refine ⟨u, ?_⟩
    have hps : ∀ r : ZMod 3, parSum t r u =
        (if (0 : ZMod 3) = r then y 0 else 0) + (if (1 : ZMod 3) = r then y 1 else 0) := by
      intro r
      rw [parSum_apply]
      have hsub : ∀ a ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r),
          u a = (if a = 0 then y 0 else 0) + (if a = 1 then y 1 else 0) := by
        intro a _
        dsimp only [u]
        by_cases ha0 : a = 0
        · simp only [ha0, ↓reduceIte, h01, add_zero]
        · simp only [ha0, ↓reduceIte, zero_add]
      rw [Finset.sum_congr rfl hsub, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_ite_eq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_zero]
      · rw [Finset.sum_ite_eq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_one]
    have hp0 : parSum t 0 u = y 0 := by rw [hps 0]; simp
    have hp1 : parSum t 1 u = y 1 := by rw [hps 1]; simp
    have hp2 : parSum t 2 u = 0 := by
      rw [hps 2]
      simp only [z3_zero_ne_two, z3_one_ne_two, ↓reduceIte, add_zero]
    funext i; fin_cases i
    · dsimp only [chk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [↓reduceIte, hp0, hp2, add_zero]; rfl
    · dsimp only [chk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, hp1, hp2, add_zero]; rfl
  have hrk := LinearMap.finrank_range_add_finrank_ker chk
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Module.finrank_fin_fun] at hrk
  have hdimL : Module.finrank F (Lane (3 * t)) = 3 * t := by
    rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
  rw [hdimL] at hrk
  omega

lemma range_tri_eq_imSub (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    LinearMap.range (tri : Lane (3 * t) →ₗ[F] Lane (3 * t)) = imSub t := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t))
  have hdimL : Module.finrank F (Lane (3 * t)) = 3 * t := by
    rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
  rw [hdimL] at hrk
  have hker := finrank_ker_tri_le t
  have him := finrank_imSub_add_two t ht
  exact Submodule.eq_of_le_of_finrank_le (range_tri_le_imSub t) (by omega)

lemma finrank_ker_tri (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    Module.finrank F (LinearMap.ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t))) = 2 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t))
  have hdimL : Module.finrank F (Lane (3 * t)) = 3 * t := by
    rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
  rw [hdimL, range_tri_eq_imSub t ht] at hrk
  have him := finrank_imSub_add_two t ht
  omega

lemma card_res3_fiber (t : ℕ) (_ht : 0 < t) [NeZero (3 * t)] (r : ZMod 3) :
    (Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r)).card = t := by
  have heq : (Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r)).card =
      (Finset.univ : Finset (Fin t)).card := by
    symm
    refine Finset.card_nbij (fun k : Fin t => ((3 * k.val + r.val : ℕ) : ZMod (3 * t))) ?_ ?_ ?_
    · intro k _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [map_natCast]
      push_cast
      rw [z3_three_zero, zero_mul, zero_add, ZMod.natCast_zmod_val]
    · intro k1 _ k2 _ h
      have hlt1 : 3 * k1.val + r.val < 3 * t := by have := r.val_lt; omega
      have hlt2 : 3 * k2.val + r.val < 3 * t := by have := r.val_lt; omega
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
      exact Fin.ext (by omega)
    · intro a ha
      have hfa := (Finset.mem_filter.mp ha).2
      have hmod : a.val % 3 = r.val := by
        have hcast : ((a.val : ℕ) : ZMod 3) = r := by
          rw [← map_natCast (res3 t), ZMod.natCast_zmod_val, hfa]
        have := congrArg ZMod.val hcast
        rwa [ZMod.val_natCast] at this
      have hdiv : a.val / 3 < t := by have := a.val_lt; omega
      refine ⟨⟨a.val / 3, hdiv⟩, Finset.mem_univ _, ?_⟩
      dsimp only
      have hrec : 3 * (a.val / 3) + r.val = a.val := by omega
      rw [hrec, ZMod.natCast_zmod_val]
  rw [heq, Finset.card_univ, Fintype.card_fin]

lemma finrank_supp_le_card_sub_one (t : ℕ) [NeZero (3 * t)]
    (U' : Submodule F (Lane (3 * t))) (hU'im : U' ≤ imSub t) (S : Finset (ZMod (3 * t)))
    (hsupp : ∀ u ∈ U', ∀ a, a ∉ S → u a = 0) (hSne : S.Nonempty) :
    Module.finrank F U' + 1 ≤ S.card := by
  classical
  rcases hSne with ⟨a0, ha0⟩
  let r0 := res3 t a0
  let phi : ({a : ZMod (3 * t) // a ∈ S} → F) →ₗ[F] F :=
    { toFun := fun f =>
        ∑ a : {a : ZMod (3 * t) // a ∈ S},
          if res3 t a.1 = r0 ∨ res3 t a.1 = r0 + 1 then f a else 0
      map_add' := fun f g => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        split_ifs <;> simp
      map_smul' := fun c f => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        split_ifs <;> simp }
  let emb : U' →ₗ[F] LinearMap.ker phi :=
    { toFun := fun u => ⟨fun a => u.1 a.1, by
        rw [LinearMap.mem_ker]
        dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk]
        have hsum_r : ∀ r : ZMod 3,
            ∑ a : {a : ZMod (3 * t) // a ∈ S}, (if res3 t a.1 = r then u.1 a.1 else 0) =
              parSum t r u.1 := by
          intro r
          rw [parSum_apply]
          rw [Finset.sum_coe_sort_eq_attach, ← Finset.sum_filter]
          have hsub : (∑ x ∈ S.attach.filter (fun a : {a // a ∈ S} => res3 t a.1 = r), u.1 x.1) =
              ∑ a ∈ S.filter (fun a : ZMod (3 * t) => res3 t a = r), u.1 a := by
            refine Finset.sum_nbij (fun x => x.1) ?_ ?_ ?_ (fun _ _ => rfl)
            · intro x hx
              exact Finset.mem_filter.mpr ⟨x.2, (Finset.mem_filter.mp hx).2⟩
            · intro x1 _ x2 _ h; exact Subtype.ext h
            · intro a ha
              rcases Finset.mem_filter.mp ha with ⟨haS, har⟩
              exact ⟨⟨a, haS⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, har⟩, rfl⟩
          rw [hsub]
          refine Finset.sum_subset (fun a ha => ?_) (fun a ha hnot => ?_)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
          · exact hsupp u.1 u.2 a (fun hS => hnot (Finset.mem_filter.mpr ⟨hS, (Finset.mem_filter.mp ha).2⟩))
        have hdisj : ∀ a : {a : ZMod (3 * t) // a ∈ S},
            (if res3 t a.1 = r0 ∨ res3 t a.1 = r0 + 1 then u.1 a.1 else 0) =
              (if res3 t a.1 = r0 then u.1 a.1 else 0) +
              (if res3 t a.1 = r0 + 1 then u.1 a.1 else 0) := by
          intro a
          by_cases h1 : res3 t a.1 = r0 <;> by_cases h2 : res3 t a.1 = r0 + 1
          · exact absurd (h1.symm.trans h2) (z3_ne_add_one r0)
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
        simp_rw [hdisj]
        rw [Finset.sum_add_distrib, hsum_r r0, hsum_r (r0 + 1)]
        rw [parSum_eq_of_mem_imSub t (hU'im u.2) r0 (r0 + 1), z2_add_self]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective emb := by
    intro u v huv
    apply Subtype.ext; funext a
    by_cases ha : a ∈ S
    · exact congrFun (congrArg Subtype.val huv) ⟨a, ha⟩
    · rw [hsupp u.1 u.2 a ha, hsupp v.1 v.2 a ha]
  have hsurj : Function.Surjective phi := by
    intro c
    refine ⟨fun a => if a.1 = a0 then c else 0, ?_⟩
    dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : ∀ a : {a : ZMod (3 * t) // a ∈ S},
        (if res3 t a.1 = r0 ∨ res3 t a.1 = r0 + 1 then (if a.1 = a0 then c else 0) else 0) =
          if a = ⟨a0, ha0⟩ then c else 0 := by
      intro a
      by_cases h : a = ⟨a0, ha0⟩
      · subst h; simp only [r0, true_or, ↓reduceIte]
      · have hne : a.1 ≠ a0 := fun heq => h (Subtype.ext heq)
        simp only [hne, h, ↓reduceIte, ite_self]
    simp_rw [h1]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hrk := LinearMap.finrank_range_add_finrank_ker phi
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hrk
  have hdim : Module.finrank F ({a : ZMod (3 * t) // a ∈ S} → F) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [hdim] at hrk
  omega

lemma finrank_supp_le_card_sub_two (t : ℕ) [NeZero (3 * t)]
    (U' : Submodule F (Lane (3 * t))) (hU'im : U' ≤ imSub t) (S : Finset (ZMod (3 * t)))
    (hsupp : ∀ u ∈ U', ∀ a, a ∉ S → u a = 0)
    (a0 a1 : ZMod (3 * t)) (ha0 : a0 ∈ S) (ha1 : a1 ∈ S) (hne : res3 t a0 ≠ res3 t a1) :
    Module.finrank F U' + 2 ≤ S.card := by
  classical
  let r0 := res3 t a0
  let r1 := res3 t a1
  let r2 := -(r0 + r1)
  have hr02 : r0 ≠ r2 := (z3_third_ne r0 r1 hne).1
  have hr12 : r1 ≠ r2 := (z3_third_ne r0 r1 hne).2
  let phi : ({a : ZMod (3 * t) // a ∈ S} → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun f i =>
        if i.val = 0 then
          ∑ a : {a : ZMod (3 * t) // a ∈ S},
            if res3 t a.1 = r0 ∨ res3 t a.1 = r2 then f a else 0
        else
          ∑ a : {a : ZMod (3 * t) // a ∈ S},
            if res3 t a.1 = r1 ∨ res3 t a.1 = r2 then f a else 0
      map_add' := fun f g => by
        funext i; dsimp only [Pi.add_apply]; split_ifs <;>
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          split_ifs <;> simp
      map_smul' := fun c f => by
        funext i; dsimp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;>
        · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          split_ifs <;> simp }
  let emb : U' →ₗ[F] LinearMap.ker phi :=
    { toFun := fun u => ⟨fun a => u.1 a.1, by
        rw [LinearMap.mem_ker]
        have hsum_r : ∀ r : ZMod 3,
            ∑ a : {a : ZMod (3 * t) // a ∈ S}, (if res3 t a.1 = r then u.1 a.1 else 0) =
              parSum t r u.1 := by
          intro r
          rw [parSum_apply]
          rw [Finset.sum_coe_sort_eq_attach, ← Finset.sum_filter]
          have hsub : (∑ x ∈ S.attach.filter (fun a : {a // a ∈ S} => res3 t a.1 = r), u.1 x.1) =
              ∑ a ∈ S.filter (fun a : ZMod (3 * t) => res3 t a = r), u.1 a := by
            refine Finset.sum_nbij (fun x => x.1) ?_ ?_ ?_ (fun _ _ => rfl)
            · intro x hx
              exact Finset.mem_filter.mpr ⟨x.2, (Finset.mem_filter.mp hx).2⟩
            · intro x1 _ x2 _ h; exact Subtype.ext h
            · intro a ha
              rcases Finset.mem_filter.mp ha with ⟨haS, har⟩
              exact ⟨⟨a, haS⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, har⟩, rfl⟩
          rw [hsub]
          refine Finset.sum_subset (fun a ha => ?_) (fun a ha hnot => ?_)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
          · exact hsupp u.1 u.2 a (fun hS => hnot (Finset.mem_filter.mpr ⟨hS, (Finset.mem_filter.mp ha).2⟩))
        have hpair : ∀ ra rb : ZMod 3, ra ≠ rb →
            ∑ a : {a : ZMod (3 * t) // a ∈ S},
              (if res3 t a.1 = ra ∨ res3 t a.1 = rb then u.1 a.1 else 0) = 0 := by
          intro ra rb hab
          have hdisj : ∀ a : {a : ZMod (3 * t) // a ∈ S},
              (if res3 t a.1 = ra ∨ res3 t a.1 = rb then u.1 a.1 else 0) =
                (if res3 t a.1 = ra then u.1 a.1 else 0) +
                (if res3 t a.1 = rb then u.1 a.1 else 0) := by
            intro a
            by_cases h1 : res3 t a.1 = ra <;> by_cases h2 : res3 t a.1 = rb
            · exact absurd (h1.symm.trans h2) hab
            · simp [h1, hab]
            · simp [h2, hab.symm]
            · simp [h1, h2]
          simp_rw [hdisj]
          rw [Finset.sum_add_distrib, hsum_r ra, hsum_r rb,
            parSum_eq_of_mem_imSub t (hU'im u.2) ra rb, z2_add_self]
        funext i; fin_cases i
        · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
          simp only [↓reduceIte]; exact hpair r0 r2 hr02
        · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
          simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hpair r1 r2 hr12⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective emb := by
    intro u v huv
    apply Subtype.ext; funext a
    by_cases ha : a ∈ S
    · exact congrFun (congrArg Subtype.val huv) ⟨a, ha⟩
    · rw [hsupp u.1 u.2 a ha, hsupp v.1 v.2 a ha]
  have hsurj : Function.Surjective phi := by
    intro y
    have ha01 : a0 ≠ a1 := fun h => hne (congrArg (res3 t) h)
    refine ⟨fun a => if a.1 = a0 then y 0 else if a.1 = a1 then y 1 else 0, ?_⟩
    funext i; fin_cases i
    · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [↓reduceIte]
      have h1 : ∀ a : {a : ZMod (3 * t) // a ∈ S},
          (if res3 t a.1 = r0 ∨ res3 t a.1 = r2 then
            (if a.1 = a0 then y 0 else if a.1 = a1 then y 1 else 0) else 0) =
            if a = ⟨a0, ha0⟩ then y 0 else 0 := by
        intro a
        by_cases h : a = ⟨a0, ha0⟩
        · subst h; simp only [r0, true_or, ↓reduceIte]
        · have hne0 : a.1 ≠ a0 := fun heq => h (Subtype.ext heq)
          by_cases h1a : a.1 = a1
          · have hnot : ¬ (res3 t a.1 = r0 ∨ res3 t a.1 = r2) := by
              rw [h1a]; exact not_or.mpr ⟨hne.symm, hr12⟩
            simp only [hnot, h, ↓reduceIte]
          · simp only [hne0, h1a, h, ↓reduceIte, ite_self]
      simp_rw [h1]; rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]; rfl
    · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
      have h1 : ∀ a : {a : ZMod (3 * t) // a ∈ S},
          (if res3 t a.1 = r1 ∨ res3 t a.1 = r2 then
            (if a.1 = a0 then y 0 else if a.1 = a1 then y 1 else 0) else 0) =
            if a = ⟨a1, ha1⟩ then y 1 else 0 := by
        intro a
        by_cases h : a = ⟨a1, ha1⟩
        · subst h; simp only [r1, ha01.symm, true_or, ↓reduceIte]
        · have hne1 : a.1 ≠ a1 := fun heq => h (Subtype.ext heq)
          by_cases h0a : a.1 = a0
          · have hnot : ¬ (res3 t a.1 = r1 ∨ res3 t a.1 = r2) := by
              rw [h0a]; exact not_or.mpr ⟨hne, hr02⟩
            simp only [hnot, h, ↓reduceIte]
          · simp only [h0a, hne1, h, ↓reduceIte, ite_self]
      simp_rw [h1]; rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]; rfl
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hrk := LinearMap.finrank_range_add_finrank_ker phi
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
  have hdim : Module.finrank F ({a : ZMod (3 * t) // a ∈ S} → F) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [hdim] at hrk
  omega

lemma card_union_shift_ge {m : ℕ} [NeZero m] (S : Finset (ZMod m))
    (hne : S.Nonempty) (hnu : S ≠ Finset.univ) :
    S.card + 1 ≤ (S ∪ S.image (fun a => a - 1)).card := by
  classical
  have hss : S ⊂ S ∪ S.image (fun a => a - 1) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_union_left, ?_⟩
    intro heq
    apply hnu
    rcases hne with ⟨a0, ha0⟩
    have hstep : ∀ a ∈ S, a - 1 ∈ S := by
      intro a ha
      have : a - 1 ∈ S ∪ S.image (fun x => x - 1) :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)
      rwa [← heq] at this
    have hsub : ∀ k : ℕ, a0 - (k : ZMod m) ∈ S := by
      intro k
      induction k with
      | zero => simpa using ha0
      | succ k ih =>
        have h := hstep _ ih
        have he : a0 - (k : ZMod m) - 1 = a0 - ((k + 1 : ℕ) : ZMod m) := by
          push_cast; rw [sub_sub]
        rwa [he] at h
    ext b
    simp only [Finset.mem_univ, iff_true]
    have h := hsub (a0 - b).val
    rw [ZMod.natCast_zmod_val, sub_sub_cancel] at h
    exact h
  exact Finset.card_lt_card hss

lemma card_union_shift_mono_res (t : ℕ) [NeZero (3 * t)] (S : Finset (ZMod (3 * t)))
    (r : ZMod 3) (hS : ∀ a ∈ S, res3 t a = r) :
    (S ∪ S.image (fun a => a - 1)).card = 2 * S.card := by
  classical
  have hdisj : Disjoint S (S.image (fun a => a - 1)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rcases Finset.mem_image.mp hb2 with ⟨a, ha, rfl⟩
    have h1 := hS a ha
    have h2 := hS (a - 1) hb1
    rw [map_sub, map_one, h1] at h2
    exact z3_ne_sub_one r h2.symm
  have hinj : Function.Injective (fun a : ZMod (3 * t) => a - 1) :=
    fun _ _ h => sub_left_inj.mp h
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S hinj, Nat.two_mul]

lemma card_union_shift_add_mono_res (t : ℕ) [NeZero (3 * t)] (S : Finset (ZMod (3 * t)))
    (r : ZMod 3) (hS : ∀ a ∈ S, res3 t a = r) :
    (S ∪ S.image (fun a => a + 1)).card = 2 * S.card := by
  classical
  have hdisj : Disjoint S (S.image (fun a => a + 1)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rcases Finset.mem_image.mp hb2 with ⟨a, ha, rfl⟩
    have h1 := hS a ha
    have h2 := hS (a + 1) hb1
    rw [map_add, map_one, h1] at h2
    exact z3_ne_add_one r h2.symm
  have hinj : Function.Injective (fun a : ZMod (3 * t) => a + 1) :=
    fun _ _ h => (add_left_inj 1).mp h
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S hinj, Nat.two_mul]

lemma gap_imSub (t : ℕ) (ht : 0 < t) [NeZero (3 * t)]
    (U' V' : Submodule F (Lane (3 * t))) (hU'im : U' ≤ imSub t) (hV'im : V' ≤ imSub t)
    (hU' : U' ≠ ⊥) (hV' : V' ≠ ⊥)
    (hQ : ∀ u ∈ U', ∀ v ∈ V', ∀ a : ZMod (3 * t),
      u a * v a = 0 ∧ u a * v (a - 1) = 0) :
    Module.finrank F U' + Module.finrank F V' + (if t = 1 then 1 else if t = 2 then 3 else 4) ≤
      3 * t - 1 := by
  classical
  by_cases ht1 : t = 1
  · subst ht1
    exfalso
    have hexU : ∃ u ∈ U', u ≠ 0 := by
      by_contra h; push Not at h; apply hU'
      rw [eq_bot_iff]; intro u hu; exact (Submodule.mem_bot F).mpr (h u hu)
    have hexV : ∃ v ∈ V', v ≠ 0 := by
      by_contra h; push Not at h; apply hV'
      rw [eq_bot_iff]; intro v hv; exact (Submodule.mem_bot F).mpr (h v hv)
    rcases hexU with ⟨u, huU, hu0⟩
    rcases hexV with ⟨v, hvV, hv0⟩
    have hconst : ∀ w : Lane 3, w ∈ imSub 1 → ∀ a : ZMod 3, w a = w 0 := by
      intro w hw a
      have hp := parSum_eq_of_mem_imSub 1 hw a 0
      have hval : ∀ r : ZMod 3, parSum 1 r w = w r := by
        intro r
        rw [parSum_apply]
        have hf : Finset.univ.filter (fun x : ZMod 3 => res3 1 x = r) = {r} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, res3_one_id]
        rw [hf, Finset.sum_singleton]
      rw [hval a, hval 0] at hp
      exact hp
    have hu_nz : u 0 ≠ 0 := by
      intro hz; apply hu0; funext a; rw [hconst u (hU'im huU) a]; exact hz
    have hv_nz : v 0 ≠ 0 := by
      intro hz; apply hv0; funext a; rw [hconst v (hV'im hvV) a]; exact hz
    have h0 := (hQ u huU v hvV 0).1
    rcases z2_eq_zero_or_one (u 0) with hu1 | hu1
    · exact hu_nz hu1
    · rcases z2_eq_zero_or_one (v 0) with hv1 | hv1
      · exact hv_nz hv1
      · rw [hu1, hv1] at h0; exact one_ne_zero h0
  · let A : Finset (ZMod (3 * t)) :=
      Finset.univ.filter (fun a => ∃ u ∈ U', u a ≠ 0)
    let B : Finset (ZMod (3 * t)) :=
      Finset.univ.filter (fun b => ∃ v ∈ V', v b ≠ 0)
    have hsuppA : ∀ u ∈ U', ∀ a, a ∉ A → u a = 0 := by
      intro u hu a ha
      by_contra hne
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, hne⟩)
    have hsuppB : ∀ v ∈ V', ∀ b, b ∉ B → v b = 0 := by
      intro v hv b hb
      by_contra hne
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hne⟩)
    have hAne : A.Nonempty := by
      have hex : ∃ u ∈ U', u ≠ 0 := by
        by_contra h; push Not at h; apply hU'
        rw [eq_bot_iff]; intro u hu; exact (Submodule.mem_bot F).mpr (h u hu)
      rcases hex with ⟨u, hu, hu0⟩
      have hexA : ∃ a, u a ≠ 0 := by
        by_contra h; push Not at h; apply hu0; funext a; exact h a
      rcases hexA with ⟨a, ha⟩
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, ha⟩⟩
    have hBne : B.Nonempty := by
      have hex : ∃ v ∈ V', v ≠ 0 := by
        by_contra h; push Not at h; apply hV'
        rw [eq_bot_iff]; intro v hv; exact (Submodule.mem_bot F).mpr (h v hv)
      rcases hex with ⟨v, hv, hv0⟩
      have hexB : ∃ b, v b ≠ 0 := by
        by_contra h; push Not at h; apply hv0; funext b; exact h b
      rcases hexB with ⟨b, hb⟩
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hb⟩⟩
    have hdisjAB : Disjoint (A ∪ A.image (fun a => a - 1)) B := by
      rw [Finset.disjoint_left]
      intro b hb1 hb2
      rcases (Finset.mem_filter.mp hb2).2 with ⟨v, hv, hvb⟩
      rcases Finset.mem_union.mp hb1 with hbA | hbIm
      · rcases (Finset.mem_filter.mp hbA).2 with ⟨u, hu, hub⟩
        rcases mul_eq_zero.mp (hQ u hu v hv b).1 with h1 | h2
        · exact hub h1
        · exact hvb h2
      · rcases Finset.mem_image.mp hbIm with ⟨a, ha, rfl⟩
        rcases (Finset.mem_filter.mp ha).2 with ⟨u, hu, hua⟩
        rcases mul_eq_zero.mp (hQ u hu v hv a).2 with h1 | h2
        · exact hua h1
        · exact hvb h2
    have hdisjBA : Disjoint A (B ∪ B.image (fun b => b + 1)) := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      rcases (Finset.mem_filter.mp ha1).2 with ⟨u, hu, hua⟩
      rcases Finset.mem_union.mp ha2 with haB | haIm
      · rcases (Finset.mem_filter.mp haB).2 with ⟨v, hv, hva⟩
        rcases mul_eq_zero.mp (hQ u hu v hv a).1 with h1 | h2
        · exact hua h1
        · exact hva h2
      · rcases Finset.mem_image.mp haIm with ⟨b, hb, rfl⟩
        rcases (Finset.mem_filter.mp hb).2 with ⟨v, hv, hvb⟩
        have h0 := (hQ u hu v hv (b + 1)).2
        rw [add_sub_cancel_right] at h0
        rcases mul_eq_zero.mp h0 with h1 | h2
        · exact hua h1
        · exact hvb h2
    have hAnu : A ≠ Finset.univ := by
      intro h
      rcases hBne with ⟨b, hb⟩
      have hbA : b ∈ A ∪ A.image (fun a => a - 1) :=
        Finset.mem_union_left _ (h ▸ Finset.mem_univ b)
      exact Finset.disjoint_left.mp hdisjAB hbA hb
    have hsum_card1 : (A ∪ A.image (fun a => a - 1)).card + B.card ≤ 3 * t := by
      have := Finset.card_union_of_disjoint hdisjAB
      have hle : ((A ∪ A.image (fun a => a - 1)) ∪ B).card ≤
          (Finset.univ : Finset (ZMod (3 * t))).card :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_univ, ZMod.card] at hle
      omega
    have hsum_card2 : A.card + (B ∪ B.image (fun b => b + 1)).card ≤ 3 * t := by
      have := Finset.card_union_of_disjoint hdisjBA
      have hle : (A ∪ (B ∪ B.image (fun b => b + 1))).card ≤
          (Finset.univ : Finset (ZMod (3 * t))).card :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_univ, ZMod.card] at hle
      omega
    have hdimU_pos : 1 ≤ Module.finrank F U' := by
      by_contra h
      have h0 : Module.finrank F U' = 0 := by omega
      exact hU' ((Submodule.finrank_eq_zero).mp h0)
    have hdimV_pos : 1 ≤ Module.finrank F V' := by
      by_contra h
      have h0 : Module.finrank F V' = 0 := by omega
      exact hV' ((Submodule.finrank_eq_zero).mp h0)
    have hU1 := finrank_supp_le_card_sub_one t U' hU'im A hsuppA hAne
    have hV1 := finrank_supp_le_card_sub_one t V' hV'im B hsuppB hBne
    by_cases hA2 : ∃ a0 ∈ A, ∃ a1 ∈ A, res3 t a0 ≠ res3 t a1
    · rcases hA2 with ⟨a0, ha0, a1, ha1, hneA⟩
      have hU2 := finrank_supp_le_card_sub_two t U' hU'im A hsuppA a0 a1 ha0 ha1 hneA
      by_cases hB2 : ∃ b0 ∈ B, ∃ b1 ∈ B, res3 t b0 ≠ res3 t b1
      · rcases hB2 with ⟨b0, hb0, b1, hb1, hneB⟩
        have hV2 := finrank_supp_le_card_sub_two t V' hV'im B hsuppB b0 b1 hb0 hb1 hneB
        have hexp := card_union_shift_ge A hAne hAnu
        split_ifs <;> omega
      · push Not at hB2
        rcases hBne with ⟨b0, hb0⟩
        have hBmono := card_union_shift_add_mono_res t B (res3 t b0) (fun b hb => hB2 b hb b0 hb0)
        split_ifs <;> omega
    · push Not at hA2
      rcases hAne with ⟨a0, ha0⟩
      have hAmono := card_union_shift_mono_res t A (res3 t a0) (fun a ha => hA2 a ha a0 ha0)
      by_cases hB2 : ∃ b0 ∈ B, ∃ b1 ∈ B, res3 t b0 ≠ res3 t b1
      · rcases hB2 with ⟨b0, hb0, b1, hb1, hneB⟩
        have hV2 := finrank_supp_le_card_sub_two t V' hV'im B hsuppB b0 b1 hb0 hb1 hneB
        split_ifs <;> omega
      · push Not at hB2
        rcases hBne with ⟨b0, hb0⟩
        have hAle : A.card ≤ t := by
          have hsub : A ⊆ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = res3 t a0) := by
            intro a ha
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA2 a ha a0 ha0⟩
          exact (Finset.card_le_card hsub).trans_eq (card_res3_fiber t ht (res3 t a0))
        have hBle : B.card ≤ t := by
          have hsub : B ⊆ Finset.univ.filter (fun b : ZMod (3 * t) => res3 t b = res3 t b0) := by
            intro b hb
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB2 b hb b0 hb0⟩
          exact (Finset.card_le_card hsub).trans_eq (card_res3_fiber t ht (res3 t b0))
        split_ifs <;> omega

def ixN (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def rotN (n : ℕ) (hn : 0 < n) (s : ℕ) (w : Fin n → F) (i : Fin n) : F :=
  w (ixN n hn (i.val + n - s % n))

def mixN (n : ℕ) (hn : 0 < n) (w : Fin n → F) (i : Fin n) : F :=
  let old := rotN n hn 3 w
  old i + old (ixN n hn (i.val + 2)) + old (ixN n hn (i.val + n - 2))

def outN (n : ℕ) (hn : 0 < n) (name c raw : Fin n → F) (i : Fin n) : F :=
  let old := rotN n hn 3 raw + name
  let y := fun j : Fin n => old j + old (ixN n hn (j.val + 2)) + old (ixN n hn (j.val + n - 2))
  y i + (1 + y (ixN n hn (i.val + 1))) * y (ixN n hn (i.val + 2)) + rotN n hn 4 raw i + c i

noncomputable def runN (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F) (w : Fin n → F) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.finRange h).foldl (fun z i => 2 * z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)

def siteN (t : ℕ) (j : Fin (3*t-4)) : ℕ := if t = 2 then 2+3*j.val else j.val

def numN (t : ℕ) : ℕ := if t = 2 then 21 else 19

lemma ixN_eq_iff (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    ixN n hn a = ixN n hn b ↔ a % n = b % n := by
  simp only [ixN, Fin.mk.injEq]

lemma mixN_add (n : ℕ) (hn : 0 < n) (w1 w2 : Fin n → F) :
    mixN n hn (w1 + w2) = mixN n hn w1 + mixN n hn w2 := by
  funext i; dsimp only [mixN, rotN, Pi.add_apply]; abel

lemma mixN_smul (n : ℕ) (hn : 0 < n) (c : F) (w : Fin n → F) :
    mixN n hn (c • w) = c • mixN n hn w := by
  funext i; dsimp only [mixN, rotN, Pi.smul_apply, smul_eq_mul]; ring

def evenLane (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    (Fin (6 * t) → F) →ₗ[F] Lane (3 * t) where
  toFun w a := mixN (6 * t) (by omega) w ⟨2 * a.val, by have := a.val_lt; omega⟩
  map_add' w1 w2 := by funext a; exact congrFun (mixN_add (6 * t) (by omega) w1 w2) _
  map_smul' c w := by funext a; exact congrFun (mixN_smul (6 * t) (by omega) c w) _

def oddLane (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    (Fin (6 * t) → F) →ₗ[F] Lane (3 * t) where
  toFun w a := mixN (6 * t) (by omega) w ⟨2 * a.val + 1, by have := a.val_lt; omega⟩
  map_add' w1 w2 := by funext a; exact congrFun (mixN_add (6 * t) (by omega) w1 w2) _
  map_smul' c w := by funext a; exact congrFun (mixN_smul (6 * t) (by omega) c w) _

def splitIdx (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    ZMod (3 * t) ⊕ ZMod (3 * t) ≃ Fin (6 * t) where
  toFun s := match s with
    | Sum.inl a => ixN (6 * t) (by omega) (2 * a.val + 6 * t - 3)
    | Sum.inr a => ixN (6 * t) (by omega) (2 * a.val + 6 * t - 2)
  invFun i := if i.val % 2 = 1 then
      Sum.inl (((i.val + 3) / 2 : ℕ) : ZMod (3 * t))
    else
      Sum.inr (((i.val + 2) / 2 : ℕ) : ZMod (3 * t))
  left_inv s := by
    cases s with
    | inl a =>
      have ha : a.val < 3 * t := a.val_lt
      have hmod : (2 * a.val + 6 * t - 3) % (6 * t) % 2 = 1 := by
        have h2 : 2 ∣ 6 * t := ⟨3 * t, by omega⟩
        rw [Nat.mod_mod_of_dvd _ h2]; omega
      dsimp only [ixN]
      simp only [hmod, ↓reduceIte]
      congr 1
      have hdiv : ((2 * a.val + 6 * t - 3) % (6 * t) + 3) / 2 % (3 * t) = a.val := by
        by_cases h : 2 * a.val < 3
        · have heq : (2 * a.val + 6 * t - 3) % (6 * t) = 2 * a.val + 6 * t - 3 :=
            Nat.mod_eq_of_lt (by omega)
          rw [heq]
          have : (2 * a.val + 6 * t - 3 + 3) / 2 = a.val + 3 * t := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        · have heq : (2 * a.val + 6 * t - 3) % (6 * t) = 2 * a.val - 3 := by
            have h1 : 2 * a.val + 6 * t - 3 = (2 * a.val - 3) + 6 * t := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [heq]
          have : (2 * a.val - 3 + 3) / 2 = a.val := by omega
          rw [this, Nat.mod_eq_of_lt ha]
      apply ZMod.val_injective (3 * t)
      rw [ZMod.val_natCast, hdiv]
    | inr a =>
      have ha : a.val < 3 * t := a.val_lt
      have hmod : (2 * a.val + 6 * t - 2) % (6 * t) % 2 ≠ 1 := by
        have h2 : 2 ∣ 6 * t := ⟨3 * t, by omega⟩
        rw [Nat.mod_mod_of_dvd _ h2]; omega
      dsimp only [ixN]
      simp only [hmod, ↓reduceIte]
      congr 1
      have hdiv : ((2 * a.val + 6 * t - 2) % (6 * t) + 2) / 2 % (3 * t) = a.val := by
        by_cases h : 2 * a.val < 2
        · have heq : (2 * a.val + 6 * t - 2) % (6 * t) = 2 * a.val + 6 * t - 2 :=
            Nat.mod_eq_of_lt (by omega)
          rw [heq]
          have : (2 * a.val + 6 * t - 2 + 2) / 2 = a.val + 3 * t := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        · have heq : (2 * a.val + 6 * t - 2) % (6 * t) = 2 * a.val - 2 := by
            have h1 : 2 * a.val + 6 * t - 2 = (2 * a.val - 2) + 6 * t := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [heq]
          have : (2 * a.val - 2 + 2) / 2 = a.val := by omega
          rw [this, Nat.mod_eq_of_lt ha]
      apply ZMod.val_injective (3 * t)
      rw [ZMod.val_natCast, hdiv]
  right_inv i := by
    have hi : i.val < 6 * t := i.isLt
    dsimp only
    split_ifs with hodd
    · apply Fin.ext; dsimp only [ixN]
      rw [ZMod.val_natCast]
      by_cases hlt : (i.val + 3) / 2 < 3 * t
      · rw [Nat.mod_eq_of_lt hlt]
        have he : 2 * ((i.val + 3) / 2) + 6 * t - 3 = i.val + 6 * t := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hmod : (i.val + 3) / 2 % (3 * t) = (i.val + 3) / 2 - 3 * t := by
          have he : (i.val + 3) / 2 = ((i.val + 3) / 2 - 3 * t) + 3 * t := by omega
          conv_lhs => rw [he]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have he : 2 * ((i.val + 3) / 2 - 3 * t) + 6 * t - 3 = i.val := by omega
        rw [he, Nat.mod_eq_of_lt hi]
    · apply Fin.ext; dsimp only [ixN]
      rw [ZMod.val_natCast]
      by_cases hlt : (i.val + 2) / 2 < 3 * t
      · rw [Nat.mod_eq_of_lt hlt]
        have he : 2 * ((i.val + 2) / 2) + 6 * t - 2 = i.val + 6 * t := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hmod : (i.val + 2) / 2 % (3 * t) = (i.val + 2) / 2 - 3 * t := by
          have he : (i.val + 2) / 2 = ((i.val + 2) / 2 - 3 * t) + 3 * t := by omega
          conv_lhs => rw [he]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have he : 2 * ((i.val + 2) / 2 - 3 * t) + 6 * t - 2 = i.val := by omega
        rw [he, Nat.mod_eq_of_lt hi]

def splitW (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    (Fin (6 * t) → F) ≃ₗ[F] Lane (3 * t) × Lane (3 * t) where
  toFun w := (fun a => w (splitIdx t ht (Sum.inl a)), fun a => w (splitIdx t ht (Sum.inr a)))
  invFun p i := match (splitIdx t ht).symm i with
    | Sum.inl a => p.1 a
    | Sum.inr a => p.2 a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv w := by
    funext i
    dsimp only
    cases h : (splitIdx t ht).symm i with
    | inl a =>
      dsimp only
      have : splitIdx t ht (Sum.inl a) = i := by rw [← h, Equiv.apply_symm_apply]
      rw [this]
    | inr a =>
      dsimp only
      have : splitIdx t ht (Sum.inr a) = i := by rw [← h, Equiv.apply_symm_apply]
      rw [this]
  right_inv p := by
    apply Prod.ext <;> funext a <;> dsimp only <;> rw [Equiv.symm_apply_apply]

lemma splitW_fst (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) (a : ZMod (3 * t)) :
    (splitW t ht w).1 a = w (ixN (6 * t) (by omega) (2 * a.val + 6 * t - 3)) := rfl

lemma splitW_snd (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) (a : ZMod (3 * t)) :
    (splitW t ht w).2 a = w (ixN (6 * t) (by omega) (2 * a.val + 6 * t - 2)) := rfl

lemma mixN_mod_shift (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (w : Fin n → F) (i : Fin n) :
    mixN n hn w i =
      w (ixN n hn (i.val + n - 3)) +
      w (ixN n hn (i.val + n - 1)) +
      w (ixN n hn (i.val + n - 5)) := by
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  dsimp only [mixN, rotN]
  rw [h3]
  have e1 : ixN n hn ((ixN n hn (i.val + 2)).val + n - 3) = ixN n hn (i.val + n - 1) := by
    rw [ixN_eq_iff]; dsimp only [ixN]
    have hi : i.val < n := i.isLt
    have h1 : (i.val + 2) % n + n - 3 = (i.val + 2) % n + (n - 3) := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : i.val + 2 + (n - 3) = i.val + n - 1 := by omega
    rw [h2]
  have e2 : ixN n hn ((ixN n hn (i.val + n - 2)).val + n - 3) = ixN n hn (i.val + n - 5) := by
    rw [ixN_eq_iff]; dsimp only [ixN]
    have hi : i.val < n := i.isLt
    have h1 : (i.val + n - 2) % n + n - 3 = (i.val + n - 2) % n + (n - 3) := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : i.val + n - 2 + (n - 3) = (i.val + n - 5) + n := by omega
    rw [h2, Nat.add_mod_right]
  rw [e1, e2]

lemma zmod_sub_one_val (m : ℕ) (hm : 0 < m) [NeZero m] (a : ZMod m) :
    (a - 1).val = (a.val + m - 1) % m := by
  have h0 : ((m : ℕ) : ZMod m) = 0 := ZMod.natCast_self m
  have h1 : ((a.val + m - 1 : ℕ) : ZMod m) + 1 = a := by
    have h2 : ((a.val + m - 1 : ℕ) : ZMod m) + ((1 : ℕ) : ZMod m) =
        ((a.val + m : ℕ) : ZMod m) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
    rw [Nat.cast_one, Nat.cast_add, h0, add_zero, ZMod.natCast_zmod_val] at h2
    exact h2
  have heq : a - 1 = ((a.val + m - 1 : ℕ) : ZMod m) := (eq_sub_of_add_eq h1).symm
  rw [heq, ZMod.val_natCast]

lemma zmod_add_one_val (m : ℕ) [NeZero m] (a : ZMod m) :
    (a + 1).val = (a.val + 1) % m := by
  have heq : a + 1 = ((a.val + 1 : ℕ) : ZMod m) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [heq, ZMod.val_natCast]

lemma evenLane_eq_tri (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) :
    evenLane t ht w = tri (splitW t ht w).1 := by
  funext a
  change mixN (6 * t) (by omega) w ⟨2 * a.val, _⟩ =
    (splitW t ht w).1 a + (splitW t ht w).1 (a + 1) + (splitW t ht w).1 (a - 1)
  rw [splitW_fst, splitW_fst, splitW_fst, mixN_mod_shift (6 * t) (by omega) (by omega)]
  dsimp only
  have ha : a.val < 3 * t := a.val_lt
  have hplus : ixN (6 * t) (by omega) (2 * a.val + 6 * t - 1) =
      ixN (6 * t) (by omega) (2 * (a + 1).val + 6 * t - 3) := by
    rw [ixN_eq_iff, zmod_add_one_val (3 * t) a]
    by_cases hlt : a.val + 1 < 3 * t
    · rw [Nat.mod_eq_of_lt hlt]
      have : 2 * (a.val + 1) + 6 * t - 3 = 2 * a.val + 6 * t - 1 := by omega
      rw [this]
    · have hae : a.val = 3 * t - 1 := by omega
      rw [hae, show 3 * t - 1 + 1 = 3 * t by omega, Nat.mod_self]
      have h1 : 2 * (3 * t - 1) + 6 * t - 1 = (6 * t - 3) + 6 * t := by omega
      have h2 : 2 * 0 + 6 * t - 3 = 6 * t - 3 := by omega
      rw [h1, h2, Nat.add_mod_right]
  have hminus : ixN (6 * t) (by omega) (2 * a.val + 6 * t - 5) =
      ixN (6 * t) (by omega) (2 * (a - 1).val + 6 * t - 3) := by
    rw [ixN_eq_iff, zmod_sub_one_val (3 * t) (by omega) a]
    by_cases h0 : a.val = 0
    · rw [h0, show 0 + 3 * t - 1 = 3 * t - 1 by omega]
      rw [Nat.mod_eq_of_lt (by omega : 3 * t - 1 < 3 * t)]
      have h1 : 2 * 0 + 6 * t - 5 = 6 * t - 5 := by omega
      have h2 : 2 * (3 * t - 1) + 6 * t - 3 = (6 * t - 5) + 6 * t := by omega
      rw [h1, h2, Nat.add_mod_right]
    · have h1 : (a.val + 3 * t - 1) % (3 * t) = a.val - 1 := by
        have he : a.val + 3 * t - 1 = (a.val - 1) + 3 * t := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      have h2 : 2 * (a.val - 1) + 6 * t - 3 = 2 * a.val + 6 * t - 5 := by omega
      rw [h2]
  rw [hplus, hminus]

lemma oddLane_eq_tri (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) :
    oddLane t ht w = tri (splitW t ht w).2 := by
  funext a
  change mixN (6 * t) (by omega) w ⟨2 * a.val + 1, _⟩ =
    (splitW t ht w).2 a + (splitW t ht w).2 (a + 1) + (splitW t ht w).2 (a - 1)
  rw [splitW_snd, splitW_snd, splitW_snd, mixN_mod_shift (6 * t) (by omega) (by omega)]
  dsimp only
  have ha : a.val < 3 * t := a.val_lt
  have hcur : 2 * a.val + 1 + 6 * t - 3 = 2 * a.val + 6 * t - 2 := by omega
  have hplus : ixN (6 * t) (by omega) (2 * a.val + 1 + 6 * t - 1) =
      ixN (6 * t) (by omega) (2 * (a + 1).val + 6 * t - 2) := by
    rw [ixN_eq_iff, zmod_add_one_val (3 * t) a]
    by_cases hlt : a.val + 1 < 3 * t
    · rw [Nat.mod_eq_of_lt hlt]
      have : 2 * (a.val + 1) + 6 * t - 2 = 2 * a.val + 1 + 6 * t - 1 := by omega
      rw [this]
    · have hae : a.val = 3 * t - 1 := by omega
      rw [hae, show 3 * t - 1 + 1 = 3 * t by omega, Nat.mod_self]
      have h1 : 2 * (3 * t - 1) + 1 + 6 * t - 1 = (6 * t - 2) + 6 * t := by omega
      have h2 : 2 * 0 + 6 * t - 2 = 6 * t - 2 := by omega
      rw [h1, h2, Nat.add_mod_right]
  have hminus : ixN (6 * t) (by omega) (2 * a.val + 1 + 6 * t - 5) =
      ixN (6 * t) (by omega) (2 * (a - 1).val + 6 * t - 2) := by
    rw [ixN_eq_iff, zmod_sub_one_val (3 * t) (by omega) a]
    by_cases h0 : a.val = 0
    · rw [h0, show 0 + 3 * t - 1 = 3 * t - 1 by omega]
      rw [Nat.mod_eq_of_lt (by omega : 3 * t - 1 < 3 * t)]
      have h1 : 2 * 0 + 1 + 6 * t - 5 = 6 * t - 4 := by omega
      have h2 : 2 * (3 * t - 1) + 6 * t - 2 = (6 * t - 4) + 6 * t := by omega
      rw [h1, h2, Nat.add_mod_right]
    · have h1 : (a.val + 3 * t - 1) % (3 * t) = a.val - 1 := by
        have he : a.val + 3 * t - 1 = (a.val - 1) + 3 * t := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      have h2 : 2 * (a.val - 1) + 6 * t - 2 = 2 * a.val + 1 + 6 * t - 5 := by omega
      rw [h2]
  rw [hcur, hplus, hminus]

lemma evenLane_mem_imSub (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) :
    evenLane t ht w ∈ imSub t := by
  rw [evenLane_eq_tri, ← range_tri_eq_imSub t ht]
  exact LinearMap.mem_range_self _ _

lemma oddLane_mem_imSub (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) :
    oddLane t ht w ∈ imSub t := by
  rw [oddLane_eq_tri, ← range_tri_eq_imSub t ht]
  exact LinearMap.mem_range_self _ _

lemma exists_even_odd (t : ℕ) (ht : 0 < t) [NeZero (3 * t)]
    {u v : Lane (3 * t)} (hu : u ∈ imSub t) (hv : v ∈ imSub t) :
    ∃ w : Fin (6 * t) → F, evenLane t ht w = u ∧ oddLane t ht w = v := by
  rw [← range_tri_eq_imSub t ht] at hu hv
  rcases hu with ⟨x, rfl⟩
  rcases hv with ⟨y, rfl⟩
  refine ⟨(splitW t ht).symm (x, y), ?_, ?_⟩
  · rw [evenLane_eq_tri, LinearEquiv.apply_symm_apply]
  · rw [oddLane_eq_tri, LinearEquiv.apply_symm_apply]

lemma finrank_ker_even_inf_odd (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    Module.finrank F
      ((LinearMap.ker (evenLane t ht) ⊓ LinearMap.ker (oddLane t ht) :
        Submodule F (Fin (6 * t) → F))) = 4 := by
  let S : Submodule F (Fin (6 * t) → F) :=
    LinearMap.ker (evenLane t ht) ⊓ LinearMap.ker (oddLane t ht)
  let e : S ≃ₗ[F]
      LinearMap.ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t)) ×
      LinearMap.ker (tri : Lane (3 * t) →ₗ[F] Lane (3 * t)) :=
    { toFun := fun w =>
        (⟨(splitW t ht w.1).1, by
            rw [LinearMap.mem_ker, ← evenLane_eq_tri]; exact LinearMap.mem_ker.mp w.2.1⟩,
         ⟨(splitW t ht w.1).2, by
            rw [LinearMap.mem_ker, ← oddLane_eq_tri]; exact LinearMap.mem_ker.mp w.2.2⟩)
      invFun := fun p =>
        ⟨(splitW t ht).symm (p.1.1, p.2.1), by
          refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
          · rw [LinearMap.mem_ker, evenLane_eq_tri, LinearEquiv.apply_symm_apply]
            exact LinearMap.mem_ker.mp p.1.2
          · rw [LinearMap.mem_ker, oddLane_eq_tri, LinearEquiv.apply_symm_apply]
            exact LinearMap.mem_ker.mp p.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => by
        apply Subtype.ext; dsimp only; exact LinearEquiv.symm_apply_apply (splitW t ht) w.1
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst (LinearEquiv.apply_symm_apply (splitW t ht) (p.1.1, p.2.1))
        · apply Subtype.ext
          exact congrArg Prod.snd (LinearEquiv.apply_symm_apply (splitW t ht) (p.1.1, p.2.1)) }
  change Module.finrank F S = 4
  rw [LinearEquiv.finrank_eq e, Module.finrank_prod, finrank_ker_tri t ht]

def Qmap (t : ℕ) [NeZero (3 * t)] :
    Lane (3 * t) →ₗ[F] Lane (3 * t) →ₗ[F] (Fin (6 * t) → F) where
  toFun u :=
    { toFun := fun v i =>
        if i.val % 2 = 0 then
          u (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v ((i.val / 2 : ℕ) : ZMod (3 * t))
        else
          u (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1)
      map_add' := fun v1 v2 => by
        funext i; simp only [Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c v => by
        funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  map_add' u1 u2 := by
    apply LinearMap.ext; intro v; funext i
    change (if i.val % 2 = 0 then
        (u1 + u2) (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v ((i.val / 2 : ℕ) : ZMod (3 * t))
      else
        (u1 + u2) (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1)) =
      (if i.val % 2 = 0 then
        u1 (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v ((i.val / 2 : ℕ) : ZMod (3 * t))
      else
        u1 (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1)) +
      (if i.val % 2 = 0 then
        u2 (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v ((i.val / 2 : ℕ) : ZMod (3 * t))
      else
        u2 (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1))
    simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c u := by
    apply LinearMap.ext; intro v; funext i
    change (if i.val % 2 = 0 then
        (c • u) (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v ((i.val / 2 : ℕ) : ZMod (3 * t))
      else
        (c • u) (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1)) =
      c * (if i.val % 2 = 0 then
        u (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v ((i.val / 2 : ℕ) : ZMod (3 * t))
      else
        u (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) * v (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1))
    simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

lemma Qmap_even_odd (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (w : Fin (6 * t) → F) (i : Fin (6 * t)) :
    Qmap t (evenLane t ht w) (oddLane t ht w) i =
      mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (i.val + 1)) *
      mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (i.val + 2)) := by
  have hi : i.val < 6 * t := i.isLt
  have hq : i.val / 2 < 3 * t := by omega
  have hv0 : ((i.val / 2 : ℕ) : ZMod (3 * t)).val = i.val / 2 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hq]
  have hv1 : (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1).val = (i.val / 2 + 1) % (3 * t) := by
    have : (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1) = ((i.val / 2 + 1 : ℕ) : ZMod (3 * t)) := by
      push_cast; rfl
    rw [this, ZMod.val_natCast]
  dsimp only [Qmap, evenLane, oddLane, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hev
  · rw [mul_comm]
    congr 1
    · congr 1; apply Fin.ext; dsimp only [ixN]
      rw [hv0, show 2 * (i.val / 2) + 1 = i.val + 1 by omega, Nat.mod_eq_of_lt (by omega)]
    · congr 1; apply Fin.ext; dsimp only [ixN]
      rw [hv1]
      by_cases hlt : i.val / 2 + 1 < 3 * t
      · rw [Nat.mod_eq_of_lt hlt, show 2 * (i.val / 2 + 1) = i.val + 2 by omega,
          Nat.mod_eq_of_lt (by omega)]
      · have he : i.val = 6 * t - 2 := by omega
        rw [he, show (6 * t - 2) / 2 + 1 = 3 * t by omega, Nat.mod_self,
          show 6 * t - 2 + 2 = 6 * t by omega, Nat.mod_self, Nat.mul_zero]
  · congr 1
    · congr 1; apply Fin.ext; dsimp only [ixN]
      rw [hv1]
      by_cases hlt : i.val / 2 + 1 < 3 * t
      · rw [Nat.mod_eq_of_lt hlt, show 2 * (i.val / 2 + 1) = i.val + 1 by omega,
          Nat.mod_eq_of_lt (by omega)]
      · have he : i.val = 6 * t - 1 := by omega
        rw [he, show (6 * t - 1) / 2 + 1 = 3 * t by omega, Nat.mod_self,
          show 6 * t - 1 + 1 = 6 * t by omega, Nat.mod_self, Nat.mul_zero]
    · congr 1; apply Fin.ext; dsimp only [ixN]
      rw [hv1]
      by_cases hlt : i.val / 2 + 1 < 3 * t
      · rw [Nat.mod_eq_of_lt hlt, show 2 * (i.val / 2 + 1) + 1 = i.val + 2 by omega,
          Nat.mod_eq_of_lt (by omega)]
      · have he : i.val = 6 * t - 1 := by omega
        rw [he, show (6 * t - 1) / 2 + 1 = 3 * t by omega, Nat.mod_self,
          show 6 * t - 1 + 2 = 1 + 6 * t by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]

lemma Qmap_eq_zero_iff (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (u v : Lane (3 * t)) :
    Qmap t u v = 0 ↔ ∀ a : ZMod (3 * t), u a * v a = 0 ∧ u a * v (a - 1) = 0 := by
  constructor
  · intro h a
    have ha1 := (a - 1).val_lt
    have hcast : (((a - 1).val : ℕ) : ZMod (3 * t)) = a - 1 := ZMod.natCast_zmod_val (a - 1)
    have hcast1 : (((a - 1).val : ℕ) : ZMod (3 * t)) + 1 = a := by rw [hcast, sub_add_cancel]
    have hev := congrFun h ⟨2 * (a - 1).val, by omega⟩
    have hodd := congrFun h ⟨2 * (a - 1).val + 1, by omega⟩
    dsimp only [Qmap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hev hodd
    have hm0 : (2 * (a - 1).val) % 2 = 0 := Nat.mul_mod_right 2 _
    have hm1 : (2 * (a - 1).val + 1) % 2 ≠ 0 := by omega
    have hd0 : (2 * (a - 1).val) / 2 = (a - 1).val := by omega
    have hd1 : (2 * (a - 1).val + 1) / 2 = (a - 1).val := by omega
    simp only [hm0, ↓reduceIte, hd0, hcast, sub_add_cancel] at hev
    simp only [hm1, ↓reduceIte, hd1, hcast, sub_add_cancel] at hodd
    exact ⟨hodd, hev⟩
  · intro h
    funext i
    dsimp only [Qmap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs
    · have h2 := (h (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1)).2
      rwa [add_sub_cancel_right] at h2
    · exact (h (((i.val / 2 : ℕ) : ZMod (3 * t)) + 1)).1

def Lbase (t : ℕ) (ht : 0 < t) (name : Fin (6 * t) → F) :
    (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F) :=
  let n := 6 * t
  let hn : 0 < n := by omega
  let y0 : Fin n → F := fun j =>
    name j + name (ixN n hn (j.val + 2)) + name (ixN n hn (j.val + n - 2))
  { toFun := fun w i =>
      mixN n hn w i + mixN n hn w (ixN n hn (i.val + 2)) +
      mixN n hn w (ixN n hn (i.val + 1)) * y0 (ixN n hn (i.val + 2)) +
      y0 (ixN n hn (i.val + 1)) * mixN n hn w (ixN n hn (i.val + 2)) +
      rotN n hn 4 w i
    map_add' := fun w1 w2 => by
      funext i
      have hm := fun j => congrFun (mixN_add n hn w1 w2) j
      simp only [Pi.add_apply] at hm
      dsimp only [Pi.add_apply, rotN]
      simp only [hm]; ring
    map_smul' := fun c w => by
      funext i
      have hm := fun j => congrFun (mixN_smul n hn c w) j
      simp only [Pi.smul_apply, smul_eq_mul] at hm
      dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, rotN]
      simp only [hm]; ring }

def cbase (t : ℕ) (ht : 0 < t) (name c : Fin (6 * t) → F) : Fin (6 * t) → F :=
  let n := 6 * t
  let hn : 0 < n := by omega
  let y0 : Fin n → F := fun j =>
    name j + name (ixN n hn (j.val + 2)) + name (ixN n hn (j.val + n - 2))
  fun i =>
    y0 i + y0 (ixN n hn (i.val + 2)) + y0 (ixN n hn (i.val + 1)) * y0 (ixN n hn (i.val + 2)) + c i

lemma outN_decomp (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (name c w : Fin (6 * t) → F) :
    outN (6 * t) (by omega) name c w =
      Qmap t (evenLane t ht w) (oddLane t ht w) + Lbase t ht name w + cbase t ht name c := by
  funext i
  dsimp only [outN, Lbase, cbase, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
  rw [Qmap_even_odd t ht w i]
  have hy : ∀ j : Fin (6 * t),
      rotN (6 * t) (by omega) 3 w j + name j +
      (rotN (6 * t) (by omega) 3 w (ixN (6 * t) (by omega) (j.val + 2)) +
        name (ixN (6 * t) (by omega) (j.val + 2))) +
      (rotN (6 * t) (by omega) 3 w (ixN (6 * t) (by omega) (j.val + 6 * t - 2)) +
        name (ixN (6 * t) (by omega) (j.val + 6 * t - 2))) =
      mixN (6 * t) (by omega) w j +
      (name j + name (ixN (6 * t) (by omega) (j.val + 2)) +
        name (ixN (6 * t) (by omega) (j.val + 6 * t - 2))) := by
    intro j; dsimp only [mixN]; abel
  rw [hy i, hy (ixN (6 * t) (by omega) (i.val + 1)), hy (ixN (6 * t) (by omega) (i.val + 2))]
  have hexp := z2_out_expand
    (mixN (6 * t) (by omega) w i)
    (mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (i.val + 1)))
    (mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (i.val + 2)))
    (name i + name (ixN (6 * t) (by omega) (i.val + 2)) +
      name (ixN (6 * t) (by omega) (i.val + 6 * t - 2)))
    (name (ixN (6 * t) (by omega) (i.val + 1)) +
      name (ixN (6 * t) (by omega) ((ixN (6 * t) (by omega) (i.val + 1)).val + 2)) +
      name (ixN (6 * t) (by omega) ((ixN (6 * t) (by omega) (i.val + 1)).val + 6 * t - 2)))
    (name (ixN (6 * t) (by omega) (i.val + 2)) +
      name (ixN (6 * t) (by omega) ((ixN (6 * t) (by omega) (i.val + 2)).val + 2)) +
      name (ixN (6 * t) (by omega) ((ixN (6 * t) (by omega) (i.val + 2)).val + 6 * t - 2)))
  rw [hexp]
  abel

noncomputable def runPref (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F)
    (r : ℕ) (w : Fin n → F) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ((List.finRange h).take r).foldl (fun z i => 2 * z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)

lemma runPref_eq_iff (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F)
    (w0 w : Fin n → F) (r : ℕ) : r ≤ h →
    (runPref n h ask r w = runPref n h ask r w0 ↔
      ∀ j : Fin h, j.val < r → ask j (runPref n h ask j.val w0) w =
        ask j (runPref n h ask j.val w0) w0) := by
  induction r with
  | zero =>
    intro _; simp [runPref]
  | succ r ih =>
    intro hr
    have hrh : r < h := by omega
    have hlt : r < (List.finRange h).length := by rw [List.length_finRange]; exact hrh
    have htake : (List.finRange h).take (r + 1) =
        (List.finRange h).take r ++ [(List.finRange h)[r]] :=
      List.take_succ_eq_append_getElem hlt
    have hget : (List.finRange h)[r] = (⟨r, hrh⟩ : Fin h) := List.getElem_finRange hlt
    have hstep : ∀ u : Fin n → F,
        runPref n h ask (r + 1) u =
          @HAdd.hAdd ℕ ℕ ℕ _ (2 * runPref n h ask r u)
            (@ite ℕ (ask ⟨r, hrh⟩ (runPref n h ask r u) u = 0) (Classical.propDecidable _) 0 1) := by
      intro u
      dsimp only [runPref]
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hget]
      rfl
    rw [hstep w, hstep w0, two_mul_add_bit_eq, ih (by omega)]
    constructor
    · rintro ⟨hprev, hcur⟩ j hj
      by_cases hjr : j.val < r
      · exact hprev j hjr
      · have hjeq : j = ⟨r, hrh⟩ := Fin.ext (by dsimp only; omega)
        have hpref : runPref n h ask r w = runPref n h ask r w0 := (ih (by omega)).mpr hprev
        rw [hpref] at hcur
        rw [hjeq]
        exact (z2_eq_iff_zero _ _).mp hcur
    · intro hall
      have hprev : ∀ j : Fin h, j.val < r →
          ask j (runPref n h ask j.val w0) w = ask j (runPref n h ask j.val w0) w0 :=
        fun j hj => hall j (by omega)
      refine ⟨hprev, ?_⟩
      have hpref : runPref n h ask r w = runPref n h ask r w0 := (ih (by omega)).mpr hprev
      rw [hpref]
      exact (z2_eq_iff_zero _ _).mpr (hall ⟨r, hrh⟩ (Nat.lt_succ_self r))

lemma runN_fiber_coset (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F) (w0 : Fin n → F) :
    ∃ K : Submodule F (Fin n → F),
      n ≤ Module.finrank F K + h ∧
      ∀ w : Fin n → F, runN n h ask w = runN n h ask w0 ↔ w + w0 ∈ K := by
  let Psi : (Fin n → F) →ₗ[F] (Fin h → F) :=
    { toFun := fun w j => ask j (runPref n h ask j.val w0) w
      map_add' := fun w1 w2 => by funext j; exact map_add _ w1 w2
      map_smul' := fun c w => by funext j; exact map_smul _ c w }
  refine ⟨LinearMap.ker Psi, ?_, ?_⟩
  · have hrk := LinearMap.finrank_range_add_finrank_ker Psi
    rw [Module.finrank_fin_fun] at hrk
    have hle : Module.finrank F Psi.range ≤ h := by
      simpa only [Module.finrank_fin_fun] using Submodule.finrank_le Psi.range
    omega
  · intro w
    have heq : ∀ u, runN n h ask u = runPref n h ask h u := by
      intro u
      dsimp only [runN, runPref]
      rw [List.take_of_length_le (by rw [List.length_finRange])]
    rw [heq w, heq w0, runPref_eq_iff n h ask w0 w h (le_refl h)]
    rw [LinearMap.mem_ker]
    constructor
    · intro hall
      funext j
      dsimp only [Psi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      rw [map_add, hall j j.isLt, z2_add_self]
    · intro hker j _
      have hj := congrFun hker j
      dsimp only [Psi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hj
      rw [map_add] at hj
      calc ask j (runPref n h ask j.val w0) w
          = ask j (runPref n h ask j.val w0) w +
              (ask j (runPref n h ask j.val w0) w0 + ask j (runPref n h ask j.val w0) w0) := by
                rw [z2_add_self, add_zero]
        _ = (ask j (runPref n h ask j.val w0) w + ask j (runPref n h ask j.val w0) w0) +
              ask j (runPref n h ask j.val w0) w0 := by rw [add_assoc]
        _ = ask j (runPref n h ask j.val w0) w0 := by rw [hj, zero_add]

lemma double_count_quadratic (t : ℕ) (ht : 0 < t) [NeZero (3 * t)]
    (K : Submodule F (Fin (6 * t) → F))
    (L : (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F)) (d : Fin (6 * t) → F) :
    let KZ : Submodule F (Fin (6 * t) → F) := K ⊓ LinearMap.ker (evenLane t ht)
    Nat.card KZ * Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d} ≤
      Nat.card {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = 0} := by
  classical
  intro KZ
  let G : K → Prop := fun x => Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d
  have hstep1 : Nat.card KZ * Nat.card {x : K // G x} ≤
      Nat.card {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = L p.2.1} := by
    have e1 : KZ × {x : K // G x} ≃ {q : K × K // G q.2 ∧ q.2.1 + q.1.1 ∈ KZ} :=
      { toFun := fun p => ⟨(⟨p.2.1.1 + p.1.1, K.add_mem p.2.1.2 p.1.2.1⟩, p.2.1), ⟨p.2.2, by
          have : p.2.1.1 + (p.2.1.1 + p.1.1) = p.1.1 := by
            rw [← add_assoc, vec_add_self, zero_add]
          rw [this]; exact p.1.2⟩⟩
        invFun := fun q => (⟨q.1.2.1 + q.1.1.1, q.2.2⟩, ⟨q.1.2, q.2.1⟩)
        left_inv := fun p => by
          apply Prod.ext
          · apply Subtype.ext; dsimp only
            rw [← add_assoc, vec_add_self, zero_add]
          · rfl
        right_inv := fun q => by
          apply Subtype.ext; apply Prod.ext
          · apply Subtype.ext; dsimp only
            rw [← add_assoc, vec_add_self, zero_add]
          · rfl }
    rw [← Nat.card_prod, Nat.card_congr e1]
    let _ : Fintype K := Fintype.ofFinite K
    let _ : Fintype KZ := Fintype.ofFinite KZ
    have hs1 : Nat.card {q : K × K // G q.2 ∧ q.2.1 + q.1.1 ∈ KZ} =
        ∑ k : K, Nat.card {g : K // G g ∧ g.1 + k.1 ∈ KZ} := by
      have e : {q : K × K // G q.2 ∧ q.2.1 + q.1.1 ∈ KZ} ≃
          Σ k : K, {g : K // G g ∧ g.1 + k.1 ∈ KZ} :=
        { toFun := fun q => ⟨q.1.1, ⟨q.1.2, q.2⟩⟩
          invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun _ _ => Fintype.card_eq_nat_card)
    have hs2 : Nat.card {p : K × KZ //
          Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = L p.2.1} =
        ∑ k : K, Nat.card {κ : KZ //
          Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = L κ.1} := by
      have e : {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = L p.2.1} ≃
          Σ k : K, {κ : KZ // Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = L κ.1} :=
        { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
          invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun _ _ => Fintype.card_eq_nat_card)
    rw [hs1, hs2]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rcases isEmpty_or_nonempty {g : K // G g ∧ g.1 + k.1 ∈ KZ} with hE | ⟨⟨g0, hg0, hm0⟩⟩
    · rw [Nat.card_of_isEmpty]; exact Nat.zero_le _
    · have hmem : ∀ g : {g : K // G g ∧ g.1 + k.1 ∈ KZ}, g.1.1 + g0.1 ∈ KZ := by
        intro g
        have hsum : (g.1.1 + k.1) + (g0.1 + k.1) = g.1.1 + g0.1 := by
          have : (g.1.1 + k.1) + (g0.1 + k.1) = g.1.1 + g0.1 + (k.1 + k.1) := by abel
          rw [this, vec_add_self, add_zero]
        rw [← hsum]
        exact KZ.add_mem g.2.2 hm0
      refine Nat.card_le_card_of_injective (fun g => ⟨⟨g.1.1 + g0.1, hmem g⟩, ?_⟩) ?_
      · have he1 : evenLane t ht g.1.1 = evenLane t ht k.1 := by
          have hz : evenLane t ht (g.1.1 + k.1) = 0 := LinearMap.mem_ker.mp g.2.2.2
          rw [map_add] at hz
          calc evenLane t ht g.1.1
              = evenLane t ht g.1.1 + (evenLane t ht k.1 + evenLane t ht k.1) := by
                  rw [vec_add_self, add_zero]
            _ = (evenLane t ht g.1.1 + evenLane t ht k.1) + evenLane t ht k.1 := by rw [add_assoc]
            _ = evenLane t ht k.1 := by rw [hz, zero_add]
        have he0 : evenLane t ht g0.1 = evenLane t ht k.1 := by
          have hz : evenLane t ht (g0.1 + k.1) = 0 := LinearMap.mem_ker.mp hm0.2
          rw [map_add] at hz
          calc evenLane t ht g0.1
              = evenLane t ht g0.1 + (evenLane t ht k.1 + evenLane t ht k.1) := by
                  rw [vec_add_self, add_zero]
            _ = (evenLane t ht g0.1 + evenLane t ht k.1) + evenLane t ht k.1 := by rw [add_assoc]
            _ = evenLane t ht k.1 := by rw [hz, zero_add]
        show Qmap t (evenLane t ht k.1) (oddLane t ht (g.1.1 + g0.1)) = L (g.1.1 + g0.1)
        rw [map_add, map_add, map_add, ← he1, g.2.1, he1, ← he0, hg0]
        have : (L g.1.1 + d) + (L g0.1 + d) = L g.1.1 + L g0.1 + (d + d) := by abel
        rw [this, vec_add_self, add_zero]
      · intro g1 g2 heq
        have h1 : g1.1.1 + g0.1 = g2.1.1 + g0.1 := congrArg (fun x => x.1.1) heq
        exact Subtype.ext (Subtype.ext (add_right_cancel h1))
  have hstep2 :
      Nat.card {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = L p.2.1} ≤
      Nat.card {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = 0} := by
    let _ : Fintype K := Fintype.ofFinite K
    let _ : Fintype KZ := Fintype.ofFinite KZ
    have hs1 : Nat.card {p : K × KZ //
          Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = L p.2.1} =
        ∑ κ : KZ, Nat.card {k : K //
          Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = L κ.1} := by
      have e : {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = L p.2.1} ≃
          Σ κ : KZ, {k : K // Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = L κ.1} :=
        { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
          invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun _ _ => Fintype.card_eq_nat_card)
    have hs2 : Nat.card {p : K × KZ //
          Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = 0} =
        ∑ κ : KZ, Nat.card {k : K //
          Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = 0} := by
      have e : {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = 0} ≃
          Σ κ : KZ, {k : K // Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = 0} :=
        { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
          invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun _ _ => Fintype.card_eq_nat_card)
    rw [hs1, hs2]
    refine Finset.sum_le_sum (fun κ _ => ?_)
    rcases isEmpty_or_nonempty {k : K // Qmap t (evenLane t ht k.1) (oddLane t ht κ.1) = L κ.1}
      with hE | ⟨⟨k0, hk0⟩⟩
    · rw [Nat.card_of_isEmpty]; exact Nat.zero_le _
    · refine Nat.card_le_card_of_injective (fun k => ⟨k.1 + k0, ?_⟩) ?_
      · show Qmap t (evenLane t ht (k.1.1 + k0.1)) (oddLane t ht κ.1) = 0
        rw [map_add, map_add, LinearMap.add_apply, k.2, hk0, vec_add_self]
      · intro k1 k2 heq
        exact Subtype.ext (add_right_cancel (congrArg Subtype.val heq))
  exact hstep1.trans hstep2

-- The abstract rank intersection proof is from lean/PEqualNP/Outside/L_lib_1082.lean
-- at 89d2fd4116d94c448b241700eb4b4b27f657d92a.
section Abs

open Module

variable {ι : Type*} [DecidableEq ι]

def IsRk (r : Finset ι → ℕ) : Prop :=
  r ∅ = 0 ∧ (∀ A B : Finset ι, A ⊆ B → r A ≤ r B) ∧
  (∀ A B : Finset ι, r (A ∪ B) + r (A ∩ B) ≤ r A + r B) ∧ (∀ a : ι, r {a} ≤ 1)

theorem rk_insert_le {r : Finset ι → ℕ} (h : IsRk r) (a : ι) (A : Finset ι) :
    r (insert a A) ≤ r {a} + r A := by
  have := h.2.2.1 {a} A
  rw [← Finset.insert_eq] at this
  omega

theorem rk_union_le {r : Finset ι → ℕ} (h : IsRk r) (A D : Finset ι) :
    r (A ∪ D) ≤ r A + D.card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert x D hx ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hx]
    have h1 := rk_insert_le h x (A ∪ D)
    have h2 := h.2.2.2 x
    omega

theorem rk_le_sum {r : Finset ι → ℕ} (h : IsRk r) (A : Finset ι) :
    r A ≤ ∑ e ∈ A, r {e} := by
  induction A using Finset.induction_on with
  | empty => simp [h.1]
  | insert x A hx ih =>
    rw [Finset.sum_insert hx]
    have h1 := rk_insert_le h x A
    omega

theorem weak {r1 r2 : Finset ι → ℕ} (h1 : IsRk r1) (h2 : IsRk r2) (S A E : Finset ι)
    (hS : S ⊆ E) (i1 : r1 S = S.card) (i2 : r2 S = S.card) :
    S.card ≤ r1 A + r2 (E \ A) := by
  have e1 : S ∩ A ∪ S \ A = S := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have e2 : S \ A ∪ S ∩ A = S := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have a1 := rk_union_le h1 (S ∩ A) (S \ A)
  have b1 := rk_union_le h2 (S \ A) (S ∩ A)
  rw [e1] at a1
  rw [e2] at b1
  have a2 := h1.2.1 (S ∩ A) A Finset.inter_subset_right
  have b2 := h2.2.1 (S \ A) (E \ A) (Finset.sdiff_subset_sdiff hS le_rfl)
  have c := Finset.card_inter_add_card_sdiff S A
  omega

theorem contr {r : Finset ι → ℕ} (h : IsRk r) (e : ι) (he : r {e} = 1) :
    IsRk (fun A => r (insert e A) - 1) := by
  have lb : ∀ A : Finset ι, 1 ≤ r (insert e A) := fun A => by
    have := h.2.1 {e} (insert e A) (by simp)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [he]
  · intro A B hAB
    have := h.2.1 _ _ (Finset.insert_subset_insert e hAB)
    simp only
    omega
  · intro A B
    have := h.2.2.1 (insert e A) (insert e B)
    rw [← Finset.insert_union_distrib, ← Finset.insert_inter_distrib] at this
    have := lb A
    have := lb B
    have := lb (A ∪ B)
    have := lb (A ∩ B)
    simp only
    omega
  · intro a
    have h1 := rk_insert_le h e {a}
    have h2 := h.2.2.2 a
    simp only
    omega

theorem inter (n : ℕ) : ∀ (r1 r2 : Finset ι → ℕ), IsRk r1 → IsRk r2 → ∀ E : Finset ι,
    E.card = n → ∃ S ⊆ E, ∃ C ⊆ E, r1 S = S.card ∧ r2 S = S.card ∧
      r1 C + r2 (E \ C) = S.card := by
  induction n with
  | zero =>
    intro r1 r2 h1 h2 E hE
    rw [Finset.card_eq_zero] at hE
    subst hE
    exact ⟨∅, subset_refl _, ∅, subset_refl _, by simp [h1.1, h2.1]⟩
  | succ n ih =>
    intro r1 r2 h1 h2 E hE
    by_cases hx : ∃ e ∈ E, r1 {e} = 1 ∧ r2 {e} = 1
    · obtain ⟨e, heE, he1, he2⟩ := hx
      have hcard : (E.erase e).card = n := by rw [Finset.card_erase_of_mem heE]; omega
      obtain ⟨S1, hS1, A, hA, i1, j1, c1⟩ := ih r1 r2 h1 h2 _ hcard
      obtain ⟨S2, hS2, B, hB, i2, j2, c2⟩ :=
        ih _ _ (contr h1 e he1) (contr h2 e he2) _ hcard
      obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image E.powerset
        (fun C => r1 C + r2 (E \ C)) ⟨∅, Finset.empty_mem_powerset E⟩
      rw [Finset.mem_powerset] at hC
      have heS2 : e ∉ S2 := fun h => by have := hS2 h; simp at this
      have heA : e ∉ A := fun h => by have := hA h; simp at this
      have heB : e ∉ B := fun h => by have := hB h; simp at this
      have lb1 := h1.2.1 {e} (insert e S2) (by simp)
      have lb2 := h2.2.1 {e} (insert e S2) (by simp)
      have hS1E : S1 ⊆ E := hS1.trans (Finset.erase_subset e E)
      have hS2E : insert e S2 ⊆ E :=
        Finset.insert_subset heE (hS2.trans (Finset.erase_subset e E))
      have k1 : r1 (insert e S2) = (insert e S2).card := by
        rw [Finset.card_insert_of_notMem heS2]; omega
      have k2 : r2 (insert e S2) = (insert e S2).card := by
        rw [Finset.card_insert_of_notMem heS2]; omega
      by_cases hp : r1 C + r2 (E \ C) ≤ S1.card
      · refine ⟨S1, hS1E, C, hC, i1, j1, ?_⟩
        have := weak h1 h2 S1 C E hS1E i1 j1
        omega
      by_cases hq : r1 C + r2 (E \ C) ≤ S2.card + 1
      · refine ⟨insert e S2, hS2E, C, hC, k1, k2, ?_⟩
        have := weak h1 h2 _ C E hS2E k1 k2
        rw [Finset.card_insert_of_notMem heS2] at this ⊢
        omega
      exfalso
      have hAE : A ⊆ E := hA.trans (Finset.erase_subset e E)
      have hBE : insert e B ⊆ E := Finset.insert_subset heE (hB.trans (Finset.erase_subset e E))
      have s1 := h1.2.2.1 A (insert e B)
      have s2 := h2.2.2.1 ((E.erase e) \ A) (E \ B)
      have m1 := hmin (A ∩ insert e B)
        (Finset.mem_powerset.2 (Finset.inter_subset_left.trans hAE))
      have m2 := hmin (A ∪ insert e B) (Finset.mem_powerset.2 (Finset.union_subset hAE hBE))
      have q1 : (E.erase e \ A) ∪ (E \ B) = E \ (A ∩ insert e B) := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heA, heB, heE]
        · simp [hxe]; tauto
      have q2 : (E.erase e \ A) ∩ (E \ B) = E \ (A ∪ insert e B) := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heA, heB, heE]
        · simp [hxe]; tauto
      have q3 : insert e (E.erase e \ B) = E \ B := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heB, heE]
        · simp [hxe]
      rw [q1, q2] at s2
      rw [q3] at c2
      have lb3 := h1.2.1 {e} (insert e B) (by simp)
      have lb4 := h2.2.1 {e} (E \ B) (by simp [heE, heB])
      omega
    · simp only [not_exists, not_and] at hx
      refine ⟨∅, Finset.empty_subset _, E.filter (fun e => r1 {e} = 0),
        Finset.filter_subset _ _, by simp [h1.1], by simp [h2.1], ?_⟩
      have a := rk_le_sum h1 (E.filter (fun e => r1 {e} = 0))
      have b := rk_le_sum h2 (E \ E.filter (fun e => r1 {e} = 0))
      rw [Finset.sum_eq_zero (fun i hi => (Finset.mem_filter.1 hi).2)] at a
      rw [Finset.sum_eq_zero] at b
      · simp only [Finset.card_empty]; omega
      · intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hi
        have h3 := h1.2.2.2 i
        have h4 := h2.2.2.2 i
        have h5 := hx i hi.1
        have h6 := hi.2 hi.1
        omega

end Abs

section Lin

open Module

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  {ι : Type*} [DecidableEq ι]

noncomputable def lrk (u : ι → V) (A : Finset ι) : ℕ :=
  finrank F (Submodule.span F (u '' (A : Set ι)))

theorem lrk_isRk [FiniteDimensional F V] (u : ι → V) : IsRk (lrk (F := F) u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [lrk]
  · intro A B hAB
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 hAB)))
  · intro A B
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (u '' (A : Set ι)))
      (Submodule.span F (u '' (B : Set ι)))
    have e : Submodule.span F (u '' ((A ∪ B : Finset ι) : Set ι)) =
        Submodule.span F (u '' (A : Set ι)) ⊔ Submodule.span F (u '' (B : Set ι)) := by
      rw [Finset.coe_union, Set.image_union, Submodule.span_union]
    have hle : Submodule.span F (u '' ((A ∩ B : Finset ι) : Set ι)) ≤
        Submodule.span F (u '' (A : Set ι)) ⊓ Submodule.span F (u '' (B : Set ι)) :=
      le_inf (Submodule.span_mono (Set.image_mono (by simp)))
        (Submodule.span_mono (Set.image_mono (by simp)))
    have := Submodule.finrank_mono hle
    unfold lrk
    rw [e]
    omega
  · intro a
    unfold lrk
    rw [Finset.coe_singleton, Set.image_singleton]
    by_cases hv : u a = 0
    · rw [hv, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]; omega
    · rw [finrank_span_singleton hv]

theorem li_iff (u : ι → V) (S : Finset ι) :
    LinearIndependent F (fun i : S => u i.val) ↔ lrk (F := F) u S = S.card := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_coe]
  have : Set.range (fun i : S => u i.val) = u '' (S : Set ι) := by
    ext x; simp
  unfold Set.finrank lrk
  rw [this]
  constructor <;> intro h <;> omega

end Lin
-- Counting and dual projection tools are from lean/PEqualNP/Outside/L_lib_1064.lean
-- at 89d2fd4116d94c448b241700eb4b4b27f657d92a.
lemma card_good_pairs_indep (k : ℕ) :
    (Finset.univ.filter (fun uv : (Fin k → F) × (Fin k → F) =>
      ∀ c : Fin k, uv.1 c * uv.2 c = 0)).card = 3 ^ k := by
  classical
  let eEquiv : ((Fin k → F) × (Fin k → F)) ≃ (Fin k → F × F) :=
    { toFun := fun uv c => (uv.1 c, uv.2 c)
      invFun := fun f => (fun c => (f c).1, fun c => (f c).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbij : (Finset.univ.filter (fun uv : (Fin k → F) × (Fin k → F) =>
        ∀ c : Fin k, uv.1 c * uv.2 c = 0)).card =
      (Finset.univ.filter (fun f : Fin k → F × F => ∀ c : Fin k, (f c).1 * (f c).2 = 0)).card := by
    refine Finset.card_bij (fun uv _ => eEquiv uv) ?_ ?_ ?_
    · intro uv huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
      exact huv
    · intro u _ v _ h; exact eEquiv.injective h
    · intro f hf
      refine ⟨eEquiv.symm f, ?_, eEquiv.apply_symm_apply f⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact hf
  rw [hbij]
  let S0 : Finset (F × F) := Finset.univ.filter (fun p : F × F => p.1 * p.2 = 0)
  have hS0 : S0.card = 3 := by decide
  have hpi : Finset.univ.filter (fun f : Fin k → F × F => ∀ c : Fin k, (f c).1 * (f c).2 = 0) =
      Fintype.piFinset (fun _ : Fin k => S0) := by
    ext f; simp [S0, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset, Finset.prod_const, hS0, Finset.card_univ, Fintype.card_fin]

lemma card_linear_map_domain {U V : Type*} [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (φ : U →ₗ[F] V) (hsurj : Function.Surjective φ) :
    Fintype.card U = Fintype.card V * Nat.card (LinearMap.ker φ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hfiber : ∀ v : V, (Finset.univ.filter (fun u : U => φ u = v)).card =
      Fintype.card (LinearMap.ker φ) := by
    intro v
    obtain ⟨u0, hu0⟩ := hsurj v
    refine Finset.card_bij (fun u hu => (⟨u - u0, by
        rw [LinearMap.mem_ker, map_sub, (Finset.mem_filter.mp hu).2, hu0]
        exact sub_self v⟩ : LinearMap.ker φ)) ?_ ?_ ?_
    · intro u _; exact Finset.mem_univ _
    · intro u1 _ u2 _ h
      have : u1 - u0 = u2 - u0 := congrArg Subtype.val h
      exact sub_left_inj.mp this
    · intro w _
      refine ⟨w.1 + u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Subtype.ext (by abel)⟩
      rw [map_add, LinearMap.mem_ker.mp w.2, zero_add, hu0]
  have hpart : Fintype.card U = ∑ v : V, (Finset.univ.filter (fun u : U => φ u = v)).card := by
    rw [← Finset.card_univ, ← Finset.card_biUnion]
    · congr 1; ext u; simp
    · intro v1 _ v2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro u h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart]
  simp_rw [hfiber]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma card_hits_le_of_good {P Q : Type*} [AddCommGroup P] [Module F P] [Fintype P]
    [AddCommGroup Q] [Module F Q] [Fintype Q]
    {V1 V2 : Type*} [AddCommGroup V1] [Module F V1] [Fintype V1]
    [AddCommGroup V2] [Module F V2] [Fintype V2]
    (φ : P →ₗ[F] V1) (ψ : Q →ₗ[F] V2)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (pred : P × Q → Prop) (G : Finset (V1 × V2))
    (himp : ∀ w : P × Q, pred w → (φ w.1, ψ w.2) ∈ G) :
    Fintype.card V1 * Fintype.card V2 * Nat.card {w : P × Q // pred w} ≤
      G.card * Nat.card P * Nat.card Q := by
  classical
  have hP := card_linear_map_domain φ hφ
  have hQ := card_linear_map_domain ψ hψ
  rw [Nat.card_eq_fintype_card] at hP hQ
  let Φ : P × Q →ₗ[F] V1 × V2 := LinearMap.prodMap φ ψ
  have hΦ : Function.Surjective Φ := fun ⟨v1, v2⟩ => by
    obtain ⟨x, hx⟩ := hφ v1; obtain ⟨y, hy⟩ := hψ v2
    exact ⟨(x, y), Prod.ext hx hy⟩
  have hker : Fintype.card (LinearMap.ker Φ) =
      Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ) := by
    have heq : Fintype.card (LinearMap.ker Φ) =
        Fintype.card (LinearMap.ker φ × LinearMap.ker ψ) :=
      Fintype.card_congr
        { toFun := fun z => (⟨z.1.1, (Prod.ext_iff.mp (LinearMap.mem_ker.mp z.2)).1⟩,
            ⟨z.1.2, (Prod.ext_iff.mp (LinearMap.mem_ker.mp z.2)).2⟩)
          invFun := fun z => ⟨(z.1.1, z.2.1), LinearMap.mem_ker.mpr
            (Prod.ext (LinearMap.mem_ker.mp z.1.2) (LinearMap.mem_ker.mp z.2.2))⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [heq, Fintype.card_prod]
  have hfiber : ∀ p : V1 × V2, (Finset.univ.filter (fun w : P × Q => Φ w = p)).card =
      Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ) := by
    intro p
    obtain ⟨w0, hw0⟩ := hΦ p
    rw [← hker]
    refine Finset.card_bij (fun w hw => (⟨w - w0, by
        rw [LinearMap.mem_ker, map_sub, (Finset.mem_filter.mp hw).2, hw0]; exact sub_self p⟩ : LinearMap.ker Φ)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro w1 _ w2 _ h; exact sub_left_inj.mp (congrArg Subtype.val h)
    · intro z _
      refine ⟨z.1 + w0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Subtype.ext (by abel)⟩
      rw [map_add, LinearMap.mem_ker.mp z.2, zero_add, hw0]
  have hhits : Nat.card {w : P × Q // pred w} ≤
      G.card * (Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsub : Finset.univ.filter pred ⊆ G.biUnion (fun p => Finset.univ.filter (fun w : P × Q => Φ w = p)) := by
      intro w hw
      rw [Finset.mem_biUnion]
      exact ⟨Φ w, himp w (Finset.mem_filter.mp hw).2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hle := Finset.card_le_card hsub
    have hbu : (G.biUnion (fun p => Finset.univ.filter (fun w : P × Q => Φ w = p))).card ≤
        ∑ p ∈ G, (Finset.univ.filter (fun w : P × Q => Φ w = p)).card := Finset.card_biUnion_le
    have hsum : ∑ p ∈ G, (Finset.univ.filter (fun w : P × Q => Φ w = p)).card =
        G.card * (Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ)) := by
      simp_rw [hfiber]; rw [Finset.sum_const, smul_eq_mul]
    exact (hle.trans hbu).trans_eq hsum
  rw [Nat.card_eq_fintype_card (α := P), Nat.card_eq_fintype_card (α := Q), hP, hQ]
  have hmul := Nat.mul_le_mul_left (Fintype.card V1 * Fintype.card V2) hhits
  calc Fintype.card V1 * Fintype.card V2 * Nat.card {w : P × Q // pred w}
      ≤ Fintype.card V1 * Fintype.card V2 *
        (G.card * (Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ))) := hmul
    _ = G.card * (Fintype.card V1 * Fintype.card (LinearMap.ker φ)) *
        (Fintype.card V2 * Fintype.card (LinearMap.ker ψ)) := by ring
lemma finrank_dualAnnihilator_add {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    (W : Submodule F U) :
    Module.finrank F W.dualAnnihilator + Module.finrank F W = Module.finrank F U := by
  obtain ⟨W', hcompl⟩ := Submodule.exists_isCompl W
  let proj : U →ₗ[F] W := W.linearProjOfIsCompl W' hcompl
  have hsurj : Function.Surjective (LinearMap.dualMap W.subtype) := by
    intro α
    refine ⟨α.comp proj, LinearMap.ext fun w => ?_⟩
    rw [LinearMap.dualMap_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    exact congrArg α (Submodule.linearProjOfIsCompl_apply_left hcompl w)
  have hker : LinearMap.ker (LinearMap.dualMap W.subtype) = W.dualAnnihilator := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
    constructor
    · intro h u hu
      exact LinearMap.congr_fun h ⟨u, hu⟩
    · intro h
      apply LinearMap.ext; intro w
      exact h w.1 w.2
  have hrk := LinearMap.finrank_range_add_finrank_ker (LinearMap.dualMap W.subtype)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrk
  have hWdual : Module.finrank F (Module.Dual F W) = Module.finrank F W := Subspace.dual_finrank_eq
  have hUdual : Module.finrank F (Module.Dual F U) = Module.finrank F U := Subspace.dual_finrank_eq
  omega

lemma linearIndependent_dual_iff_surjective {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    {k : ℕ} (f : Fin k → U →ₗ[F] F) :
    LinearIndependent F f → Function.Surjective (fun u : U => fun c : Fin k => f c u) := by
  intro hind
  let φ : U →ₗ[F] (Fin k → F) := LinearMap.pi f
  change Function.Surjective φ
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hdual_inj : Function.Injective (LinearMap.dualMap φ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro α hα
    rw [LinearMap.mem_ker] at hα
    have hsum : ∑ c : Fin k, α (Pi.single c 1) • f c = 0 := by
      apply LinearMap.ext; intro u
      have hu := LinearMap.congr_fun hα u
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hu
      have hdecomp : φ u = ∑ c : Fin k, f c u • Pi.single c (1 : F) := by
        ext c'
        simp [φ, Pi.single_apply]
      rw [hdecomp, map_sum] at hu
      simp only [map_smul, smul_eq_mul] at hu
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      rw [← hu]
      refine Finset.sum_congr rfl fun c _ => mul_comm _ _
    have hc0 := Fintype.linearIndependent_iff.mp hind (fun c => α (Pi.single c 1)) hsum
    apply LinearMap.ext; intro v
    have hv : v = ∑ c : Fin k, v c • Pi.single c (1 : F) := by
      ext c'; simp [Pi.single_apply]
    rw [hv, map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_smul, hc0 c, smul_zero]
  have h1 : Module.finrank F (Module.Dual F (Fin k → F)) =
      Module.finrank F (LinearMap.range (LinearMap.dualMap φ)) :=
    (LinearEquiv.ofInjective _ hdual_inj).finrank_eq
  have h2 : Module.finrank F (LinearMap.range (LinearMap.dualMap φ)) ≤
      Module.finrank F (LinearMap.range φ) := by
    have hker := LinearMap.finrank_range_add_finrank_ker φ
    have hsub : LinearMap.range (LinearMap.dualMap φ) ≤ (LinearMap.ker φ).dualAnnihilator := by
      rintro _ ⟨α, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro u hu
      simp [LinearMap.dualMap_apply, LinearMap.mem_ker.mp hu]
    have hle1 := Submodule.finrank_mono hsub
    have hann := finrank_dualAnnihilator_add (LinearMap.ker φ)
    omega
  have h3 := Submodule.finrank_le (LinearMap.range φ)
  have h4 : Module.finrank F (Module.Dual F (Fin k → F)) = Module.finrank F (Fin k → F) :=
    Subspace.dual_finrank_eq
  omega

lemma finrank_span_eval_eq_sub_ker {E U : Type*} [DecidableEq E]
    [AddCommGroup U] [Module F U] [Module.Finite F U]
    (f : E → U →ₗ[F] F) (A : Finset E) :
    Module.finrank F (Submodule.span F (f '' (A : Set E))) +
      Module.finrank F (⨅ e ∈ A, LinearMap.ker (f e) : Submodule F U) = Module.finrank F U := by
  classical
  let φ : U →ₗ[F] (A → F) := LinearMap.pi (fun e : A => f e.1)
  have hker : LinearMap.ker φ = (⨅ e ∈ A, LinearMap.ker (f e) : Submodule F U) := by
    ext u
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, φ]
    constructor
    · intro h e he
      exact congrFun h ⟨e, he⟩
    · intro h
      funext e
      exact h e.1 e.2
  have hdual_range : LinearMap.range (LinearMap.dualMap φ) = Submodule.span F (f '' (A : Set E)) := by
    apply le_antisymm
    · rintro _ ⟨α, rfl⟩
      have hdecomp : LinearMap.dualMap φ α = ∑ e : A, α (Pi.single e 1) • f e.1 := by
        apply LinearMap.ext; intro u
        simp only [LinearMap.dualMap_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        have hu : φ u = ∑ e : A, f e.1 u • Pi.single e (1 : F) := by
          ext e'; simp [φ, Pi.single_apply]
        rw [hu, map_sum]
        refine Finset.sum_congr rfl fun e _ => by rw [map_smul, smul_eq_mul, mul_comm]
      rw [hdecomp]
      apply Submodule.sum_mem
      intro e _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.1, e.2, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      refine ⟨LinearMap.proj ⟨e, he⟩, LinearMap.ext fun u => rfl⟩
  have hker_eq : LinearMap.range (LinearMap.dualMap φ) = (LinearMap.ker φ).dualAnnihilator := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨α, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro u hu; simp [LinearMap.dualMap_apply, LinearMap.mem_ker.mp hu]
    · have h1 := LinearMap.finrank_range_add_finrank_ker φ
      have h2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.dualMap φ)
      have hann := finrank_dualAnnihilator_add (LinearMap.ker φ)
      have hAdual : Module.finrank F (Module.Dual F (A → F)) = Module.finrank F (A → F) := Subspace.dual_finrank_eq
      have hkerD : LinearMap.ker (LinearMap.dualMap φ) = (LinearMap.range φ).dualAnnihilator := by
        ext α
        simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator, LinearMap.mem_range]
        constructor
        · rintro h _ ⟨u, rfl⟩; exact LinearMap.congr_fun h u
        · intro h; apply LinearMap.ext; intro u; exact h (φ u) ⟨u, rfl⟩
      have hannR := finrank_dualAnnihilator_add (LinearMap.range φ)
      rw [hkerD] at h2
      omega
  rw [← hdual_range, hker_eq, ← hker]
  exact finrank_dualAnnihilator_add (LinearMap.ker φ)

def widthSixPair (r : ZMod 3) : Lane 6 :=
  fun i => if i.val % 3 = r.val then 1 else 0

def widthSixWord (a b c d : F) : Lane 6 :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then a + d else if i = 4 then b + d else c + d

lemma widthSix_word_of_mem (u : Lane 6) (hu : u ∈ imSub 2) :
    u = widthSixWord (u 0) (u 1) (u 2) (u 2 + u 5) := by
  obtain ⟨h0, h1⟩ := (mem_imSub_iff 2 u).mp hu
  rw [parSum_apply, parSum_apply, z6_filter_0, z6_filter_2,
    Finset.sum_pair z6_0_ne_3, Finset.sum_pair z6_2_ne_5] at h0
  rw [parSum_apply, parSum_apply, z6_filter_1, z6_filter_2,
    Finset.sum_pair z6_1_ne_4, Finset.sum_pair z6_2_ne_5] at h1
  have h3 : u 3 = u 0 + (u 2 + u 5) := by
    calc
      u 3 = u 0 + (u 0 + u 3) := by rw [← add_assoc, z2_add_self, zero_add]
      _ = _ := by rw [h0]
  have h4 : u 4 = u 1 + (u 2 + u 5) := by
    calc
      u 4 = u 1 + (u 1 + u 4) := by rw [← add_assoc, z2_add_self, zero_add]
      _ = _ := by rw [h1]
  have h5 : u 5 = u 2 + (u 2 + u 5) := by rw [← add_assoc, z2_add_self, zero_add]
  funext i
  rcases z6_elems i with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · exact h3
  · exact h4
  · exact h5

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma widthSix_word_compatible : ∀ (a b c d e f g h : F),
    let x := widthSixWord a b c d
    let y := widthSixWord e f g h
    (∀ i : ZMod 6, x i * y i = 0 ∧ x i * y (i - 1) = 0) →
    x = 0 ∨ y = 0 ∨ ∃ r : ZMod 3, x = widthSixPair r ∧ y = widthSixPair (r + 1) := by
  intro a b c d
  rcases z2_eq_zero_or_one a with rfl | rfl <;>
    rcases z2_eq_zero_or_one b with rfl | rfl <;>
    rcases z2_eq_zero_or_one c with rfl | rfl <;>
    rcases z2_eq_zero_or_one d with rfl | rfl <;> decide

lemma widthSix_compatible (u v : Lane 6) (hu : u ∈ imSub 2) (hv : v ∈ imSub 2)
    (h : ∀ i : ZMod 6, u i * v i = 0 ∧ u i * v (i - 1) = 0) :
    u = 0 ∨ v = 0 ∨ ∃ r : ZMod 3, u = widthSixPair r ∧ v = widthSixPair (r + 1) := by
  have eU := widthSix_word_of_mem u hu
  have eV := widthSix_word_of_mem v hv
  rw [eU, eV] at h ⊢
  exact widthSix_word_compatible _ _ _ _ _ _ _ _ h

def widthSixFive (i : Fin 5) : Lane 6 :=
  if i = 0 then 0 else if i = 1 then widthSixPair 0
  else if i = 2 then widthSixPair 1 else if i = 3 then widthSixPair 2
  else widthSixPair 0 + widthSixPair 1

lemma widthSix_five_inj (i j : Fin 5) (h : widthSixFive i = widthSixFive j) : i = j := by
  let decode (w : Lane 6) : Fin 5 :=
    if w 0 = 1 then (if w 1 = 1 then 4 else 1)
    else if w 1 = 1 then 2 else if w 2 = 1 then 3 else 0
  have hinv (k : Fin 5) : decode (widthSixFive k) = k := by
    fin_cases k <;> rfl
  exact (hinv i).symm.trans ((congrArg decode h).trans (hinv j))

lemma widthSix_missing (U : Submodule F (Lane 6)) (hcard : Nat.card U = 4) :
    ∃ r : ZMod 3, widthSixPair r ∉ U := by
  classical
  by_contra hn
  have hall (r : ZMod 3) : widthSixPair r ∈ U := by
    by_contra hr
    exact hn ⟨r, hr⟩
  let f (i : Fin 5) : U := ⟨widthSixFive i, by
    unfold widthSixFive
    split_ifs
    · exact U.zero_mem
    · exact hall 0
    · exact hall 1
    · exact hall 2
    · exact U.add_mem (hall 0) (hall 1)⟩
  have hc := Nat.card_le_card_of_injective f (fun i j h =>
    widthSix_five_inj i j (congrArg Subtype.val h))
  rw [Nat.card_fin, hcard] at hc
  omega

lemma small_upper (U V : Submodule F (Lane 6)) (hU : U ≤ imSub 2) (hV : V ≤ imSub 2)
    (hdim : 6 ≤ Module.finrank F U + Module.finrank F V) :
    64 * Nat.card {p : U × V // ∀ a : ZMod 6,
      p.1.1 a * p.2.1 a = 0 ∧ p.1.1 a * p.2.1 (a - 1) = 0} ≤
      21 * (Nat.card U * Nat.card V) := by
  classical
  let W := {p : U × V // ∀ a : ZMod 6,
    p.1.1 a * p.2.1 a = 0 ∧ p.1.1 a * p.2.1 (a - 1) = 0}
  let E := {r : ZMod 3 // widthSixPair r ∈ U ∧ widthSixPair (r + 1) ∈ V}
  change 64 * Nat.card W ≤ _
  have hex (p : W) (hu : p.1.1 ≠ 0) (hv : p.1.2 ≠ 0) :
      ∃ r : ZMod 3, p.1.1.1 = widthSixPair r ∧ p.1.2.1 = widthSixPair (r + 1) := by
    rcases widthSix_compatible p.1.1.1 p.1.2.1 (hU p.1.1.2) (hV p.1.2.2) p.2 with h | h | h
    · exact (hu (Subtype.ext h)).elim
    · exact (hv (Subtype.ext h)).elim
    · exact h
  let ix (p : W) (hu : p.1.1 ≠ 0) (hv : p.1.2 ≠ 0) : E :=
    ⟨(hex p hu hv).choose, by
      have hs := (hex p hu hv).choose_spec
      exact ⟨by rw [← hs.1]; exact p.1.1.2, by rw [← hs.2]; exact p.1.2.2⟩⟩
  let emb (p : W) : V ⊕ ({u : U // u ≠ 0} ⊕ E) :=
    if hu : p.1.1 = 0 then Sum.inl p.1.2 else Sum.inr
      (if hv : p.1.2 = 0 then Sum.inl ⟨p.1.1, hu⟩ else Sum.inr (ix p hu hv))
  have hinj : Function.Injective emb := by
    intro p q h
    dsimp only [emb] at h
    by_cases hp : p.1.1 = 0 <;> by_cases hq : q.1.1 = 0
    · rw [dif_pos hp, dif_pos hq] at h
      exact Subtype.ext (Prod.ext (hp.trans hq.symm) (Sum.inl.inj h))
    · simp [hp, hq] at h
    · simp [hp, hq] at h
    · rw [dif_neg hp, dif_neg hq] at h
      have h := Sum.inr.inj h
      by_cases hpv : p.1.2 = 0 <;> by_cases hqv : q.1.2 = 0
      · rw [dif_pos hpv, dif_pos hqv] at h
        exact Subtype.ext (Prod.ext (congrArg Subtype.val (Sum.inl.inj h)) (hpv.trans hqv.symm))
      · simp [hpv, hqv] at h
      · simp [hpv, hqv] at h
      · rw [dif_neg hpv, dif_neg hqv] at h
        have hi : (hex p hp hpv).choose = (hex q hq hqv).choose :=
          congrArg Subtype.val (Sum.inr.inj h)
        have hs := (hex p hp hpv).choose_spec
        have ht := (hex q hq hqv).choose_spec
        rw [hi] at hs
        exact Subtype.ext (Prod.ext (Subtype.ext (hs.1.trans ht.1.symm))
          (Subtype.ext (hs.2.trans ht.2.symm)))
  have hcount : Nat.card W ≤ Nat.card V + (Nat.card {u : U // u ≠ 0} + Nat.card E) := by
    simpa only [Nat.card_sum] using (Nat.card_le_card_of_injective emb hinj)
  have hnonzero : Nat.card {u : U // u ≠ 0} = Nat.card U - 1 := by
    let _ : Fintype U := Fintype.ofFinite U
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun u : U => u = 0))
  have hE : Nat.card E ≤ 3 := by
    simpa only [Nat.card_zmod] using
      (Nat.card_le_card_of_injective (Subtype.val : E → ZMod 3) Subtype.val_injective)
  have hEmiss (r : ZMod 3) (hr : ¬(widthSixPair r ∈ U ∧ widthSixPair (r + 1) ∈ V)) :
      Nat.card E ≤ 2 := by
    let _ : Fintype E := Fintype.ofFinite E
    have hlt : Fintype.card E < Fintype.card (ZMod 3) := Fintype.card_subtype_lt hr
    rw [ZMod.card] at hlt
    rw [Nat.card_eq_fintype_card]
    omega
  let dU := Module.finrank F U
  let dV := Module.finrank F V
  change 6 ≤ dU + dV at hdim
  have hi := finrank_imSub_add_two 2 (by decide)
  have hdU : dU ≤ 4 := by
    have hm := Submodule.finrank_mono hU
    change dU ≤ Module.finrank F (imSub 2) at hm
    omega
  have hdV : dV ≤ 4 := by
    have hm := Submodule.finrank_mono hV
    change dV ≤ Module.finrank F (imSub 2) at hm
    omega
  have hpowU : Nat.card U = 2 ^ dU := card_eq_two_pow_finrank
  have hpowV : Nat.card V = 2 ^ dV := card_eq_two_pow_finrank
  have hEU (h : dU = 2) : Nat.card E ≤ 2 := by
    obtain ⟨r, hr⟩ := widthSix_missing U (by rw [hpowU, h]; norm_num)
    exact hEmiss r (fun hh => hr hh.1)
  have hEV (h : dV = 2) : Nat.card E ≤ 2 := by
    obtain ⟨r, hr⟩ := widthSix_missing V (by rw [hpowV, h]; norm_num)
    exact hEmiss (r - 1) (fun hh => hr (by simpa only [sub_add_cancel] using hh.2))
  have hE' : Nat.card E ≤ if dU = 2 ∨ dV = 2 then 2 else 3 := by
    split_ifs with h
    · exact h.elim hEU hEV
    · exact hE
  have hcases : (dU = 2 ∧ dV = 4) ∨ (dU = 3 ∧ dV = 3) ∨ (dU = 3 ∧ dV = 4) ∨
      (dU = 4 ∧ dV = 2) ∨ (dU = 4 ∧ dV = 3) ∨ (dU = 4 ∧ dV = 4) := by omega
  rcases hcases with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
  all_goals
    rw [hnonzero, hpowU, hpowV, hu, hv] at hcount
    rw [hpowU, hpowV, hu, hv]
    rw [hu, hv] at hE'
    norm_num at hcount hE' ⊢
    omega


lemma rect_ceiling (t : ℕ) (ht : 3 ≤ t) [NeZero (3*t)]
    {U V : Submodule F (Lane (3*t))} (hU : U ≤ imSub t) (hV : V ≤ imSub t)
    (S : Submodule F U) (T : Submodule F V) (hS : S ≠ ⊥) (hT : T ≠ ⊥)
    (hzero : ∀ u ∈ S, ∀ v ∈ T, Qmap t u.1 v.1 = 0) :
    Module.finrank F S + Module.finrank F T + 5 ≤ 3*t := by
  let S' := S.map U.subtype
  let T' := T.map V.subtype
  have hS' : S' ≤ imSub t := by rintro _ ⟨u, _, rfl⟩; exact hU u.2
  have hT' : T' ≤ imSub t := by rintro _ ⟨v, _, rfl⟩; exact hV v.2
  have hSdim : Module.finrank F S' = Module.finrank F S :=
    (Submodule.equivMapOfInjective U.subtype Subtype.val_injective S).finrank_eq.symm
  have hTdim : Module.finrank F T' = Module.finrank F T :=
    (Submodule.equivMapOfInjective V.subtype Subtype.val_injective T).finrank_eq.symm
  have hSn : S' ≠ ⊥ := by
    intro h
    apply hS
    apply Submodule.finrank_eq_zero.mp
    rw [← hSdim, h, finrank_bot]
  have hTn : T' ≠ ⊥ := by
    intro h
    apply hT
    apply Submodule.finrank_eq_zero.mp
    rw [← hTdim, h, finrank_bot]
  have hz : ∀ u ∈ S', ∀ v ∈ T', ∀ a : ZMod (3*t),
      u a * v a = 0 ∧ u a * v (a - 1) = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (Qmap_eq_zero_iff t (by omega) u.1 v.1).mp (hzero u hu v hv)
  have h := gap_imSub t (by omega) S' T' hS' hT' hSn hTn hz
  rw [if_neg (by omega), if_neg (by omega), hSdim, hTdim] at h
  omega

lemma low_dimension_count {U V Y : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    [AddCommGroup V] [Module F V] [Module.Finite F V] [AddCommGroup Y] [Module F Y]
    (B : U →ₗ[F] V →ₗ[F] Y) (m : ℕ) (hm : 6 ≤ m)
    (hdim : m ≤ Module.finrank F U + Module.finrank F V)
    (hd : 2 ≤ Module.finrank F U) (hd' : Module.finrank F U ≤ 4)
    (hrect : ∀ (S : Submodule F U) (T : Submodule F V), S ≠ ⊥ → T ≠ ⊥ →
      (∀ u ∈ S, ∀ v ∈ T, B u v = 0) → Module.finrank F S + Module.finrank F T + 5 ≤ m) :
    64 * Nat.card {p : U × V // B p.1 p.2 = 0} ≤ 19 * (Nat.card U * Nat.card V) := by
  classical
  have : Finite U := Module.finite_of_finite F
  have : Finite V := Module.finite_of_finite F
  let _ : Fintype U := Fintype.ofFinite U
  let _ : Fintype V := Fintype.ofFinite V
  let d := Module.finrank F U
  let r := 6 - d
  have hcardU : Nat.card U = 2^d := card_eq_two_pow_finrank
  have hsum : Nat.card {p : U × V // B p.1 p.2 = 0} =
      ∑ u : U, Nat.card {v : V // B u v = 0} := by
    let e : {p : U × V // B p.1 p.2 = 0} ≃ Σ u : U, {v : V // B u v = 0} :=
      { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
        invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun _ _ => Fintype.card_eq_nat_card)
  have hrow : ∀ u : U, u ≠ 0 →
      2^r * Nat.card {v : V // B u v = 0} ≤ Nat.card V := by
    intro u hu
    let T := LinearMap.ker (B u)
    have hT : Module.finrank F T + r ≤ Module.finrank F V := by
      by_cases hbot : T = ⊥
      · rw [hbot, finrank_bot]
        dsimp [r, d]; omega
      · let S := Submodule.span F ({u} : Set U)
        have hSdim : Module.finrank F S = 1 := finrank_span_singleton hu
        have hSne : S ≠ ⊥ := fun h => by rw [h, finrank_bot] at hSdim; omega
        have h := hrect S T hSne hbot (fun x hx v hv => by
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
          rw [map_smul, LinearMap.smul_apply, LinearMap.mem_ker.mp hv, smul_zero])
        rw [hSdim] at h
        dsimp [r, d]; omega
    have hcount : Nat.card {v : V // B u v = 0} = 2^Module.finrank F T := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => LinearMap.mem_ker.symm)),
        card_eq_two_pow_finrank]
    rw [hcount, card_eq_two_pow_finrank (V := V), ← Nat.pow_add, Nat.add_comm r]
    exact Nat.pow_le_pow_right (by decide) hT
  have h0 : Nat.card {v : V // B 0 v = 0} = Nat.card V :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => by simp))
  have hb : 2^r * Nat.card {p : U × V // B p.1 p.2 = 0} ≤
      (2^r + (2^d - 1)) * Nat.card V := by
    rw [hsum, Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : U)),
      h0, Nat.add_mul]
    apply Nat.add_le_add_left
    calc ∑ u ∈ Finset.univ.erase (0 : U), 2^r * Nat.card {v : V // B u v = 0}
        ≤ ∑ _u ∈ Finset.univ.erase (0 : U), Nat.card V :=
          Finset.sum_le_sum (fun u hu => hrow u (Finset.mem_erase.mp hu).1)
      _ = _ := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_eq_nat_card, hcardU]
  have hdlo : 2 ≤ d := hd
  have hdhi : d ≤ 4 := hd'
  have hmul : 2^d * 2^r = 64 := by dsimp only [r]; interval_cases d <;> decide
  have hnum : 2^d * (2^r + (2^d - 1)) ≤ 19 * 2^d := by
    dsimp only [r]; interval_cases d <;> decide
  calc 64 * Nat.card {p : U × V // B p.1 p.2 = 0} =
      2^d * (2^r * Nat.card {p : U × V // B p.1 p.2 = 0}) := by rw [← Nat.mul_assoc, hmul]
    _ ≤ 2^d * ((2^r + (2^d - 1)) * Nat.card V) := Nat.mul_le_mul_left _ hb
    _ ≤ 19 * (Nat.card U * Nat.card V) := by
      rw [← Nat.mul_assoc, hcardU, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ hnum

lemma large_upper (t : ℕ) (ht : 3 ≤ t) [NeZero (3*t)]
    (U V : Submodule F (Lane (3*t))) (hU : U ≤ imSub t) (hV : V ≤ imSub t)
    (hdim : 3*t ≤ Module.finrank F U + Module.finrank F V) :
    64 * Nat.card {p : U × V // Qmap t p.1.1 p.2.1 = 0} ≤ 19 * (Nat.card U * Nat.card V) := by
  classical
  let B : U →ₗ[F] V →ₗ[F] (Fin (6*t) → F) :=
    { toFun := fun u => (Qmap t u.1).comp V.subtype
      map_add' := fun u v => by ext x i; exact congrFun (LinearMap.congr_fun (map_add (Qmap t) u.1 v.1) x.1) i
      map_smul' := fun c u => by ext x i; exact congrFun (LinearMap.congr_fun (map_smul (Qmap t) c u.1) x.1) i }
  have hrect : ∀ (S : Submodule F U) (T : Submodule F V), S ≠ ⊥ → T ≠ ⊥ →
      (∀ u ∈ S, ∀ v ∈ T, B u v = 0) → Module.finrank F S + Module.finrank F T + 5 ≤ 3*t :=
    fun S T hS hT hz => rect_ceiling t ht hU hV S T hS hT hz
  have hI := finrank_imSub_add_two t (by omega)
  have hUr := Submodule.finrank_mono hU
  have hVr := Submodule.finrank_mono hV
  have hU2 : 2 ≤ Module.finrank F U := by omega
  have hV2 : 2 ≤ Module.finrank F V := by omega
  change 64 * Nat.card {p : U × V // B p.1 p.2 = 0} ≤ _
  by_cases hu : Module.finrank F U ≤ 4
  · exact low_dimension_count B (3*t) (by omega) hdim hU2 hu hrect
  by_cases hv : Module.finrank F V ≤ 4
  · let e : {p : U × V // B p.1 p.2 = 0} ≃ {p : V × U // B.flip p.1 p.2 = 0} :=
      { toFun := fun p => ⟨p.1.swap, p.2⟩
        invFun := fun p => ⟨p.1.swap, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.mul_comm (Nat.card U) (Nat.card V)]
    exact low_dimension_count B.flip (3*t) (by omega) (by omega) hV2 hv (fun S T hS hT hz => by
      have h := hrect T S hT hS (fun u hu v hv => hz v hv u hu)
      omega)
  let E := ZMod (3*t) × Bool
  let el : E → U →ₗ[F] F := fun e => (LinearMap.proj e.1).comp U.subtype
  let er : E → V →ₗ[F] F := fun e => (LinearMap.proj (if e.2 then e.1 - 1 else e.1)).comp V.subtype
  have hzero : ∀ (u : U) (v : V), B u v = 0 ↔ ∀ e : E, el e u * er e v = 0 := by
    intro u v
    change Qmap t u.1 v.1 = 0 ↔ _
    rw [Qmap_eq_zero_iff t (by omega)]
    constructor
    · intro h e
      rcases e with ⟨a, b⟩
      cases b
      · exact (h a).1
      · exact (h a).2
    · intro h a
      exact ⟨h (a, false), h (a, true)⟩
  obtain ⟨I, _, A, _, hLi, hRi, hrk⟩ := inter _ _ _
    (lrk_isRk (F := F) el) (lrk_isRk (F := F) er) (Finset.univ : Finset E) rfl
  have hlarge : 5 ≤ I.card := by
    by_contra! hlt
    let S : Submodule F U := ⨅ e ∈ A, LinearMap.ker (el e)
    let T : Submodule F V := ⨅ e ∈ (Finset.univ \ A : Finset E), LinearMap.ker (er e)
    have hLS := finrank_span_eval_eq_sub_ker el A
    have hRT := finrank_span_eval_eq_sub_ker er (Finset.univ \ A)
    change lrk el A + Module.finrank F S = _ at hLS
    change lrk er (Finset.univ \ A) + Module.finrank F T = _ at hRT
    have hS : S ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hLS; omega
    have hT : T ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hRT; omega
    have hz : ∀ u ∈ S, ∀ v ∈ T, B u v = 0 := by
      intro u hus v hvt
      simp only [S, Submodule.mem_iInf, LinearMap.mem_ker] at hus
      simp only [T, Submodule.mem_iInf, LinearMap.mem_ker] at hvt
      apply (hzero u v).mpr
      intro e
      by_cases he : e ∈ A
      · rw [hus e he, zero_mul]
      · rw [hvt e (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩), mul_zero]
    have hk := hrect S T hS hT hz
    omega
  obtain ⟨J, hJ, hJcard⟩ := Finset.exists_subset_card_eq hlarge
  let eqJ : Fin 5 ≃ J := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hJcard])).symm
  let inc : Fin 5 → I := fun c => ⟨(eqJ c).1, hJ (eqJ c).2⟩
  have hinj : Function.Injective inc := fun a b h =>
    eqJ.injective (Subtype.ext (congrArg (fun z : I => z.1) h))
  let φ : U →ₗ[F] (Fin 5 → F) := LinearMap.pi (fun c => el (inc c).1)
  let ψ : V →ₗ[F] (Fin 5 → F) := LinearMap.pi (fun c => er (inc c).1)
  have hφ : Function.Surjective φ := linearIndependent_dual_iff_surjective _
    (((li_iff el I).mpr hLi).comp inc hinj)
  have hψ : Function.Surjective ψ := linearIndependent_dual_iff_surjective _
    (((li_iff er I).mpr hRi).comp inc hinj)
  let _ : Fintype U := Fintype.ofFinite U
  let _ : Fintype V := Fintype.ofFinite V
  let G := Finset.univ.filter (fun uv : (Fin 5 → F) × (Fin 5 → F) => ∀ i, uv.1 i * uv.2 i = 0)
  have h := card_hits_le_of_good φ ψ hφ hψ (fun (p : U × V) => B p.1 p.2 = 0) G
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (hzero _ _).mp hp (inc i).1⟩)
  have hG : G.card = 3^5 := card_good_pairs_indep 5
  have hc : Fintype.card (Fin 5 → F) = 32 := by simp
  rw [hG, hc, show 32 * 32 = 1024 by decide, show 3 ^ 5 = 243 by decide] at h
  have h' : 1024 * Nat.card {p : U × V // B p.1 p.2 = 0} ≤
      243 * (Nat.card U * Nat.card V) := by simpa only [← Nat.mul_assoc] using h
  omega

lemma lane_upper (t : ℕ) (ht2 : 2 ≤ t) [NeZero (3*t)]
    (U V : Submodule F (Lane (3*t))) (hU : U ≤ imSub t) (hV : V ≤ imSub t)
    (hdim : 3*t ≤ Module.finrank F U + Module.finrank F V) :
    64 * Nat.card {p : U × V // Qmap t p.1.1 p.2.1 = 0} ≤ numN t * (Nat.card U * Nat.card V) := by
  by_cases ht : t = 2
  · subst t
    rw [Nat.card_congr (Equiv.subtypeEquivRight
      (fun p : U × V => Qmap_eq_zero_iff 2 (by decide) p.1.1 p.2.1))]
    exact small_upper U V hU hV hdim
  · simpa only [numN, if_neg ht] using large_upper t (by omega) U V hU hV hdim


lemma coset_upper_bound (t : ℕ) (ht : 0 < t) (ht2 : 2 ≤ t) [NeZero (3 * t)]
    (name c : Fin (6 * t) → F) (w0 : Fin (6 * t) → F)
    (K : Submodule F (Fin (6 * t) → F)) (hK : 6 * t ≤ Module.finrank F K + (3 * t - 4))
    (A : (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F)) (b : Fin (6 * t) → F) :
    (64 : ℕ) * Nat.card {x : K // outN (6 * t) (by omega) name c (w0 + x.1) = A (w0 + x.1) + b} ≤
      numN t * Nat.card K := by
  classical
  let L : (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F) :=
    A + Lbase t ht name +
    ((Qmap t (evenLane t ht w0)).comp (oddLane t ht)) +
    (LinearMap.flip (Qmap t) (oddLane t ht w0)).comp (evenLane t ht)
  let d : Fin (6 * t) → F :=
    A w0 + b + Lbase t ht name w0 + cbase t ht name c +
    Qmap t (evenLane t ht w0) (oddLane t ht w0)
  have heq : ∀ x : K,
      outN (6 * t) (by omega) name c (w0 + x.1) = A (w0 + x.1) + b ↔
      Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d := by
    intro x
    rw [outN_decomp t ht name c (w0 + x.1)]
    have hq : Qmap t (evenLane t ht (w0 + x.1)) (oddLane t ht (w0 + x.1)) =
        Qmap t (evenLane t ht w0) (oddLane t ht w0) +
        Qmap t (evenLane t ht w0) (oddLane t ht x.1) +
        Qmap t (evenLane t ht x.1) (oddLane t ht w0) +
        Qmap t (evenLane t ht x.1) (oddLane t ht x.1) := by
      rw [map_add, map_add, map_add, LinearMap.add_apply, map_add, map_add]
      abel
    rw [hq, map_add, map_add]
    dsimp only [L, d, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      dsimp only [Pi.add_apply] at hi ⊢
      have hsum : (Qmap t (evenLane t ht w0) (oddLane t ht w0) i +
          Qmap t (evenLane t ht w0) (oddLane t ht x.1) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht w0) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht x.1) i +
          (Lbase t ht name w0 i + Lbase t ht name x.1 i) + cbase t ht name c i) +
          (Qmap t (evenLane t ht w0) (oddLane t ht w0) i +
          Qmap t (evenLane t ht w0) (oddLane t ht x.1) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht w0) i +
          (Lbase t ht name w0 i + Lbase t ht name x.1 i) + cbase t ht name c i) =
          (A w0 i + A x.1 i + b i) +
          (Qmap t (evenLane t ht w0) (oddLane t ht w0) i +
          Qmap t (evenLane t ht w0) (oddLane t ht x.1) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht w0) i +
          (Lbase t ht name w0 i + Lbase t ht name x.1 i) + cbase t ht name c i) :=
        congrArg (· + _) hi
      have hlhs : (Qmap t (evenLane t ht w0) (oddLane t ht w0) i +
          Qmap t (evenLane t ht w0) (oddLane t ht x.1) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht w0) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht x.1) i +
          (Lbase t ht name w0 i + Lbase t ht name x.1 i) + cbase t ht name c i) +
          (Qmap t (evenLane t ht w0) (oddLane t ht w0) i +
          Qmap t (evenLane t ht w0) (oddLane t ht x.1) i +
          Qmap t (evenLane t ht x.1) (oddLane t ht w0) i +
          (Lbase t ht name w0 i + Lbase t ht name x.1 i) + cbase t ht name c i) =
          Qmap t (evenLane t ht x.1) (oddLane t ht x.1) i := by
        ring_nf; simp only [z2_two, mul_zero, zero_mul, add_zero, zero_add]
      rw [hlhs] at hsum
      rw [hsum]; abel
    · intro h
      funext i
      have hi := congrFun h i
      dsimp only [Pi.add_apply] at hi ⊢
      rw [hi]
      ring_nf; simp only [z2_two, mul_zero, zero_mul, add_zero, zero_add]
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq)]
  let KZ : Submodule F (Fin (6 * t) → F) := K ⊓ LinearMap.ker (evenLane t ht)
  let fE : K →ₗ[F] Lane (3 * t) := (evenLane t ht).comp K.subtype
  let fO : KZ →ₗ[F] Lane (3 * t) := (oddLane t ht).comp KZ.subtype
  let U : Submodule F (Lane (3 * t)) := LinearMap.range fE
  let V : Submodule F (Lane (3 * t)) := LinearMap.range fO
  have hU_im : U ≤ imSub t := by
    rintro _ ⟨x, rfl⟩; exact evenLane_mem_imSub t ht x.1
  have hV_im : V ≤ imSub t := by
    rintro _ ⟨κ, rfl⟩; exact oddLane_mem_imSub t ht κ.1
  have hkerE_equiv : LinearMap.ker fE ≃ₗ[F] KZ :=
    { toFun := fun z => ⟨z.1.1, Submodule.mem_inf.mpr ⟨z.1.2, LinearMap.mem_ker.mp z.2⟩⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, LinearMap.mem_ker.mpr z.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hker_fO_le : Module.finrank F (LinearMap.ker fO) ≤ 4 := by
    let S : Submodule F (Fin (6 * t) → F) :=
      LinearMap.ker (evenLane t ht) ⊓ LinearMap.ker (oddLane t ht)
    let emb : LinearMap.ker fO →ₗ[F] S :=
      { toFun := fun z => ⟨z.1.1, Submodule.mem_inf.mpr ⟨z.1.2.2, LinearMap.mem_ker.mp z.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective emb := by
      intro z1 z2 h
      have hv : z1.1.1 = z2.1.1 := congrArg (fun x => x.1) h
      exact Subtype.ext (Subtype.ext hv)
    exact (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq (finrank_ker_even_inf_odd t ht)
  have hrkE : Module.finrank F U + Module.finrank F KZ = Module.finrank F K := by
    have h := LinearMap.finrank_range_add_finrank_ker fE
    rw [LinearEquiv.finrank_eq hkerE_equiv] at h
    exact h
  have hrkO : Module.finrank F V + Module.finrank F (LinearMap.ker fO) = Module.finrank F KZ :=
    LinearMap.finrank_range_add_finrank_ker fO
  have hdimUV : 3 * t ≤ Module.finrank F U + Module.finrank F V := by omega
  have hbil := lane_upper t ht2 U V hU_im hV_im hdimUV
  let fEO : K × KZ →ₗ[F] Lane (3 * t) × Lane (3 * t) := fE.prodMap fO
  have hpre := card_preimage_linear fEO (fun p => Qmap t p.1 p.2 = 0)
  let hrange_e : fEO.range ≃ₗ[F] U × V :=
    { toFun := fun z =>
        (⟨z.1.1, by rcases z.2 with ⟨⟨x, _⟩, hx⟩; exact ⟨x, congrArg Prod.fst hx⟩⟩,
         ⟨z.1.2, by rcases z.2 with ⟨⟨_, κ⟩, hκ⟩; exact ⟨κ, congrArg Prod.snd hκ⟩⟩)
      invFun := fun p =>
        ⟨(p.1.1, p.2.1), by
          rcases p.1.2 with ⟨x, hx⟩; rcases p.2.2 with ⟨κ, hκ⟩
          exact ⟨(x, κ), Prod.ext hx hκ⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hker_e : LinearMap.ker fEO ≃ₗ[F] LinearMap.ker fE × LinearMap.ker fO :=
    { toFun := fun z =>
        (⟨z.1.1, LinearMap.mem_ker.mpr (congrArg Prod.fst (LinearMap.mem_ker.mp z.2))⟩,
         ⟨z.1.2, LinearMap.mem_ker.mpr (congrArg Prod.snd (LinearMap.mem_ker.mp z.2))⟩)
      invFun := fun p =>
        ⟨(p.1.1, p.2.1), LinearMap.mem_ker.mpr (Prod.ext (LinearMap.mem_ker.mp p.1.2)
          (LinearMap.mem_ker.mp p.2.2))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard_UV : Nat.card {y : fEO.range // Qmap t y.1.1 y.1.2 = 0} =
      Nat.card {p : U × V // Qmap t p.1.1 p.2.1 = 0} :=
    Nat.card_congr
      { toFun := fun y => ⟨hrange_e y.1, by change Qmap t y.1.1.1 y.1.1.2 = 0; exact y.2⟩
        invFun := fun p => ⟨hrange_e.symm p.1, by change Qmap t p.1.1.1 p.1.2.1 = 0; exact p.2⟩
        left_inv := fun y => Subtype.ext (hrange_e.symm_apply_apply y.1)
        right_inv := fun p => Subtype.ext (hrange_e.apply_symm_apply p.1) }
  have hcard_KZ_K : Nat.card KZ * Nat.card U = Nat.card K := by
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, card_eq_two_pow_finrank,
      ← Nat.pow_add, Nat.add_comm, hrkE]
  have hcard_kerO_KZ : Nat.card (LinearMap.ker fO) * Nat.card V = Nat.card KZ := by
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, card_eq_two_pow_finrank,
      ← Nat.pow_add, Nat.add_comm, hrkO]
  have hcard_kerEO : Nat.card (LinearMap.ker fEO) = Nat.card KZ * Nat.card (LinearMap.ker fO) := by
    rw [Nat.card_congr hker_e.toEquiv, Nat.card_prod, Nat.card_congr hkerE_equiv.toEquiv]
  have hdc := double_count_quadratic t ht K L d
  have hmul : (64 : ℕ) * (Nat.card KZ *
      Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d}) ≤
      numN t * (Nat.card K * Nat.card KZ) := by
    calc (64 : ℕ) * (Nat.card KZ *
          Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d})
        ≤ (64 : ℕ) * Nat.card {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = 0} :=
          Nat.mul_le_mul_left _ hdc
      _ = (64 : ℕ) * (Nat.card (LinearMap.ker fEO) * Nat.card {p : U × V // Qmap t p.1.1 p.2.1 = 0}) := by
          rw [← hcard_UV]; exact congrArg ((64 : ℕ) * ·) hpre
      _ = Nat.card (LinearMap.ker fEO) * ((64 : ℕ) * Nat.card {p : U × V // Qmap t p.1.1 p.2.1 = 0}) := by
          rw [Nat.mul_left_comm]
      _ ≤ Nat.card (LinearMap.ker fEO) * (numN t * (Nat.card U * Nat.card V)) :=
          Nat.mul_le_mul_left _ hbil
      _ = numN t * ((Nat.card KZ * Nat.card U) * (Nat.card (LinearMap.ker fO) * Nat.card V)) := by
          rw [hcard_kerEO]; ring
      _ = numN t * (Nat.card K * Nat.card KZ) := by rw [hcard_KZ_K, hcard_kerO_KZ]
  have hKZ_pos : 0 < Nat.card KZ := by
    rw [card_eq_two_pow_finrank]; exact Nat.pos_of_ne_zero (by positivity)
  have hre : Nat.card KZ * ((64 : ℕ) *
      Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d}) ≤
      Nat.card KZ * (numN t * Nat.card K) := by
    calc Nat.card KZ * ((64 : ℕ) * _)
        = (64 : ℕ) * (Nat.card KZ * _) := Nat.mul_left_comm _ _ _
      _ ≤ numN t * (Nat.card K * Nat.card KZ) := hmul
      _ = Nat.card KZ * (numN t * Nat.card K) := by ring
  exact Nat.le_of_mul_le_mul_left hre hKZ_pos

theorem upper_bound (t : ℕ) (ht : 0 < t) (ht2 : 2 ≤ t) [NeZero (3 * t)]
    (name c : Fin (6 * t) → F)
    (ask : Fin (3 * t - 4) → ℕ → (Fin (6 * t) → F) →ₗ[F] F)
    (A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F))
    (b : ℕ → Fin (6 * t) → F) :
    (64 : ℕ) * Nat.card {w : Fin (6 * t) → F //
      outN (6 * t) (by omega) name c w =
        A (runN (6 * t) (3 * t - 4) ask w) w + b (runN (6 * t) (3 * t - 4) ask w)} ≤
      numN t * 2 ^ (6 * t) := by
  classical
  let P : Finset ℕ := Finset.univ.image (runN (6 * t) (3 * t - 4) ask)
  have hpart_hit : Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 4) ask w) w + b (runN (6 * t) (3 * t - 4) ask w)} =
      ∑ p ∈ P, Nat.card {w : Fin (6 * t) → F //
        runN (6 * t) (3 * t - 4) ask w = p ∧
        outN (6 * t) (by omega) name c w = A p w + b p} := by
    simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    have hdisj : (P : Set ℕ).PairwiseDisjoint (fun p =>
        Finset.univ.filter (fun w : Fin (6 * t) → F =>
          runN (6 * t) (3 * t - 4) ask w = p ∧
          outN (6 * t) (by omega) name c w = A p w + b p)) := by
      intro p1 _ p2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
    rw [← Finset.card_biUnion hdisj]
    congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, P,
      Finset.mem_image]
    constructor
    · intro h; exact ⟨runN (6 * t) (3 * t - 4) ask w, ⟨w, rfl⟩, rfl, h⟩
    · rintro ⟨p, _, rfl, h⟩; exact h
  have hpart_all : 2 ^ (6 * t) =
      ∑ p ∈ P, Nat.card {w : Fin (6 * t) → F // runN (6 * t) (3 * t - 4) ask w = p} := by
    simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    have hdisj : (P : Set ℕ).PairwiseDisjoint (fun p =>
        Finset.univ.filter (fun w : Fin (6 * t) → F => runN (6 * t) (3 * t - 4) ask w = p)) := by
      intro p1 _ p2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [← Finset.card_biUnion hdisj]
    have huniv : P.biUnion (fun p =>
        Finset.univ.filter (fun w : Fin (6 * t) → F => runN (6 * t) (3 * t - 4) ask w = p)) =
        Finset.univ := by
      ext w
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, P,
        Finset.mem_image]
      exact ⟨runN (6 * t) (3 * t - 4) ask w, ⟨w, rfl⟩, rfl⟩
    rw [huniv, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hpart_hit, hpart_all, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  rcases Finset.mem_image.mp hp with ⟨w0, _, rfl⟩
  obtain ⟨K, hK, hcoset⟩ := runN_fiber_coset (6 * t) (3 * t - 4) ask w0
  have e_hit : {w : Fin (6 * t) → F //
      runN (6 * t) (3 * t - 4) ask w = runN (6 * t) (3 * t - 4) ask w0 ∧
      outN (6 * t) (by omega) name c w =
        A (runN (6 * t) (3 * t - 4) ask w0) w + b (runN (6 * t) (3 * t - 4) ask w0)} ≃
      {x : K // outN (6 * t) (by omega) name c (w0 + x.1) =
        A (runN (6 * t) (3 * t - 4) ask w0) (w0 + x.1) + b (runN (6 * t) (3 * t - 4) ask w0)} :=
    { toFun := fun w => ⟨⟨w.1 + w0, (hcoset w.1).mp w.2.1⟩, by
        have hww : w0 + (w.1 + w0) = w.1 := by
          have : w0 + (w.1 + w0) = w.1 + (w0 + w0) := by abel
          rw [this, vec_add_self, add_zero]
        rw [hww]; exact w.2.2⟩
      invFun := fun x => ⟨w0 + x.1.1, ⟨(hcoset (w0 + x.1.1)).mpr (by
          have : (w0 + x.1.1) + w0 = x.1.1 := by
            have : (w0 + x.1.1) + w0 = x.1.1 + (w0 + w0) := by abel
            rw [this, vec_add_self, add_zero]
          rw [this]; exact x.1.2), x.2⟩⟩
      left_inv := fun w => by
        apply Subtype.ext; dsimp only
        have : w0 + (w.1 + w0) = w.1 + (w0 + w0) := by abel
        rw [this, vec_add_self, add_zero]
      right_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext; dsimp only
        have : (w0 + x.1.1) + w0 = x.1.1 + (w0 + w0) := by abel
        rw [this, vec_add_self, add_zero] }
  have e_all : {w : Fin (6 * t) → F //
      runN (6 * t) (3 * t - 4) ask w = runN (6 * t) (3 * t - 4) ask w0} ≃ K :=
    { toFun := fun w => ⟨w.1 + w0, (hcoset w.1).mp w.2⟩
      invFun := fun x => ⟨w0 + x.1, (hcoset (w0 + x.1)).mpr (by
        have : (w0 + x.1) + w0 = x.1 + (w0 + w0) := by abel
        rw [this, vec_add_self, add_zero]; exact x.2)⟩
      left_inv := fun w => by
        apply Subtype.ext; dsimp only
        have : w0 + (w.1 + w0) = w.1 + (w0 + w0) := by abel
        rw [this, vec_add_self, add_zero]
      right_inv := fun x => by
        apply Subtype.ext; dsimp only
        have : (w0 + x.1) + w0 = x.1 + (w0 + w0) := by abel
        rw [this, vec_add_self, add_zero] }
  rw [Nat.card_congr e_hit, Nat.card_congr e_all]
  exact coset_upper_bound t ht ht2 name c w0 K hK
    (A (runN (6 * t) (3 * t - 4) ask w0)) (b (runN (6 * t) (3 * t - 4) ask w0))


def freeKey (t : ℕ) [NeZero (3 * t)] (u : Lane (3 * t)) : F × F :=
  if t = 2 then (u 0, u 1)
  else (u ((3 * t - 4 : ℕ) : ZMod (3 * t)), u ((3 * t - 1 : ℕ) : ZMod (3 * t)))

def residual (t : ℕ) [NeZero (3 * t)] (p : F × F) : Lane (3 * t) := fun a =>
  if t = 2 then
    if a.val = 0 ∨ a.val = 3 then p.1
    else if a.val = 1 ∨ a.val = 4 then p.2 else 0
  else
    if a.val = 3 * t - 4 then p.1
    else if a.val = 3 * t - 3 ∨ a.val = 3 * t - 2 then p.1 + p.2
    else if a.val = 3 * t - 1 then p.2 else 0

private lemma residual_six_values (p : F × F) :
    residual 2 p 0 = p.1 ∧ residual 2 p 1 = p.2 ∧ residual 2 p 2 = 0 ∧
    residual 2 p 3 = p.1 ∧ residual 2 p 4 = p.2 ∧ residual 2 p 5 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma residual_tail_values (t : ℕ) (ht : 3 ≤ t) [NeZero (3 * t)] (p : F × F) :
    residual t p ((3 * t - 4 : ℕ) : ZMod (3 * t)) = p.1 ∧
    residual t p ((3 * t - 3 : ℕ) : ZMod (3 * t)) = p.1 + p.2 ∧
    residual t p ((3 * t - 2 : ℕ) : ZMod (3 * t)) = p.1 + p.2 ∧
    residual t p ((3 * t - 1 : ℕ) : ZMod (3 * t)) = p.2 := by
  have ht' : t ≠ 2 := by omega
  have hv (i : ℕ) (hi : i < 3 * t) : (((i : ℕ) : ZMod (3 * t))).val = i := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  constructor
  · simp [residual, ht', hv (3 * t - 4) (by omega)]
  constructor
  · simp [residual, ht', hv (3 * t - 3) (by omega), show 3 * t - 3 ≠ 3 * t - 4 by omega]
  constructor
  · simp [residual, ht', hv (3 * t - 2) (by omega), show 3 * t - 2 ≠ 3 * t - 4 by omega]
  · simp [residual, ht', hv (3 * t - 1) (by omega), show 3 * t - 1 ≠ 3 * t - 4 by omega,
      show 3 * t - 1 ≠ 3 * t - 3 by omega, show 3 * t - 1 ≠ 3 * t - 2 by omega]

private lemma residual_below_tail (t : ℕ) (ht : 3 ≤ t) [NeZero (3 * t)] (p : F × F)
    (a : ZMod (3 * t)) (ha : a.val < 3 * t - 4) : residual t p a = 0 := by
  simp [residual, show t ≠ 2 by omega, show a.val ≠ 3 * t - 4 by omega,
    show a.val ≠ 3 * t - 3 by omega, show a.val ≠ 3 * t - 2 by omega,
    show a.val ≠ 3 * t - 1 by omega]

private lemma residual_parSum_six (u : Lane 6) :
    parSum 2 0 u = u 0 + u 3 ∧ parSum 2 1 u = u 1 + u 4 ∧ parSum 2 2 u = u 2 + u 5 := by
  constructor
  · rw [parSum_apply, z6_filter_0, Finset.sum_pair z6_0_ne_3]
  constructor
  · rw [parSum_apply, z6_filter_1, Finset.sum_pair z6_1_ne_4]
  · rw [parSum_apply, z6_filter_2, Finset.sum_pair z6_2_ne_5]

private lemma residual_parSum_tail (t : ℕ) (ht : 3 ≤ t) [NeZero (3 * t)]
    (u : Lane (3 * t)) (hz : ∀ a, a.val < 3 * t - 4 → u a = 0) :
    parSum t 0 u = u ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∧
    parSum t 1 u = u ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∧
    parSum t 2 u = u ((3 * t - 4 : ℕ) : ZMod (3 * t)) + u ((3 * t - 1 : ℕ) : ZMod (3 * t)) := by
  let c (i : ℕ) : ZMod (3 * t) := (3 * t - i : ℕ)
  have hc (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 4) : (c i).val = 3 * t - i := by
    dsimp only [c]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hcoord (a : ZMod (3 * t)) (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 4) :
      a = c i ↔ a.val = 3 * t - i := by
    rw [← hc i hi hi']
    exact ⟨congrArg ZMod.val, fun h => ZMod.val_injective (3 * t) h⟩
  have hres (a : ZMod (3 * t)) (r : ZMod 3) : res3 t a = r ↔ a.val % 3 = r.val := by
    constructor
    · intro h
      have hcast : ((a.val : ℕ) : ZMod 3) = r := by
        rw [← map_natCast (res3 t), ZMod.natCast_zmod_val, h]
      have hv := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast] at hv
    · intro h
      have hcast : ((a.val : ℕ) : ZMod 3) = r := by
        apply ZMod.val_injective 3
        rwa [ZMod.val_natCast]
      rwa [← map_natCast (res3 t), ZMod.natCast_zmod_val] at hcast
  have hsum (r : ZMod 3) (s : Finset (ZMod (3 * t)))
      (hs : ∀ a, a ∈ s ↔ 3 * t - 4 ≤ a.val ∧ a.val % 3 = r.val) :
      parSum t r u = ∑ a ∈ s, u a := by
    rw [parSum_apply]
    symm
    apply Finset.sum_subset
    · intro a ha
      have h := (hs a).mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hres a r).mpr h.2⟩
    · intro a ha hn
      have hre := (hres a r).mp (Finset.mem_filter.mp ha).2
      apply hz a
      by_contra! hn'
      exact hn ((hs a).mpr ⟨hn', hre⟩)
  change parSum t 0 u = u (c 3) ∧ parSum t 1 u = u (c 2) ∧
    parSum t 2 u = u (c 4) + u (c 1)
  constructor
  · rw [hsum 0 {c 3} (by
      intro a
      have ha := a.val_lt
      simp only [Finset.mem_singleton, hcoord a 3 (by omega) (by omega)]
      change a.val = 3 * t - 3 ↔ 3 * t - 4 ≤ a.val ∧ a.val % 3 = 0
      omega), Finset.sum_singleton]
  constructor
  · rw [hsum 1 {c 2} (by
      intro a
      have ha := a.val_lt
      simp only [Finset.mem_singleton, hcoord a 2 (by omega) (by omega)]
      change a.val = 3 * t - 2 ↔ 3 * t - 4 ≤ a.val ∧ a.val % 3 = 1
      omega), Finset.sum_singleton]
  · have hne : c 4 ≠ c 1 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [hc 4 (by omega) (by omega), hc 1 (by omega) (by omega)] at hv
      omega
    rw [hsum 2 {c 4, c 1} (by
      intro a
      have ha := a.val_lt
      simp only [Finset.mem_insert, Finset.mem_singleton,
        hcoord a 4 (by omega) (by omega), hcoord a 1 (by omega) (by omega)]
      change (a.val = 3 * t - 4 ∨ a.val = 3 * t - 1) ↔
        3 * t - 4 ≤ a.val ∧ a.val % 3 = 2
      omega), Finset.sum_pair hne]

lemma residual_mem (t : ℕ) (ht2 : 2 ≤ t) [NeZero (3 * t)] (p : F × F) :
    residual t p ∈ imSub t := by
  by_cases he : t = 2
  · subst t
    obtain ⟨h0, h1, h2⟩ := residual_parSum_six (residual 2 p)
    obtain ⟨v0, v1, v2, v3, v4, v5⟩ := residual_six_values p
    simp only [mem_imSub_iff, h0, h1, h2, v0, v1, v2, v3, v4, v5, z2_add_self, add_zero,
      and_self]
  · have ht : 3 ≤ t := by omega
    obtain ⟨h0, h1, h2⟩ := residual_parSum_tail t ht (residual t p) (residual_below_tail t ht p)
    obtain ⟨v4, v3, v2, v1⟩ := residual_tail_values t ht p
    rw [mem_imSub_iff, h0, h1, h2, v4, v3, v2, v1]
    exact ⟨rfl, rfl⟩

lemma residual_key (t : ℕ) (ht2 : 2 ≤ t) [NeZero (3 * t)] (p : F × F) :
    freeKey t (residual t p) = p := by
  by_cases he : t = 2
  · subst t
    obtain ⟨v0, v1, _⟩ := residual_six_values p
    calc
      freeKey 2 (residual 2 p) = (p.1, p.2) := by rw [freeKey, if_pos rfl, v0, v1]
      _ = p := by cases p; rfl
  · obtain ⟨v4, _, _, v1⟩ := residual_tail_values t (by omega) p
    calc
      freeKey t (residual t p) = (p.1, p.2) := by rw [freeKey, if_neg he, v4, v1]
      _ = p := by cases p; rfl

lemma residual_site (t : ℕ) (ht2 : 2 ≤ t) [NeZero (3 * t)] (p : F × F)
    (j : Fin (3 * t - 4)) : residual t p (siteN t j : ZMod (3 * t)) = 0 := by
  by_cases he : t = 2
  · subst t
    have hc : ∀ k : Fin (3 * 2 - 4),
        (siteN 2 k : ZMod 6) = 2 ∨ (siteN 2 k : ZMod 6) = 5 := by decide
    obtain ⟨_, _, v2, _, _, v5⟩ := residual_six_values p
    rcases hc j with h | h
    · rw [h]; exact v2
    · rw [h]; exact v5
  · apply residual_below_tail t (by omega) p
    have hj := j.isLt
    simpa only [siteN, if_neg he, ZMod.val_natCast, Nat.mod_eq_of_lt (show j.val < 3 * t by omega)] using hj

lemma residual_identify (t : ℕ) (ht2 : 2 ≤ t) [NeZero (3 * t)] {u : Lane (3 * t)}
    (hu : u ∈ imSub t) (hz : ∀ j : Fin (3 * t - 4), u (siteN t j : ZMod (3 * t)) = 0) :
    u = residual t (freeKey t u) := by
  by_cases he : t = 2
  · subst t
    have u2 : u 2 = 0 := hz ⟨0, by omega⟩
    have u5 : u 5 = 0 := hz ⟨1, by omega⟩
    obtain ⟨h0, h1, h2⟩ := residual_parSum_six u
    obtain ⟨e0, e1⟩ := (mem_imSub_iff 2 u).mp hu
    rw [h0, h2, u2, u5, add_zero] at e0
    rw [h1, h2, u2, u5, add_zero] at e1
    have cancel (a b : F) (h : a + b = 0) : b = a := by
      calc
        b = a + (a + b) := by rw [← add_assoc, z2_add_self, zero_add]
        _ = a := by rw [h, add_zero]
    have u3 := cancel _ _ e0
    have u4 := cancel _ _ e1
    change u = residual 2 (u 0, u 1)
    obtain ⟨v0, v1, v2, v3, v4, v5⟩ := residual_six_values (u 0, u 1)
    funext a
    rcases z6_elems a with rfl | rfl | rfl | rfl | rfl | rfl
    · exact v0.symm
    · exact v1.symm
    · exact u2.trans v2.symm
    · exact u3.trans v3.symm
    · exact u4.trans v4.symm
    · exact u5.trans v5.symm
  · have ht : 3 ≤ t := by omega
    have hlow (a : ZMod (3 * t)) (ha : a.val < 3 * t - 4) : u a = 0 := by
      simpa only [siteN, if_neg he, ZMod.natCast_zmod_val] using hz ⟨a.val, ha⟩
    obtain ⟨h0, h1, h2⟩ := residual_parSum_tail t ht u hlow
    obtain ⟨e0, e1⟩ := (mem_imSub_iff t u).mp hu
    rw [h0, h2] at e0
    rw [h1, h2] at e1
    simp only [freeKey, if_neg he]
    obtain ⟨v4, v3, v2, v1⟩ := residual_tail_values t ht
      (u ((3 * t - 4 : ℕ) : ZMod (3 * t)), u ((3 * t - 1 : ℕ) : ZMod (3 * t)))
    funext a
    by_cases ha : a.val < 3 * t - 4
    · exact (hlow a ha).trans (residual_below_tail t ht _ a ha).symm
    · have hlt := a.val_lt
      have hc : a.val = 3 * t - 4 ∨ a.val = 3 * t - 3 ∨
          a.val = 3 * t - 2 ∨ a.val = 3 * t - 1 := by omega
      rcases hc with h | h | h | h
      · rw [← ZMod.natCast_zmod_val a, h]; exact v4.symm
      · rw [← ZMod.natCast_zmod_val a, h]; exact e0.trans v3.symm
      · rw [← ZMod.natCast_zmod_val a, h]; exact e1.trans v2.symm
      · rw [← ZMod.natCast_zmod_val a, h]; exact v1.symm


private lemma price_card_filter {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] :
    Nat.card {x : A // P x} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private def priceSixCompat (v : Lane 6) : Prop :=
  v 0 + v 3 = v 2 + v 5 ∧ v 1 + v 4 = v 2 + v 5

private def priceSixProducts (p : F × F) (v : Lane 6) : Prop :=
  (p.1 * v 0 = 0 ∧ p.1 * v 5 = 0) ∧
  (p.2 * v 1 = 0 ∧ p.2 * v 0 = 0) ∧
  (p.1 * v 3 = 0 ∧ p.1 * v 2 = 0) ∧
  (p.2 * v 4 = 0 ∧ p.2 * v 3 = 0)

private def priceSix (q : (F × F) × Lane 6) : Prop :=
  priceSixCompat q.2 ∧ priceSixProducts q.1 q.2

private def priceSixDecidable : DecidablePred priceSix := fun q => by
  unfold priceSix priceSixCompat priceSixProducts
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma priceSix_card : Nat.card {q : (F × F) × Lane 6 // priceSix q} = 21 := by
  letI : DecidablePred priceSix := priceSixDecidable
  rw [price_card_filter]
  decide +kernel

private lemma priceSix_compat (v : Lane 6) : v ∈ imSub 2 ↔ priceSixCompat v := by
  obtain ⟨h0, h1, h2⟩ := residual_parSum_six v
  rw [mem_imSub_iff, h0, h1, h2, priceSixCompat]

private lemma priceSix_q (p : F × F) (v : Lane 6) :
    Qmap 2 (residual 2 p) v = 0 ↔ priceSixProducts p v := by
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := residual_six_values p
  have m0 : (0 : ZMod 6) - 1 = 5 := by decide
  have m1 : (1 : ZMod 6) - 1 = 0 := by decide
  have m3 : (3 : ZMod 6) - 1 = 2 := by decide
  have m4 : (4 : ZMod 6) - 1 = 3 := by decide
  rw [Qmap_eq_zero_iff 2 (by decide), priceSixProducts]
  constructor
  · intro h
    simpa only [r0, r1, r3, r4, m0, m1, m3, m4] using ⟨h 0, h 1, h 3, h 4⟩
  · rintro ⟨h0, h1, h3, h4⟩ a
    rcases z6_elems a with rfl | rfl | rfl | rfl | rfl | rfl
    · rwa [r0, m0]
    · rwa [r1, m1]
    · simp only [r2, zero_mul, and_self]
    · rwa [r3, m3]
    · rwa [r4, m4]
    · simp only [r5, zero_mul, and_self]

private def priceTail (q : (F × F) × (Fin 5 → F)) : Prop :=
  (q.1.1 * q.2 1 = 0 ∧ q.1.1 * q.2 0 = 0) ∧
  ((q.1.1 + q.1.2) * q.2 2 = 0 ∧ (q.1.1 + q.1.2) * q.2 1 = 0) ∧
  ((q.1.1 + q.1.2) * q.2 3 = 0 ∧ (q.1.1 + q.1.2) * q.2 2 = 0) ∧
  (q.1.2 * q.2 4 = 0 ∧ q.1.2 * q.2 3 = 0)

private def priceTailDecidable : DecidablePred priceTail := fun q => by
  unfold priceTail
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma priceTail_card : Nat.card {q : (F × F) × (Fin 5 → F) // priceTail q} = 38 := by
  letI : DecidablePred priceTail := priceTailDecidable
  rw [price_card_filter]
  decide +kernel

private def priceIndex (t : ℕ) (i : Fin 5) : ZMod (3 * t) :=
  (3 * t - 5 + i.val : ℕ)

private lemma priceIndex_val (t : ℕ) (ht : 3 ≤ t) [NeZero (3 * t)] (i : Fin 5) :
    (priceIndex t i).val = 3 * t - 5 + i.val := by
  have hi := i.isLt
  rw [priceIndex, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

private lemma priceIndex_prev (t : ℕ) (i j : Fin 5) (h : i.val + 1 = j.val) :
    priceIndex t j - 1 = priceIndex t i := by
  have he : priceIndex t i + 1 = priceIndex t j := by
    unfold priceIndex
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_assoc, h]
  exact (eq_sub_of_add_eq he).symm

private lemma priceTail_q (t : ℕ) (ht : 3 ≤ t) [NeZero (3 * t)]
    (p : F × F) (v : Lane (3 * t)) :
    Qmap t (residual t p) v = 0 ↔ priceTail (p, fun i => v (priceIndex t i)) := by
  have indexCast (i : Fin 5) (n : ℕ) (hn : 3 * t - 5 + i.val = n) :
      priceIndex t i = (n : ZMod (3 * t)) := by rw [priceIndex, hn]
  have e1 := indexCast 1 (3 * t - 4) (by change 3 * t - 5 + 1 = _; omega)
  have e2 := indexCast 2 (3 * t - 3) (by change 3 * t - 5 + 2 = _; omega)
  have e3 := indexCast 3 (3 * t - 2) (by change 3 * t - 5 + 3 = _; omega)
  have e4 := indexCast 4 (3 * t - 1) (by change 3 * t - 5 + 4 = _; omega)
  obtain ⟨r1, r2, r3, r4⟩ := residual_tail_values t ht p
  rw [← e1] at r1
  rw [← e2] at r2
  rw [← e3] at r3
  rw [← e4] at r4
  have m1 := priceIndex_prev t 0 1 (by decide)
  have m2 := priceIndex_prev t 1 2 (by decide)
  have m3 := priceIndex_prev t 2 3 (by decide)
  have m4 := priceIndex_prev t 3 4 (by decide)
  rw [Qmap_eq_zero_iff t (by omega), priceTail]
  constructor
  · intro h
    exact ⟨by simpa only [r1, m1] using h (priceIndex t 1),
      by simpa only [r2, m2] using h (priceIndex t 2),
      by simpa only [r3, m3] using h (priceIndex t 3),
      by simpa only [r4, m4] using h (priceIndex t 4)⟩
  · rintro ⟨h1, h2, h3, h4⟩ a
    by_cases ha : a.val < 3 * t - 4
    · simp only [residual_below_tail t ht p a ha, zero_mul, and_self]
    have hlt := a.val_lt
    have hc : a.val = 3 * t - 4 ∨ a.val = 3 * t - 3 ∨
        a.val = 3 * t - 2 ∨ a.val = 3 * t - 1 := by omega
    rcases hc with h | h | h | h
    · rw [← ZMod.natCast_zmod_val a, h, ← e1, r1, m1]; exact h1
    · rw [← ZMod.natCast_zmod_val a, h, ← e2, r2, m2]; exact h2
    · rw [← ZMod.natCast_zmod_val a, h, ← e3, r3, m3]; exact h3
    · rw [← ZMod.natCast_zmod_val a, h, ← e4, r4, m4]; exact h4

private def priceTailEval (t : ℕ) [NeZero (3 * t)] : imSub t →ₗ[F] (Fin 5 → F) where
  toFun v i := v.1 (priceIndex t i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma price_parSum_single (t : ℕ) [NeZero (3 * t)] (a₀ : ZMod (3 * t))
    (c : F) (r : ZMod 3) :
    parSum t r (fun a => if a = a₀ then c else 0) = if res3 t a₀ = r then c else 0 := by
  rw [parSum_apply, Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma priceTailEval_surj (t : ℕ) (ht : 3 ≤ t) [NeZero (3 * t)] :
    Function.Surjective (priceTailEval t) := by
  classical
  have hinj : Function.Injective (priceIndex t) := by
    intro i j h
    have hv := congrArg ZMod.val h
    rw [priceIndex_val t ht, priceIndex_val t ht] at hv
    exact Fin.ext (by omega)
  intro y
  let w : Lane (3 * t) := Function.extend (priceIndex t) y (fun _ => 0)
  let c₀ : Lane (3 * t) := fun a => if a = 0 then parSum t 2 w - parSum t 0 w else 0
  let c₁ : Lane (3 * t) := fun a => if a = 1 then parSum t 2 w - parSum t 1 w else 0
  let v : Lane (3 * t) := w + c₀ + c₁
  have hv : v ∈ imSub t := by
    rw [mem_imSub_iff]
    simp only [v, c₀, c₁, map_add, price_parSum_single, map_zero, map_one, if_true,
      zero_ne_one, one_ne_zero, z3_zero_ne_two, z3_one_ne_two, if_false, add_zero]
    constructor <;> abel
  refine ⟨⟨v, hv⟩, ?_⟩
  funext i
  have h0 : priceIndex t i ≠ 0 := by
    intro he
    have h := congrArg ZMod.val he
    rw [priceIndex_val t ht, ZMod.val_zero] at h
    omega
  have h1 : priceIndex t i ≠ 1 := by
    intro he
    have h := congrArg ZMod.val he
    rw [priceIndex_val t ht, ZMod.val_one'' (by omega)] at h
    omega
  change v (priceIndex t i) = y i
  simpa only [v, c₀, c₁, Pi.add_apply, h0, h1, if_false, add_zero, w] using
    hinj.extend_apply y (fun _ => 0) i

private lemma price_card_surj {X Y : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] (f : X →ₗ[F] Y) (hf : Function.Surjective f) (P : Y → Prop) :
    Nat.card {x : X // P (f x)} = Nat.card (LinearMap.ker f) * Nat.card {y : Y // P y} := by
  let e : f.range ≃ Y :=
    { toFun := Subtype.val
      invFun := fun y => ⟨y, hf y⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have eP : {y : f.range // P y.1} ≃ {y : Y // P y} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  rw [card_preimage_linear f P, Nat.card_congr eP]

lemma residual_count (t : ℕ) (ht2 : 2 ≤ t) [NeZero (3 * t)] :
    64 * Nat.card {p : (F × F) × imSub t // Qmap t (residual t p.1) p.2.1 = 0} =
      numN t * Nat.card ((F × F) × imSub t) := by
  by_cases he : t = 2
  · subst t
    let e : {q : (F × F) × imSub 2 // Qmap 2 (residual 2 q.1) q.2.1 = 0} ≃
        {q : (F × F) × Lane 6 // priceSix q} :=
      { toFun := fun q => ⟨(q.1.1, q.1.2.1),
          (priceSix_compat q.1.2.1).mp q.1.2.2, (priceSix_q q.1.1 q.1.2.1).mp q.2⟩
        invFun := fun q => ⟨(q.1.1, ⟨q.1.2, (priceSix_compat q.1.2).mpr q.2.1⟩),
          (priceSix_q q.1.1 q.1.2).mpr q.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hk : Nat.card (F × F) = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    have hr := finrank_imSub_add_two 2 (by decide)
    have hr' : Module.finrank F (imSub 2) = 4 := by omega
    rw [Nat.card_congr e, priceSix_card, Nat.card_prod, hk, card_eq_two_pow_finrank, hr']
    rfl
  · have ht : 3 ≤ t := by omega
    let f : (F × F) × imSub t →ₗ[F] (F × F) × (Fin 5 → F) :=
      LinearMap.id.prodMap (priceTailEval t)
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨v, hv⟩ := priceTailEval_surj t ht q.2
      exact ⟨(q.1, v), Prod.ext rfl hv⟩
    let e : {q : (F × F) × imSub t // Qmap t (residual t q.1) q.2.1 = 0} ≃
        {q : (F × F) × imSub t // priceTail (f q)} :=
      Equiv.subtypeEquivRight (fun q => priceTail_q t ht q.1 q.2.1)
    have htotal : Nat.card ((F × F) × (Fin 5 → F)) = 128 := by
      rw [Nat.card_eq_fintype_card]
      norm_num [Fintype.card_prod, Fintype.card_fun]
    have hall := price_card_surj f hf (fun _ => True)
    simp only [Nat.card_subtype_true, htotal] at hall
    rw [Nat.card_congr e, price_card_surj f hf priceTail, priceTail_card, hall, numN, if_neg he]
    omega


-- Adapts the fixed-bank construction in lean/PEqualNP/Outside/L_meta_33654.lean
-- at 89d2fd4116d94c448b241700eb4b4b27f657d92a to a two-coordinate residual.
theorem lower_bound (t : ℕ) (ht : 0 < t) (ht2 : 2 ≤ t) [NeZero (3 * t)]
    (name c : Fin (6 * t) → F) :
    ∃ (ask : Fin (3 * t - 4) → ℕ → (Fin (6 * t) → F) →ₗ[F] F)
      (A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F))
      (b : ℕ → Fin (6 * t) → F),
      (∀ j p w, ask j p w = mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (2 * siteN t j))) ∧
      64 * Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 4) ask w) w + b (runN (6 * t) (3 * t - 4) ask w)} =
        numN t * 2 ^ (6 * t) := by
  classical
  let ask : Fin (3 * t - 4) → ℕ → (Fin (6 * t) → F) →ₗ[F] F :=
    fun j _ =>
      { toFun := fun w => mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (2 * siteN t j))
        map_add' := fun w1 w2 => congrFun (mixN_add (6 * t) (by omega) w1 w2) _
        map_smul' := fun r w => congrFun (mixN_smul (6 * t) (by omega) r w) _ }
  have hask_even : ∀ j p w, ask j p w = evenLane t ht w (siteN t j : ZMod (3 * t)) := by
    intro j p w
    dsimp only [ask, evenLane, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; apply Fin.ext; dsimp only [ixN]
    have hlt : siteN t j < 3 * t := by
      have hj := j.isLt
      unfold siteN
      split_ifs <;> omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]
  let key : Lane (3 * t) →ₗ[F] F × F :=
    { toFun := freeKey t
      map_add' := by intro u v; unfold freeKey; split_ifs <;> rfl
      map_smul' := by intro r u; unfold freeKey; split_ifs <;> rfl }
  let adjust : Lane (3 * t) → Lane (3 * t) := fun u => u + residual t (freeKey t u)
  have hadjust_mem (u : Lane (3 * t)) (hu : u ∈ imSub t) : adjust u ∈ imSub t :=
    (imSub t).add_mem hu (residual_mem t ht2 (freeKey t u))
  have hadjust_site (u : Lane (3 * t)) (j : Fin (3 * t - 4)) :
      adjust u (siteN t j : ZMod (3 * t)) = u (siteN t j : ZMod (3 * t)) := by
    dsimp only [adjust, Pi.add_apply]
    rw [residual_site t ht2, add_zero]
  have hadjust_key (u : Lane (3 * t)) : freeKey t (adjust u) = 0 := by
    change key (u + residual t (freeKey t u)) = 0
    rw [map_add]
    change freeKey t u + freeKey t (residual t (freeKey t u)) = 0
    rw [residual_key t ht2]
    apply Prod.ext
    · exact z2_add_self (freeKey t u).1
    · exact z2_add_self (freeKey t u).2
  let ubase : ℕ → Lane (3 * t) := fun p =>
    if hp : ∃ w : Fin (6 * t) → F, runN (6 * t) (3 * t - 4) ask w = p then
      adjust (evenLane t ht (Classical.choose hp))
    else 0
  let A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F) :=
    fun p => (Qmap t (ubase p)).comp (oddLane t ht) + Lbase t ht name
  let b : ℕ → Fin (6 * t) → F := fun _ => cbase t ht name c
  refine ⟨ask, A, b, fun _ _ _ => rfl, ?_⟩
  have hubase_diff : ∀ w : Fin (6 * t) → F,
      evenLane t ht w + ubase (runN (6 * t) (3 * t - 4) ask w) =
        residual t (freeKey t (evenLane t ht w)) := by
    intro w
    have hex : ∃ w' : Fin (6 * t) → F,
        runN (6 * t) (3 * t - 4) ask w' = runN (6 * t) (3 * t - 4) ask w := ⟨w, rfl⟩
    set w0 := Classical.choose hex
    have hw0 : runN (6 * t) (3 * t - 4) ask w0 = runN (6 * t) (3 * t - 4) ask w :=
      Classical.choose_spec hex
    have hub : ubase (runN (6 * t) (3 * t - 4) ask w) = adjust (evenLane t ht w0) := dif_pos hex
    rw [hub]
    have hpref : runPref (6 * t) (3 * t - 4) ask (3 * t - 4) w =
        runPref (6 * t) (3 * t - 4) ask (3 * t - 4) w0 := by
      have heq : ∀ u, runN (6 * t) (3 * t - 4) ask u =
          runPref (6 * t) (3 * t - 4) ask (3 * t - 4) u := by
        intro u; dsimp only [runN, runPref]
        rw [List.take_of_length_le (by rw [List.length_finRange])]
      rw [← heq w, ← heq w0, hw0]
    have hall := (runPref_eq_iff (6 * t) (3 * t - 4) ask w0 w (3 * t - 4) (le_refl _)).mp hpref
    have hm := (imSub t).add_mem (evenLane_mem_imSub t ht w)
      (hadjust_mem _ (evenLane_mem_imSub t ht w0))
    have hz : ∀ j : Fin (3 * t - 4),
        (evenLane t ht w + adjust (evenLane t ht w0)) (siteN t j : ZMod (3 * t)) = 0 := by
      intro j
      have hj := hall j j.isLt
      rw [hask_even j (runPref (6 * t) (3 * t - 4) ask j.val w0) w,
        hask_even j (runPref (6 * t) (3 * t - 4) ask j.val w0) w0] at hj
      rw [Pi.add_apply, hadjust_site, hj, z2_add_self]
    have hk : freeKey t (evenLane t ht w + adjust (evenLane t ht w0)) =
        freeKey t (evenLane t ht w) := by
      change key (evenLane t ht w + adjust (evenLane t ht w0)) = key (evenLane t ht w)
      rw [map_add]
      change freeKey t (evenLane t ht w) + freeKey t (adjust (evenLane t ht w0)) = _
      rw [hadjust_key, add_zero]
      rfl
    exact (residual_identify t ht2 hm hz).trans (congrArg (residual t) hk)
  have hhit_iff : ∀ w : Fin (6 * t) → F,
      outN (6 * t) (by omega) name c w =
        A (runN (6 * t) (3 * t - 4) ask w) w + b (runN (6 * t) (3 * t - 4) ask w) ↔
      Qmap t (residual t (freeKey t (evenLane t ht w))) (oddLane t ht w) = 0 := by
    intro w
    rw [← hubase_diff w, outN_decomp t ht name c w]
    dsimp only [A, b, LinearMap.add_apply, LinearMap.comp_apply]
    rw [map_add, LinearMap.add_apply]
    constructor
    · intro h
      have h1 := add_right_cancel (add_right_cancel h)
      rw [h1, vec_add_self]
    · intro h
      have h1 : Qmap t (evenLane t ht w) (oddLane t ht w) =
          Qmap t (ubase (runN (6 * t) (3 * t - 4) ask w)) (oddLane t ht w) := by
        calc Qmap t (evenLane t ht w) (oddLane t ht w)
            = (Qmap t (evenLane t ht w) (oddLane t ht w) +
                Qmap t (ubase (runN (6 * t) (3 * t - 4) ask w)) (oddLane t ht w)) +
              Qmap t (ubase (runN (6 * t) (3 * t - 4) ask w)) (oddLane t ht w) := by
                rw [add_assoc, vec_add_self, add_zero]
          _ = _ := by rw [h, zero_add]
      rw [h1]
  let f : (Fin (6 * t) → F) →ₗ[F] (F × F) × imSub t :=
    (key.comp (evenLane t ht)).prod
      ((oddLane t ht).codRestrict (imSub t) (oddLane_mem_imSub t ht))
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨w, he, ho⟩ := exists_even_odd t ht (residual_mem t ht2 p.1) p.2.2
    refine ⟨w, Prod.ext ?_ (Subtype.ext ho)⟩
    change freeKey t (evenLane t ht w) = p.1
    rw [he, residual_key t ht2]
  let good : (F × F) × imSub t → Prop := fun p => Qmap t (residual t p.1) p.2.1 = 0
  have hpre := card_preimage_linear f good
  let erange : f.range ≃ₗ[F] (F × F) × imSub t :=
    (LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.mpr hsurj)).trans Submodule.topEquiv
  have hrange : Nat.card {y : f.range // good y.1} = Nat.card {p // good p} :=
    Nat.card_congr
      { toFun := fun y => ⟨erange y.1, y.2⟩
        invFun := fun p => ⟨erange.symm p.1, p.2⟩
        left_inv := fun y => Subtype.ext (erange.symm_apply_apply y.1)
        right_inv := fun p => Subtype.ext (erange.apply_symm_apply p.1) }
  have htotal : Nat.card (LinearMap.ker f) * Nat.card ((F × F) × imSub t) = 2 ^ (6 * t) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, ← Nat.pow_add, Nat.add_comm, hrk]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hhit_iff)]
  change 64 * Nat.card {w // good (f w)} = numN t * 2 ^ (6 * t)
  rw [hpre, hrange, Nat.mul_left_comm 64, show 64 * Nat.card {p // good p} =
    numN t * Nat.card ((F × F) × imSub t) from residual_count t ht2,
    Nat.mul_left_comm _ (numN t), htotal]


lemma main (t : ℕ) (ht : 0 < t) (ht2 : 2 ≤ t) (name c : Fin (6 * t) → F) (fixed : Bool) (k : ℕ) :
    (∃ (ask : Fin (3 * t - 4) → ℕ → (Fin (6 * t) → F) →ₗ[F] F)
       (A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F))
       (b : ℕ → Fin (6 * t) → F),
      (fixed = true → ∀ j p w,
        ask j p w = mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (2 * siteN t j))) ∧
      k ≤ Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 4) ask w) w + b (runN (6 * t) (3 * t - 4) ask w)}) ↔
    64 * k ≤ numN t * 2 ^ (6 * t) := by
  have : NeZero (3 * t) := ⟨by omega⟩
  constructor
  · rintro ⟨ask, A, b, _, hk⟩
    exact (Nat.mul_le_mul_left 64 hk).trans (upper_bound t ht ht2 name c ask A b)
  · intro hk
    obtain ⟨ask, A, b, hfix, heq⟩ := lower_bound t ht ht2 name c
    exact ⟨ask, A, b, fun _ => hfix, Nat.le_of_mul_le_mul_left (hk.trans heq.symm.le) (by decide)⟩

end PEqualNP.Outside.L_meta_33656_aux

theorem PEqualNP.Outside.L_meta_33656 : ∀ (t : ℕ) (ht : 0 < t), 2 ≤ t →
  let h := 3*t-4
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
  let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
    (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let site := fun j : Fin h => if t = 2 then (2+3*j.val) else j.val
  let num := if t = 2 then 21 else 19
  ∀ (name c : W) (fixed : Bool) (k : ℕ),
    (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w = mix w (ix (2*site j))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔ 64*k ≤ num*2^n := by
  intro t ht ht2
  dsimp only
  intro name c fixed k
  have hsite : ∀ j : Fin (3 * t - 4),
      @ite ℕ (t = 2) (Classical.propDecidable _) (2 + 3 * j.val) j.val =
        PEqualNP.Outside.L_meta_33656_aux.siteN t j := by
    intro j; dsimp only [PEqualNP.Outside.L_meta_33656_aux.siteN]; split_ifs <;> rfl
  have hnum : @ite ℕ (t = 2) (Classical.propDecidable _) 21 19 =
      PEqualNP.Outside.L_meta_33656_aux.numN t := by
    dsimp only [PEqualNP.Outside.L_meta_33656_aux.numN]; split_ifs <;> rfl
  simp only [hsite, hnum]
  exact PEqualNP.Outside.L_meta_33656_aux.main t ht ht2 name c fixed k

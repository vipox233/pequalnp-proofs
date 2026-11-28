import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

namespace PEqualNP.Outside.L_meta_33654

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

lemma nat_pow_convex (g d : ℕ) (hd1 : 1 ≤ d) (hdg : d < g) :
    2 ^ (g + 1) + 2 ^ d * (2 ^ d - 1) ≤ (2 ^ g + 1) * 2 ^ d := by
  have h2d : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd1
  have hdg2 : 2 ^ d ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) (le_of_lt hdg)
  have hmul : (2 ^ d - 2) * 2 ^ d ≤ (2 ^ d - 2) * 2 ^ g := Nat.mul_le_mul_left _ hdg2
  have h1 : (2 ^ d - 2) * 2 ^ d + 2 * 2 ^ d = 2 ^ d * 2 ^ d := by
    rw [← Nat.add_mul, Nat.sub_add_cancel h2d]
  have h2 : (2 ^ d - 2) * 2 ^ g + 2 * 2 ^ g = 2 ^ d * 2 ^ g := by
    rw [← Nat.add_mul, Nat.sub_add_cancel h2d]
  have h3 : 2 ^ d * (2 ^ d - 1) + 2 ^ d = 2 ^ d * 2 ^ d := by
    have hpos : 1 ≤ 2 ^ d := by omega
    calc 2 ^ d * (2 ^ d - 1) + 2 ^ d = 2 ^ d * (2 ^ d - 1) + 2 ^ d * 1 := by rw [Nat.mul_one]
      _ = 2 ^ d * ((2 ^ d - 1) + 1) := by rw [← Nat.mul_add]
      _ = 2 ^ d * 2 ^ d := by rw [Nat.sub_add_cancel hpos]
  have h4 : 2 ^ (g + 1) = 2 * 2 ^ g := by rw [Nat.pow_succ, Nat.mul_comm]
  have h5 : (2 ^ g + 1) * 2 ^ d = 2 ^ d * 2 ^ g + 2 ^ d := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ g)]
  omega

theorem bilinear_zero_frac
    {U V W : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W]
    (B : U →ₗ[F] V →ₗ[F] W) (g : ℕ) (_hg : 1 ≤ g)
    (hU : 1 ≤ Module.finrank F U) (hV : 1 ≤ Module.finrank F V)
    (hUV : g + 1 ≤ Module.finrank F U + Module.finrank F V)
    (hgap : ∀ (U' : Submodule F U) (V' : Submodule F V),
      U' ≠ ⊥ → V' ≠ ⊥ → (∀ u ∈ U', ∀ v ∈ V', B u v = 0) →
      Module.finrank F U' + Module.finrank F V' + g ≤ Module.finrank F U + Module.finrank F V) :
    2 ^ (g + 1) * Nat.card {p : U × V // B p.1 p.2 = 0} ≤
      (2 ^ g + 1) * (Nat.card U * Nat.card V) := by
  classical
  have : Finite U := Module.finite_of_finite F
  have : Finite V := Module.finite_of_finite F
  let _ : Fintype U := Fintype.ofFinite U
  let _ : Fintype V := Fintype.ofFinite V
  have hsum : Nat.card {p : U × V // B p.1 p.2 = 0} =
      ∑ u : U, Nat.card {v : V // B u v = 0} := by
    have e : {p : U × V // B p.1 p.2 = 0} ≃ Σ u : U, {v : V // B u v = 0} :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, ← Fintype.card_eq_nat_card, Fintype.card_sigma]
    refine Finset.sum_congr rfl (fun u _ => Fintype.card_eq_nat_card)
  have hker_card : ∀ u : U, Nat.card {v : V // B u v = 0} =
      2 ^ Module.finrank F (LinearMap.ker (B u)) := by
    intro u
    have e : {v : V // B u v = 0} ≃ LinearMap.ker (B u) :=
      Equiv.subtypeEquivRight (fun _ => LinearMap.mem_ker.symm)
    rw [Nat.card_congr e, card_eq_two_pow_finrank]
  have hcardU : Nat.card U = 2 ^ Module.finrank F U := card_eq_two_pow_finrank
  have hcardV : Nat.card V = 2 ^ Module.finrank F V := card_eq_two_pow_finrank
  let U0 : Submodule F U := LinearMap.ker B
  by_cases hbr : U0 ≠ ⊥ ∨ g ≤ Module.finrank F U
  · have hU0_dim : Module.finrank F U0 + g ≤ Module.finrank F U := by
      have htop : (⊤ : Submodule F V) ≠ ⊥ := by
        intro hbot
        have : Module.finrank F (⊤ : Submodule F V) = 0 := by
          rw [hbot]; exact finrank_bot F V
        rw [finrank_top] at this; omega
      rcases hbr with hne | hle
      · have hg0 := hgap U0 ⊤ hne htop (fun u hu v _ => by
          have : B u = 0 := LinearMap.mem_ker.mp hu
          rw [this]; rfl)
        rw [finrank_top] at hg0; omega
      · by_cases hne : U0 = ⊥
        · have : Module.finrank F U0 = 0 := (Submodule.finrank_eq_zero).mpr hne
          omega
        · have hg0 := hgap U0 ⊤ hne htop (fun u hu v _ => by
            have : B u = 0 := LinearMap.mem_ker.mp hu
            rw [this]; rfl)
          rw [finrank_top] at hg0; omega
    have hcardU0_le : 2 ^ g * Nat.card U0 ≤ Nat.card U := by
      rw [card_eq_two_pow_finrank, hcardU, ← Nat.pow_add, Nat.add_comm]
      exact Nat.pow_le_pow_right (by omega) hU0_dim
    have hnot : ∀ u : U, u ∉ U0 → 2 * Nat.card {v : V // B u v = 0} ≤ Nat.card V := by
      intro u hu
      have hne : LinearMap.ker (B u) ≠ ⊤ := by
        intro htop
        apply hu
        rw [LinearMap.mem_ker]
        ext v
        have hv : v ∈ LinearMap.ker (B u) := by rw [htop]; trivial
        exact LinearMap.mem_ker.mp hv
      have hlt : LinearMap.ker (B u) < ⊤ := lt_of_le_of_ne le_top hne
      have hfl : Module.finrank F (LinearMap.ker (B u)) < Module.finrank F V := by
        simpa only [finrank_top] using Submodule.finrank_lt_finrank_of_lt hlt
      rw [hker_card, hcardV, ← Nat.pow_succ']
      exact Nat.pow_le_pow_right (by omega) hfl
    have hin : ∀ u : U, Nat.card {v : V // B u v = 0} ≤ Nat.card V := by
      intro u
      rw [hker_card, hcardV]
      exact Nat.pow_le_pow_right (by omega) (Submodule.finrank_le _)
    have h2H : 2 * Nat.card {p : U × V // B p.1 p.2 = 0} ≤
        (Nat.card U + Nat.card U0) * Nat.card V := by
      rw [hsum, Finset.mul_sum]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : U => u ∈ U0)]
      have s1 : ∑ u ∈ Finset.univ.filter (fun u : U => u ∈ U0),
          2 * Nat.card {v : V // B u v = 0} ≤
          (Finset.univ.filter (fun u : U => u ∈ U0)).card * (2 * Nat.card V) := by
        calc ∑ u ∈ Finset.univ.filter (fun u : U => u ∈ U0),
              2 * Nat.card {v : V // B u v = 0}
            ≤ ∑ _u ∈ Finset.univ.filter (fun u : U => u ∈ U0), (2 * Nat.card V) :=
              Finset.sum_le_sum (fun u _ => Nat.mul_le_mul_left 2 (hin u))
          _ = _ := by rw [Finset.sum_const, smul_eq_mul]
      have s2 : ∑ u ∈ Finset.univ.filter (fun u : U => u ∉ U0),
          2 * Nat.card {v : V // B u v = 0} ≤
          (Finset.univ.filter (fun u : U => u ∉ U0)).card * Nat.card V := by
        calc ∑ u ∈ Finset.univ.filter (fun u : U => u ∉ U0),
              2 * Nat.card {v : V // B u v = 0}
            ≤ ∑ _u ∈ Finset.univ.filter (fun u : U => u ∉ U0), Nat.card V :=
              Finset.sum_le_sum (fun u hu => hnot u (Finset.mem_filter.mp hu).2)
          _ = _ := by rw [Finset.sum_const, smul_eq_mul]
      have hc0 : (Finset.univ.filter (fun u : U => u ∈ U0)).card = Nat.card U0 := by
        rw [← Fintype.card_eq_nat_card, Fintype.card_subtype]
      have hc1 : (Finset.univ.filter (fun u : U => u ∈ U0)).card +
          (Finset.univ.filter (fun u : U => u ∉ U0)).card = Nat.card U := by
        rw [card_filter_add_not, Fintype.card_eq_nat_card]
      have htot := Nat.add_le_add s1 s2
      have hcard_eq : (Finset.univ.filter (fun u : U => u ∈ U0)).card * (2 * Nat.card V) +
          (Finset.univ.filter (fun u : U => u ∉ U0)).card * Nat.card V =
          (Nat.card U + Nat.card U0) * Nat.card V := by
        have hstep1 : (Finset.univ.filter (fun u : U => u ∈ U0)).card * (2 * Nat.card V) =
            (2 * (Finset.univ.filter (fun u : U => u ∈ U0)).card) * Nat.card V := by
          rw [← Nat.mul_assoc, Nat.mul_comm _ 2]
        rw [hstep1, ← Nat.add_mul, show 2 * (Finset.univ.filter (fun u : U => u ∈ U0)).card +
            (Finset.univ.filter (fun u : U => u ∉ U0)).card = Nat.card U + Nat.card U0 by omega]
      exact htot.trans_eq hcard_eq
    calc 2 ^ (g + 1) * Nat.card {p : U × V // B p.1 p.2 = 0}
        = 2 ^ g * (2 * Nat.card {p : U × V // B p.1 p.2 = 0}) := by
            rw [Nat.pow_succ, ← Nat.mul_assoc]
      _ ≤ 2 ^ g * ((Nat.card U + Nat.card U0) * Nat.card V) := Nat.mul_le_mul_left _ h2H
      _ = (2 ^ g * Nat.card U + 2 ^ g * Nat.card U0) * Nat.card V := by ring
      _ ≤ (2 ^ g * Nat.card U + Nat.card U) * Nat.card V :=
            Nat.mul_le_mul_right _ (Nat.add_le_add_left hcardU0_le _)
      _ = (2 ^ g + 1) * (Nat.card U * Nat.card V) := by ring
  · push Not at hbr
    rcases hbr with ⟨_, hdg⟩
    set d := Module.finrank F U
    have hnz : ∀ u : U, u ≠ 0 →
        2 ^ (g - d + 1) * Nat.card {v : V // B u v = 0} ≤ Nat.card V := by
      intro u hu
      let Vu : Submodule F V := LinearMap.ker (B u)
      have hdim : Module.finrank F Vu + (g - d + 1) ≤ Module.finrank F V := by
        by_cases hVu : Vu = ⊥
        · have : Module.finrank F Vu = 0 := (Submodule.finrank_eq_zero).mpr hVu
          omega
        · have hsp_ne : Submodule.span F ({u} : Set U) ≠ ⊥ := by
            intro hbot
            have : u ∈ (⊥ : Submodule F U) := by
              rw [← hbot]; exact Submodule.mem_span_singleton_self u
            exact hu ((Submodule.mem_bot F).mp this)
          have hsp_dim : Module.finrank F (Submodule.span F ({u} : Set U)) = 1 :=
            finrank_span_singleton hu
          have hg0 := hgap (Submodule.span F {u}) Vu hsp_ne hVu (fun x hx v hv => by
            obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
            rw [map_smul, LinearMap.smul_apply, LinearMap.mem_ker.mp hv, smul_zero])
          rw [hsp_dim] at hg0
          omega
      rw [hker_card, hcardV, ← Nat.pow_add, Nat.add_comm]
      exact Nat.pow_le_pow_right (by omega) hdim
    have h0 : Nat.card {v : V // B 0 v = 0} = Nat.card V := by
      refine Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => by simp))
    have hpowH : 2 ^ (g - d + 1) * Nat.card {p : U × V // B p.1 p.2 = 0} ≤
        (2 ^ (g - d + 1) + (2 ^ d - 1)) * Nat.card V := by
      rw [hsum, Finset.mul_sum]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : U)), h0]
      have hrest : ∑ u ∈ Finset.univ.erase (0 : U), 2 ^ (g - d + 1) * Nat.card {v : V // B u v = 0} ≤
          (Finset.univ.erase (0 : U)).card * Nat.card V := by
        calc ∑ u ∈ Finset.univ.erase (0 : U), 2 ^ (g - d + 1) * Nat.card {v : V // B u v = 0}
            ≤ ∑ _u ∈ Finset.univ.erase (0 : U), Nat.card V :=
              Finset.sum_le_sum (fun u hu => hnz u (Finset.mem_erase.mp hu).1)
          _ = _ := by rw [Finset.sum_const, smul_eq_mul]
      have hcard_er : (Finset.univ.erase (0 : U)).card = 2 ^ d - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_eq_nat_card, hcardU]
      rw [hcard_er] at hrest
      rw [Nat.add_mul]
      exact Nat.add_le_add_left hrest _
    have hexp : d + (g - d + 1) = g + 1 := by omega
    calc 2 ^ (g + 1) * Nat.card {p : U × V // B p.1 p.2 = 0}
        = 2 ^ d * (2 ^ (g - d + 1) * Nat.card {p : U × V // B p.1 p.2 = 0}) := by
            rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
      _ ≤ 2 ^ d * ((2 ^ (g - d + 1) + (2 ^ d - 1)) * Nat.card V) := Nat.mul_le_mul_left _ hpowH
      _ = (2 ^ (g + 1) + 2 ^ d * (2 ^ d - 1)) * Nat.card V := by
            rw [← Nat.mul_assoc, Nat.mul_add, ← Nat.pow_add, hexp]
      _ ≤ ((2 ^ g + 1) * 2 ^ d) * Nat.card V :=
            Nat.mul_le_mul_right _ (nat_pow_convex g d hU hdg)
      _ = (2 ^ g + 1) * (Nat.card U * Nat.card V) := by
            rw [hcardU, Nat.mul_assoc]

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

def siteN (t : ℕ) (j : Fin (3 * t - 3)) : ℕ :=
  if t = 2 then (if j.val = 0 then 2 else j.val + 3) else j.val

def numN (t : ℕ) : ℕ := if t = 1 then 3 else if t = 2 then 9 else 17

def denN (t : ℕ) : ℕ := if t = 1 then 4 else if t = 2 then 16 else 32

def gapN (t : ℕ) : ℕ := if t = 1 then 1 else if t = 2 then 3 else 4

lemma denN_eq_pow (t : ℕ) : denN t = 2 ^ (gapN t + 1) := by
  dsimp only [denN, gapN]; split_ifs <;> norm_num

lemma numN_eq_pow (t : ℕ) : numN t = 2 ^ gapN t + 1 := by
  dsimp only [numN, gapN]; split_ifs <;> norm_num

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

lemma coset_upper_bound (t : ℕ) (ht : 0 < t) [NeZero (3 * t)]
    (name c : Fin (6 * t) → F) (w0 : Fin (6 * t) → F)
    (K : Submodule F (Fin (6 * t) → F)) (hK : 6 * t ≤ Module.finrank F K + (3 * t - 3))
    (A : (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F)) (b : Fin (6 * t) → F) :
    denN t * Nat.card {x : K // outN (6 * t) (by omega) name c (w0 + x.1) = A (w0 + x.1) + b} ≤
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
  have hdimUV : 3 * t - 1 ≤ Module.finrank F U + Module.finrank F V := by omega
  have him_dim := finrank_imSub_add_two t ht
  have hU_le : Module.finrank F U ≤ 3 * t - 2 := by
    have := Submodule.finrank_mono hU_im; omega
  have hV_le : Module.finrank F V ≤ 3 * t - 2 := by
    have := Submodule.finrank_mono hV_im; omega
  have hU_pos : 1 ≤ Module.finrank F U := by omega
  have hV_pos : 1 ≤ Module.finrank F V := by omega
  let B : U →ₗ[F] V →ₗ[F] (Fin (6 * t) → F) :=
    { toFun := fun u =>
        { toFun := fun v => Qmap t u.1 v.1
          map_add' := fun v1 v2 => map_add (Qmap t u.1) v1.1 v2.1
          map_smul' := fun c v => map_smul (Qmap t u.1) c v.1 }
      map_add' := fun u1 u2 => by
        apply LinearMap.ext; intro v; funext i
        exact congrFun (congrArg (fun f => f v.1) (map_add (Qmap t) u1.1 u2.1)) i
      map_smul' := fun c u => by
        apply LinearMap.ext; intro v; funext i
        exact congrFun (congrArg (fun f => f v.1) (map_smul (Qmap t) c u.1)) i }
  have hgap : ∀ (U' : Submodule F U) (V' : Submodule F V),
      U' ≠ ⊥ → V' ≠ ⊥ → (∀ u ∈ U', ∀ v ∈ V', B u v = 0) →
      Module.finrank F U' + Module.finrank F V' + gapN t ≤
        Module.finrank F U + Module.finrank F V := by
    intro U' V' hU' hV' hB0
    let U'' : Submodule F (Lane (3 * t)) := U'.map U.subtype
    let V'' : Submodule F (Lane (3 * t)) := V'.map V.subtype
    have hU''_im : U'' ≤ imSub t := by
      rintro _ ⟨u, _, rfl⟩; exact hU_im u.2
    have hV''_im : V'' ≤ imSub t := by
      rintro _ ⟨v, _, rfl⟩; exact hV_im v.2
    have hU''_ne : U'' ≠ ⊥ := by
      intro hbot
      apply hU'
      rw [eq_bot_iff]; intro u hu
      have : U.subtype u ∈ (⊥ : Submodule F (Lane (3 * t))) := by
        rw [← hbot]; exact Submodule.mem_map_of_mem hu
      exact (Submodule.mem_bot F).mpr (Subtype.ext ((Submodule.mem_bot F).mp this))
    have hV''_ne : V'' ≠ ⊥ := by
      intro hbot
      apply hV'
      rw [eq_bot_iff]; intro v hv
      have : V.subtype v ∈ (⊥ : Submodule F (Lane (3 * t))) := by
        rw [← hbot]; exact Submodule.mem_map_of_mem hv
      exact (Submodule.mem_bot F).mpr (Subtype.ext ((Submodule.mem_bot F).mp this))
    have hU''_dim : Module.finrank F U'' = Module.finrank F U' :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype Subtype.val_injective U')).symm
    have hV''_dim : Module.finrank F V'' = Module.finrank F V' :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective V.subtype Subtype.val_injective V')).symm
    have hQ0 : ∀ u ∈ U'', ∀ v ∈ V'', ∀ a : ZMod (3 * t),
        u a * v a = 0 ∧ u a * v (a - 1) = 0 := by
      intro u hu v hv
      rcases Submodule.mem_map.mp hu with ⟨u0, hu0, rfl⟩
      rcases Submodule.mem_map.mp hv with ⟨v0, hv0, rfl⟩
      exact (Qmap_eq_zero_iff t ht u0.1 v0.1).mp (hB0 u0 hu0 v0 hv0)
    have hg := gap_imSub t ht U'' V'' hU''_im hV''_im hU''_ne hV''_ne hQ0
    dsimp only [gapN]
    rw [← hU''_dim, ← hV''_dim]
    exact hg.trans hdimUV
  have hUV_gap : gapN t + 1 ≤ Module.finrank F U + Module.finrank F V := by
    dsimp only [gapN]; split_ifs <;> omega
  have hgap_pos : 1 ≤ gapN t := by dsimp only [gapN]; split_ifs <;> omega
  have hbil := bilinear_zero_frac B (gapN t) hgap_pos hU_pos hV_pos hUV_gap hgap
  rw [← denN_eq_pow t, ← numN_eq_pow t] at hbil
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
      Nat.card {p : U × V // B p.1 p.2 = 0} :=
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
  have hmul : denN t * (Nat.card KZ *
      Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d}) ≤
      numN t * (Nat.card K * Nat.card KZ) := by
    calc denN t * (Nat.card KZ *
          Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d})
        ≤ denN t * Nat.card {p : K × KZ // Qmap t (evenLane t ht p.1.1) (oddLane t ht p.2.1) = 0} :=
          Nat.mul_le_mul_left _ hdc
      _ = denN t * (Nat.card (LinearMap.ker fEO) * Nat.card {p : U × V // B p.1 p.2 = 0}) := by
          rw [← hcard_UV]; exact congrArg (denN t * ·) hpre
      _ = Nat.card (LinearMap.ker fEO) * (denN t * Nat.card {p : U × V // B p.1 p.2 = 0}) := by
          rw [Nat.mul_left_comm]
      _ ≤ Nat.card (LinearMap.ker fEO) * (numN t * (Nat.card U * Nat.card V)) :=
          Nat.mul_le_mul_left _ hbil
      _ = numN t * ((Nat.card KZ * Nat.card U) * (Nat.card (LinearMap.ker fO) * Nat.card V)) := by
          rw [hcard_kerEO]; ring
      _ = numN t * (Nat.card K * Nat.card KZ) := by rw [hcard_KZ_K, hcard_kerO_KZ]
  have hKZ_pos : 0 < Nat.card KZ := by
    rw [card_eq_two_pow_finrank]; exact Nat.pos_of_ne_zero (by positivity)
  have hre : Nat.card KZ * (denN t *
      Nat.card {x : K // Qmap t (evenLane t ht x.1) (oddLane t ht x.1) = L x.1 + d}) ≤
      Nat.card KZ * (numN t * Nat.card K) := by
    calc Nat.card KZ * (denN t * _)
        = denN t * (Nat.card KZ * _) := Nat.mul_left_comm _ _ _
      _ ≤ numN t * (Nat.card K * Nat.card KZ) := hmul
      _ = Nat.card KZ * (numN t * Nat.card K) := by ring
  exact Nat.le_of_mul_le_mul_left hre hKZ_pos

theorem upper_bound (t : ℕ) (ht : 0 < t) [NeZero (3 * t)]
    (name c : Fin (6 * t) → F)
    (ask : Fin (3 * t - 3) → ℕ → (Fin (6 * t) → F) →ₗ[F] F)
    (A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F))
    (b : ℕ → Fin (6 * t) → F) :
    denN t * Nat.card {w : Fin (6 * t) → F //
      outN (6 * t) (by omega) name c w =
        A (runN (6 * t) (3 * t - 3) ask w) w + b (runN (6 * t) (3 * t - 3) ask w)} ≤
      numN t * 2 ^ (6 * t) := by
  classical
  let P : Finset ℕ := Finset.univ.image (runN (6 * t) (3 * t - 3) ask)
  have hpart_hit : Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 3) ask w) w + b (runN (6 * t) (3 * t - 3) ask w)} =
      ∑ p ∈ P, Nat.card {w : Fin (6 * t) → F //
        runN (6 * t) (3 * t - 3) ask w = p ∧
        outN (6 * t) (by omega) name c w = A p w + b p} := by
    simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    have hdisj : (P : Set ℕ).PairwiseDisjoint (fun p =>
        Finset.univ.filter (fun w : Fin (6 * t) → F =>
          runN (6 * t) (3 * t - 3) ask w = p ∧
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
    · intro h; exact ⟨runN (6 * t) (3 * t - 3) ask w, ⟨w, rfl⟩, rfl, h⟩
    · rintro ⟨p, _, rfl, h⟩; exact h
  have hpart_all : 2 ^ (6 * t) =
      ∑ p ∈ P, Nat.card {w : Fin (6 * t) → F // runN (6 * t) (3 * t - 3) ask w = p} := by
    simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    have hdisj : (P : Set ℕ).PairwiseDisjoint (fun p =>
        Finset.univ.filter (fun w : Fin (6 * t) → F => runN (6 * t) (3 * t - 3) ask w = p)) := by
      intro p1 _ p2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [← Finset.card_biUnion hdisj]
    have huniv : P.biUnion (fun p =>
        Finset.univ.filter (fun w : Fin (6 * t) → F => runN (6 * t) (3 * t - 3) ask w = p)) =
        Finset.univ := by
      ext w
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, P,
        Finset.mem_image]
      exact ⟨runN (6 * t) (3 * t - 3) ask w, ⟨w, rfl⟩, rfl⟩
    rw [huniv, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hpart_hit, hpart_all, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  rcases Finset.mem_image.mp hp with ⟨w0, _, rfl⟩
  obtain ⟨K, hK, hcoset⟩ := runN_fiber_coset (6 * t) (3 * t - 3) ask w0
  have e_hit : {w : Fin (6 * t) → F //
      runN (6 * t) (3 * t - 3) ask w = runN (6 * t) (3 * t - 3) ask w0 ∧
      outN (6 * t) (by omega) name c w =
        A (runN (6 * t) (3 * t - 3) ask w0) w + b (runN (6 * t) (3 * t - 3) ask w0)} ≃
      {x : K // outN (6 * t) (by omega) name c (w0 + x.1) =
        A (runN (6 * t) (3 * t - 3) ask w0) (w0 + x.1) + b (runN (6 * t) (3 * t - 3) ask w0)} :=
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
      runN (6 * t) (3 * t - 3) ask w = runN (6 * t) (3 * t - 3) ask w0} ≃ K :=
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
  exact coset_upper_bound t ht name c w0 K hK
    (A (runN (6 * t) (3 * t - 3) ask w0)) (b (runN (6 * t) (3 * t - 3) ask w0))

def dStar (t : ℕ) [NeZero (3 * t)] : Lane (3 * t) :=
  if t = 1 then
    fun _ => 1
  else if t = 2 then
    fun a => if a = 0 ∨ a = 3 then 1 else 0
  else
    fun a => if a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
                a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
                a = ((3 * t - 1 : ℕ) : ZMod (3 * t)) then 1 else 0

lemma dStar_ne_zero (t : ℕ) (_ht : 0 < t) [NeZero (3 * t)] : dStar t ≠ 0 := by
  intro h
  dsimp only [dStar] at h
  split_ifs at h with ht1 ht2
  · have := congrFun h 0; exact one_ne_zero this
  · have := congrFun h 0; simp at this
  · have := congrFun h ((3 * t - 1 : ℕ) : ZMod (3 * t)); simp at this

lemma parSum_single (t : ℕ) [NeZero (3 * t)] (a0 : ZMod (3 * t)) (c : F) (r : ZMod 3) :
    parSum t r (fun a => if a = a0 then c else 0) = if res3 t a0 = r then c else 0 := by
  rw [parSum_apply, Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma dStar_mem_imSub (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] : dStar t ∈ imSub t := by
  dsimp only [dStar]
  split_ifs with ht1 ht2
  · subst ht1
    rw [mem_imSub_iff]
    have hval : ∀ r : ZMod 3, parSum 1 r (fun _ => 1) = 1 := by
      intro r; rw [parSum_apply]
      have hf : Finset.univ.filter (fun x : ZMod 3 => res3 1 x = r) = {r} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, res3_one_id]
      rw [hf, Finset.sum_singleton]
    rw [hval, hval, hval]; exact ⟨rfl, rfl⟩
  · subst ht2
    rw [mem_imSub_iff]
    have hps : ∀ r : ZMod 3, parSum 2 r (fun a => if a = 0 ∨ a = 3 then 1 else 0) = 0 := by
      intro r
      have hdecomp : (fun a : ZMod 6 => if a = 0 ∨ a = 3 then (1 : F) else 0) =
          (fun a => if a = 0 then 1 else 0) + (fun a => if a = 3 then 1 else 0) := by
        funext a; revert a; decide
      rw [hdecomp, map_add, parSum_single, parSum_single]
      have hr0 : res3 2 0 = 0 := by decide
      have hr3 : res3 2 3 = 0 := by decide
      rw [hr0, hr3, z2_add_self]
    rw [hps, hps, hps]; exact ⟨rfl, rfl⟩
  · have h3 : 3 ≤ t := by omega
    have hdecomp : (fun a : ZMod (3 * t) =>
        if a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
           a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
           a = ((3 * t - 1 : ℕ) : ZMod (3 * t)) then (1 : F) else 0) =
        (fun a => if a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) then 1 else 0) +
        (fun a => if a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) then 1 else 0) +
        (fun a => if a = ((3 * t - 1 : ℕ) : ZMod (3 * t)) then 1 else 0) := by
      have hne12 : ((3 * t - 3 : ℕ) : ZMod (3 * t)) ≠ ((3 * t - 2 : ℕ) : ZMod (3 * t)) := by
        intro h; have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      have hne13 : ((3 * t - 3 : ℕ) : ZMod (3 * t)) ≠ ((3 * t - 1 : ℕ) : ZMod (3 * t)) := by
        intro h; have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      have hne23 : ((3 * t - 2 : ℕ) : ZMod (3 * t)) ≠ ((3 * t - 1 : ℕ) : ZMod (3 * t)) := by
        intro h; have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      funext a; dsimp only [Pi.add_apply]
      by_cases h1 : a = ((3 * t - 3 : ℕ) : ZMod (3 * t))
      · subst h1; simp [hne12, hne13]
      · by_cases h2 : a = ((3 * t - 2 : ℕ) : ZMod (3 * t))
        · subst h2; simp [hne12.symm, hne23]
        · by_cases h3a : a = ((3 * t - 1 : ℕ) : ZMod (3 * t))
          · subst h3a; simp [hne13.symm, hne23.symm]
          · simp [h1, h2, h3a]
    have hr3a : res3 t ((3 * t - 3 : ℕ) : ZMod (3 * t)) = 0 := by
      rw [map_natCast, show 3 * t - 3 = 3 * (t - 1) by omega]
      push_cast; rw [z3_three_zero, zero_mul]
    have hr3b : res3 t ((3 * t - 2 : ℕ) : ZMod (3 * t)) = 1 := by
      rw [map_natCast, show 3 * t - 2 = 3 * (t - 1) + 1 by omega]
      push_cast; rw [z3_three_zero, zero_mul, zero_add]
    have hr3c : res3 t ((3 * t - 1 : ℕ) : ZMod (3 * t)) = 2 := by
      rw [map_natCast, show 3 * t - 1 = 3 * (t - 1) + 2 by omega]
      push_cast; rw [z3_three_zero, zero_mul, zero_add]
    have hps : ∀ r : ZMod 3, parSum t r (fun a =>
        if a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
           a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
           a = ((3 * t - 1 : ℕ) : ZMod (3 * t)) then (1 : F) else 0) = 1 := by
      intro r
      rw [hdecomp, map_add, map_add, parSum_single, parSum_single, parSum_single,
        hr3a, hr3b, hr3c]
      revert r; decide
    rw [mem_imSub_iff, hps 0, hps 1, hps 2]
    exact ⟨rfl, rfl⟩

lemma siteN_lt (t : ℕ) (ht : 0 < t) (j : Fin (3 * t - 3)) : siteN t j < 3 * t := by
  dsimp only [siteN]; split_ifs <;> omega

lemma dStar_at_site (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (j : Fin (3 * t - 3)) :
    dStar t ((siteN t j : ℕ) : ZMod (3 * t)) = 0 := by
  by_cases ht1 : t = 1
  · subst ht1; exact absurd j.isLt (by omega)
  · by_cases ht2 : t = 2
    · subst ht2
      dsimp only [dStar, siteN]
      have hj : j.val < 3 := j.isLt
      have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · rw [h0]; decide
      · rw [h1]; decide
      · rw [h2]; decide
    · dsimp only [dStar, siteN]
      simp only [ht1, ht2, ↓reduceIte]
      have hlt : j.val < 3 * t - 3 := j.isLt
      have hne : ∀ m : ℕ, m < 3 * t → m ≠ j.val →
          ((j.val : ℕ) : ZMod (3 * t)) ≠ ((m : ℕ) : ZMod (3 * t)) := by
        intro m hm hne' heq
        have hv := congrArg ZMod.val heq
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt hm] at hv
        exact hne' hv.symm
      have hnot : ¬ (((j.val : ℕ) : ZMod (3 * t)) = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
          ((j.val : ℕ) : ZMod (3 * t)) = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
          ((j.val : ℕ) : ZMod (3 * t)) = ((3 * t - 1 : ℕ) : ZMod (3 * t))) := by
        push Not
        exact ⟨hne (3 * t - 3) (by omega) (by omega),
               hne (3 * t - 2) (by omega) (by omega),
               hne (3 * t - 1) (by omega) (by omega)⟩
      simp only [hnot, ↓reduceIte]

lemma eq_zero_or_dStar_of_sites (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] {u : Lane (3 * t)}
    (hu : u ∈ imSub t)
    (hs : ∀ j : Fin (3 * t - 3), u ((siteN t j : ℕ) : ZMod (3 * t)) = 0) :
    u = 0 ∨ u = dStar t := by
  by_cases ht1 : t = 1
  · subst ht1
    have hconst : ∀ a : ZMod 3, u a = u 0 := by
      intro a
      have hp := parSum_eq_of_mem_imSub 1 hu a 0
      have hval : ∀ r : ZMod 3, parSum 1 r u = u r := by
        intro r; rw [parSum_apply]
        have hf : Finset.univ.filter (fun x : ZMod 3 => res3 1 x = r) = {r} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, res3_one_id]
        rw [hf, Finset.sum_singleton]
      rw [hval a, hval 0] at hp; exact hp
    rcases z2_eq_zero_or_one (u 0) with h0 | h1
    · left; funext a; rw [hconst a, h0]; rfl
    · right; funext a; rw [hconst a, h1]; dsimp only [dStar]; rfl
  · by_cases ht2 : t = 2
    · subst ht2
      have hu2 : u 2 = 0 := hs ⟨0, by omega⟩
      have hu4 : u 4 = 0 := hs ⟨1, by omega⟩
      have hu5 : u 5 = 0 := hs ⟨2, by omega⟩
      have hp02 := parSum_eq_of_mem_imSub 2 hu 0 2
      have hp12 := parSum_eq_of_mem_imSub 2 hu 1 2
      rw [parSum_apply, parSum_apply, z6_filter_0, z6_filter_2,
        Finset.sum_pair z6_0_ne_3, Finset.sum_pair z6_2_ne_5, hu2, hu5, add_zero] at hp02
      rw [parSum_apply, parSum_apply, z6_filter_1, z6_filter_2,
        Finset.sum_pair z6_1_ne_4, Finset.sum_pair z6_2_ne_5,
        hu4, hu2, hu5, add_zero, add_zero] at hp12
      have hu3 : u 3 = u 0 := by
        calc u 3 = (u 0 + u 3) + u 0 := by
              have : (u 0 + u 3) + u 0 = u 3 + (u 0 + u 0) := by abel
              rw [this, z2_add_self, add_zero]
          _ = u 0 := by rw [hp02, zero_add]
      rcases z2_eq_zero_or_one (u 0) with h0 | h1
      · left; funext a
        rcases z6_elems a with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [h0, hp12, hu2, hu3, hu4, hu5]
      · right; funext a; dsimp only [dStar]
        rcases z6_elems a with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [h1, hp12, hu2, hu3, hu4, hu5] <;> decide
    · have h3 : 3 ≤ t := by omega
      have hzero : ∀ a : ZMod (3 * t), a.val < 3 * t - 3 → u a = 0 := by
        intro a ha
        have h := hs ⟨a.val, ha⟩
        dsimp only [siteN] at h
        simp only [ht2, ↓reduceIte, ZMod.natCast_zmod_val] at h
        exact h
      have hps_eq : ∀ r : ZMod 3,
          parSum t r u = u ((3 * t - 3 + r.val : ℕ) : ZMod (3 * t)) := by
        intro r
        rw [parSum_apply]
        let a_r : ZMod (3 * t) := ((3 * t - 3 + r.val : ℕ) : ZMod (3 * t))
        have hmem : a_r ∈ Finset.univ.filter (fun a : ZMod (3 * t) => res3 t a = r) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          dsimp only [a_r]; rw [map_natCast]
          have h1 : 3 * t - 3 + r.val = 3 * (t - 1) + r.val := by omega
          rw [h1]; push_cast
          rw [z3_three_zero, zero_mul, zero_add, ZMod.natCast_zmod_val]
        rw [Finset.sum_eq_single a_r]
        · intro a ha hne
          have hfa := (Finset.mem_filter.mp ha).2
          by_cases hlt : a.val < 3 * t - 3
          · exact hzero a hlt
          · exfalso; apply hne
            have hrlt : r.val < 3 := r.val_lt
            have halt : a.val < 3 * t := a.val_lt
            have hmod : a.val % 3 = r.val := by
              have hcast : ((a.val : ℕ) : ZMod 3) = r := by
                rw [← map_natCast (res3 t), ZMod.natCast_zmod_val, hfa]
              have := congrArg ZMod.val hcast
              rwa [ZMod.val_natCast] at this
            have hveq : a.val = 3 * t - 3 + r.val := by omega
            apply ZMod.val_injective (3 * t)
            dsimp only [a_r]
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), hveq]
        · intro hnot; exact absurd hmem hnot
      have h01 := parSum_eq_of_mem_imSub t hu 0 1
      have h02 := parSum_eq_of_mem_imSub t hu 0 2
      rw [hps_eq 0, hps_eq 1] at h01
      rw [hps_eq 0, hps_eq 2] at h02
      have hv0 : (0 : ZMod 3).val = 0 := rfl
      have hv1 : (1 : ZMod 3).val = 1 := rfl
      have hv2 : (2 : ZMod 3).val = 2 := rfl
      rw [hv0, hv1, Nat.add_zero, show 3 * t - 3 + 1 = 3 * t - 2 by omega] at h01
      rw [hv0, hv2, Nat.add_zero, show 3 * t - 3 + 2 = 3 * t - 1 by omega] at h02
      set c0 := u ((3 * t - 3 : ℕ) : ZMod (3 * t))
      rcases z2_eq_zero_or_one c0 with hc | hc
      · left; funext a
        by_cases hlt : a.val < 3 * t - 3
        · exact hzero a hlt
        · have halt : a.val < 3 * t := a.val_lt
          have hcases : a.val = 3 * t - 3 ∨ a.val = 3 * t - 2 ∨ a.val = 3 * t - 1 := by omega
          rcases hcases with h | h | h
          · rw [← ZMod.natCast_zmod_val a, h]; exact hc
          · rw [← ZMod.natCast_zmod_val a, h, ← h01]; exact hc
          · rw [← ZMod.natCast_zmod_val a, h, ← h02]; exact hc
      · right; funext a
        dsimp only [dStar]
        simp only [ht1, ht2, ↓reduceIte]
        by_cases hlt : a.val < 3 * t - 3
        · have hne : ∀ m : ℕ, m < 3 * t → m ≠ a.val → a ≠ ((m : ℕ) : ZMod (3 * t)) := by
            intro m hm hne' heq
            have hv := congrArg ZMod.val heq
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm] at hv
            exact hne' hv.symm
          have hnot : ¬ (a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
              a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
              a = ((3 * t - 1 : ℕ) : ZMod (3 * t))) := by
            push Not
            exact ⟨hne (3 * t - 3) (by omega) (by omega),
                   hne (3 * t - 2) (by omega) (by omega),
                   hne (3 * t - 1) (by omega) (by omega)⟩
          simp only [hzero a hlt, hnot, ↓reduceIte]
        · have halt : a.val < 3 * t := a.val_lt
          have hcases : a.val = 3 * t - 3 ∨ a.val = 3 * t - 2 ∨ a.val = 3 * t - 1 := by omega
          rcases hcases with h | h | h
          · have ha : a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) := by
              rw [← ZMod.natCast_zmod_val a, h]
            simp only [ha, true_or, ↓reduceIte]; exact hc
          · have ha : a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) := by
              rw [← ZMod.natCast_zmod_val a, h]
            simp only [ha, true_or, or_true, ↓reduceIte, ← h01]; exact hc
          · have ha : a = ((3 * t - 1 : ℕ) : ZMod (3 * t)) := by
              rw [← ZMod.natCast_zmod_val a, h]
            simp only [ha, or_true, ↓reduceIte, ← h02]; exact hc

lemma card_Q_dStar_imSub (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] :
    2 ^ gapN t * Nat.card {v : imSub t // Qmap t (dStar t) v.1 = 0} = Nat.card (imSub t) := by
  classical
  by_cases ht1 : t = 1
  · subst ht1
    dsimp only [gapN]; simp only [↓reduceIte]
    let phi : imSub 1 →ₗ[F] F :=
      { toFun := fun v => v.1 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hker : ∀ v : imSub 1, Qmap 1 (dStar 1) v.1 = 0 ↔ phi v = 0 := by
      intro v
      rw [Qmap_eq_zero_iff 1 (by omega)]
      have hconst : ∀ a : ZMod 3, v.1 a = v.1 0 := by
        intro a
        have hp := parSum_eq_of_mem_imSub 1 v.2 a 0
        have hval : ∀ r : ZMod 3, parSum 1 r v.1 = v.1 r := by
          intro r; rw [parSum_apply]
          have hf : Finset.univ.filter (fun x : ZMod 3 => res3 1 x = r) = {r} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, res3_one_id]
          rw [hf, Finset.sum_singleton]
        rw [hval a, hval 0] at hp; exact hp
      constructor
      · intro h; have h0 := (h 0).1; dsimp only [dStar] at h0; simpa [phi] using h0
      · intro h a
        dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk] at h
        rw [hconst a, hconst (a - 1), h, mul_zero]; exact ⟨rfl, rfl⟩
    have hsurj : Function.Surjective phi := by
      intro c
      refine ⟨⟨fun _ => c, ?_⟩, rfl⟩
      rw [mem_imSub_iff]
      have hval : ∀ r : ZMod 3, parSum 1 r (fun _ => c) = c := by
        intro r; rw [parSum_apply]
        have hf : Finset.univ.filter (fun x : ZMod 3 => res3 1 x = r) = {r} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, res3_one_id]
        rw [hf, Finset.sum_singleton]
      rw [hval, hval, hval]; exact ⟨rfl, rfl⟩
    have he : {v : imSub 1 // Qmap 1 (dStar 1) v.1 = 0} ≃ LinearMap.ker phi :=
      Equiv.subtypeEquivRight (fun v => (hker v).trans LinearMap.mem_ker.symm)
    rw [Nat.card_congr he]
    have hrk := LinearMap.finrank_range_add_finrank_ker phi
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hrk
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, ← Nat.pow_add, hrk]
  · by_cases ht2 : t = 2
    · subst ht2
      dsimp only [gapN]; simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
      let phi : imSub 2 →ₗ[F] (Fin 3 → F) :=
        { toFun := fun v i => if i.val = 0 then v.1 0 else if i.val = 1 then v.1 2 else v.1 3
          map_add' := fun _ _ => by funext i; dsimp only [Pi.add_apply]; split_ifs <;> rfl
          map_smul' := fun _ _ => by funext i; dsimp only [Pi.smul_apply]; split_ifs <;> rfl }
      have hker : ∀ v : imSub 2, Qmap 2 (dStar 2) v.1 = 0 ↔ phi v = 0 := by
        intro v
        rw [Qmap_eq_zero_iff 2 (by omega)]
        constructor
        · intro h
          have h0 := (h 0).1
          have h3 := (h 3).1
          have h3m := (h 3).2
          dsimp only [dStar] at h0 h3 h3m
          simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, true_or, or_true, one_mul,
            show (3 : ZMod 6) - 1 = 2 by decide] at h0 h3 h3m
          funext i; fin_cases i
          · exact h0
          · exact h3m
          · exact h3
        · intro h
          have h0 : v.1 0 = 0 := congrFun h 0
          have h2 : v.1 2 = 0 := congrFun h 1
          have h3 : v.1 3 = 0 := congrFun h 2
          have hp02 := parSum_eq_of_mem_imSub 2 v.2 0 2
          rw [parSum_apply, parSum_apply, z6_filter_0, z6_filter_2,
            Finset.sum_pair z6_0_ne_3, Finset.sum_pair z6_2_ne_5,
            h0, h3, h2, add_zero, zero_add] at hp02
          have h5 : v.1 5 = 0 := hp02.symm
          intro a
          dsimp only [dStar]
          rcases z6_elems a with rfl | rfl | rfl | rfl | rfl | rfl
          · simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, true_or, one_mul,
              show (0 : ZMod 6) - 1 = 5 by decide, h0, h5, and_self]
          · simp only [show (2 : ℕ) ≠ 1 by decide,
              show ¬ ((1 : ZMod 6) = 0 ∨ (1 : ZMod 6) = 3) by decide,
              ↓reduceIte, zero_mul, and_self]
          · simp only [show (2 : ℕ) ≠ 1 by decide,
              show ¬ ((2 : ZMod 6) = 0 ∨ (2 : ZMod 6) = 3) by decide,
              ↓reduceIte, zero_mul, and_self]
          · simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, or_true, one_mul,
              show (3 : ZMod 6) - 1 = 2 by decide, h3, h2, and_self]
          · simp only [show (2 : ℕ) ≠ 1 by decide,
              show ¬ ((4 : ZMod 6) = 0 ∨ (4 : ZMod 6) = 3) by decide,
              ↓reduceIte, zero_mul, and_self]
          · simp only [show (2 : ℕ) ≠ 1 by decide,
              show ¬ ((5 : ZMod 6) = 0 ∨ (5 : ZMod 6) = 3) by decide,
              ↓reduceIte, zero_mul, and_self]
      have hsurj : Function.Surjective phi := by
        intro y
        let v : Lane 6 := fun a =>
          if a = 0 then y 0 else if a = 1 then y 0 + y 2 else if a = 2 then y 1
          else if a = 3 then y 2 else if a = 5 then y 0 + y 1 + y 2 else 0
        have hv : v ∈ imSub 2 := by
          rw [mem_imSub_iff, parSum_apply, parSum_apply, parSum_apply,
            z6_filter_0, z6_filter_1, z6_filter_2, Finset.sum_pair z6_0_ne_3,
            Finset.sum_pair z6_1_ne_4, Finset.sum_pair z6_2_ne_5]
          have hv0 : v 0 = y 0 := rfl
          have hv1 : v 1 = y 0 + y 2 := rfl
          have hv2 : v 2 = y 1 := rfl
          have hv3 : v 3 = y 2 := rfl
          have hv4 : v 4 = 0 := rfl
          have hv5 : v 5 = y 0 + y 1 + y 2 := rfl
          rw [hv0, hv1, hv2, hv3, hv4, hv5, add_zero]
          have hy2 : y 1 + (y 0 + y 1 + y 2) = y 0 + y 2 := by
            have : y 1 + (y 0 + y 1 + y 2) = (y 0 + y 2) + (y 1 + y 1) := by abel
            rw [this, z2_add_self, add_zero]
          rw [hy2]; exact ⟨rfl, rfl⟩
        refine ⟨⟨v, hv⟩, ?_⟩
        funext i; fin_cases i <;> rfl
      have he : {v : imSub 2 // Qmap 2 (dStar 2) v.1 = 0} ≃ LinearMap.ker phi :=
        Equiv.subtypeEquivRight (fun v => (hker v).trans LinearMap.mem_ker.symm)
      rw [Nat.card_congr he]
      have hrk := LinearMap.finrank_range_add_finrank_ker phi
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
      rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, ← Nat.pow_add, hrk]
    · have h3 : 3 ≤ t := by omega
      dsimp only [gapN]; simp only [ht1, ht2, ↓reduceIte]
      let p0 : ZMod (3 * t) := ((3 * t - 4 : ℕ) : ZMod (3 * t))
      let p1 : ZMod (3 * t) := ((3 * t - 3 : ℕ) : ZMod (3 * t))
      let p2 : ZMod (3 * t) := ((3 * t - 2 : ℕ) : ZMod (3 * t))
      let p3 : ZMod (3 * t) := ((3 * t - 1 : ℕ) : ZMod (3 * t))
      let phi : imSub t →ₗ[F] (Fin 4 → F) :=
        { toFun := fun v i =>
            if i.val = 0 then v.1 p0 else if i.val = 1 then v.1 p1
            else if i.val = 2 then v.1 p2 else v.1 p3
          map_add' := fun _ _ => by funext i; dsimp only [Pi.add_apply]; split_ifs <;> rfl
          map_smul' := fun _ _ => by funext i; dsimp only [Pi.smul_apply]; split_ifs <;> rfl }
      have hp1m : p1 - 1 = p0 := by
        dsimp only [p0, p1]
        have : ((3 * t - 4 : ℕ) : ZMod (3 * t)) + ((1 : ℕ) : ZMod (3 * t)) =
            ((3 * t - 3 : ℕ) : ZMod (3 * t)) := by
          rw [← Nat.cast_add, show 3 * t - 4 + 1 = 3 * t - 3 by omega]
        rw [Nat.cast_one] at this
        exact (eq_sub_of_add_eq this).symm
      have hp2m : p2 - 1 = p1 := by
        dsimp only [p1, p2]
        have : ((3 * t - 3 : ℕ) : ZMod (3 * t)) + ((1 : ℕ) : ZMod (3 * t)) =
            ((3 * t - 2 : ℕ) : ZMod (3 * t)) := by
          rw [← Nat.cast_add, show 3 * t - 3 + 1 = 3 * t - 2 by omega]
        rw [Nat.cast_one] at this
        exact (eq_sub_of_add_eq this).symm
      have hp3m : p3 - 1 = p2 := by
        dsimp only [p2, p3]
        have : ((3 * t - 2 : ℕ) : ZMod (3 * t)) + ((1 : ℕ) : ZMod (3 * t)) =
            ((3 * t - 1 : ℕ) : ZMod (3 * t)) := by
          rw [← Nat.cast_add, show 3 * t - 2 + 1 = 3 * t - 1 by omega]
        rw [Nat.cast_one] at this
        exact (eq_sub_of_add_eq this).symm
      have hker : ∀ v : imSub t, Qmap t (dStar t) v.1 = 0 ↔ phi v = 0 := by
        intro v
        rw [Qmap_eq_zero_iff t ht]
        constructor
        · intro h
          have h1 := h p1
          have h2 := h p2
          have h3' := h p3
          dsimp only [dStar] at h1 h2 h3'
          simp only [ht1, ht2, ↓reduceIte, p1, p2, p3, true_or, or_true, one_mul] at h1 h2 h3'
          rw [hp1m] at h1
          funext i; fin_cases i
          · exact h1.2
          · exact h1.1
          · exact h2.1
          · exact h3'.1
        · intro h a
          have h0 : v.1 p0 = 0 := congrFun h 0
          have h1 : v.1 p1 = 0 := congrFun h 1
          have h2 : v.1 p2 = 0 := congrFun h 2
          have h3' : v.1 p3 = 0 := congrFun h 3
          dsimp only [dStar]
          simp only [ht1, ht2, ↓reduceIte]
          by_cases ha : a = p1 ∨ a = p2 ∨ a = p3
          · have ha' : a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
                a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
                a = ((3 * t - 1 : ℕ) : ZMod (3 * t)) := ha
            simp only [ha', ↓reduceIte, one_mul]
            rcases ha with rfl | rfl | rfl
            · rw [hp1m]; exact ⟨h1, h0⟩
            · rw [hp2m]; exact ⟨h2, h1⟩
            · rw [hp3m]; exact ⟨h3', h2⟩
          · have ha' : ¬ (a = ((3 * t - 3 : ℕ) : ZMod (3 * t)) ∨
                a = ((3 * t - 2 : ℕ) : ZMod (3 * t)) ∨
                a = ((3 * t - 1 : ℕ) : ZMod (3 * t))) := ha
            simp only [ha', ↓reduceIte, zero_mul, and_self]
      have hsurj : Function.Surjective phi := by
        intro y
        have hneq : ∀ m1 m2 : ℕ, m1 < 3 * t → m2 < 3 * t → m1 ≠ m2 →
            ((m1 : ℕ) : ZMod (3 * t)) ≠ ((m2 : ℕ) : ZMod (3 * t)) := by
          intro m1 m2 hm1 hm2 hne heq
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hv
          exact hne hv
        let v : Lane (3 * t) :=
          (fun a => if a = 0 then y 1 else 0) +
          (fun a => if a = 1 then y 2 else 0) +
          (fun a => if a = 2 then y 0 + y 3 else 0) +
          (fun a => if a = p0 then y 0 else 0) +
          (fun a => if a = p1 then y 1 else 0) +
          (fun a => if a = p2 then y 2 else 0) +
          (fun a => if a = p3 then y 3 else 0)
        have hr_2 : res3 t 2 = 2 := by
          rw [show (2 : ZMod (3 * t)) = 1 + 1 by norm_num, map_add, map_one]; norm_num
        have hr_p0 : res3 t p0 = 2 := by
          dsimp only [p0]; rw [map_natCast, show 3 * t - 4 = 3 * (t - 2) + 2 by omega]
          push_cast; rw [z3_three_zero, zero_mul, zero_add]
        have hr_p1 : res3 t p1 = 0 := by
          dsimp only [p1]; rw [map_natCast, show 3 * t - 3 = 3 * (t - 1) by omega]
          push_cast; rw [z3_three_zero, zero_mul]
        have hr_p2 : res3 t p2 = 1 := by
          dsimp only [p2]; rw [map_natCast, show 3 * t - 2 = 3 * (t - 1) + 1 by omega]
          push_cast; rw [z3_three_zero, zero_mul, zero_add]
        have hr_p3 : res3 t p3 = 2 := by
          dsimp only [p3]; rw [map_natCast, show 3 * t - 1 = 3 * (t - 1) + 2 by omega]
          push_cast; rw [z3_three_zero, zero_mul, zero_add]
        have hv : v ∈ imSub t := by
          have hps : ∀ r : ZMod 3, parSum t r v = 0 := by
            intro r
            dsimp only [v]
            simp only [map_add, parSum_single, map_zero, map_one, hr_2, hr_p0, hr_p1, hr_p2, hr_p3]
            rcases z3_elems r with rfl | rfl | rfl
            · have h10 : (1 : ZMod 3) ≠ 0 := by decide
              have h20 : (2 : ZMod 3) ≠ 0 := by decide
              simp only [h10, h20, ↓reduceIte, zero_add, add_zero, z2_add_self]
            · have h01 : (0 : ZMod 3) ≠ 1 := by decide
              have h21 : (2 : ZMod 3) ≠ 1 := by decide
              simp only [h01, h21, ↓reduceIte, zero_add, add_zero, z2_add_self]
            · simp only [z3_zero_ne_two, z3_one_ne_two, ↓reduceIte, zero_add, add_zero]
              have : y 0 + y 3 + y 0 + y 3 = (y 0 + y 0) + (y 3 + y 3) := by abel
              rw [this, z2_add_self, z2_add_self, add_zero]
          rw [mem_imSub_iff, hps 0, hps 1, hps 2]; exact ⟨rfl, rfl⟩
        refine ⟨⟨v, hv⟩, ?_⟩
        have h0_ne : ∀ m, 5 ≤ m → m < 3 * t → ((m : ℕ) : ZMod (3 * t)) ≠ 0 := fun m hm1 hm2 => by
          simpa using hneq m 0 hm2 (by omega) (by omega)
        have h1_ne : ∀ m, 5 ≤ m → m < 3 * t → ((m : ℕ) : ZMod (3 * t)) ≠ 1 := fun m hm1 hm2 => by
          simpa using hneq m 1 hm2 (by omega) (by omega)
        have h2_ne : ∀ m, 5 ≤ m → m < 3 * t → ((m : ℕ) : ZMod (3 * t)) ≠ 2 := fun m hm1 hm2 => by
          simpa using hneq m 2 hm2 (by omega) (by omega)
        have hdisj : p0 ≠ p1 ∧ p0 ≠ p2 ∧ p0 ≠ p3 ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 :=
          ⟨hneq _ _ (by omega) (by omega) (by omega),
           hneq _ _ (by omega) (by omega) (by omega),
           hneq _ _ (by omega) (by omega) (by omega),
           hneq _ _ (by omega) (by omega) (by omega),
           hneq _ _ (by omega) (by omega) (by omega),
           hneq _ _ (by omega) (by omega) (by omega)⟩
        funext i; fin_cases i
        · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, v, Pi.add_apply]
          simp only [↓reduceIte, hdisj.1, hdisj.2.1, hdisj.2.2.1,
            show p0 ≠ 0 from h0_ne (3 * t - 4) (by omega) (by omega),
            show p0 ≠ 1 from h1_ne (3 * t - 4) (by omega) (by omega),
            show p0 ≠ 2 from h2_ne (3 * t - 4) (by omega) (by omega), zero_add, add_zero]
          rfl
        · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, v, Pi.add_apply]
          simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte,
            hdisj.1.symm, hdisj.2.2.2.1, hdisj.2.2.2.2.1,
            show p1 ≠ 0 from h0_ne (3 * t - 3) (by omega) (by omega),
            show p1 ≠ 1 from h1_ne (3 * t - 3) (by omega) (by omega),
            show p1 ≠ 2 from h2_ne (3 * t - 3) (by omega) (by omega), zero_add, add_zero]
          rfl
        · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, v, Pi.add_apply]
          simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
            hdisj.2.1.symm, hdisj.2.2.2.1.symm, hdisj.2.2.2.2.2,
            show p2 ≠ 0 from h0_ne (3 * t - 2) (by omega) (by omega),
            show p2 ≠ 1 from h1_ne (3 * t - 2) (by omega) (by omega),
            show p2 ≠ 2 from h2_ne (3 * t - 2) (by omega) (by omega), zero_add, add_zero]
          rfl
        · dsimp only [phi, LinearMap.coe_mk, AddHom.coe_mk, v, Pi.add_apply]
          simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
            show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
            hdisj.2.2.1.symm, hdisj.2.2.2.2.1.symm, hdisj.2.2.2.2.2.symm,
            show p3 ≠ 0 from h0_ne (3 * t - 1) (by omega) (by omega),
            show p3 ≠ 1 from h1_ne (3 * t - 1) (by omega) (by omega),
            show p3 ≠ 2 from h2_ne (3 * t - 1) (by omega) (by omega), zero_add, add_zero]
          rfl
      have he : {v : imSub t // Qmap t (dStar t) v.1 = 0} ≃ LinearMap.ker phi :=
        Equiv.subtypeEquivRight (fun v => (hker v).trans LinearMap.mem_ker.symm)
      rw [Nat.card_congr he]
      have hrk := LinearMap.finrank_range_add_finrank_ker phi
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
      rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, ← Nat.pow_add, hrk]

theorem lower_bound (t : ℕ) (ht : 0 < t) [NeZero (3 * t)] (name c : Fin (6 * t) → F) :
    ∃ (ask : Fin (3 * t - 3) → ℕ → (Fin (6 * t) → F) →ₗ[F] F)
      (A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F))
      (b : ℕ → Fin (6 * t) → F),
      (∀ j p w, ask j p w = mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (2 * siteN t j))) ∧
      denN t * Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 3) ask w) w + b (runN (6 * t) (3 * t - 3) ask w)} =
        numN t * 2 ^ (6 * t) := by
  classical
  let ask : Fin (3 * t - 3) → ℕ → (Fin (6 * t) → F) →ₗ[F] F :=
    fun j _ =>
      { toFun := fun w => mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (2 * siteN t j))
        map_add' := fun w1 w2 => congrFun (mixN_add (6 * t) (by omega) w1 w2) _
        map_smul' := fun r w => congrFun (mixN_smul (6 * t) (by omega) r w) _ }
  have hask_even : ∀ j p w, ask j p w = evenLane t ht w ((siteN t j : ℕ) : ZMod (3 * t)) := by
    intro j p w
    dsimp only [ask, evenLane, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; apply Fin.ext; dsimp only [ixN]
    have hlt := siteN_lt t ht j
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]
  let ubase : ℕ → Lane (3 * t) := fun p =>
    if hp : ∃ w : Fin (6 * t) → F, runN (6 * t) (3 * t - 3) ask w = p then
      evenLane t ht (Classical.choose hp)
    else 0
  let A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F) :=
    fun p => (Qmap t (ubase p)).comp (oddLane t ht) + Lbase t ht name
  let b : ℕ → Fin (6 * t) → F := fun _ => cbase t ht name c
  refine ⟨ask, A, b, fun _ _ _ => rfl, ?_⟩
  obtain ⟨xStar, hxE, hxO⟩ := exists_even_odd t ht (dStar_mem_imSub t ht) (imSub t).zero_mem
  have hrun_shift : ∀ w : Fin (6 * t) → F,
      runN (6 * t) (3 * t - 3) ask (w + xStar) = runN (6 * t) (3 * t - 3) ask w := by
    intro w
    have hEq : ∀ j p, ask j p (w + xStar) = ask j p w := by
      intro j p
      rw [hask_even j p (w + xStar), hask_even j p w, map_add, hxE, Pi.add_apply,
        dStar_at_site t ht j, add_zero]
    dsimp only [runN]
    have hfold : ∀ (l : List (Fin (3 * t - 3))) (z : ℕ),
        (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
         l.foldl (fun z i => 2 * z + (if ask i z (w + xStar) = 0 then 0 else 1)) z) =
        (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
         l.foldl (fun z i => 2 * z + (if ask i z w = 0 then 0 else 1)) z) := by
      intro l
      induction l with
      | nil => intro z; rfl
      | cons hd tl ih =>
        intro z
        dsimp only [List.foldl_cons]
        rw [hEq hd z]
        exact ih _
    exact hfold (List.finRange (3 * t - 3)) 0
  have hubase_diff : ∀ w : Fin (6 * t) → F,
      evenLane t ht w + ubase (runN (6 * t) (3 * t - 3) ask w) = 0 ∨
      evenLane t ht w + ubase (runN (6 * t) (3 * t - 3) ask w) = dStar t := by
    intro w
    have hex : ∃ w' : Fin (6 * t) → F,
        runN (6 * t) (3 * t - 3) ask w' = runN (6 * t) (3 * t - 3) ask w := ⟨w, rfl⟩
    set w0 := Classical.choose hex
    have hw0 : runN (6 * t) (3 * t - 3) ask w0 = runN (6 * t) (3 * t - 3) ask w :=
      Classical.choose_spec hex
    have hub : ubase (runN (6 * t) (3 * t - 3) ask w) = evenLane t ht w0 := dif_pos hex
    rw [hub]
    have hpref : runPref (6 * t) (3 * t - 3) ask (3 * t - 3) w =
        runPref (6 * t) (3 * t - 3) ask (3 * t - 3) w0 := by
      have heq : ∀ u, runN (6 * t) (3 * t - 3) ask u =
          runPref (6 * t) (3 * t - 3) ask (3 * t - 3) u := by
        intro u; dsimp only [runN, runPref]
        rw [List.take_of_length_le (by rw [List.length_finRange])]
      rw [← heq w, ← heq w0, hw0]
    have hall := (runPref_eq_iff (6 * t) (3 * t - 3) ask w0 w (3 * t - 3) (le_refl _)).mp hpref
    refine eq_zero_or_dStar_of_sites t ht
      ((imSub t).add_mem (evenLane_mem_imSub t ht w) (evenLane_mem_imSub t ht w0)) ?_
    intro j
    have hj := hall j j.isLt
    rw [hask_even j (runPref (6 * t) (3 * t - 3) ask j.val w0) w,
      hask_even j (runPref (6 * t) (3 * t - 3) ask j.val w0) w0] at hj
    dsimp only [Pi.add_apply]
    rw [hj, z2_add_self]
  have hhit_iff : ∀ w : Fin (6 * t) → F,
      outN (6 * t) (by omega) name c w =
        A (runN (6 * t) (3 * t - 3) ask w) w + b (runN (6 * t) (3 * t - 3) ask w) ↔
      evenLane t ht w = ubase (runN (6 * t) (3 * t - 3) ask w) ∨
        (evenLane t ht w ≠ ubase (runN (6 * t) (3 * t - 3) ask w) ∧
          Qmap t (dStar t) (oddLane t ht w) = 0) := by
    intro w
    rw [outN_decomp t ht name c w]
    dsimp only [A, b, LinearMap.add_apply, LinearMap.comp_apply]
    have hcancel : Qmap t (evenLane t ht w) (oddLane t ht w) + Lbase t ht name w + cbase t ht name c =
        Qmap t (ubase (runN (6 * t) (3 * t - 3) ask w)) (oddLane t ht w) + Lbase t ht name w +
          cbase t ht name c ↔
        Qmap t (evenLane t ht w + ubase (runN (6 * t) (3 * t - 3) ask w)) (oddLane t ht w) = 0 := by
      rw [map_add, LinearMap.add_apply]
      constructor
      · intro h
        have h1 := add_right_cancel (add_right_cancel h)
        rw [h1, vec_add_self]
      · intro h
        have h1 : Qmap t (evenLane t ht w) (oddLane t ht w) =
            Qmap t (ubase (runN (6 * t) (3 * t - 3) ask w)) (oddLane t ht w) := by
          calc Qmap t (evenLane t ht w) (oddLane t ht w)
              = (Qmap t (evenLane t ht w) (oddLane t ht w) +
                  Qmap t (ubase (runN (6 * t) (3 * t - 3) ask w)) (oddLane t ht w)) +
                Qmap t (ubase (runN (6 * t) (3 * t - 3) ask w)) (oddLane t ht w) := by
                  rw [add_assoc, vec_add_self, add_zero]
            _ = _ := by rw [h, zero_add]
        rw [h1]
    rw [hcancel]
    have h0_iff : evenLane t ht w + ubase (runN (6 * t) (3 * t - 3) ask w) = 0 ↔
        evenLane t ht w = ubase (runN (6 * t) (3 * t - 3) ask w) := by
      constructor
      · intro h
        calc evenLane t ht w = (evenLane t ht w + ubase (runN (6 * t) (3 * t - 3) ask w)) +
                ubase (runN (6 * t) (3 * t - 3) ask w) := by
                  rw [add_assoc, vec_add_self, add_zero]
          _ = _ := by rw [h, zero_add]
      · intro h; rw [h, vec_add_self]
    rcases hubase_diff w with h0 | hd
    · rw [h0, map_zero, LinearMap.zero_apply]
      simp [h0_iff.mp h0]
    · rw [hd]
      have hne : evenLane t ht w ≠ ubase (runN (6 * t) (3 * t - 3) ask w) := by
        intro heq; exact dStar_ne_zero t ht (hd.symm.trans (h0_iff.mpr heq))
      simp [hne]
  let P0 : (Fin (6 * t) → F) → Prop := fun w =>
    evenLane t ht w = ubase (runN (6 * t) (3 * t - 3) ask w)
  have hP0_swap : ∀ w : Fin (6 * t) → F, P0 (w + xStar) ↔ ¬ P0 w := by
    intro w
    dsimp only [P0]
    rw [hrun_shift w, map_add, hxE]
    have h0_iff : ∀ u1 u2 : Lane (3 * t), u1 = u2 ↔ u1 + u2 = 0 := by
      intro u1 u2; constructor
      · intro h; rw [h, vec_add_self]
      · intro h
        calc u1 = (u1 + u2) + u2 := by rw [add_assoc, vec_add_self, add_zero]
          _ = u2 := by rw [h, zero_add]
    rcases hubase_diff w with h0 | hd
    · have hw : evenLane t ht w = ubase (runN (6 * t) (3 * t - 3) ask w) := (h0_iff _ _).mpr h0
      rw [hw]
      constructor
      · intro h _
        exact dStar_ne_zero t ht (add_left_cancel (h.trans (add_zero _).symm))
      · intro h; exact absurd rfl h
    · have hnw : evenLane t ht w ≠ ubase (runN (6 * t) (3 * t - 3) ask w) := by
        intro h; exact dStar_ne_zero t ht (hd.symm.trans ((h0_iff _ _).mp h))
      have he : evenLane t ht w + dStar t = ubase (runN (6 * t) (3 * t - 3) ask w) := by
        rw [← hd]
        have : evenLane t ht w + (evenLane t ht w + ubase (runN (6 * t) (3 * t - 3) ask w)) =
            (evenLane t ht w + evenLane t ht w) + ubase (runN (6 * t) (3 * t - 3) ask w) := by abel
        rw [this, vec_add_self, zero_add]
      rw [he]
      exact ⟨fun _ => hnw, fun _ => rfl⟩
  have hcard_P0 : 2 * Nat.card {w : Fin (6 * t) → F // P0 w} = 2 ^ (6 * t) := by
    have e : {w : Fin (6 * t) → F // P0 w} ≃ {w : Fin (6 * t) → F // ¬ P0 w} :=
      { toFun := fun w => ⟨w.1 + xStar, fun h => (hP0_swap w.1).mp h w.2⟩
        invFun := fun w => ⟨w.1 + xStar, (hP0_swap w.1).mpr w.2⟩
        left_inv := fun w => Subtype.ext (by dsimp only; rw [add_assoc, vec_add_self, add_zero])
        right_inv := fun w => Subtype.ext (by dsimp only; rw [add_assoc, vec_add_self, add_zero]) }
    have hsplit : Nat.card {w : Fin (6 * t) → F // P0 w} +
        Nat.card {w : Fin (6 * t) → F // ¬ P0 w} = 2 ^ (6 * t) := by
      simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
      rw [card_filter_add_not, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [← Nat.card_congr e] at hsplit
    omega
  have hcard_P1 :
      2 * Nat.card {w : Fin (6 * t) → F // ¬ P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0} =
      Nat.card {w : Fin (6 * t) → F // Qmap t (dStar t) (oddLane t ht w) = 0} := by
    have e : {w : Fin (6 * t) → F // ¬ P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0} ≃
        {w : Fin (6 * t) → F // P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0} :=
      { toFun := fun w => ⟨w.1 + xStar, ⟨(hP0_swap w.1).mpr w.2.1, by
          rw [map_add, hxO, add_zero]; exact w.2.2⟩⟩
        invFun := fun w => ⟨w.1 + xStar, ⟨fun h => (hP0_swap w.1).mp h w.2.1, by
          rw [map_add, hxO, add_zero]; exact w.2.2⟩⟩
        left_inv := fun w => Subtype.ext (by dsimp only; rw [add_assoc, vec_add_self, add_zero])
        right_inv := fun w => Subtype.ext (by dsimp only; rw [add_assoc, vec_add_self, add_zero]) }
    have hsplit :
        Nat.card {w : Fin (6 * t) → F // P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0} +
        Nat.card {w : Fin (6 * t) → F // ¬ P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0} =
        Nat.card {w : Fin (6 * t) → F // Qmap t (dStar t) (oddLane t ht w) = 0} := by
      simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
      have hdisj : Disjoint
          (Finset.univ.filter (fun w : Fin (6 * t) → F =>
            P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0))
          (Finset.univ.filter (fun w : Fin (6 * t) → F =>
            ¬ P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0)) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [← Nat.card_congr e] at hsplit
    omega
  have hcard_hit_split :
      Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 3) ask w) w + b (runN (6 * t) (3 * t - 3) ask w)} =
      Nat.card {w : Fin (6 * t) → F // P0 w} +
      Nat.card {w : Fin (6 * t) → F // ¬ P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0} := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hhit_iff)]
    simp only [← Fintype.card_eq_nat_card, Fintype.card_subtype]
    have hdisj : Disjoint
        (Finset.univ.filter (fun w : Fin (6 * t) → F => P0 w))
        (Finset.univ.filter (fun w : Fin (6 * t) → F =>
          ¬ P0 w ∧ Qmap t (dStar t) (oddLane t ht w) = 0)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hQ_dStar_W :
      2 ^ gapN t * Nat.card {w : Fin (6 * t) → F // Qmap t (dStar t) (oddLane t ht w) = 0} =
      2 ^ (6 * t) := by
    let fO : (Fin (6 * t) → F) →ₗ[F] imSub t :=
      (oddLane t ht).codRestrict (imSub t) (oddLane_mem_imSub t ht)
    have hsurj : Function.Surjective fO := by
      intro v
      obtain ⟨w, _, hw⟩ := exists_even_odd t ht (imSub t).zero_mem v.2
      exact ⟨w, Subtype.ext hw⟩
    have hpre := card_preimage_linear fO (fun v : imSub t => Qmap t (dStar t) v.1 = 0)
    let hrange_e : fO.range ≃ₗ[F] imSub t :=
      (LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.mpr hsurj)).trans Submodule.topEquiv
    have hre_val : ∀ y : fO.range, (hrange_e y).1 = y.1.1 := fun _ => rfl
    have hres_val : ∀ v : imSub t, (hrange_e.symm v).1.1 = v.1 := fun _ => rfl
    have hcard_r : Nat.card {y : fO.range // Qmap t (dStar t) y.1.1 = 0} =
        Nat.card {v : imSub t // Qmap t (dStar t) v.1 = 0} :=
      Nat.card_congr
        { toFun := fun y => ⟨hrange_e y.1, by rw [hre_val]; exact y.2⟩
          invFun := fun v => ⟨hrange_e.symm v.1, by rw [hres_val]; exact v.2⟩
          left_inv := fun y => Subtype.ext (hrange_e.symm_apply_apply y.1)
          right_inv := fun v => Subtype.ext (hrange_e.apply_symm_apply v.1) }
    have htot : Nat.card (LinearMap.ker fO) * Nat.card (imSub t) = 2 ^ (6 * t) := by
      have hrk := LinearMap.finrank_range_add_finrank_ker fO
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
      rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, ← Nat.pow_add, Nat.add_comm, hrk]
    calc 2 ^ gapN t * Nat.card {w : Fin (6 * t) → F // Qmap t (dStar t) (oddLane t ht w) = 0}
        = 2 ^ gapN t * (Nat.card (LinearMap.ker fO) *
            Nat.card {v : imSub t // Qmap t (dStar t) v.1 = 0}) := by
            rw [← hcard_r]; exact congrArg (2 ^ gapN t * ·) hpre
      _ = Nat.card (LinearMap.ker fO) *
            (2 ^ gapN t * Nat.card {v : imSub t // Qmap t (dStar t) v.1 = 0}) := Nat.mul_left_comm _ _ _
      _ = Nat.card (LinearMap.ker fO) * Nat.card (imSub t) := by rw [card_Q_dStar_imSub t ht]
      _ = 2 ^ (6 * t) := htot
  rw [denN_eq_pow, numN_eq_pow, hcard_hit_split, Nat.pow_succ, Nat.mul_assoc,
    Nat.mul_add, hcard_P0, hcard_P1, Nat.mul_add, hQ_dStar_W]
  ring

theorem main (t : ℕ) (ht : 0 < t) (name c : Fin (6 * t) → F) (fixed : Bool) (k : ℕ) :
    (∃ (ask : Fin (3 * t - 3) → ℕ → (Fin (6 * t) → F) →ₗ[F] F)
       (A : ℕ → (Fin (6 * t) → F) →ₗ[F] (Fin (6 * t) → F))
       (b : ℕ → Fin (6 * t) → F),
      (fixed = true → ∀ j p w,
        ask j p w = mixN (6 * t) (by omega) w (ixN (6 * t) (by omega) (2 * siteN t j))) ∧
      k ≤ Nat.card {w : Fin (6 * t) → F //
        outN (6 * t) (by omega) name c w =
          A (runN (6 * t) (3 * t - 3) ask w) w + b (runN (6 * t) (3 * t - 3) ask w)}) ↔
    denN t * k ≤ numN t * 2 ^ (6 * t) := by
  have : NeZero (3 * t) := ⟨by omega⟩
  constructor
  · rintro ⟨ask, A, b, _, hk⟩
    exact (Nat.mul_le_mul_left (denN t) hk).trans (upper_bound t ht name c ask A b)
  · intro hk
    obtain ⟨ask, A, b, hfix, heq⟩ := lower_bound t ht name c
    refine ⟨ask, A, b, fun _ => hfix, ?_⟩
    have hden : 0 < denN t := by dsimp only [denN]; split_ifs <;> omega
    exact Nat.le_of_mul_le_mul_left (hk.trans heq.symm.le) hden

end PEqualNP.Outside.L_meta_33654

theorem PEqualNP.Outside.L_meta_33654 : ∀ (t : ℕ) (ht : 0 < t),
  let h := 3*t-3
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
  let site := fun j : Fin h => if t = 2 then (if j.val = 0 then 2 else j.val+3) else j.val
  let num := if t = 1 then 3 else if t = 2 then 9 else 17
  let den := if t = 1 then 4 else if t = 2 then 16 else 32
  ∀ (name c : W) (fixed : Bool) (k : ℕ),
    (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w = mix w (ix (2*site j))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔ den*k ≤ num*2^n := by
  intro t ht
  dsimp only
  intro name c fixed k
  have hsite : ∀ j : Fin (3 * t - 3),
      @ite ℕ (t = 2) (Classical.propDecidable _)
        (@ite ℕ (j.val = 0) (Classical.propDecidable _) 2 (j.val + 3)) j.val =
      PEqualNP.Outside.L_meta_33654.siteN t j := by
    intro j; dsimp only [PEqualNP.Outside.L_meta_33654.siteN]; split_ifs <;> rfl
  have hnum :
      @ite ℕ (t = 1) (Classical.propDecidable _) 3
        (@ite ℕ (t = 2) (Classical.propDecidable _) 9 17) =
      PEqualNP.Outside.L_meta_33654.numN t := by
    dsimp only [PEqualNP.Outside.L_meta_33654.numN]; split_ifs <;> rfl
  have hden :
      @ite ℕ (t = 1) (Classical.propDecidable _) 4
        (@ite ℕ (t = 2) (Classical.propDecidable _) 16 32) =
      PEqualNP.Outside.L_meta_33654.denN t := by
    dsimp only [PEqualNP.Outside.L_meta_33654.denN]; split_ifs <;> rfl
  simp only [hsite, hnum, hden]
  exact PEqualNP.Outside.L_meta_33654.main t ht name c fixed k

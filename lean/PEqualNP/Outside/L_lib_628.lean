import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_628_aux

private theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

private theorem linearMap_fiber_card {A B : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (φ : A →ₗ[ZMod 2] B) (b : B) (hb : b ∈ LinearMap.range φ) :
    Nat.card {a : A // φ a = b} * Nat.card (LinearMap.range φ) = Nat.card A := by
  classical
  have hfib_eq : ∀ y : LinearMap.range φ,
      Nat.card {a : A // φ a = y.1} = Nat.card {a : A // φ a = 0} := by
    intro y
    obtain ⟨a0, ha0⟩ := y.2
    refine Nat.card_congr
      { toFun := fun ⟨a, ha⟩ => ⟨a - a0, by rw [map_sub, ha, ha0, sub_self]⟩
        invFun := fun ⟨k, hk⟩ => ⟨k + a0, by rw [map_add, hk, ha0, zero_add]⟩
        left_inv := fun ⟨a, _⟩ => Subtype.ext (sub_add_cancel a a0)
        right_inv := fun ⟨k, _⟩ => Subtype.ext (add_sub_cancel_right k a0) }
  have hsum : Fintype.card A = ∑ y : LinearMap.range φ,
      ((Finset.univ : Finset A).filter (fun a => φ a = y.1)).card := by
    have h1 := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A))
      (t := (Finset.univ : Finset (LinearMap.range φ)))
      (f := fun a => (⟨φ a, ⟨a, rfl⟩⟩ : LinearMap.range φ))
      (fun a _ => Finset.mem_univ _)
    rw [Finset.card_univ] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ext a
    simp [Subtype.ext_iff]
  have hconst : ∀ y : LinearMap.range φ,
      ((Finset.univ : Finset A).filter (fun a => φ a = y.1)).card =
      Nat.card {a : A // φ a = 0} := by
    intro y
    rw [← hfib_eq y, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [hfib_eq ⟨b, hb⟩, Nat.card_eq_fintype_card (α := LinearMap.range φ),
    Nat.card_eq_fintype_card (α := A), hsum, mul_comm]

private def dirsSub {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2))
    (H : Submodule (ZMod 2) (Fin t → ZMod 2)) : Submodule (ZMod 2) (Fin g → ZMod 2) :=
  { carrier := {v | ∀ x, (f (x + v) - f x) - (f v - f 0) ∈ H}, add_mem' := fun {u v} hu hv x => by
      have h1 : (f (x + v + u) - f (x + v)) - (f u - f 0) ∈ H := hu (x + v)
      have h2 : (f (x + v) - f x) - (f v - f 0) ∈ H := hv x
      have h3 : (f (v + u) - f v) - (f u - f 0) ∈ H := hu v
      have hmem := H.sub_mem (H.add_mem h1 h2) h3
      have heq : ((f (x + v + u) - f (x + v)) - (f u - f 0) +
          ((f (x + v) - f x) - (f v - f 0))) - ((f (v + u) - f v) - (f u - f 0)) =
          (f (x + (u + v)) - f x) - (f (u + v) - f 0) := by
        rw [show x + v + u = x + (u + v) by abel, show v + u = u + v by abel]
        abel
      rwa [heq] at hmem
    zero_mem' := fun x => by simp
    smul_mem' := fun c {v} hv x => by
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using hv x }

private def growSub {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2))
    (prior : Submodule (ZMod 2) (Fin t → ZMod 2)) : Submodule (ZMod 2) (Fin t → ZMod 2) :=
  prior ⊔ Submodule.span (ZMod 2) ((fun value => f value - f 0) '' (dirsSub f prior : Set (Fin g → ZMod 2)))

private def quotShift {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2))
    (K : Submodule (ZMod 2) (Fin t → ZMod 2)) :
    dirsSub f K →ₗ[ZMod 2] ((Fin t → ZMod 2) ⧸ K) :=
  { toFun := fun v => Submodule.Quotient.mk (f v.1 - f 0)
    map_add' := fun u v => by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      have h := u.2 v.1
      have heq : (f (u.1 + v.1) - f 0) - ((f u.1 - f 0) + (f v.1 - f 0)) =
          (f (v.1 + u.1) - f v.1) - (f u.1 - f 0) := by
        rw [show u.1 + v.1 = v.1 + u.1 by abel]
        abel
      change (f (u.1 + v.1) - f 0) - ((f u.1 - f 0) + (f v.1 - f 0)) ∈ K
      rw [heq]
      exact h
    map_smul' := fun c v => by
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simp }

private theorem mem_growSub_iff {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2))
    (K : Submodule (ZMod 2) (Fin t → ZMod 2)) (y : Fin t → ZMod 2) :
    y ∈ growSub f K ↔ Submodule.Quotient.mk (p := K) y ∈ LinearMap.range (quotShift f K) := by
  constructor
  · intro hy
    let S : Submodule (ZMod 2) (Fin t → ZMod 2) :=
      (LinearMap.range (quotShift f K)).comap K.mkQ
    have hle : growSub f K ≤ S := by
      refine sup_le ?_ ?_
      · intro z hz
        show K.mkQ z ∈ LinearMap.range (quotShift f K)
        have h0 : K.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero K).2 hz
        rw [h0]
        exact Submodule.zero_mem _
      · rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    exact hle hy
  · rintro ⟨⟨v, hv⟩, heq⟩
    have hdiff : (f v - f 0) - y ∈ K := (Submodule.Quotient.eq K).1 heq
    have hmem1 : y - (f v - f 0) ∈ K := by
      have := K.neg_mem hdiff
      rwa [neg_sub] at this
    have hmem2 : f v - f 0 ∈ Submodule.span (ZMod 2)
        ((fun value => f value - f 0) '' (dirsSub f K : Set (Fin g → ZMod 2))) :=
      Submodule.subset_span ⟨v, hv, rfl⟩
    have hsum := Submodule.add_mem_sup hmem1 hmem2
    rwa [sub_add_cancel] at hsum

private theorem card_growSub_eq {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2))
    (K : Submodule (ZMod 2) (Fin t → ZMod 2)) :
    Nat.card ↥K * Nat.card (LinearMap.range (quotShift f K)) = Nat.card ↥(growSub f K) := by
  classical
  let K2 := growSub f K
  have hle : K ≤ K2 := le_sup_left
  let π : K2 →ₗ[ZMod 2] ((Fin t → ZMod 2) ⧸ K) := K.mkQ.comp K2.subtype
  have hrange : LinearMap.range π = LinearMap.range (quotShift f K) := by
    ext q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      constructor
      · rintro ⟨⟨z, hz⟩, hqz⟩
        have hmem : z ∈ K2 := hz
        rw [mem_growSub_iff] at hmem
        have hqeq : Submodule.Quotient.mk (p := K) z = Submodule.Quotient.mk (p := K) y := hqz
        rwa [← hqeq]
      · intro hq
        have hmem : y ∈ K2 := (mem_growSub_iff f K y).2 hq
        exact ⟨⟨y, hmem⟩, rfl⟩
  have hfib := linearMap_fiber_card π 0 (Submodule.zero_mem _)
  rw [hrange] at hfib
  have hker_eq : Nat.card {z : K2 // π z = 0} = Nat.card ↥K := by
    refine Nat.card_congr
      { toFun := fun ⟨⟨z, _⟩, hz⟩ => ⟨z, (Submodule.Quotient.mk_eq_zero K).1 hz⟩
        invFun := fun ⟨z, hz⟩ => ⟨⟨z, hle hz⟩, (Submodule.Quotient.mk_eq_zero K).2 hz⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  rw [hker_eq] at hfib
  exact hfib

private theorem H_stabilize {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2)) :
    let H := fun j : ℕ => ((growSub f)^[j]) (⊥ : Submodule (ZMod 2) (Fin t → ZMod 2))
    H (t + 1) = H t := by
  intro H
  have hmono : ∀ j, H j ≤ H (j + 1) := by
    intro j
    show ((growSub f)^[j]) ⊥ ≤ ((growSub f)^[j + 1]) ⊥
    rw [Function.iterate_succ_apply']
    exact le_sup_left
  have hstick : ∀ k, H (k + 1) = H k → ∀ d, H (k + d) = H k := by
    intro k hk d
    induction d with
    | zero => rfl
    | succ d ihd =>
      have h1 : H (k + (d + 1)) = growSub f (H (k + d)) := by
        show ((growSub f)^[k + d + 1]) ⊥ = growSub f (((growSub f)^[k + d]) ⊥)
        exact Function.iterate_succ_apply' (growSub f) (k + d) ⊥
      rw [h1, ihd]
      exact (Function.iterate_succ_apply' (growSub f) k ⊥).symm.trans hk
  by_contra hne
  have hstrict : ∀ j ≤ t, H j < H (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) fun heq => hne ?_
    have h1 := hstick j heq.symm (t - j)
    have h2 := hstick j heq.symm (t + 1 - j)
    rw [show j + (t - j) = t by omega] at h1
    rw [show j + (t + 1 - j) = t + 1 by omega] at h2
    exact h2.trans h1.symm
  have hdim : ∀ j ≤ t + 1, j ≤ Module.finrank (ZMod 2) (H j) := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ihj =>
      intro hj
      have hlt : Module.finrank (ZMod 2) (H j) < Module.finrank (ZMod 2) (H (j + 1)) :=
        Submodule.finrank_lt_finrank_of_lt (hstrict j (by omega))
      have hprev := ihj (by omega)
      omega
  have htop : Module.finrank (ZMod 2) (H (t + 1)) ≤ t := by
    calc Module.finrank (ZMod 2) (H (t + 1))
        ≤ Module.finrank (ZMod 2) (Fin t → ZMod 2) := Submodule.finrank_le _
      _ = t := by simp
  have hge := hdim (t + 1) (le_refl _)
  omega

private theorem fiber_count_aux {g t : ℕ} (f : (Fin g → ZMod 2) → (Fin t → ZMod 2)) :
    let H := fun j : ℕ => ((growSub f)^[j]) (⊥ : Submodule (ZMod 2) (Fin t → ZMod 2))
    ∀ (j : ℕ) (x : Fin g → ZMod 2) (y : Fin t → ZMod 2),
      let num := Nat.card {v : Fin g → ZMod 2 // v ∈ (dirsSub f (H j) : Set (Fin g → ZMod 2)) ∧ f (x + v) = y}
      (y - f x ∈ H (j + 1) → num * Nat.card ↥(H (j + 1)) = Nat.card ↥(dirsSub f (H j))) ∧
      (y - f x ∉ H (j + 1) → num = 0) := by
  intro H j
  have hnot : ∀ (k : ℕ) (x : Fin g → ZMod 2) (y : Fin t → ZMod 2),
      y - f x ∉ H (k + 1) →
      Nat.card {v : Fin g → ZMod 2 // v ∈ (dirsSub f (H k) : Set (Fin g → ZMod 2)) ∧ f (x + v) = y} = 0 := by
    intro k x y hny
    classical
    have hempty : IsEmpty {v : Fin g → ZMod 2 // v ∈ (dirsSub f (H k) : Set (Fin g → ZMod 2)) ∧ f (x + v) = y} := by
      refine ⟨fun ⟨v, hv, hfv⟩ => hny ?_⟩
      have h1 : (f (x + v) - f x) - (f v - f 0) ∈ H k := hv x
      have h2 : f v - f 0 ∈ Submodule.span (ZMod 2)
          ((fun value => f value - f 0) '' (dirsSub f (H k) : Set (Fin g → ZMod 2))) :=
        Submodule.subset_span ⟨v, hv, rfl⟩
      have hsum : (f (x + v) - f x) ∈ growSub f (H k) := by
        have := Submodule.add_mem_sup h1 h2
        rwa [sub_add_cancel] at this
      have heq : H (k + 1) = growSub f (H k) := Function.iterate_succ_apply' (growSub f) k ⊥
      rw [heq, ← hfv]
      exact hsum
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero
  induction j with
  | zero =>
    intro x y
    refine ⟨fun hy => ?_, hnot 0 x y⟩
    classical
    have hH0 : H 0 = ⊥ := rfl
    have hH1 : H 1 = growSub f ⊥ := rfl
    let D0 := dirsSub f ⊥
    let ψ : D0 →ₗ[ZMod 2] ((Fin t → ZMod 2) ⧸ (⊥ : Submodule (ZMod 2) (Fin t → ZMod 2))) :=
      quotShift f ⊥
    have hmem : Submodule.Quotient.mk (p := (⊥ : Submodule (ZMod 2) (Fin t → ZMod 2))) (y - f x) ∈
        LinearMap.range ψ := (mem_growSub_iff f ⊥ (y - f x)).1 hy
    have hfib := linearMap_fiber_card ψ (Submodule.Quotient.mk (y - f x)) hmem
    have hcg := card_growSub_eq f (⊥ : Submodule (ZMod 2) (Fin t → ZMod 2))
    have hbot : Nat.card ↥(⊥ : Submodule (ZMod 2) (Fin t → ZMod 2)) = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
      exact ⟨0, fun ⟨z, hz⟩ => Subtype.ext ((Submodule.mem_bot (ZMod 2)).1 hz)⟩
    rw [hbot, one_mul] at hcg
    rw [hcg] at hfib
    have heqv : Nat.card {v : Fin g → ZMod 2 // v ∈ (dirsSub f (H 0) : Set (Fin g → ZMod 2)) ∧ f (x + v) = y} =
        Nat.card {v : D0 // ψ v = Submodule.Quotient.mk (y - f x)} := by
      refine Nat.card_congr
        { toFun := fun ⟨v, hv, hfv⟩ => ⟨⟨v, hv⟩, by
            apply (Submodule.Quotient.eq ⊥).2
            have h0 := hv x
            rw [hH0, Submodule.mem_bot] at h0
            rw [Submodule.mem_bot, ← hfv]
            have := congrArg (fun z => -z) h0
            simpa [sub_eq_add_neg] using this⟩
          invFun := fun ⟨⟨v, hv⟩, hψ⟩ => ⟨v, hv, by
            have h1 : (f v - f 0) - (y - f x) = 0 :=
              (Submodule.mem_bot (ZMod 2)).1 ((Submodule.Quotient.eq ⊥).1 hψ)
            have h0 : (f (x + v) - f x) - (f v - f 0) = 0 :=
              (Submodule.mem_bot (ZMod 2)).1 (hv x)
            have h2 := congrArg₂ (· + ·) h0 h1
            simp only [add_zero] at h2
            have h3 : f (x + v) - y = 0 := by
              calc f (x + v) - y = ((f (x + v) - f x) - (f v - f 0)) + ((f v - f 0) - (y - f x)) := by abel
                _ = 0 := h2
            exact sub_eq_zero.1 h3⟩
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    rw [heqv, hH1, hH0]
    exact hfib
  | succ j ih =>
    intro x y
    refine ⟨fun hy => ?_, hnot (j + 1) x y⟩
    classical
    let K0 := H j
    let K1 := H (j + 1)
    let K2 := H (j + 2)
    have hK1 : K1 = growSub f K0 := Function.iterate_succ_apply' (growSub f) j ⊥
    have hK2 : K2 = growSub f K1 := Function.iterate_succ_apply' (growSub f) (j + 1) ⊥
    have hK01 : K0 ≤ K1 := by rw [hK1]; exact le_sup_left
    let D0 := dirsSub f K0
    let D1 := dirsSub f K1
    have hD01 : D0 ≤ D1 := fun v hv x0 => hK01 (hv x0)
    let ψ : D1 →ₗ[ZMod 2] ((Fin t → ZMod 2) ⧸ K1) := quotShift f K1
    have hmem : Submodule.Quotient.mk (p := K1) (y - f x) ∈ LinearMap.range ψ := by
      change y - f x ∈ K2 at hy
      rw [hK2] at hy
      exact (mem_growSub_iff f K1 (y - f x)).1 hy
    have hT_eq : Nat.card {v : D1 // ψ v = Submodule.Quotient.mk (y - f x)} *
        Nat.card (LinearMap.range ψ) = Nat.card ↥D1 :=
      linearMap_fiber_card ψ (Submodule.Quotient.mk (y - f x)) hmem
    have hcg : Nat.card ↥K1 * Nat.card (LinearMap.range ψ) = Nat.card ↥K2 := by
      rw [hK2]
      exact card_growSub_eq f K1
    let T := {v : D1 // ψ v = Submodule.Quotient.mk (y - f x)}
    let S := {w : Fin g → ZMod 2 // w ∈ (D1 : Set (Fin g → ZMod 2)) ∧ f (x + w) = y}
    let P := {p : T × D0 // f (x + p.1.1.1 + p.2.1) = y}
    have hT_mem : ∀ v : T, y - f (x + v.1.1) ∈ K1 := by
      intro v
      have h1 : (f (x + v.1.1) - f x) - (f v.1.1 - f 0) ∈ K1 := v.1.2 x
      have h2 : (f v.1.1 - f 0) - (y - f x) ∈ K1 := (Submodule.Quotient.eq K1).1 v.2
      have hsum := K1.add_mem h1 h2
      have heq : ((f (x + v.1.1) - f x) - (f v.1.1 - f 0)) + ((f v.1.1 - f 0) - (y - f x)) =
          f (x + v.1.1) - y := by abel
      rw [heq] at hsum
      have hneg := K1.neg_mem hsum
      rwa [neg_sub] at hneg
    have hP_count1 : Nat.card P * Nat.card ↥K1 = Nat.card T * Nat.card ↥D0 := by
      have hcardP : Nat.card P = ∑ v : T,
          Nat.card {u : Fin g → ZMod 2 // u ∈ (D0 : Set (Fin g → ZMod 2)) ∧ f (x + v.1.1 + u) = y} := by
        rw [Nat.card_eq_fintype_card]
        have hfib := Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset P))
          (t := (Finset.univ : Finset T))
          (f := fun p : P => p.1.1)
          (fun _ _ => Finset.mem_univ _)
        rw [Finset.card_univ] at hfib
        rw [hfib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Nat.card_eq_fintype_card]
        have heqv : {p : P // p.1.1 = v} ≃
            {u : Fin g → ZMod 2 // u ∈ (D0 : Set (Fin g → ZMod 2)) ∧ f (x + v.1.1 + u) = y} :=
          { toFun := fun ⟨⟨⟨v', ⟨u, hu⟩⟩, hfu⟩, hv'⟩ => ⟨u, hu, by rw [← hv']; exact hfu⟩
            invFun := fun ⟨u, hu, hfu⟩ => ⟨⟨⟨v, ⟨u, hu⟩⟩, hfu⟩, rfl⟩
            left_inv := fun ⟨⟨⟨v', ⟨u, hu⟩⟩, hfu⟩, hv'⟩ => by subst hv'; rfl
            right_inv := fun ⟨_, _, _⟩ => rfl }
        rw [← Fintype.card_congr heqv, Fintype.card_subtype]
      rw [hcardP, Finset.sum_mul]
      have hterm : ∀ v : T,
          Nat.card {u : Fin g → ZMod 2 // u ∈ (D0 : Set (Fin g → ZMod 2)) ∧ f (x + v.1.1 + u) = y} *
            Nat.card ↥K1 = Nat.card ↥D0 := fun v => (ih (x + v.1.1) y).1 (hT_mem v)
      rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, ← Nat.card_eq_fintype_card]
    have hP_count2 : Nat.card P = Nat.card S * Nat.card ↥D0 := by
      rw [← Nat.card_prod]
      refine Nat.card_congr
        { toFun := fun ⟨⟨⟨⟨v, hv⟩, _⟩, ⟨u, hu⟩⟩, hfu⟩ =>
            ⟨⟨v + u, D1.add_mem hv (hD01 hu), by rw [← add_assoc]; exact hfu⟩, ⟨u, hu⟩⟩
          invFun := fun ⟨⟨w, hw, hfw⟩, ⟨u, hu⟩⟩ =>
            ⟨⟨⟨⟨w - u, D1.sub_mem hw (hD01 hu)⟩, by
              apply (Submodule.Quotient.eq K1).2
              have h1 : (f (x + (w - u)) - f x) - (f (w - u) - f 0) ∈ K1 :=
                (D1.sub_mem hw (hD01 hu)) x
              have h2 : y - f (x + (w - u)) ∈ K1 := by
                have ha : (f ((x + (w - u)) + u) - f (x + (w - u))) - (f u - f 0) ∈ K0 :=
                  hu (x + (w - u))
                have hb : f u - f 0 ∈ Submodule.span (ZMod 2)
                    ((fun value => f value - f 0) '' (dirsSub f K0 : Set (Fin g → ZMod 2))) :=
                  Submodule.subset_span ⟨u, hu, rfl⟩
                have hc : f ((x + (w - u)) + u) - f (x + (w - u)) ∈ K1 := by
                  rw [hK1]
                  have := Submodule.add_mem_sup ha hb
                  rwa [sub_add_cancel] at this
                have hxw : (x + (w - u)) + u = x + w := by abel
                rwa [hxw, hfw] at hc
              have h3 := K1.sub_mem (K1.neg_mem h1) h2
              have heq : -((f (x + (w - u)) - f x) - (f (w - u) - f 0)) - (y - f (x + (w - u))) =
                  (f (w - u) - f 0) - (y - f x) := by abel
              rwa [heq] at h3⟩, ⟨u, hu⟩⟩, by
                have hxw : x + (w - u) + u = x + w := by abel
                rw [hxw]; exact hfw⟩
          left_inv := fun ⟨⟨⟨⟨v, hv⟩, hψ⟩, ⟨u, hu⟩⟩, hfu⟩ => by
            apply Subtype.ext
            apply Prod.ext
            · apply Subtype.ext; apply Subtype.ext; exact add_sub_cancel_right v u
            · rfl
          right_inv := fun ⟨⟨w, hw, hfw⟩, ⟨u, hu⟩⟩ => by
            apply Prod.ext
            · apply Subtype.ext; exact sub_add_cancel w u
            · rfl }
    have hD0_pos : 0 < Nat.card ↥D0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.2 ⟨0⟩
    have hSK1 : Nat.card S * Nat.card ↥K1 = Nat.card T := by
      have hmul : (Nat.card S * Nat.card ↥K1) * Nat.card ↥D0 = Nat.card T * Nat.card ↥D0 := by
        calc (Nat.card S * Nat.card ↥K1) * Nat.card ↥D0
            = (Nat.card S * Nat.card ↥D0) * Nat.card ↥K1 := by ring
          _ = Nat.card P * Nat.card ↥K1 := by rw [← hP_count2]
          _ = Nat.card T * Nat.card ↥D0 := hP_count1
      exact Nat.eq_of_mul_eq_mul_right hD0_pos hmul
    calc Nat.card S * Nat.card ↥K2
        = Nat.card S * (Nat.card ↥K1 * Nat.card (LinearMap.range ψ)) := by rw [← hcg]
      _ = (Nat.card S * Nat.card ↥K1) * Nat.card (LinearMap.range ψ) := by ring
      _ = Nat.card T * Nat.card (LinearMap.range ψ) := by rw [hSK1]
      _ = Nat.card ↥D1 := hT_eq

theorem main_aux (g t : ℕ) (f : (Fin g → ZMod 2) → (Fin t → ZMod 2)) :
    let F := ZMod 2
    let X := Fin g → F
    let Y := Fin t → F
    let dirs := fun H : Submodule F Y =>
      {v : X | ∀ x : X, (f (x+v) - f x) - (f v - f 0) ∈ H}
    let grow := fun prior : Submodule F Y =>
      prior ⊔ Submodule.span F ((fun value : X => f value - f 0) '' dirs prior)
    let H := fun j : ℕ => (grow^[j]) (⊥ : Submodule F Y)
    H (t+1) = H t ∧
    ∀ (j : ℕ) (x : X) (y : Y),
      let num := Nat.card {v : X // v ∈ dirs (H j) ∧ f (x+v) = y}
      (y - f x ∈ H (j+1) → num * Nat.card ↥(H (j+1)) = Nat.card ↥(dirs (H j))) ∧
      (y - f x ∉ H (j+1) → num = 0) := by
  exact ⟨H_stabilize f, fiber_count_aux f⟩

end PEqualNP.Outside.L_lib_628_aux

theorem PEqualNP.Outside.L_lib_628 : ∀ (g t : ℕ),
  let F := ZMod 2
  let X := Fin g → F
  let Y := Fin t → F
  ∀ f : X → Y,
    let dirs := fun H : Submodule F Y =>
      {v : X | ∀ x : X, (f (x+v) - f x) - (f v - f 0) ∈ H}
    let grow := fun prior : Submodule F Y =>
      prior ⊔ Submodule.span F ((fun value : X => f value - f 0) '' dirs prior)
    let H := fun j : ℕ => (grow^[j]) (⊥ : Submodule F Y)
    H (t+1) = H t ∧
    ∀ (j : ℕ) (x : X) (y : Y),
      let num := Nat.card {v : X // v ∈ dirs (H j) ∧ f (x+v) = y}
      (y - f x ∈ H (j+1) → num * Nat.card ↥(H (j+1)) = Nat.card ↥(dirs (H j))) ∧
      (y - f x ∉ H (j+1) → num = 0) := by
  intro g t F X Y f
  exact PEqualNP.Outside.L_lib_628_aux.main_aux g t f

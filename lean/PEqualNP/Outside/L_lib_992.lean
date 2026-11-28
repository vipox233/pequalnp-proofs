import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_992_aux


-- Part T: the run of a parity decision tree, with the answer bits given by b.

def adv_st (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) : List Bool :=
  (List.range k).foldl (fun (p : List Bool) _ => if p ∈ T then p ++ [b p] else p) []

theorem adv_st_succ (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) :
    adv_st T b (k + 1) = if adv_st T b k ∈ T then adv_st T b k ++ [b (adv_st T b k)] else adv_st T b k := by
  have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
  unfold adv_st
  rw [hr, List.foldl_append]
  rfl

theorem adv_st_inv (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) :
    (adv_st T b k).length ≤ k ∧ ((adv_st T b k).length = k ∨ adv_st T b k ∉ T) ∧
      ∀ j < (adv_st T b k).length, (adv_st T b k).take j ∈ T := by
  induction k with
  | zero => simp [adv_st]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [adv_st_succ]
    by_cases hk : adv_st T b k ∈ T
    · rw [if_pos hk]
      have hl : (adv_st T b k).length = k := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd hk h2
      refine ⟨by simp [hl], Or.inl (by simp [hl]), ?_⟩
      intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjk : j < (adv_st T b k).length
      · rw [List.take_append_of_le_length (by omega)]
        exact h3 j hjk
      · have hjeq : j = (adv_st T b k).length := by omega
        rw [hjeq, List.take_left]
        exact hk
    · rw [if_neg hk]
      exact ⟨by omega, Or.inr hk, h3⟩

theorem adv_st_stat (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) (hk : adv_st T b k ∉ T) :
    ∀ i, adv_st T b (k + i) = adv_st T b k := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← Nat.add_assoc, adv_st_succ, ih, if_neg hk]

theorem adv_st_prefix (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) :
    ∀ i, adv_st T b k <+: adv_st T b (k + i) := by
  intro i
  induction i with
  | zero => exact List.prefix_refl _
  | succ i ih =>
    rw [← Nat.add_assoc, adv_st_succ]
    by_cases hq : adv_st T b (k + i) ∈ T
    · rw [if_pos hq]
      exact ih.trans (List.prefix_append _ _)
    · rw [if_neg hq]
      exact ih

theorem adv_st_take (T : Finset (List Bool)) (b : List Bool → Bool) (N k : Nat) (hk : k ≤ N) :
    adv_st T b k = (adv_st T b N).take k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨h1, h2, -⟩ := adv_st_inv T b k
  rcases h2 with h2 | h2
  · have h := List.prefix_iff_eq_take.mp (adv_st_prefix T b k i)
    rw [h2] at h
    exact h
  · rw [adv_st_stat T b k h2 i, List.take_of_length_le h1]

theorem adv_st_bit (T : Finset (List Bool)) (b : List Bool → Bool) (N j : Nat)
    (hj : j < (adv_st T b N).length) :
    (adv_st T b N).take (j + 1) = (adv_st T b N).take j ++ [b ((adv_st T b N).take j)] := by
  have hN := (adv_st_inv T b N).1
  have h1 := adv_st_take T b N j (by omega)
  have h2 := adv_st_take T b N (j + 1) (by omega)
  rw [adv_st_succ] at h2
  by_cases hq : adv_st T b j ∈ T
  · rw [if_pos hq] at h2
    rw [← h1, ← h2]
  · rw [if_neg hq] at h2
    have h3 := congrArg List.length (h1.symm.trans h2)
    simp only [List.length_take] at h3
    omega

theorem adv_st_congr (T : Finset (List Bool)) (b b' : List Bool → Bool) (N : Nat)
    (h : ∀ j < (adv_st T b N).length, b' ((adv_st T b N).take j) = b ((adv_st T b N).take j)) :
    adv_st T b' N = adv_st T b N := by
  have key : ∀ k ≤ N, adv_st T b' k = adv_st T b k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      rw [adv_st_succ, adv_st_succ, ih']
      by_cases hq : adv_st T b k ∈ T
      · rw [if_pos hq, if_pos hq]
        have hlen : (adv_st T b k).length = k := by
          rcases (adv_st_inv T b k).2.1 with h2 | h2
          · exact h2
          · exact absurd hq h2
        have htk : adv_st T b k = (adv_st T b N).take k := adv_st_take T b N k (by omega)
        have hk1 := adv_st_take T b N (k + 1) hk
        rw [adv_st_succ, if_pos hq] at hk1
        have hlt : k < (adv_st T b N).length := by
          have h4 := congrArg List.length hk1
          simp only [List.length_append, List.length_singleton, List.length_take, hlen] at h4
          omega
        have hb : b' (adv_st T b k) = b (adv_st T b k) := by
          rw [htk]
          exact h k hlt
        rw [hb]
      · rw [if_neg hq, if_neg hq]
  exact key N le_rfl

theorem adv_st_bits_eq (T : Finset (List Bool)) (b b' : List Bool → Bool) (N : Nat)
    (h : adv_st T b' N = adv_st T b N) :
    ∀ j < (adv_st T b N).length, b' ((adv_st T b N).take j) = b ((adv_st T b N).take j) := by
  intro j hj
  have e1 := adv_st_bit T b N j hj
  have e2 := adv_st_bit T b' N j (by rw [h]; exact hj)
  rw [h] at e2
  have e3 := e1.symm.trans e2
  rw [List.append_cancel_left_eq, List.singleton_inj] at e3
  exact e3.symm

theorem adv_st_leaf (T : Finset (List Bool)) (b : List Bool → Bool) :
    adv_st T b T.card ∉ T ∧ ∀ j < (adv_st T b T.card).length, (adv_st T b T.card).take j ∈ T := by
  obtain ⟨h1, h2, h3⟩ := adv_st_inv T b T.card
  refine ⟨?_, h3⟩
  intro hmem
  rcases h2 with h2 | h2
  · have hsub : (Finset.range (T.card + 1)).image (fun j => (adv_st T b T.card).take j) ⊆ T := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      rw [Finset.mem_range] at hj
      by_cases hjk : j < T.card
      · exact h3 j (by omega)
      · have hjeq : j = (adv_st T b T.card).length := by omega
        rw [hjeq, List.take_length]
        exact hmem
    have hcard : ((Finset.range (T.card + 1)).image
        (fun j => (adv_st T b T.card).take j)).card = T.card + 1 := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range _
      · intro i hi j hj hij
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        have h4 := congrArg List.length hij
        simp only [List.length_take] at h4
        omega
    have := Finset.card_le_card hsub
    omega
  · exact h2 hmem

theorem adv_decomp (p : List Bool) : ∃ r : List Bool, ∃ k : Nat,
    p = r ++ List.replicate k true ∧ (r = [] ∨ ∃ q, r = q ++ [false]) := by
  induction p using List.reverseRecOn with
  | nil => exact ⟨[], 0, rfl, Or.inl rfl⟩
  | append_singleton p a ih =>
    cases a with
    | false => exact ⟨p ++ [false], 0, by simp, Or.inr ⟨p, rfl⟩⟩
    | true =>
      obtain ⟨r, k, hp, hr⟩ := ih
      refine ⟨r, k + 1, ?_, hr⟩
      rw [hp, List.replicate_succ', List.append_assoc]

theorem adv_leaf_card {X : Type*} [Fintype X] (T : Finset (List Bool)) (b : X → List Bool → Bool) :
    ((Finset.univ : Finset X).image (fun x => adv_st T (b x) T.card)).card ≤ T.card + 1 := by
  classical
  set R := (Finset.univ : Finset X).image (fun x => adv_st T (b x) T.card) with hR
  have hleaf : ∀ p ∈ R, p ∉ T ∧ ∀ j < p.length, p.take j ∈ T := by
    intro p hp
    rw [hR, Finset.mem_image] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact adv_st_leaf T (b x)
  have hpre : ∀ p ∈ R, ∀ p' ∈ R, p <+: p' → p = p' := by
    intro p hp p' hp' hpp
    by_contra hne
    have hlt : p.length < p'.length := by
      rcases Nat.lt_or_ge p.length p'.length with h | h
      · exact h
      · exact absurd (hpp.eq_of_length_le h) hne
    have h5 := (hleaf p' hp').2 p.length hlt
    rw [← List.prefix_iff_eq_take.mp hpp] at h5
    exact (hleaf p hp).1 h5
  let θ : List Bool → List Bool := fun p => (adv_decomp p).choose
  have hθ : ∀ p, ∃ k, p = θ p ++ List.replicate k true ∧ (θ p = [] ∨ ∃ q, θ p = q ++ [false]) :=
    fun p => (adv_decomp p).choose_spec
  have hmaps : ∀ p ∈ R, θ p ∈ insert [] (T.image (fun q => q ++ [false])) := by
    intro p hp
    obtain ⟨k, hk, hr⟩ := hθ p
    rcases hr with hr | ⟨q, hq⟩
    · rw [hr]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_image]
      refine ⟨q, ?_, hq.symm⟩
      have hqp : q = p.take q.length := by
        rw [hk, hq, List.append_assoc, List.take_left]
      have hlt : q.length < p.length := by
        rw [hk, hq]
        simp only [List.length_append, List.length_singleton, List.length_replicate]
        omega
      rw [hqp]
      exact (hleaf p hp).2 q.length hlt
  have hinj : Set.InjOn θ (R : Set (List Bool)) := by
    intro p hp p' hp' hpp
    obtain ⟨k, hk, -⟩ := hθ p
    obtain ⟨k', hk', -⟩ := hθ p'
    rcases Nat.le_total k k' with h | h
    · apply hpre p hp p' hp'
      rw [hk, hk', hpp]
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [List.replicate_add, ← List.append_assoc]
      exact List.prefix_append _ _
    · symm
      apply hpre p' hp' p hp
      rw [hk, hk', hpp]
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [List.replicate_add, ← List.append_assoc]
      exact List.prefix_append _ _
  calc R.card ≤ (insert [] (T.image (fun q => q ++ [false]))).card :=
        Finset.card_le_card_of_injOn θ (fun p hp => hmaps p hp) hinj
    _ ≤ (T.image (fun q => q ++ [false])).card + 1 := Finset.card_insert_le _ _
    _ ≤ T.card + 1 := by
        have := Finset.card_image_le (s := T) (f := fun q => q ++ [false])
        omega

-- the tree part: a largest leaf is a coset of a subspace U, and 2^(n+m) is at most (card T + 1) 2^(dim U)

theorem adv_tree_part {n m : Nat} (T : Finset (List Bool))
    (ask : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (bias : List Bool → ZMod 2) :
    ∃ (x0 : (Fin n → ZMod 2) × (Fin m → ZMod 2))
      (U : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2))),
      (∀ u ∈ U, adv_st T (fun p => decide (ask p (x0 + u) + bias p ≠ 0)) T.card =
        adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card) ∧
      2 ^ (n + m) ≤ (T.card + 1) * 2 ^ Module.finrank (ZMod 2) U := by
  classical
  set leaf : (Fin n → ZMod 2) × (Fin m → ZMod 2) → List Bool :=
    fun x => adv_st T (fun p => decide (ask p x + bias p ≠ 0)) T.card with hleaf
  set R := (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))).image leaf with hR
  have hRc : R.card ≤ T.card + 1 := adv_leaf_card T (fun x p => decide (ask p x + bias p ≠ 0))
  have hpig : ∃ p0 ∈ R, (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))).card ≤
      R.card * (Finset.univ.filter (fun x => leaf x = p0)).card := by
    by_contra hcon
    push_neg at hcon
    have hsum := Finset.card_eq_sum_card_fiberwise (f := leaf)
      (s := (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2)))) (t := R)
      (fun x _ => Finset.mem_image_of_mem leaf (Finset.mem_univ x))
    have hne : R.Nonempty := Finset.univ_nonempty.image leaf
    have hlt := Finset.sum_lt_sum_of_nonempty hne hcon
    rw [← Finset.mul_sum, ← hsum, Finset.sum_const, smul_eq_mul] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨p0, hp0R, hp0⟩ := hpig
  rw [hR, Finset.mem_image] at hp0R
  obtain ⟨x0, -, hx0⟩ := hp0R
  have hp0e : adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card = p0 := hx0
  let U : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2)) :=
    ⨅ j : Fin p0.length, LinearMap.ker (ask (p0.take j))
  have hcongr : ∀ x, (∀ j < p0.length, ask (p0.take j) x = ask (p0.take j) x0) →
      adv_st T (fun p => decide (ask p x + bias p ≠ 0)) T.card =
        adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card := by
    intro x hx
    apply adv_st_congr
    rw [hp0e]
    intro j hj
    show decide (ask (p0.take j) x + bias (p0.take j) ≠ 0) =
      decide (ask (p0.take j) x0 + bias (p0.take j) ≠ 0)
    rw [hx j hj]
  have hconv : ∀ x, leaf x = leaf x0 → ∀ j < p0.length, ask (p0.take j) x = ask (p0.take j) x0 := by
    intro x hx j hj
    have h1 := adv_st_bits_eq T (fun p => decide (ask p x0 + bias p ≠ 0))
      (fun p => decide (ask p x + bias p ≠ 0)) T.card hx
    rw [hp0e] at h1
    have h2 : decide (ask (p0.take j) x + bias (p0.take j) ≠ 0) =
        decide (ask (p0.take j) x0 + bias (p0.take j) ≠ 0) := h1 j hj
    have key : ∀ a b c : ZMod 2, decide (a + c ≠ 0) = decide (b + c ≠ 0) → a = b := by decide
    exact key _ _ _ h2
  have hmemU : ∀ x, leaf x = p0 → x - x0 ∈ U := by
    intro x hx
    rw [Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, map_sub, hconv x (hx.trans hx0.symm) j j.2, sub_self]
  have hfib : (Finset.univ.filter (fun x => leaf x = p0)).card ≤ Nat.card U := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun x => if h : x - x0 ∈ U then (⟨x - x0, h⟩ : U) else 0) (fun x _ => Finset.mem_univ _) ?_
    intro x hx x' hx' hxx
    have hx1 : leaf x = p0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hx2 : leaf x' = p0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx')).2
    have hxU := hmemU x hx1
    have hxU' := hmemU x' hx2
    simp only [dif_pos hxU, dif_pos hxU', Subtype.mk.injEq, sub_left_inj] at hxx
    exact hxx
  have hX : (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))).card = 2 ^ (n + m) := by
    simp [pow_add]
  refine ⟨x0, U, fun u hu => ?_, ?_⟩
  · apply hcongr
    intro j hj
    have h1 : ask (p0.take j) u = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hu ⟨j, hj⟩)
    rw [map_add, h1, add_zero]
  · have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [Nat.card_zmod] at h1
    rw [← h1, ← hX]
    calc _ ≤ R.card * (Finset.univ.filter (fun x => leaf x = p0)).card := hp0
      _ ≤ (T.card + 1) * Nat.card U := Nat.mul_le_mul hRc hfib

-- Part I: an information set J of a subspace V, with a linear lift

theorem adv_infoset {m : Nat} (V : Submodule (ZMod 2) (Fin m → ZMod 2)) (C : Finset (Fin m)) :
    ∃ (J : Finset (Fin m)) (lift : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)),
      (∀ u, lift u ∈ V) ∧ (∀ u, ∀ j ∈ J, lift u j = u j) ∧
      (∀ v ∈ V, (∀ j ∈ J, v j = 0) → ∀ i ∈ C, v i = 0) := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    refine ⟨∅, 0, fun u => V.zero_mem, fun u j hj => by simp at hj, fun v _ _ i hi => by simp at hi⟩
  | insert c C' hc ih =>
    obtain ⟨J', lift', h1, h2, h3⟩ := ih
    by_cases hex : ∃ v1 ∈ V, (∀ j ∈ J', v1 j = 0) ∧ v1 c = 1
    · obtain ⟨v1, hv1V, hv1J, hv1c⟩ := hex
      refine ⟨insert c J',
        lift' + LinearMap.smulRight (LinearMap.proj c - (LinearMap.proj c).comp lift') v1, ?_, ?_, ?_⟩
      · intro u
        rw [LinearMap.add_apply, LinearMap.smulRight_apply]
        exact V.add_mem (h1 u) (V.smul_mem _ hv1V)
      · intro u j hj
        simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
          LinearMap.proj_apply, LinearMap.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases Finset.mem_insert.mp hj with hj | hj
        · subst hj
          rw [hv1c]
          ring
        · rw [hv1J j hj, h2 u j hj]
          ring
      · intro v hv hvJ i hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst hi
          exact hvJ _ (Finset.mem_insert_self _ _)
        · exact h3 v hv (fun j hj => hvJ j (Finset.mem_insert_of_mem hj)) i hi
    · refine ⟨J', lift', h1, h2, ?_⟩
      intro v hv hvJ i hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst hi
        by_contra hne
        apply hex
        refine ⟨v, hv, hvJ, ?_⟩
        have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        exact key _ hne
      · exact h3 v hv hvJ i hi

-- Part M: the diagonal shift. For every linear M there is t such that whenever every
-- u keeps at most e nonzero entries of a + M u + y u on J, y agrees with t on at most e
-- coordinates of J. (Induction on J: the Schur complement of the new pivot.)

theorem adv_core {m : Nat} (J : Finset (Fin m)) :
    ∀ M : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
    ∃ t : Fin m → ZMod 2, ∀ (y a : Fin m → ZMod 2) (e : Nat),
      (∀ u : Fin m → ZMod 2, (J.filter (fun j => a j + M u j + y j * u j ≠ 0)).card ≤ e) →
      (J.filter (fun j => y j = t j)).card ≤ e := by
  classical
  induction J using Finset.induction_on with
  | empty => intro M; exact ⟨0, fun y a e _ => by simp⟩
  | insert j0 J' hj0 ih =>
    intro M
    let e0 : Fin m → ZMod 2 := Pi.single j0 1
    let Z : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
      LinearMap.id - LinearMap.smulRight (LinearMap.proj j0) e0
    let ψ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
      Z + LinearMap.smulRight ((LinearMap.proj j0).comp (M.comp Z)) e0
    obtain ⟨t', ht'⟩ := ih (M.comp ψ)
    refine ⟨Function.update t' j0 (M e0 j0 + 1), ?_⟩
    intro y a e h
    have hne : ∀ j ∈ J', j ≠ j0 := fun j hj hjj => hj0 (hjj ▸ hj)
    have hZ : ∀ u : Fin m → ZMod 2, ∀ j, j ≠ j0 → Z u j = u j := by
      intro u j hj
      simp [Z, e0, Pi.single_apply, hj]
    have hZ0 : ∀ u : Fin m → ZMod 2, Z u j0 = 0 := by
      intro u
      simp [Z, e0]
    have hval : ∀ (u : Fin m → ZMod 2) (δ : ZMod 2) (j : Fin m), j ≠ j0 →
        (ψ u + δ • e0) j = u j := by
      intro u δ j hj
      simp [ψ, hZ u j hj, e0, Pi.single_apply, hj]
    have hval0 : ∀ (u : Fin m → ZMod 2) (δ : ZMod 2),
        (ψ u + δ • e0) j0 = M (Z u) j0 + δ := by
      intro u δ
      simp [ψ, hZ0, e0]
    have hMw : ∀ (u : Fin m → ZMod 2) (δ : ZMod 2) (j : Fin m),
        M (ψ u + δ • e0) j = (M.comp ψ) u j + δ * M e0 j := by
      intro u δ j
      simp only [map_add, map_smul, LinearMap.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hMψ0 : ∀ u : Fin m → ZMod 2,
        (M.comp ψ) u j0 = M (Z u) j0 + M (Z u) j0 * M e0 j0 := by
      intro u
      simp only [ψ, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.proj_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hsplit : ∀ (Q : Fin m → Prop) [DecidablePred Q],
        ((insert j0 J').filter Q).card = (J'.filter Q).card + (if Q j0 then 1 else 0) := by
      intro Q _
      rw [Finset.filter_insert]
      by_cases hq : Q j0
      · rw [if_pos hq, if_pos hq,
          Finset.card_insert_of_notMem (fun hmem => hj0 (Finset.mem_filter.mp hmem).1)]
      · rw [if_neg hq, if_neg hq, Nat.add_zero]
    have htarget : J'.filter (fun j => y j = Function.update t' j0 (M e0 j0 + 1) j) =
        J'.filter (fun j => y j = t' j) := by
      apply Finset.filter_congr
      intro j hj
      rw [Function.update_of_ne (hne j hj)]
    rw [hsplit, htarget]
    by_cases hy : y j0 = M e0 j0 + 1
    · have hc0 : y j0 = Function.update t' j0 (M e0 j0 + 1) j0 := by
        rw [Function.update_self]
        exact hy
      rw [if_pos hc0]
      have key : ∀ u : Fin m → ZMod 2,
          (J'.filter (fun j => a j + (a j0 + 1) * M e0 j + (M.comp ψ) u j + y j * u j ≠ 0)).card
            + 1 ≤ e := by
        intro u
        have hu := h (ψ u + (a j0 + 1) • e0)
        rw [hsplit] at hu
        have hq : a j0 + M (ψ u + (a j0 + 1) • e0) j0 + y j0 * (ψ u + (a j0 + 1) • e0) j0 ≠ 0 := by
          rw [hMw, hMψ0, hval0, hy]
          generalize M (Z u) j0 = β
          generalize M e0 j0 = μ
          generalize a j0 = α
          revert α β μ
          decide
        rw [if_pos hq] at hu
        have hc : J'.filter (fun j => a j + (a j0 + 1) * M e0 j + (M.comp ψ) u j + y j * u j ≠ 0) =
            J'.filter (fun j => a j + M (ψ u + (a j0 + 1) • e0) j +
              y j * (ψ u + (a j0 + 1) • e0) j ≠ 0) := by
          apply Finset.filter_congr
          intro j hj
          rw [hMw, hval u _ j (hne j hj)]
          constructor <;> intro h1 h2 <;> apply h1 <;> linear_combination h2
        rw [hc]
        exact hu
      have he : 1 ≤ e := by
        have := key 0
        omega
      have h3 := ht' y (fun j => a j + (a j0 + 1) * M e0 j) (e - 1) (fun u => by
        show (J'.filter (fun j => a j + (a j0 + 1) * M e0 j + (M.comp ψ) u j + y j * u j ≠ 0)).card
          ≤ e - 1
        have := key u
        omega)
      omega
    · have hc0 : ¬ y j0 = Function.update t' j0 (M e0 j0 + 1) j0 := by
        rw [Function.update_self]
        exact hy
      rw [if_neg hc0]
      have h3 := ht' y a e (fun u => by
        have hu := h (ψ u + (0 : ZMod 2) • e0)
        rw [hsplit] at hu
        have hc : J'.filter (fun j => a j + (M.comp ψ) u j + y j * u j ≠ 0) =
            J'.filter (fun j => a j + M (ψ u + (0 : ZMod 2) • e0) j +
              y j * (ψ u + (0 : ZMod 2) • e0) j ≠ 0) := by
          apply Finset.filter_congr
          intro j hj
          rw [hMw, hval u _ j (hne j hj), zero_mul, add_zero]
        rw [hc]
        split_ifs at hu <;> omega)
      omega

-- Part L: the linear algebra on one leaf.

theorem adv_lin_part {n m e L : Nat}
    (z : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (P : Fin m → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (d : Fin m → ZMod 2)
    (x0 : (Fin n → ZMod 2) × (Fin m → ZMod 2))
    (U : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2)))
    (herr : ∀ u ∈ U, ((Finset.univ : Finset (Fin m)).filter
        (fun i => z (x0 + u).1 i * (x0 + u).2 i ≠ P i (x0 + u) + d i)).card ≤ e)
    (hL : 1 ≤ L)
    (hsize : 2 ^ (n + m) ≤ L * 2 ^ Module.finrank (ZMod 2) U) :
    ∃ (B : Submodule (ZMod 2) (Fin n → ZMod 2)) (center : Fin m → ZMod 2),
      2 ^ (n - Module.finrank (ZMod 2) B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e := by
  classical
  obtain ⟨J, lift, hlV, hlJ, hV0⟩ :=
    adv_infoset (U.comap (LinearMap.inr (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))) Finset.univ
  let G : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    LinearMap.pi (fun i => (P i).comp (LinearMap.inr (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)))
  obtain ⟨t, ht⟩ := adv_core J (G.comp lift)
  have hlU : ∀ u, ((0 : Fin n → ZMod 2), lift u) ∈ U := by
    intro u
    have h0 := hlV u
    rwa [Submodule.mem_comap, LinearMap.inr_apply] at h0
  have hA : ∀ s w, (s, w) ∈ U → (J.filter (fun j => z (x0.1 + s) j = t j)).card ≤ e := by
    intro s w hsw
    apply ht (z (x0.1 + s)) (fun i => z (x0.1 + s) i * (x0.2 + w) i + P i (x0 + (s, w)) + d i) e
    intro u
    have hu : (s, w) + ((0 : Fin n → ZMod 2), lift u) ∈ U := U.add_mem hsw (hlU u)
    refine le_trans (Finset.card_le_card ?_) (herr _ hu)
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    obtain ⟨hjJ, hne⟩ := hj
    have e1 : (x0 + ((s, w) + ((0 : Fin n → ZMod 2), lift u))).1 = x0.1 + s := by simp
    have e2 : (x0 + ((s, w) + ((0 : Fin n → ZMod 2), lift u))).2 j = (x0.2 + w) j + u j := by
      simp [hlJ u j hjJ, add_assoc]
    have e3 : P j (x0 + ((s, w) + ((0 : Fin n → ZMod 2), lift u))) =
        P j (x0 + (s, w)) + P j ((0 : Fin n → ZMod 2), lift u) := by
      rw [← add_assoc, map_add]
    have e4 : (G.comp lift) u j = P j ((0 : Fin n → ZMod 2), lift u) := by
      simp [G]
    rw [e1, e2, e3]
    rw [e4] at hne
    have key : ∀ a b c d f g : ZMod 2, a * b + c + d + f + a * g ≠ 0 → a * (b + g) ≠ c + f + d := by
      decide
    exact key _ _ _ _ _ _ hne
  let Ψ : ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    LinearMap.pi (fun i => if i ∈ J then
      (LinearMap.proj i).comp (LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))
      else (LinearMap.proj i).comp (z.comp (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))))
  have hΨ : ∀ x : (Fin n → ZMod 2) × (Fin m → ZMod 2), ∀ i,
      Ψ x i = if i ∈ J then x.2 i else z x.1 i := by
    intro x i
    simp only [Ψ, LinearMap.pi_apply]
    by_cases hi : i ∈ J
    · rw [if_pos hi, if_pos hi]
      rfl
    · rw [if_neg hi, if_neg hi]
      rfl
  let f : U →ₗ[ZMod 2] (Fin m → ZMod 2) := Ψ.comp U.subtype
  let g : LinearMap.ker f →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)).comp
      (U.subtype.comp (LinearMap.ker f).subtype)
  have hg : Function.Injective g := by
    intro k1 k2 h12
    obtain ⟨⟨x, hxU⟩, hxK⟩ := k1
    obtain ⟨⟨x', hxU'⟩, hxK'⟩ := k2
    have h1 : x.1 = x'.1 := h12
    have h2 : Ψ x = 0 := LinearMap.mem_ker.mp hxK
    have h2' : Ψ x' = 0 := LinearMap.mem_ker.mp hxK'
    have hmem : x.2 - x'.2 ∈
        U.comap (LinearMap.inr (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)) := by
      rw [Submodule.mem_comap, LinearMap.inr_apply]
      have hx : ((0 : Fin n → ZMod 2), x.2 - x'.2) = x - x' := by
        refine Prod.ext ?_ rfl
        show (0 : Fin n → ZMod 2) = x.1 - x'.1
        rw [h1, sub_self]
      rw [hx]
      exact U.sub_mem hxU hxU'
    have h3 : x.2 = x'.2 := by
      funext i
      have h6 := hV0 (x.2 - x'.2) hmem (fun j hj => by
        have h4 := congrFun h2 j
        have h5 := congrFun h2' j
        rw [hΨ, if_pos hj] at h4
        rw [hΨ, if_pos hj] at h5
        show x.2 j - x'.2 j = 0
        rw [h4, h5, sub_self]) i (Finset.mem_univ i)
      have h7 : x.2 i - x'.2 i = 0 := h6
      exact sub_eq_zero.mp h7
    have hxx : x = x' := Prod.ext h1 h3
    subst hxx
    rfl
  have hrank : Module.finrank (ZMod 2) U ≤ m + Module.finrank (ZMod 2) (LinearMap.range g) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : Module.finrank (ZMod 2) (LinearMap.range f) ≤ m := by
      have h5 := Submodule.finrank_le (LinearMap.range f)
      rwa [Module.finrank_fin_fun] at h5
    have h3 : Module.finrank (ZMod 2) (LinearMap.range g) =
        Module.finrank (ZMod 2) (LinearMap.ker f) := LinearMap.finrank_range_of_inj hg
    omega
  refine ⟨LinearMap.range g, fun i => if i ∈ J then t i + z x0.1 i else 1, ?_, ?_⟩
  · have h1 : 2 ^ (n + m) ≤ L * 2 ^ (m + Module.finrank (ZMod 2) (LinearMap.range g)) :=
      le_trans hsize (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hrank))
    by_cases ha : Module.finrank (ZMod 2) (LinearMap.range g) ≤ n
    · have h3 : 2 ^ (n + m) = 2 ^ (n - Module.finrank (ZMod 2) (LinearMap.range g)) *
          2 ^ (m + Module.finrank (ZMod 2) (LinearMap.range g)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h3] at h1
      exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos _)
    · rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
      exact hL
  · intro s hs
    rw [LinearMap.mem_range] at hs
    obtain ⟨⟨⟨x, hxU⟩, hxK⟩, rfl⟩ := hs
    have h2 : Ψ x = 0 := LinearMap.mem_ker.mp hxK
    refine le_trans (Finset.card_le_card ?_) (hA x.1 x.2 hxU)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hi' : z x.1 i = if i ∈ J then t i + z x0.1 i else 1 := hi
    have hΨi := congrFun h2 i
    rw [hΨ] at hΨi
    by_cases hiJ : i ∈ J
    · refine ⟨hiJ, ?_⟩
      rw [if_pos hiJ] at hi'
      rw [map_add, Pi.add_apply]
      have key : ∀ a b c : ZMod 2, a = c + b → b + a = c := by decide
      exact key _ _ _ hi'
    · exfalso
      rw [if_neg hiJ] at hi' hΨi
      rw [hi'] at hΨi
      simp at hΨi

-- The hard direction: adaptive implies cert.

theorem adaptive_cert (n m e L : Nat)
    (z : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (T : Finset (List Bool))
    (ask : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (bias : List Bool → ZMod 2)
    (P : List Bool → Fin m → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (d : List Bool → Fin m → ZMod 2)
    (hT : T.card < L)
    (hok : ∀ x : (Fin n → ZMod 2) × (Fin m → ZMod 2),
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠
        P ((List.range T.card).foldl (fun (p : List Bool) _ =>
          if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []) i x +
        d ((List.range T.card).foldl (fun (p : List Bool) _ =>
          if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []) i)).card ≤ e) :
    ∃ (B : Submodule (ZMod 2) (Fin n → ZMod 2)) (center : Fin m → ZMod 2),
      2 ^ (n - Module.finrank (ZMod 2) B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e := by
  obtain ⟨x0, U, hU, hsize⟩ := adv_tree_part T ask bias
  refine adv_lin_part z (P (adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card))
    (d (adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card)) x0 U ?_ (by omega)
    (le_trans hsize (Nat.mul_le_mul_right _ (by omega)))
  intro u hu
  have h1 := hok (x0 + u)
  have h2 : (List.range T.card).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [decide (ask p (x0 + u) + bias p ≠ 0)] else p) [] =
      adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card := hU u hu
  rw [h2] at h1
  exact h1

-- The same direction, stated with the full let block of the posted statement
-- (the form of the hypothesis hAC of C_glue).

theorem adaptive_imp_cert : ∀ (n m e L : Nat),
  let F := ZMod 2
  let S := Fin n → F
  let W := Fin m → F
  let X := S × W
  ∀ z : S →ₗ[F] W,
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let ok := fun (x : X) (P : Fin m → D) (d : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠ P i x + d i)).card ≤ e
    let adaptive := ∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → Fin m → D) (d : H → W),
      T.card < L ∧ ∀ x : X, ok x (P (run T ask bias x)) (d (run T ask bias x))
    let fixed := ∃ (h : Nat) (ask : Fin h → S →ₗ[F] F) (P : (Fin h → F) → Fin m → D) (d : (Fin h → F) → W),
      2^h ≤ L ∧ ∀ x : X, ok x (P (fun j => ask j x.1)) (d (fun j => ask j x.1))
    let cert := ∃ (B : Submodule F S) (center : W), 2^(n-Module.finrank F B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e
    adaptive → cert := by
  intro n m e L F S W X z H D run ok adaptive fixed cert hA
  obtain ⟨T, ask, bias, P, d, hT, hok⟩ := hA
  exact adaptive_cert n m e L z T ask bias P d hT hok


-- Prover C: the constructions cert to fixed and fixed to adaptive, and the glue.

-- Part 1: cert to fixed. The questions are the coordinates of the quotient map
-- onto S / B in a basis; on each coset predict with the mask of the translated center.

noncomputable def C_q {n : ℕ} (B : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ B)) → ZMod 2) :=
  (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ B)).equivFun.toLinearMap.comp B.mkQ

theorem C_q_sub {n : ℕ} (B : Submodule (ZMod 2) (Fin n → ZMod 2)) (s t : Fin n → ZMod 2)
    (hst : C_q B s = C_q B t) : s - t ∈ B := by
  have h0 : (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ B)).equivFun (B.mkQ s) =
      (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ B)).equivFun (B.mkQ t) := hst
  have h1 : (Submodule.Quotient.mk s : (Fin n → ZMod 2) ⧸ B) = Submodule.Quotient.mk t :=
    (Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ B)).equivFun.injective h0
  exact (Submodule.Quotient.eq B).mp h1

noncomputable def C_pred {n m : ℕ} (z : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (center : Fin m → ZMod 2) (r : Fin n → ZMod 2) (i : Fin m) :
    ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2 :=
  (center i + z r i + 1) •
    (LinearMap.proj i).comp (LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))

theorem C_bit : ∀ a r c v : ZMod 2, a * v ≠ (c + r + 1) * v + 0 → a - r = c := by
  decide

theorem C_coset_bound {n m e : ℕ} (z : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (B : Submodule (ZMod 2) (Fin n → ZMod 2)) (center : Fin m → ZMod 2)
    (hB : ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e)
    (r : Fin n → ZMod 2) (x : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (hr : x.1 - r ∈ B) :
    ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠
      C_pred z center r i x + (0 : Fin m → ZMod 2) i)).card ≤ e := by
  refine le_trans (Finset.card_le_card ?_) (hB _ hr)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ i, ?_⟩
  have h2 : z x.1 i * x.2 i ≠ (center i + z r i + 1) * x.2 i + 0 := hi.2
  rw [map_sub, Pi.sub_apply]
  exact C_bit _ _ _ _ h2

theorem C_cert_fixed_core (n m e L : ℕ) (z : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (B : Submodule (ZMod 2) (Fin n → ZMod 2)) (center : Fin m → ZMod 2)
    (hL : 2 ^ (n - Module.finrank (ZMod 2) B) ≤ L)
    (hB : ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e) :
    ∃ (h : ℕ) (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (P : (Fin h → ZMod 2) → Fin m → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (d : (Fin h → ZMod 2) → Fin m → ZMod 2),
      2 ^ h ≤ L ∧ ∀ x : (Fin n → ZMod 2) × (Fin m → ZMod 2),
        ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠
          P (fun j => ask j x.1) i x + d (fun j => ask j x.1) i)).card ≤ e := by
  refine ⟨Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ B), fun j => (LinearMap.proj j).comp (C_q B),
    fun a i => C_pred z center (Function.invFun (C_q B) a) i, fun _ => 0, ?_, ?_⟩
  · have h1 := Submodule.finrank_quotient_add_finrank B
    rw [Module.finrank_fin_fun] at h1
    exact (congrArg (fun t => 2 ^ t) (Nat.eq_sub_of_add_eq h1)).trans_le hL
  · intro x
    have hr : C_q B x.1 = C_q B (Function.invFun (C_q B) (C_q B x.1)) :=
      (Function.invFun_eq ⟨x.1, rfl⟩).symm
    exact C_coset_bound z B center hB (Function.invFun (C_q B) (C_q B x.1)) x (C_q_sub B _ _ hr)

-- Part 2: fixed to adaptive. The tree holds every history of length below h, so it has
-- 2^h - 1 nodes; at a history of length k it asks question k.

noncomputable def C_tree : ℕ → Finset (List Bool)
  | 0 => ∅
  | k + 1 => insert [] ((C_tree k).image (List.cons true) ∪ (C_tree k).image (List.cons false))

theorem C_tree_zero : C_tree 0 = ∅ := rfl

theorem C_tree_succ (k : ℕ) : C_tree (k + 1) =
    insert [] ((C_tree k).image (List.cons true) ∪ (C_tree k).image (List.cons false)) := rfl

theorem C_tree_mem (k : ℕ) : ∀ p : List Bool, p ∈ C_tree k ↔ p.length < k := by
  induction k with
  | zero =>
    intro p
    rw [C_tree_zero]
    exact ⟨fun hp => absurd hp (Finset.notMem_empty p), fun hp => absurd hp (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro p
    rw [C_tree_succ, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (hp | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · rw [hp]
        exact Nat.succ_pos k
      · exact Nat.succ_lt_succ ((ih a).mp ha)
      · exact Nat.succ_lt_succ ((ih a).mp ha)
    · intro hp
      cases p with
      | nil => exact Or.inl rfl
      | cons b q =>
        have hq : q ∈ C_tree k := (ih q).mpr (Nat.lt_of_succ_lt_succ hp)
        cases b with
        | true => exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
        | false => exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

theorem C_tree_card (k : ℕ) : (C_tree k).card + 1 = 2 ^ k := by
  induction k with
  | zero => simp [C_tree_zero]
  | succ k ih =>
    have hA : ((C_tree k).image (List.cons true)).card = (C_tree k).card :=
      Finset.card_image_of_injective _ List.cons_injective
    have hB : ((C_tree k).image (List.cons false)).card = (C_tree k).card :=
      Finset.card_image_of_injective _ List.cons_injective
    have hdisj : Disjoint ((C_tree k).image (List.cons true)) ((C_tree k).image (List.cons false)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_image] at hp1 hp2
      obtain ⟨a, _, rfl⟩ := hp1
      obtain ⟨b, _, hb⟩ := hp2
      exact absurd (List.cons.inj hb).1 (by decide)
    have hnil : ([] : List Bool) ∉
        (C_tree k).image (List.cons true) ∪ (C_tree k).image (List.cons false) := by
      intro hm
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hm
      rcases hm with ⟨a, _, ha⟩ | ⟨a, _, ha⟩
      · exact List.cons_ne_nil _ _ ha
      · exact List.cons_ne_nil _ _ ha
    rw [C_tree_succ, Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdisj, hA, hB,
      pow_succ]
    omega

noncomputable def C_hist {n h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (s : Fin n → ZMod 2) (k : ℕ) : List Bool :=
  (List.range k).map (fun j => if hj : j < h then decide (ask ⟨j, hj⟩ s ≠ 0) else false)

theorem C_hist_length {n h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (s : Fin n → ZMod 2) (k : ℕ) : (C_hist ask s k).length = k := by
  rw [C_hist, List.length_map, List.length_range]

theorem C_hist_succ {n h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (s : Fin n → ZMod 2) (k : ℕ) (hk : k < h) :
    C_hist ask s (k + 1) = C_hist ask s k ++ [decide (ask ⟨k, hk⟩ s ≠ 0)] := by
  rw [C_hist, C_hist, List.range_succ, List.map_append]
  show _ ++ [if hj : k < h then decide (ask ⟨k, hj⟩ s ≠ 0) else false] = _
  rw [dite_eq_left hk]

noncomputable def C_ask {n m h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (p : List Bool) : ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2 :=
  if hp : p.length < h then
    (ask ⟨p.length, hp⟩).comp (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))
  else 0

theorem C_ask_hist {n m h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (k : ℕ) (hk : k < h) :
    C_ask (m := m) ask (C_hist ask x.1 k) x = ask ⟨k, hk⟩ x.1 := by
  have hl : (C_hist ask x.1 k).length < h := by
    rw [C_hist_length]
    exact hk
  have hf : (⟨(C_hist ask x.1 k).length, hl⟩ : Fin h) = ⟨k, hk⟩ :=
    Fin.ext (C_hist_length ask x.1 k)
  rw [C_ask, dite_eq_left hl, hf, LinearMap.comp_apply, LinearMap.fst_apply]

noncomputable def C_step {n m h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (bias : List Bool → ZMod 2) (p : List Bool) :
    List Bool :=
  if p ∈ C_tree h then p ++ [decide (C_ask (m := m) ask p x + bias p ≠ 0)] else p

theorem C_foldl_iter {α β : Type} (g : α → α) (l : List β) (a : α) :
    l.foldl (fun p _ => g p) a = Nat.iterate g l.length a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih (g a)

theorem C_iter {α : Type} (g : α → α) (f : ℕ → α) (h : ℕ)
    (hs : ∀ k, k < h → g (f k) = f (k + 1)) (hh : g (f h) = f h) :
    ∀ k, Nat.iterate g k (f 0) = f (min k h) := by
  intro k
  induction k with
  | zero =>
    show f 0 = f (min 0 h)
    rw [Nat.zero_min]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases Nat.lt_or_ge k h with hk | hk
    · have e1 : min k h = k := Nat.min_eq_left (Nat.le_of_lt hk)
      have e2 : min (k + 1) h = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
      rw [e1, e2]
      exact hs k hk
    · have e1 : min k h = h := Nat.min_eq_right hk
      have e2 : min (k + 1) h = h := Nat.min_eq_right (Nat.le_succ_of_le hk)
      rw [e1, e2]
      exact hh

theorem C_run {n m h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (bias : List Bool → ZMod 2)
    (hb : ∀ p, bias p = 0) :
    (List.range (C_tree h).card).foldl (fun (p : List Bool) (_ : ℕ) =>
      if p ∈ C_tree h then p ++ [decide (C_ask (m := m) ask p x + bias p ≠ 0)] else p) [] =
      C_hist ask x.1 h := by
  have hs : ∀ k, k < h → C_step ask x bias (C_hist ask x.1 k) = C_hist ask x.1 (k + 1) := by
    intro k hk
    have hmem : C_hist ask x.1 k ∈ C_tree h := by
      rw [C_tree_mem, C_hist_length]
      exact hk
    rw [C_step, ite_eq_left hmem, C_ask_hist ask x k hk, hb, add_zero, C_hist_succ ask x.1 k hk]
  have hh : C_step ask x bias (C_hist ask x.1 h) = C_hist ask x.1 h := by
    have hmem : C_hist ask x.1 h ∉ C_tree h := by
      rw [C_tree_mem, C_hist_length]
      exact Nat.lt_irrefl h
    rw [C_step, ite_eq_right hmem]
  have hN : h ≤ (C_tree h).card := by
    have h1 := C_tree_card h
    have h2 : h < 2 ^ h := Nat.lt_two_pow_self
    omega
  have hit := C_iter (C_step ask x bias) (C_hist ask x.1) h hs hh (C_tree h).card
  rw [Nat.min_eq_right hN] at hit
  exact (C_foldl_iter (C_step ask x bias) (List.range (C_tree h).card) []).trans
    ((congrArg (fun t => Nat.iterate (C_step ask x bias) t [])
      (List.length_range (n := (C_tree h).card))).trans hit)

noncomputable def C_dec (h : ℕ) (p : List Bool) : Fin h → ZMod 2 :=
  fun j => if p[j.val]? = some true then 1 else 0

theorem C_bit2 : ∀ a : ZMod 2, (if some (decide (a ≠ 0)) = some true then (1 : ZMod 2) else 0) = a := by
  decide

theorem C_dec_hist {n h : ℕ} (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (s : Fin n → ZMod 2) : C_dec h (C_hist ask s h) = fun j => ask j s := by
  funext j
  have e1 : (C_hist ask s h)[j.val]? = some (decide (ask j s ≠ 0)) := by
    rw [C_hist, List.getElem?_map, List.getElem?_range j.isLt]
    show some (if hj : j.val < h then decide (ask ⟨j.val, hj⟩ s ≠ 0) else false) =
      some (decide (ask j s ≠ 0))
    rw [dite_eq_left j.isLt]
  show (if (C_hist ask s h)[j.val]? = some true then (1 : ZMod 2) else 0) = ask j s
  rw [e1]
  exact C_bit2 (ask j s)

theorem C_fixed_adaptive_core (n m e L h : ℕ) (z : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (ask : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (P : (Fin h → ZMod 2) → Fin m → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (d : (Fin h → ZMod 2) → Fin m → ZMod 2) (hL : 2 ^ h ≤ L)
    (hok : ∀ x : (Fin n → ZMod 2) × (Fin m → ZMod 2),
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠
        P (fun j => ask j x.1) i x + d (fun j => ask j x.1) i)).card ≤ e) :
    ∃ (T : Finset (List Bool))
      (ask' : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2)
      (P' : List Bool → Fin m → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (d' : List Bool → Fin m → ZMod 2),
      T.card < L ∧ ∀ x : (Fin n → ZMod 2) × (Fin m → ZMod 2),
        ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠
          P' ((List.range T.card).foldl (fun (p : List Bool) (_ : ℕ) =>
            if p ∈ T then p ++ [decide (ask' p x + bias p ≠ 0)] else p) []) i x +
          d' ((List.range T.card).foldl (fun (p : List Bool) (_ : ℕ) =>
            if p ∈ T then p ++ [decide (ask' p x + bias p ≠ 0)] else p) []) i)).card ≤ e := by
  refine ⟨C_tree h, C_ask ask, fun _ => 0, fun p => P (C_dec h p), fun p => d (C_dec h p), ?_, ?_⟩
  · have h1 := C_tree_card h
    omega
  · intro x
    have key := (congrArg (C_dec h) (C_run ask x (fun _ => 0) (fun _ => rfl))).trans
      (C_dec_hist ask x.1)
    exact (congrArg (fun a => ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠
      P a i x + d a i)).card ≤ e) key).mpr (hok x)

-- Part 3: the two constructions in the form of the statement, and the glue.

theorem C_cert_fixed : ∀ (n m e L : Nat),
  let F := ZMod 2
  let S := Fin n → F
  let W := Fin m → F
  let X := S × W
  ∀ z : S →ₗ[F] W,
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let ok := fun (x : X) (P : Fin m → D) (d : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠ P i x + d i)).card ≤ e
    let adaptive := ∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → Fin m → D) (d : H → W),
      T.card < L ∧ ∀ x : X, ok x (P (run T ask bias x)) (d (run T ask bias x))
    let fixed := ∃ (h : Nat) (ask : Fin h → S →ₗ[F] F) (P : (Fin h → F) → Fin m → D) (d : (Fin h → F) → W),
      2^h ≤ L ∧ ∀ x : X, ok x (P (fun j => ask j x.1)) (d (fun j => ask j x.1))
    let cert := ∃ (B : Submodule F S) (center : W), 2^(n-Module.finrank F B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e
    cert → fixed := by
  intro n m e L F S W X z H D run ok adaptive fixed cert hc
  obtain ⟨B, center, hL, hB⟩ := hc
  exact C_cert_fixed_core n m e L z B center hL hB

theorem C_fixed_adaptive : ∀ (n m e L : Nat),
  let F := ZMod 2
  let S := Fin n → F
  let W := Fin m → F
  let X := S × W
  ∀ z : S →ₗ[F] W,
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let ok := fun (x : X) (P : Fin m → D) (d : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠ P i x + d i)).card ≤ e
    let adaptive := ∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → Fin m → D) (d : H → W),
      T.card < L ∧ ∀ x : X, ok x (P (run T ask bias x)) (d (run T ask bias x))
    let fixed := ∃ (h : Nat) (ask : Fin h → S →ₗ[F] F) (P : (Fin h → F) → Fin m → D) (d : (Fin h → F) → W),
      2^h ≤ L ∧ ∀ x : X, ok x (P (fun j => ask j x.1)) (d (fun j => ask j x.1))
    let cert := ∃ (B : Submodule F S) (center : W), 2^(n-Module.finrank F B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e
    fixed → adaptive := by
  intro n m e L F S W X z H D run ok adaptive fixed cert hf
  obtain ⟨h, ask, P, d, hL, hok⟩ := hf
  exact C_fixed_adaptive_core n m e L h z ask P d hL hok

theorem C_glue (hAC : ∀ (n m e L : Nat),
  let F := ZMod 2
  let S := Fin n → F
  let W := Fin m → F
  let X := S × W
  ∀ z : S →ₗ[F] W,
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let ok := fun (x : X) (P : Fin m → D) (d : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠ P i x + d i)).card ≤ e
    let adaptive := ∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → Fin m → D) (d : H → W),
      T.card < L ∧ ∀ x : X, ok x (P (run T ask bias x)) (d (run T ask bias x))
    let fixed := ∃ (h : Nat) (ask : Fin h → S →ₗ[F] F) (P : (Fin h → F) → Fin m → D) (d : (Fin h → F) → W),
      2^h ≤ L ∧ ∀ x : X, ok x (P (fun j => ask j x.1)) (d (fun j => ask j x.1))
    let cert := ∃ (B : Submodule F S) (center : W), 2^(n-Module.finrank F B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e
    adaptive → cert) : ∀ (n m e L : Nat),
  let F := ZMod 2
  let S := Fin n → F
  let W := Fin m → F
  let X := S × W
  ∀ z : S →ₗ[F] W,
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let ok := fun (x : X) (P : Fin m → D) (d : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠ P i x + d i)).card ≤ e
    let adaptive := ∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → Fin m → D) (d : H → W),
      T.card < L ∧ ∀ x : X, ok x (P (run T ask bias x)) (d (run T ask bias x))
    let fixed := ∃ (h : Nat) (ask : Fin h → S →ₗ[F] F) (P : (Fin h → F) → Fin m → D) (d : (Fin h → F) → W),
      2^h ≤ L ∧ ∀ x : X, ok x (P (fun j => ask j x.1)) (d (fun j => ask j x.1))
    let cert := ∃ (B : Submodule F S) (center : W), 2^(n-Module.finrank F B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e
    (adaptive ↔ cert) ∧ (fixed ↔ cert) := by
  intro n m e L F S W X z H D run ok adaptive fixed cert
  have h1 : adaptive → cert := hAC n m e L z
  have h2 : cert → fixed := C_cert_fixed n m e L z
  have h3 : fixed → adaptive := C_fixed_adaptive n m e L z
  exact ⟨⟨h1, fun c => h3 (h2 c)⟩, ⟨fun f => h1 (h3 f), h2⟩⟩

end PEqualNP.Outside.L_lib_992_aux

theorem PEqualNP.Outside.L_lib_992 : ∀ (n m e L : Nat),
  let F := ZMod 2
  let S := Fin n → F
  let W := Fin m → F
  let X := S × W
  ∀ z : S →ₗ[F] W,
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let ok := fun (x : X) (P : Fin m → D) (d : W) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => z x.1 i * x.2 i ≠ P i x + d i)).card ≤ e
    let adaptive := ∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → Fin m → D) (d : H → W),
      T.card < L ∧ ∀ x : X, ok x (P (run T ask bias x)) (d (run T ask bias x))
    let fixed := ∃ (h : Nat) (ask : Fin h → S →ₗ[F] F) (P : (Fin h → F) → Fin m → D) (d : (Fin h → F) → W),
      2^h ≤ L ∧ ∀ x : X, ok x (P (fun j => ask j x.1)) (d (fun j => ask j x.1))
    let cert := ∃ (B : Submodule F S) (center : W), 2^(n-Module.finrank F B) ≤ L ∧
      ∀ s ∈ B, ((Finset.univ : Finset (Fin m)).filter (fun i => z s i = center i)).card ≤ e
    (adaptive ↔ cert) ∧ (fixed ↔ cert) :=
  PEqualNP.Outside.L_lib_992_aux.C_glue PEqualNP.Outside.L_lib_992_aux.adaptive_imp_cert

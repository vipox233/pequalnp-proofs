import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_343_aux

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Cons {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ (j : Fin p.length), q (List.take (↑j) p) x = p.get j

def AffQ (n k : ℕ) (f : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Bool) : Prop :=
  ∃ (l : ((Fin n → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
    f = fun x => decide (l x = b)

def Ok {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (x : (Fin n → ZMod 2) × (Fin k → ZMod 2)) (a : Fin m × (Fin t → ZMod 2)) : Prop :=
  (row a.1) x.1 ≠ rhs a.1 ∧ a.2 = (M a.1) x.2

def Tree {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (N J : Finset (List Bool)) (q : List Bool → (Fin n → ZMod 2) × (Fin k → ZMod 2) → Bool)
    (out : List Bool → Fin m × (Fin t → ZMod 2)) : Prop :=
  Shape N J ∧ (∀ p ∈ J, AffQ n k (q p)) ∧
    ∀ p ∈ N \ J, ∀ (x : (Fin n → ZMod 2) × (Fin k → ZMod 2)), Cons q p x → Ok row rhs M x (out p)

noncomputable def wt {k t m : ℕ} (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) (i : Fin m) : ℕ :=
  2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range (M i))

lemma fw_cons_iff {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) :
    Cons q p x ↔ ∀ (j : ℕ) (h : j < p.length), q (p.take j) x = p[j] := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

lemma fw_cons_ext {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V)
    (h : Cons q p x) : Cons q (p ++ [q p x]) x := by
  rw [fw_cons_iff] at h ⊢
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h1 | h1
  · rw [List.take_append_of_le_length h1.le, List.getElem_append_left h1]
    exact h j h1
  · subst h1
    simp

lemma fw_reach_aux {V : Type} (N J : Finset (List Bool)) (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) (d : ℕ) :
    ∃ p ∈ N, Cons q p x ∧ (p ∉ J ∨ d ≤ p.length) := by
  induction d with
  | zero => exact ⟨[], hS.1, fun j => j.elim0, Or.inr (Nat.zero_le _)⟩
  | succ d ih =>
    obtain ⟨p, hp, hc, h⟩ := ih
    by_cases hJ : p ∈ J
    · refine ⟨p ++ [q p x], ?_, fw_cons_ext q p x hc, Or.inr ?_⟩
      · have h2 := hS.2.2.2 p hJ
        cases q p x
        · exact h2.1
        · exact h2.2
      · have h3 : d ≤ p.length := h.resolve_left (not_not.mpr hJ)
        rw [List.length_append, List.length_singleton]
        omega
    · exact ⟨p, hp, hc, Or.inl hJ⟩

lemma fw_reach {V : Type} (N J : Finset (List Bool)) (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) : ∃ p ∈ N \ J, Cons q p x := by
  obtain ⟨p, hp, hc, h⟩ := fw_reach_aux N J hS q x (N.sup List.length + 1)
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hp, ?_⟩, hc⟩
  rcases h with h | h
  · exact h
  · have h1 := Finset.le_sup (f := List.length) hp
    omega

lemma fw_internal (N J : Finset (List Bool)) (hS : Shape N J) (p s : List Bool)
    (hs : s ≠ []) (h : p ++ s ∈ N) : p ∈ J := by
  induction s using List.reverseRecOn with
  | nil => exact absurd rfl hs
  | append_singleton s b ih =>
    rw [← List.append_assoc] at h
    have h1 := hS.2.2.1 _ b h
    by_cases hs1 : s = []
    · subst hs1
      simpa using h1
    · exact ih hs1 (hS.2.1 h1)

lemma fw_prefix (p r : List Bool) (H : ℕ) (hr : r.length ≤ H) (hle : p.length ≤ r.length)
    (h : (fun j : Fin H => p.getD j.val false) = fun j : Fin H => r.getD j.val false) :
    p = r.take p.length := by
  apply List.ext_getElem
  · simp [hle]
  · intro i h1 h2
    have h3 := congrFun h ⟨i, by omega⟩
    simp only at h3
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ (by omega)] at h3
    rw [List.getElem_take]
    exact h3

lemma fw_leaf_inj (N J : Finset (List Bool)) (hS : Shape N J) (H : ℕ) (p r : List Bool)
    (hp : p ∈ N \ J) (hr : r ∈ N \ J) (hrH : r.length ≤ H) (hle : p.length ≤ r.length)
    (h : (fun j : Fin H => p.getD j.val false) = fun j : Fin H => r.getD j.val false) :
    p = r := by
  have h1 := fw_prefix p r H hrH hle h
  have h2 : r.take p.length ++ r.drop p.length = r := List.take_append_drop _ _
  rw [← h1] at h2
  by_cases hd : r.drop p.length = []
  · rw [hd, List.append_nil] at h2
    exact h2
  · have h3 : p ++ r.drop p.length ∈ N := by
      rw [h2]
      exact (Finset.mem_sdiff.mp hr).1
    exact absurd (fw_internal N J hS p _ hd h3) (Finset.mem_sdiff.mp hp).2

lemma fw_leaves_card (N J : Finset (List Bool)) (hS : Shape N J) (H : ℕ)
    (hH : ∀ p ∈ N \ J, p.length ≤ H) : (N \ J).card ≤ 2 ^ H := by
  have h1 : (N \ J).card ≤ (Finset.univ : Finset (Fin H → Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun p j => p.getD j.val false)
    · intro p _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro p hp r hr h
      rcases le_total p.length r.length with hle | hle
      · exact fw_leaf_inj N J hS H p r hp hr (hH r hr) hle h
      · exact (fw_leaf_inj N J hS H r p hr hp (hH p hp) hle h.symm).symm
  simpa using h1

lemma fw_zmod2 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

lemma fw_add_eq_zero (a b : ZMod 2) (h : a + b = 0) : a = b := by
  revert a b
  decide

lemma fw_sum01 {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {m : ℕ} (I : Finset (Fin m))
    (c : Fin m → ZMod 2) (g : Fin m → E) :
    ∑ i, c i • (if i ∈ I then g i else 0) = ∑ i ∈ I.filter (fun i => c i = 1), g i := by
  have h1 : ∀ i, c i • (if i ∈ I then g i else 0) = if (i ∈ I ∧ c i = 1) then g i else 0 := by
    intro i
    rcases fw_zmod2 (c i) with h | h <;> by_cases hi : i ∈ I <;> simp [h, hi]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma fw_farkas {n m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (rhs : Fin m → ZMod 2) (I : Finset (Fin m))
    (hI : ¬ ∃ x : Fin n → ZMod 2, ∀ i ∈ I, row i x = rhs i) :
    ∃ S ⊆ I, S.sum row = 0 ∧ S.sum rhs = 1 := by
  have hker : ⨅ i, LinearMap.ker (if i ∈ I then (row i).coprod (rhs i • LinearMap.id) else 0) ≤
      LinearMap.ker (LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (ZMod 2)) := by
    intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [LinearMap.mem_ker, LinearMap.snd_apply]
    by_contra hs
    apply hI
    refine ⟨v.1, fun i hi => ?_⟩
    have h1 := hv i
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi), LinearMap.mem_ker] at h1
    have h2 : v.2 = 1 := (fw_zmod2 v.2).resolve_left hs
    simp only [LinearMap.coprod_apply, LinearMap.smul_apply, LinearMap.id_apply, h2,
      smul_eq_mul, mul_one] at h1
    exact fw_add_eq_zero _ _ h1
  have hspan := mem_span_of_iInf_ker_le_ker hker
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨c, hc⟩ := hspan
  rw [fw_sum01] at hc
  refine ⟨I.filter (fun i => c i = 1), Finset.filter_subset _ _, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    have h3 := congrArg (fun f => f (x, 0)) hc
    simpa [LinearMap.sum_apply] using h3
  · have h3 := congrArg (fun f => f (0, 1)) hc
    simpa [LinearMap.sum_apply] using h3

lemma fw_fibre {k t : ℕ} (M0 : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (y : Fin t → ZMod 2) :
    (Finset.univ.filter (fun u => M0 u = y)).card *
      2 ^ Module.finrank (ZMod 2) (LinearMap.range M0) ≤ Fintype.card (Fin k → ZMod 2) := by
  classical
  rcases Finset.eq_empty_or_nonempty (Finset.univ.filter (fun u => M0 u = y)) with he | ⟨u0, hu0⟩
  · rw [he]
    simp
  · have hu1 : M0 u0 = y := (Finset.mem_filter.mp hu0).2
    have h1 : (Finset.univ.filter (fun u => M0 u = y)).card ≤
        (Finset.univ.filter (fun u => u ∈ LinearMap.ker M0)).card := by
      apply Finset.card_le_card_of_injOn (fun u => u - u0)
      · intro u hu
        have h5 : M0 u = y := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
        simp [h5, hu1]
      · intro a _ b _ h
        exact sub_left_injective h
    have h2 : (Finset.univ.filter (fun u => u ∈ LinearMap.ker M0)).card =
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker M0) := by
      rw [← Fintype.card_subtype]
      have h6 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker M0)
      rw [ZMod.card] at h6
      convert h6
    have h3 : Fintype.card (Fin k → ZMod 2) = 2 ^ Module.finrank (ZMod 2) (Fin k → ZMod 2) := by
      have h6 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin k → ZMod 2)
      rwa [ZMod.card] at h6
    have h4 := LinearMap.finrank_range_add_finrank_ker M0
    rw [h3, ← h4, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (h1.trans h2.le)

lemma fw_dep {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (rhs : Fin m → ZMod 2) (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (out : List Bool → Fin m × (Fin t → ZMod 2)) (P : Finset (List Bool))
    (hP : ∀ x : Fin n → ZMod 2, ∃ p ∈ P, row (out p).1 x ≠ rhs (out p).1) :
    ∃ S : Finset (Fin m), (S.sum row = 0 ∧ S.sum rhs = 1) ∧
      ∑ i ∈ S, wt M i ≤ ∑ p ∈ P, wt M (out p).1 := by
  obtain ⟨S, hS, h1, h2⟩ := fw_farkas row rhs (P.image (fun p => (out p).1)) (by
    rintro ⟨x, hx⟩
    obtain ⟨p, hp, hne⟩ := hP x
    exact hne (hx _ (Finset.mem_image_of_mem _ hp)))
  refine ⟨S, ⟨h1, h2⟩, ?_⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))

lemma fw_avg {U : Type} [Fintype U] [Nonempty U] (Lv : Finset (List Bool))
    (R : List Bool → U → Prop) [∀ p u, Decidable (R p u)] (w : List Bool → ℕ)
    (h : ∀ p ∈ Lv, (Finset.univ.filter (fun u => R p u)).card * w p ≤ Fintype.card U) :
    ∃ u : U, ∑ p ∈ Lv.filter (fun p => R p u), w p ≤ Lv.card := by
  have key : ∑ u : U, ∑ p ∈ Lv.filter (fun p => R p u), w p ≤ ∑ _u : U, Lv.card := by
    calc ∑ u : U, ∑ p ∈ Lv.filter (fun p => R p u), w p
        = ∑ u : U, ∑ p ∈ Lv, if R p u then w p else 0 := by
          simp_rw [Finset.sum_filter]
      _ = ∑ p ∈ Lv, ∑ u : U, if R p u then w p else 0 := Finset.sum_comm
      _ = ∑ p ∈ Lv, (Finset.univ.filter (fun u => R p u)).card * w p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ Lv, Fintype.card U := Finset.sum_le_sum h
      _ = ∑ _u : U, Lv.card := by
          simp [mul_comm]
  obtain ⟨u, _, hu⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key
  exact ⟨u, hu⟩

theorem fwd {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) (H K : ℕ)
    (N J : Finset (List Bool)) (q : List Bool → (Fin n → ZMod 2) × (Fin k → ZMod 2) → Bool)
    (out : List Bool → Fin m × (Fin t → ZMod 2))
    (hT : Tree row rhs M N J q out) (hH : ∀ p ∈ N \ J, p.length ≤ H) (hK : (N \ J).card ≤ K) :
    ∃ S : Finset (Fin m), (S.sum row = 0 ∧ S.sum rhs = 1) ∧
      ∑ i ∈ S, wt M i ≤ K ∧ ∑ i ∈ S, wt M i ≤ 2 ^ H := by
  classical
  obtain ⟨hS, _, hOk⟩ := hT
  have hL := fw_leaves_card N J hS H hH
  obtain ⟨u, hu⟩ := fw_avg (U := Fin k → ZMod 2) (N \ J)
    (fun p u => ∃ x : Fin n → ZMod 2, Cons q p (x, u)) (fun p => wt M (out p).1) (by
      intro p hp
      refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_))
        (fw_fibre (M (out p).1) (out p).2)
      intro v hv
      obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hOk p hp (x, v) hx).2).symm⟩)
  obtain ⟨S, hdep, hw⟩ := fw_dep row rhs M out
    ((N \ J).filter (fun p => ∃ x : Fin n → ZMod 2, Cons q p (x, u))) (by
      intro x
      obtain ⟨p, hp, hc⟩ := fw_reach N J hS q (x, u)
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, x, hc⟩, (hOk p hp (x, u) hc).1⟩)
  exact ⟨S, hdep, (hw.trans hu).trans hK, (hw.trans hu).trans hL⟩

def bw_Has {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (Z : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Prop) (h c : ℕ) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → (Fin n → ZMod 2) × (Fin k → ZMod 2) → Bool)
    (out : List Bool → Fin m × (Fin t → ZMod 2)),
    Shape N J ∧ (∀ p ∈ J, AffQ n k (q p)) ∧
    (∀ p ∈ N \ J, ∀ x, Z x → Cons q p x → Ok row rhs M x (out p)) ∧
    (∀ p ∈ N \ J, p.length ≤ h) ∧ (N \ J).card ≤ c

theorem bw_mono {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (Z Z' : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Prop) (h h' c c' : ℕ)
    (hZ : ∀ x, Z' x → Z x) (hh : h ≤ h') (hc : c ≤ c') (H : bw_Has row rhs M Z h c) :
    bw_Has row rhs M Z' h' c' := by
  obtain ⟨N, J, q, out, s, a, k0, d, e⟩ := H
  exact ⟨N, J, q, out, s, a, fun p hp x hz => k0 p hp x (hZ x hz),
    fun p hp => (d p hp).trans hh, e.trans hc⟩

theorem bw_leaf {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (Z : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Prop) (a : Fin m × (Fin t → ZMod 2))
    (ha : ∀ x, Z x → Ok row rhs M x a) : bw_Has row rhs M Z 0 1 := by
  refine ⟨{[]}, ∅, fun _ _ => false, fun _ => a, ⟨by simp, by simp, ?_, by simp⟩, by simp, ?_, ?_, by simp⟩
  · intro p b hp
    simp at hp
  · intro p _ x hz _
    exact ha x hz
  · intro p hp
    simp at hp
    simp [hp]

def bw_nn (N0 N1 : Finset (List Bool)) : Finset (List Bool) :=
  insert [] (N0.image (List.cons false) ∪ N1.image (List.cons true))

theorem bw_nn_nil (N0 N1 : Finset (List Bool)) : [] ∈ bw_nn N0 N1 := by simp [bw_nn]

theorem bw_nn_false (N0 N1 : Finset (List Bool)) (r : List Bool) :
    (false :: r) ∈ bw_nn N0 N1 ↔ r ∈ N0 := by simp [bw_nn]

theorem bw_nn_true (N0 N1 : Finset (List Bool)) (r : List Bool) :
    (true :: r) ∈ bw_nn N0 N1 ↔ r ∈ N1 := by simp [bw_nn]

theorem bw_nn_shape (N0 J0 N1 J1 : Finset (List Bool)) (h0 : Shape N0 J0) (h1 : Shape N1 J1) :
    Shape (bw_nn N0 N1) (bw_nn J0 J1) := by
  refine ⟨bw_nn_nil _ _, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact bw_nn_nil _ _
    · cases c
      · rw [bw_nn_false] at hp ⊢
        exact h0.2.1 hp
      · rw [bw_nn_true] at hp ⊢
        exact h1.2.1 hp
  · intro p b hp
    rcases p with _ | ⟨c, r⟩
    · exact bw_nn_nil _ _
    · cases c
      · rw [List.cons_append, bw_nn_false] at hp
        rw [bw_nn_false]
        exact h0.2.2.1 r b hp
      · rw [List.cons_append, bw_nn_true] at hp
        rw [bw_nn_true]
        exact h1.2.2.1 r b hp
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact ⟨(bw_nn_false _ _ _).2 h0.1, (bw_nn_true _ _ _).2 h1.1⟩
    · cases c
      · rw [bw_nn_false] at hp
        rw [List.cons_append, List.cons_append, bw_nn_false, bw_nn_false]
        exact h0.2.2.2 r hp
      · rw [bw_nn_true] at hp
        rw [List.cons_append, List.cons_append, bw_nn_true, bw_nn_true]
        exact h1.2.2.2 r hp

theorem bw_nn_leaves (N0 J0 N1 J1 : Finset (List Bool)) :
    bw_nn N0 N1 \ bw_nn J0 J1 =
      (N0 \ J0).image (List.cons false) ∪ (N1 \ J1).image (List.cons true) := by
  ext p
  rcases p with _ | ⟨c, r⟩
  · simp [bw_nn]
  · cases c <;> simp [bw_nn]

def bw_nq {V : Type} (f : V → Bool) (q0 q1 : List Bool → V → Bool) : List Bool → V → Bool
  | [] => f
  | false :: r => q0 r
  | true :: r => q1 r

def bw_nout {O : Type} (o0 o1 : List Bool → O) : List Bool → O
  | [] => o0 []
  | false :: r => o0 r
  | true :: r => o1 r

theorem bw_cons {V : Type} (q : List Bool → V → Bool) (c : Bool) (p : List Bool) (x : V) :
    Cons q (c :: p) x ↔ q [] x = c ∧ Cons (fun r => q (c :: r)) p x := by
  unfold Cons
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0, by simp⟩, fun j => ?_⟩
    have := h ⟨j.1 + 1, by simp⟩
    simpa using this
  · rintro ⟨h0, h1⟩ ⟨j, hj⟩
    rcases j with _ | j
    · simpa using h0
    · have := h1 ⟨j, by simpa using hj⟩
      simpa using this

theorem bw_node {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (Z : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Prop)
    (l : ((Fin n → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (h c0 c1 : ℕ)
    (H0 : bw_Has row rhs M (fun x => Z x ∧ l x ≠ b) h c0)
    (H1 : bw_Has row rhs M (fun x => Z x ∧ l x = b) h c1) :
    bw_Has row rhs M Z (h + 1) (c0 + c1) := by
  obtain ⟨N0, J0, q0, o0, s0, a0, k0, d0, e0⟩ := H0
  obtain ⟨N1, J1, q1, o1, s1, a1, k1, d1, e1⟩ := H1
  refine ⟨bw_nn N0 N1, bw_nn J0 J1, bw_nq (fun x => decide (l x = b)) q0 q1, bw_nout o0 o1,
    bw_nn_shape _ _ _ _ s0 s1, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact ⟨l, b, rfl⟩
    · cases c
      · exact a0 r ((bw_nn_false _ _ _).1 hp)
      · exact a1 r ((bw_nn_true _ _ _).1 hp)
  · intro p hp x hz hc
    rw [bw_nn_leaves] at hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hf, hc'⟩ := (bw_cons _ _ _ _).1 hc
      exact k0 r hr x ⟨hz, by simpa [bw_nq] using hf⟩ hc'
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hf, hc'⟩ := (bw_cons _ _ _ _).1 hc
      exact k1 r hr x ⟨hz, by simpa [bw_nq] using hf⟩ hc'
  · intro p hp
    rw [bw_nn_leaves] at hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      simpa using d0 r hr
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      simpa using d1 r hr
  · rw [bw_nn_leaves]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le.trans e0) (Finset.card_image_le.trans e1))

theorem bw_z2_a : ∀ a b : ZMod 2, a ≠ b + 1 → a - b = 0 := by decide

theorem bw_z2_b : ∀ a b w : ZMod 2, a = b + 1 → w ≠ 0 → a - (b + w) = 0 := by decide

theorem bw_z2_c : ∀ a b : ZMod 2, a = b + 1 ↔ a + b = 1 := by decide

theorem bw_z2_d : ∀ u v : ZMod 2, u + v = 1 → v ≠ 1 → u = 1 := by decide

theorem bw_z2_e : ∀ a b : ZMod 2, a + b = 1 → a ≠ b := by decide

theorem bw_read_bot {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2)
    (Z : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Prop) (i : Fin m) (y0 : Fin t → ZMod 2) (d : ℕ)
    (hZ : ∀ x, Z x → row i x.1 ≠ rhs i ∧ M i x.2 - y0 = 0) : bw_Has row rhs M Z d (2 ^ d) :=
  bw_mono row rhs M Z Z 0 d 1 (2 ^ d) (fun _ hx => hx) (Nat.zero_le _) Nat.one_le_two_pow
    (bw_leaf row rhs M Z (i, y0)
      (fun x hx => ⟨(hZ x hx).1, (sub_eq_zero.1 (hZ x hx).2).symm⟩))

theorem bw_read {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) (i : Fin m) :
    ∀ (d : ℕ) (D : Submodule (ZMod 2) (Fin t → ZMod 2)) (y0 : Fin t → ZMod 2)
      (Z : (Fin n → ZMod 2) × (Fin k → ZMod 2) → Prop),
      Module.finrank (ZMod 2) D ≤ d →
      (∀ x, Z x → row i x.1 ≠ rhs i ∧ M i x.2 - y0 ∈ D) → bw_Has row rhs M Z d (2 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro D y0 Z hd hZ
    have hD : D = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)
    subst hD
    exact bw_read_bot row rhs M Z i y0 0 (fun x hx => ⟨(hZ x hx).1, by simpa using (hZ x hx).2⟩)
  | succ d ih =>
    intro D y0 Z hd hZ
    by_cases hD : D = ⊥
    · subst hD
      exact bw_read_bot row rhs M Z i y0 (d + 1)
        (fun x hx => ⟨(hZ x hx).1, by simpa using (hZ x hx).2⟩)
    · obtain ⟨v, hvD, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
      obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
        by_contra hcon
        exact hv0 (funext fun c => by_contra fun hc => hcon ⟨c, hc⟩)
      have hlt : Module.finrank (ZMod 2)
          ↥(D ⊓ LinearMap.ker (LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2)) <
          Module.finrank (ZMod 2) D := by
        apply Submodule.finrank_lt_finrank_of_lt
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hv : v ∈ D ⊓ LinearMap.ker (LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
          by
            rw [heq]
            exact hvD
        exact hc (by simpa using (Submodule.mem_inf.1 hv).2)
      have hle : Module.finrank (ZMod 2)
          ↥(D ⊓ LinearMap.ker (LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2)) ≤ d := by
        omega
      have e2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [e2]
      refine bw_node row rhs M Z
        ((LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2) ∘ₗ M i ∘ₗ
          LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2)) (y0 c + 1) d (2 ^ d) (2 ^ d)
        ?_ ?_
      · refine ih _ y0 _ hle ?_
        rintro x ⟨hz, hx⟩
        refine ⟨(hZ x hz).1, Submodule.mem_inf.2 ⟨(hZ x hz).2, ?_⟩⟩
        have hx' : M i x.2 c ≠ y0 c + 1 := hx
        simpa using bw_z2_a _ _ hx'
      · refine ih _ (y0 + v) _ hle ?_
        rintro x ⟨hz, hx⟩
        refine ⟨(hZ x hz).1, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
        · have e3 : M i x.2 - (y0 + v) = (M i x.2 - y0) - v := by abel
          rw [e3]
          exact D.sub_mem (hZ x hz).2 hvD
        · have hx' : M i x.2 c = y0 c + 1 := hx
          simpa using bw_z2_b _ _ _ hx' hc

theorem bw_q {m : ℕ} (e : Fin m → ℕ) (h : ℕ) :
    ∀ (c : ℕ) (G : Finset (Fin m)), G.card ≤ c → (∀ i ∈ G, e i ≤ h) →
      ∃ A ⊆ G, ∑ i ∈ A, 2 ^ e i = min (∑ i ∈ G, 2 ^ e i) (2 ^ h) := by
  intro c
  induction c with
  | zero =>
    intro G hG _
    have hG0 : G = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hG)
    subst hG0
    exact ⟨∅, le_rfl, by simp⟩
  | succ c ih =>
    intro G hG he
    rcases G.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, le_rfl, by simp⟩
    · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image G e hne
      have hsum : 2 ^ e i0 + ∑ i ∈ G.erase i0, 2 ^ e i = ∑ i ∈ G, 2 ^ e i :=
        Finset.add_sum_erase G (fun i => 2 ^ e i) hi0
      by_cases hR : 2 ^ h ≤ ∑ i ∈ G.erase i0, 2 ^ e i
      · obtain ⟨A, hA, hAs⟩ := ih (G.erase i0)
          (by rw [Finset.card_erase_of_mem hi0]; omega)
          (fun i hi => he i (Finset.mem_of_mem_erase hi))
        refine ⟨A, hA.trans (Finset.erase_subset _ _), ?_⟩
        rw [hAs, min_eq_right hR, min_eq_right (hR.trans (hsum ▸ Nat.le_add_left _ _))]
      · refine ⟨G, le_rfl, ?_⟩
        obtain ⟨a, ha⟩ : 2 ^ e i0 ∣ ∑ i ∈ G.erase i0, 2 ^ e i :=
          Finset.dvd_sum (fun i hi => Nat.pow_dvd_pow 2 (hmin i (Finset.mem_of_mem_erase hi)))
        obtain ⟨b, hb⟩ : 2 ^ e i0 ∣ 2 ^ h := Nat.pow_dvd_pow 2 (he i0 hi0)
        have hab : a < b :=
          lt_of_not_ge (fun hcon => hR (by rw [ha, hb]; exact Nat.mul_le_mul_left _ hcon))
        have hm : 2 ^ e i0 * (a + 1) ≤ 2 ^ e i0 * b := Nat.mul_le_mul_left _ hab
        rw [min_eq_left]
        rw [← hsum, ha, hb]
        linarith

theorem bw_split {m : ℕ} (e : Fin m → ℕ) (h : ℕ) (G : Finset (Fin m)) (hc : 2 ≤ G.card)
    (hs : ∑ i ∈ G, 2 ^ e i ≤ 2 ^ (h + 1)) :
    ∃ A ⊆ G, A.Nonempty ∧ (G \ A).Nonempty ∧ ∑ i ∈ A, 2 ^ e i ≤ 2 ^ h ∧
      ∑ i ∈ G \ A, 2 ^ e i ≤ 2 ^ h := by
  by_cases hT : ∑ i ∈ G, 2 ^ e i ≤ 2 ^ h
  · obtain ⟨a, ha⟩ : G.Nonempty := Finset.card_pos.1 (by omega)
    have hsub : {a} ⊆ G := Finset.singleton_subset_iff.2 ha
    refine ⟨{a}, hsub, Finset.singleton_nonempty a, ?_, ?_, ?_⟩
    · apply Finset.card_pos.1
      have hcc := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_singleton] at hcc
      omega
    · exact (Finset.sum_le_sum_of_subset hsub).trans hT
    · exact (Finset.sum_le_sum_of_subset Finset.sdiff_subset).trans hT
  · have hT := lt_of_not_ge hT
    have he : ∀ i ∈ G, e i ≤ h := by
      intro i hi
      have h1 : 2 ^ e i + ∑ j ∈ G.erase i, 2 ^ e j = ∑ j ∈ G, 2 ^ e j :=
        Finset.add_sum_erase G (fun j => 2 ^ e j) hi
      obtain ⟨j, hj⟩ : (G.erase i).Nonempty :=
        Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hi]; omega)
      have h2 : 2 ^ e j ≤ ∑ j ∈ G.erase i, 2 ^ e j :=
        Finset.single_le_sum (f := fun j => 2 ^ e j) (fun _ _ => Nat.zero_le _) hj
      have h3 : 0 < 2 ^ e j := Nat.two_pow_pos _
      have h4 : 2 ^ e i < 2 ^ (h + 1) := by omega
      have h5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h4
      omega
    obtain ⟨A, hA, hAs⟩ := bw_q e h G.card G le_rfl he
    rw [min_eq_right hT.le] at hAs
    have hsd := Finset.sum_sdiff (f := fun i => 2 ^ e i) hA
    have hp : 2 ^ (h + 1) = 2 ^ h + 2 ^ h := by ring
    have hpos : 0 < 2 ^ h := Nat.two_pow_pos _
    refine ⟨A, hA, ?_, ?_, hAs.le, by omega⟩
    · apply Finset.nonempty_of_sum_ne_zero (f := fun i => 2 ^ e i)
      omega
    · apply Finset.nonempty_of_sum_ne_zero (f := fun i => 2 ^ e i)
      omega

theorem bw_iso_single {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) (i : Fin m) (h : ℕ) (hw : wt M i ≤ 2 ^ h) :
    bw_Has row rhs M (fun x => ∑ j ∈ ({i} : Finset (Fin m)), (row j x.1 + rhs j) = 1) h
      (∑ j ∈ ({i} : Finset (Fin m)), wt M j) := by
  rw [Finset.sum_singleton]
  have hr : Module.finrank (ZMod 2) ↥(LinearMap.range (M i)) ≤ h :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hw
  refine bw_mono row rhs M _ _ _ h _ _ (fun _ hx => hx) hr le_rfl
    (bw_read row rhs M i _ (LinearMap.range (M i)) 0 _ le_rfl ?_)
  intro x hx
  rw [Finset.sum_singleton] at hx
  exact ⟨bw_z2_e _ _ hx, by simp⟩

theorem bw_iso {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) :
    ∀ (c : ℕ) (G : Finset (Fin m)) (h : ℕ), G.card ≤ c → G.Nonempty →
      ∑ i ∈ G, wt M i ≤ 2 ^ h →
      bw_Has row rhs M (fun x => ∑ i ∈ G, (row i x.1 + rhs i) = 1) h (∑ i ∈ G, wt M i) := by
  intro c
  induction c with
  | zero =>
    intro G h hc hne
    exact absurd (Finset.card_eq_zero.1 (Nat.le_zero.1 hc)) hne.ne_empty
  | succ c ih =>
    intro G h hc hne hs
    by_cases h1 : G.card ≤ 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (le_antisymm h1 (Finset.card_pos.2 hne))
      exact bw_iso_single row rhs M i h (by simpa using hs)
    · have hcs : G.card ≤ ∑ i ∈ G, wt M i := by
        have hh := Finset.card_nsmul_le_sum G (fun i => wt M i) 1 (fun i _ => Nat.one_le_two_pow)
        simpa using hh
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
        rcases h with _ | h'
        · simp at hs
          omega
        · exact ⟨h', rfl⟩
      obtain ⟨A, hA, hAn, hBn, hAs, hBs⟩ :=
        bw_split (fun i => Module.finrank (ZMod 2) ↥(LinearMap.range (M i))) h' G (by omega) hs
      have hcard : (G \ A).card + A.card = G.card := Finset.card_sdiff_add_card_eq_card hA
      have hAp := Finset.card_pos.2 hAn
      have hBp := Finset.card_pos.2 hBn
      have hsd : ∑ i ∈ G \ A, wt M i + ∑ i ∈ A, wt M i = ∑ i ∈ G, wt M i := Finset.sum_sdiff hA
      rw [← hsd]
      refine bw_node row rhs M _
        ((∑ i ∈ A, row i) ∘ₗ LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2))
        (∑ i ∈ A, rhs i + 1) h' _ _ ?_ ?_
      · refine bw_mono row rhs M _ _ h' h' _ _ ?_ le_rfl le_rfl
          (ih (G \ A) h' (by omega) hBn hBs)
        rintro x ⟨hz, hx⟩
        have hsd2 := Finset.sum_sdiff (f := fun i => row i x.1 + rhs i) hA
        have hAe : ∑ i ∈ A, (row i x.1 + rhs i) = (∑ i ∈ A, row i) x.1 + ∑ i ∈ A, rhs i := by
          rw [Finset.sum_add_distrib, LinearMap.sum_apply]
        apply bw_z2_d _ (∑ i ∈ A, (row i x.1 + rhs i))
        · rw [hsd2]
          exact hz
        · rw [hAe]
          intro hh
          exact hx ((bw_z2_c _ _).2 hh)
      · refine bw_mono row rhs M _ _ h' h' _ _ ?_ le_rfl le_rfl
          (ih A h' (by omega) hAn hAs)
        rintro x ⟨_, hx⟩
        have hAe : ∑ i ∈ A, (row i x.1 + rhs i) = (∑ i ∈ A, row i) x.1 + ∑ i ∈ A, rhs i := by
          rw [Finset.sum_add_distrib, LinearMap.sum_apply]
        show ∑ i ∈ A, (row i x.1 + rhs i) = 1
        rw [hAe]
        exact (bw_z2_c _ _).1 hx

theorem bwd {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) (H K : ℕ)
    (S : Finset (Fin m)) (h0 : S.sum row = 0) (h1 : S.sum rhs = 1)
    (hK : ∑ i ∈ S, wt M i ≤ K) (hH : ∑ i ∈ S, wt M i ≤ 2 ^ H) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → (Fin n → ZMod 2) × (Fin k → ZMod 2) → Bool)
      (out : List Bool → Fin m × (Fin t → ZMod 2)),
      Tree row rhs M N J q out ∧ (∀ p ∈ N \ J, p.length ≤ H) ∧ (N \ J).card ≤ K := by
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [Finset.sum_empty] at h1
      exact absurd h1 (by decide)
    · exact hS
  obtain ⟨N, J, q, out, s, a, k0, d, e⟩ := bw_iso row rhs M S.card S H le_rfl hne hH
  refine ⟨N, J, q, out, ⟨s, a, fun p hp x hc => k0 p hp x ?_ hc⟩, d, e.trans hK⟩
  show ∑ i ∈ S, (row i x.1 + rhs i) = 1
  rw [Finset.sum_add_distrib, ← LinearMap.sum_apply, h0, h1]
  simp

theorem final {n k t m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
    (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] Fin t → ZMod 2) (H K : ℕ) :
    (∃ (N J : Finset (List Bool)) (q : List Bool → (Fin n → ZMod 2) × (Fin k → ZMod 2) → Bool)
        (out : List Bool → Fin m × (Fin t → ZMod 2)),
      Tree row rhs M N J q out ∧ (∀ p ∈ N \ J, p.length + 0 ≤ H) ∧ ∑ _p ∈ N \ J, 1 ≤ K) ↔
    ∃ S : Finset (Fin m), (S.sum row = 0 ∧ S.sum rhs = 1) ∧
      ∑ i ∈ S, 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range (M i)) ≤ K ∧
        ∑ i ∈ S, 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range (M i)) ≤ 2 ^ H := by
  constructor
  · rintro ⟨N, J, q, out, hT, hH, hK⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hK
    exact fwd row rhs M H K N J q out hT hH hK
  · rintro ⟨S, ⟨h0, h1⟩, hK, hH⟩
    obtain ⟨N, J, q, out, hT, hH', hK'⟩ := bwd row rhs M H K S h0 h1 hK hH
    refine ⟨N, J, q, out, hT, hH', ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    exact hK'

end PEqualNP.Outside.L_pcx_343_aux

theorem PEqualNP.Outside.L_pcx_343 : (∀ (n k t : ℕ),
  let X := Fin n → ZMod 2
  let U := Fin k → ZMod 2
  let Y := Fin t → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  let fits := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (depth leaves : O → ℕ) (H K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
      cert qs ok N J q out ∧ (∀ p ∈ N \ J, p.length + depth (out p) ≤ H) ∧
      (N \ J).sum (fun p => leaves (out p)) ≤ K
  ∀ (m : ℕ) (row : Fin m → X →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
      (M : Fin m → U →ₗ[ZMod 2] Y),
    let oddDep := fun S : Finset (Fin m) => S.sum row = 0 ∧ S.sum rhs = 1
    let wt := fun i : Fin m => 2^(Module.finrank (ZMod 2) (LinearMap.range (M i)))
    let answer := fun (z : X × U) (a : Fin m × Y) => row a.1 z.1 ≠ rhs a.1 ∧ a.2 = M a.1 z.2
    ∀ H K : ℕ, fits (queries (X × U)) answer (fun _ => 0) (fun _ => 1) H K ↔
      ∃ S : Finset (Fin m), oddDep S ∧ S.sum wt ≤ K ∧ S.sum wt ≤ 2^H) := by
  intro n k t
  dsimp only
  intro m row rhs M H K
  exact PEqualNP.Outside.L_pcx_343_aux.final row rhs M H K

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1063

open Finset

theorem z01 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide

theorem zflip : ∀ u c : ZMod 2, u = c ∨ u = c + 1 := by decide

theorem one_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem zne : ∀ c : ZMod 2, c ≠ c + 1 := by decide

theorem half {W : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    (P : W → Prop) [DecidablePred P] (d : W) (hP : ∀ w, P (w + d) ↔ P w)
    (f : W → ZMod 2) (hf : ∀ w, f (w + d) = f w + 1) (c : ZMod 2) :
    2 * (univ.filter (fun w => P w ∧ f w = c)).card = (univ.filter P).card := by
  have hf' : ∀ w, f (w - d) = f w + 1 := by
    intro w
    have h := hf (w - d)
    rw [sub_add_cancel] at h
    rw [h, add_assoc, one_one, add_zero]
  have e : (univ.filter (fun w => P w ∧ f w = c)).card
      = (univ.filter (fun w => P w ∧ f w = c + 1)).card := by
    apply Finset.card_nbij' (· + d) (· - d)
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      exact ⟨(hP w).2 hw.1, by rw [hf, hw.2]⟩
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      refine ⟨(hP (w - d)).1 (by rw [sub_add_cancel]; exact hw.1), ?_⟩
      rw [hf', hw.2, add_assoc, one_one, add_zero]
    · intro w _
      simp
    · intro w _
      simp
  have hu : univ.filter P = (univ.filter (fun w => P w ∧ f w = c)) ∪
      (univ.filter (fun w => P w ∧ f w = c + 1)) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro hp
      rcases zflip (f w) c with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hd : Disjoint (univ.filter (fun w => P w ∧ f w = c))
      (univ.filter (fun w => P w ∧ f w = c + 1)) := by
    rw [disjoint_filter]
    intro w _ h1 h2
    exact zne c (h1.2.symm.trans h2.2)
  rw [hu, card_union_of_disjoint hd, ← e]
  ring

theorem dual_vec {E ι : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite ι]
    (L : ι → E →ₗ[ZMod 2] ZMod 2) (hL : LinearIndependent (ZMod 2) L) (s : ι) :
    ∃ x, L s x = 1 ∧ ∀ t, t ≠ s → L t x = 0 := by
  by_contra hne
  push Not at hne
  have hle : ⨅ t : {t // t ≠ s}, LinearMap.ker (L t.val) ≤ LinearMap.ker (L s) := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx
    rw [LinearMap.mem_ker]
    rcases z01 (L s x) with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht, h2⟩ := hne x h
      exact h2 (hx ⟨t, ht⟩)
  have hspan := mem_span_of_iInf_ker_le_ker hle
  have hr : Set.range (fun t : {t // t ≠ s} => L t.val) = L '' {t | t ≠ s} := by
    ext g
    simp
  apply hL.notMem_span_image (s := {t | t ≠ s}) (x := s) (by simp)
  rw [← hr]
  exact hspan

theorem side {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {m : ℕ}
    (a : Fin m → E →ₗ[ZMod 2] ZMod 2) (xs : Fin m → E) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (g : E →ₗ[ZMod 2] ZMod 2) :
    (∃ x, (∀ s ∈ S, a s x = 0) ∧ g x = 1) ∨ (∀ x, g x = ∑ s ∈ S, a s x * g (xs s)) := by
  by_cases h : ∃ x, (∀ s ∈ S, a s x = 0) ∧ g x = 1
  · exact Or.inl h
  · right
    intro x
    have hz : ∀ t ∈ S, a t (x - ∑ s ∈ S, a s x • xs s) = 0 := by
      intro t ht
      rw [map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single t, (hxs t ht).1, mul_one, sub_self]
      · intro s hs hst
        rw [(hxs s hs).2 t ht (Ne.symm hst), mul_zero]
      · intro h'
        exact absurd ht h'
    have hg : g (x - ∑ s ∈ S, a s x • xs s) = 0 := by
      rcases z01 (g (x - ∑ s ∈ S, a s x • xs s)) with h0 | h1
      · exact h0
      · exact absurd ⟨_, hz, h1⟩ h
    rw [map_sub, map_sum] at hg
    simp only [map_smul, smul_eq_mul] at hg
    exact sub_eq_zero.1 hg

theorem pick {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {m : ℕ}
    (a : Fin m → E →ₗ[ZMod 2] ZMod 2) (xs : Fin m → E) (S : Finset (Fin m))
    (g : E →ₗ[ZMod 2] ZMod 2) (hrep : ∀ x, g x = ∑ s ∈ S, a s x * g (xs s)) (hg : g ≠ 0) :
    ∃ t ∈ S, g (xs t) = 1 := by
  by_contra h
  push Not at h
  apply hg
  refine LinearMap.ext (fun x => ?_)
  rw [hrep x, LinearMap.zero_apply]
  apply sum_eq_zero
  intro s hs
  rcases z01 (g (xs s)) with h0 | h1
  · rw [h0, mul_zero]
  · exact absurd h1 (h s hs)

theorem invx {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (T : Finset (Fin m))
    (x : Fin l → ZMod 2) (hx : ∀ t ∈ T, a t x = 0) (w : (Fin l → ZMod 2) × (Fin r → ZMod 2)) :
    (∀ t ∈ T, a t (w + (x, 0)).1 * b t (w + (x, 0)).2 = 0) ↔
      (∀ t ∈ T, a t w.1 * b t w.2 = 0) := by
  apply forall₂_congr
  intro t ht
  simp [map_add, hx t ht]

theorem invy {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (T : Finset (Fin m))
    (y : Fin r → ZMod 2) (hy : ∀ t ∈ T, b t y = 0) (w : (Fin l → ZMod 2) × (Fin r → ZMod 2)) :
    (∀ t ∈ T, a t (w + (0, y)).1 * b t (w + (0, y)).2 = 0) ↔
      (∀ t ∈ T, a t w.1 * b t w.2 = 0) := by
  apply forall₂_congr
  intro t ht
  simp [map_add, hy t ht]

theorem count {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (xs : Fin m → (Fin l → ZMod 2))
    (ys : Fin m → (Fin r → ZMod 2)) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (hys : ∀ s ∈ S, b s (ys s) = 1 ∧ ∀ t ∈ S, t ≠ s → b t (ys s) = 0) :
    ∀ T ⊆ S, 4 ^ T.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      ∀ t ∈ T, a t w.1 * b t w.2 = 0)).card =
      3 ^ T.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert s T hs ih =>
    intro hsub
    have hT : T ⊆ S := (subset_insert s T).trans hsub
    have hsS : s ∈ S := hsub (mem_insert_self s T)
    have hx0 : ∀ t ∈ T, a t (xs s) = 0 := by
      intro t ht
      exact (hxs s hsS).2 t (hT ht) (by rintro rfl; exact hs ht)
    have hy0 : ∀ t ∈ T, b t (ys s) = 0 := by
      intro t ht
      exact (hys s hsS).2 t (hT ht) (by rintro rfl; exact hs ht)
    have h1 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      ∀ t ∈ T, a t w.1 * b t w.2 = 0) (xs s, 0) (invx a b T (xs s) hx0)
      (fun w => a s w.1) (by intro w; simp [(hxs s hsS).1]) 0
    have h2 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      ∀ t ∈ T, a t w.1 * b t w.2 = 0) (xs s, 0) (invx a b T (xs s) hx0)
      (fun w => a s w.1) (by intro w; simp [(hxs s hsS).1]) 1
    have h3 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      (∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 1) (0, ys s)
      (fun w => and_congr (invy a b T (ys s) hy0 w) (by simp))
      (fun w => b s w.2) (by intro w; simp [(hys s hsS).1]) 0
    have hU : univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ∀ t ∈ insert s T, a t w.1 * b t w.2 = 0) =
        univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          (∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 0) ∪
        univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ((∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 1) ∧ b s w.2 = 0) := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_union, forall_mem_insert]
      rcases z01 (a s w.1) with h | h <;> rcases z01 (b s w.2) with h' | h' <;> simp [h, h']
    have hD : Disjoint (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          (∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 0))
        (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ((∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 1) ∧ b s w.2 = 0)) := by
      rw [disjoint_filter]
      intro w _ g1 g2
      rw [g1.2] at g2
      exact absurd g2.1.2 (by decide)
    rw [hU, card_union_of_disjoint hD, card_insert_of_notMem hs]
    have key : 4 * ((univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          (∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 0)).card +
        (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ((∀ t ∈ T, a t w.1 * b t w.2 = 0) ∧ a s w.1 = 1) ∧ b s w.2 = 0)).card) =
        3 * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ∀ t ∈ T, a t w.1 * b t w.2 = 0)).card := by
      omega
    rw [pow_succ, pow_succ, mul_assoc, key, ← mul_assoc, mul_comm _ 3, mul_assoc, ih hT]
    ring

theorem arithA (k N q0 g : ℕ) (hc : 4 ^ k * q0 = 3 ^ k * N) (e : q0 = 4 * g) :
    3 ^ k * N ≤ 9 * 4 ^ k * g := by
  calc 3 ^ k * N = 4 ^ k * q0 := hc.symm
    _ = 4 * (4 ^ k * g) := by rw [e]; ring
    _ ≤ 9 * (4 ^ k * g) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 9 * 4 ^ k * g := by ring

theorem arith1 (n N q0 q3 g : ℕ) (hc : 4 ^ n * q0 = 3 ^ n * N) (e : q0 = 8 * q3)
    (e3 : q3 ≤ g) : 3 ^ (n + 1) * N ≤ 9 * 4 ^ (n + 1) * g := by
  calc 3 ^ (n + 1) * N = 3 * (3 ^ n * N) := by ring
    _ = 3 * (4 ^ n * q0) := by rw [hc]
    _ = 24 * (4 ^ n * q3) := by rw [e]; ring
    _ ≤ 36 * (4 ^ n * g) := Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul_left _ e3)
    _ = 9 * 4 ^ (n + 1) * g := by ring

theorem arith2 (n N q0 q4 g : ℕ) (hc : 4 ^ n * q0 = 3 ^ n * N) (e : q0 = 16 * q4)
    (e3 : q4 ≤ g) : 3 ^ (n + 2) * N ≤ 9 * 4 ^ (n + 2) * g := by
  calc 3 ^ (n + 2) * N = 9 * (3 ^ n * N) := by ring
    _ = 9 * (4 ^ n * q0) := by rw [hc]
    _ = 144 * (4 ^ n * q4) := by rw [e]; ring
    _ ≤ 144 * (4 ^ n * g) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e3)
    _ = 9 * 4 ^ (n + 2) * g := by ring

theorem caseAA {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (xs : Fin m → (Fin l → ZMod 2))
    (ys : Fin m → (Fin r → ZMod 2)) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (hys : ∀ s ∈ S, b s (ys s) = 1 ∧ ∀ t ∈ S, t ≠ s → b t (ys s) = 0) (i : Fin m)
    (x0 : Fin l → ZMod 2) (hx0 : (∀ s ∈ S, a s x0 = 0) ∧ a i x0 = 1)
    (y0 : Fin r → ZMod 2) (hy0 : (∀ s ∈ S, b s y0 = 0) ∧ b i y0 = 1) :
    3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) ≤
      9 * 4 ^ S.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1)).card := by
  have h1 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ∀ s ∈ S, a s w.1 * b s w.2 = 0) (x0, 0) (invx a b S x0 hx0.1)
    (fun w => a i w.1) (by intro w; simp [hx0.2]) 1
  have h2 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    (∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) (0, y0)
    (fun w => and_congr (invy a b S y0 hy0.1 w) (by simp))
    (fun w => b i w.2) (by intro w; simp [hy0.2]) 1
  have hc := count a b xs ys S hxs hys S (subset_refl S)
  exact arithA _ _ _ _ hc (by omega)

theorem caseAB {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (xs : Fin m → (Fin l → ZMod 2))
    (ys : Fin m → (Fin r → ZMod 2)) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (hys : ∀ s ∈ S, b s (ys s) = 1 ∧ ∀ t ∈ S, t ≠ s → b t (ys s) = 0) (i : Fin m)
    (x0 : Fin l → ZMod 2) (hx0 : (∀ s ∈ S, a s x0 = 0) ∧ a i x0 = 1)
    (t : Fin m) (ht : t ∈ S) (hbt : b i (ys t) = 1) :
    3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) ≤
      9 * 4 ^ S.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1)).card := by
  have hT : ∀ s ∈ S.erase t, s ≠ t ∧ s ∈ S := fun s hs => mem_erase.1 hs
  have hi1 : ∀ s ∈ S.erase t, a s (xs t) = 0 :=
    fun s hs => (hxs t ht).2 s (hT s hs).2 (hT s hs).1
  have hi2 : ∀ s ∈ S.erase t, a s x0 = 0 := fun s hs => hx0.1 s (hT s hs).2
  have hi3 : ∀ s ∈ S.erase t, b s (ys t) = 0 :=
    fun s hs => (hys t ht).2 s (hT s hs).2 (hT s hs).1
  have h1 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) (xs t, 0) (invx a b _ (xs t) hi1)
    (fun w => a t w.1) (by intro w; simp [(hxs t ht).1]) 0
  have h2 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    (∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) ∧ a t w.1 = 0) (x0, 0)
    (fun w => and_congr (invx a b _ x0 hi2 w) (by simp [hx0.1 t ht]))
    (fun w => a i w.1) (by intro w; simp [hx0.2]) 1
  have h3 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ((∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) ∧ a t w.1 = 0) ∧ a i w.1 = 1) (0, ys t)
    (fun w => and_congr (and_congr (invy a b _ (ys t) hi3 w) (by simp)) (by simp))
    (fun w => b i w.2) (by intro w; simp [hbt]) 1
  have hsub : univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      (((∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) ∧ a t w.1 = 0) ∧ a i w.1 = 1) ∧
        b i w.2 = 1) ⊆
      univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨⟨fun s hs => ?_, hw.1.2⟩, hw.2⟩
    by_cases hst : s = t
    · rw [hst, hw.1.1.2, zero_mul]
    · exact hw.1.1.1 s (mem_erase.2 ⟨hst, hs⟩)
  have hc := count a b xs ys S hxs hys (S.erase t) (erase_subset t S)
  have hk : S.card = (S.erase t).card + 1 := by
    rw [card_erase_of_mem ht]
    have := card_pos.2 ⟨t, ht⟩
    omega
  rw [hk]
  exact arith1 _ _ _ _ _ hc (by omega) (card_le_card hsub)

theorem caseBA {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (xs : Fin m → (Fin l → ZMod 2))
    (ys : Fin m → (Fin r → ZMod 2)) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (hys : ∀ s ∈ S, b s (ys s) = 1 ∧ ∀ t ∈ S, t ≠ s → b t (ys s) = 0) (i : Fin m)
    (t : Fin m) (ht : t ∈ S) (hat : a i (xs t) = 1)
    (y0 : Fin r → ZMod 2) (hy0 : (∀ s ∈ S, b s y0 = 0) ∧ b i y0 = 1) :
    3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) ≤
      9 * 4 ^ S.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1)).card := by
  have hT : ∀ s ∈ S.erase t, s ≠ t ∧ s ∈ S := fun s hs => mem_erase.1 hs
  have hi1 : ∀ s ∈ S.erase t, a s (xs t) = 0 :=
    fun s hs => (hxs t ht).2 s (hT s hs).2 (hT s hs).1
  have hi2 : ∀ s ∈ S.erase t, b s y0 = 0 := fun s hs => hy0.1 s (hT s hs).2
  have hi3 : ∀ s ∈ S.erase t, b s (ys t) = 0 :=
    fun s hs => (hys t ht).2 s (hT s hs).2 (hT s hs).1
  have h1 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) (0, ys t) (invy a b _ (ys t) hi3)
    (fun w => b t w.2) (by intro w; simp [(hys t ht).1]) 0
  have h2 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    (∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) ∧ b t w.2 = 0) (0, y0)
    (fun w => and_congr (invy a b _ y0 hi2 w) (by simp [hy0.1 t ht]))
    (fun w => b i w.2) (by intro w; simp [hy0.2]) 1
  have h3 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ((∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) ∧ b t w.2 = 0) ∧ b i w.2 = 1) (xs t, 0)
    (fun w => and_congr (and_congr (invx a b _ (xs t) hi1 w) (by simp)) (by simp))
    (fun w => a i w.1) (by intro w; simp [hat]) 1
  have hsub : univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      (((∀ s ∈ S.erase t, a s w.1 * b s w.2 = 0) ∧ b t w.2 = 0) ∧ b i w.2 = 1) ∧
        a i w.1 = 1) ⊆
      univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨⟨fun s hs => ?_, hw.2⟩, hw.1.2⟩
    by_cases hst : s = t
    · rw [hst, hw.1.1.2, mul_zero]
    · exact hw.1.1.1 s (mem_erase.2 ⟨hst, hs⟩)
  have hc := count a b xs ys S hxs hys (S.erase t) (erase_subset t S)
  have hk : S.card = (S.erase t).card + 1 := by
    rw [card_erase_of_mem ht]
    have := card_pos.2 ⟨t, ht⟩
    omega
  rw [hk]
  exact arith1 _ _ _ _ _ hc (by omega) (card_le_card hsub)

theorem caseBB {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (xs : Fin m → (Fin l → ZMod 2))
    (ys : Fin m → (Fin r → ZMod 2)) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (hys : ∀ s ∈ S, b s (ys s) = 1 ∧ ∀ t ∈ S, t ≠ s → b t (ys s) = 0) (i : Fin m)
    (t t' : Fin m) (ht : t ∈ S) (ht' : t' ∈ S) (htt : t ≠ t')
    (hat : a i (xs t) = 1) (hbt : b i (ys t') = 1) :
    3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) ≤
      9 * 4 ^ S.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1)).card := by
  have hT : ∀ s ∈ (S.erase t).erase t', s ≠ t ∧ s ≠ t' ∧ s ∈ S := by
    intro s hs
    rcases mem_erase.1 hs with ⟨h1, h2⟩
    rcases mem_erase.1 h2 with ⟨h3, h4⟩
    exact ⟨h3, h1, h4⟩
  have hi1 : ∀ s ∈ (S.erase t).erase t', a s (xs t') = 0 :=
    fun s hs => (hxs t' ht').2 s (hT s hs).2.2 (hT s hs).2.1
  have hi2 : ∀ s ∈ (S.erase t).erase t', a s (xs t) = 0 :=
    fun s hs => (hxs t ht).2 s (hT s hs).2.2 (hT s hs).1
  have hi3 : ∀ s ∈ (S.erase t).erase t', b s (ys t) = 0 :=
    fun s hs => (hys t ht).2 s (hT s hs).2.2 (hT s hs).1
  have hi4 : ∀ s ∈ (S.erase t).erase t', b s (ys t') = 0 :=
    fun s hs => (hys t' ht').2 s (hT s hs).2.2 (hT s hs).2.1
  have ha : a t' (xs t) = 0 := (hxs t ht).2 t' ht' (Ne.symm htt)
  have hb : b t (ys t') = 0 := (hys t' ht').2 t ht htt
  have h1 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ∀ s ∈ (S.erase t).erase t', a s w.1 * b s w.2 = 0) (xs t', 0) (invx a b _ (xs t') hi1)
    (fun w => a t' w.1) (by intro w; simp [(hxs t' ht').1]) 0
  have h2 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    (∀ s ∈ (S.erase t).erase t', a s w.1 * b s w.2 = 0) ∧ a t' w.1 = 0) (xs t, 0)
    (fun w => and_congr (invx a b _ (xs t) hi2 w) (by simp [ha]))
    (fun w => a i w.1) (by intro w; simp [hat]) 1
  have h3 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    ((∀ s ∈ (S.erase t).erase t', a s w.1 * b s w.2 = 0) ∧ a t' w.1 = 0) ∧ a i w.1 = 1)
    (0, ys t)
    (fun w => and_congr (and_congr (invy a b _ (ys t) hi3 w) (by simp)) (by simp))
    (fun w => b t w.2) (by intro w; simp [(hys t ht).1]) 0
  have h4 := half (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
    (((∀ s ∈ (S.erase t).erase t', a s w.1 * b s w.2 = 0) ∧ a t' w.1 = 0) ∧ a i w.1 = 1) ∧
      b t w.2 = 0) (0, ys t')
    (fun w => and_congr (and_congr (and_congr (invy a b _ (ys t') hi4 w) (by simp))
      (by simp)) (by simp [hb]))
    (fun w => b i w.2) (by intro w; simp [hbt]) 1
  have hsub : univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
      ((((∀ s ∈ (S.erase t).erase t', a s w.1 * b s w.2 = 0) ∧ a t' w.1 = 0) ∧
        a i w.1 = 1) ∧ b t w.2 = 0) ∧ b i w.2 = 1) ⊆
      univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨⟨fun s hs => ?_, hw.1.1.2⟩, hw.2⟩
    by_cases hst : s = t
    · rw [hst, hw.1.2, mul_zero]
    · by_cases hst' : s = t'
      · rw [hst', hw.1.1.1.2, zero_mul]
      · exact hw.1.1.1.1 s (mem_erase.2 ⟨hst', mem_erase.2 ⟨hst, hs⟩⟩)
  have hsub2 : (S.erase t).erase t' ⊆ S := (erase_subset _ _).trans (erase_subset _ _)
  have hc := count a b xs ys S hxs hys ((S.erase t).erase t') hsub2
  have hk : S.card = ((S.erase t).erase t').card + 2 := by
    have ht2 : t' ∈ S.erase t := mem_erase.2 ⟨Ne.symm htt, ht'⟩
    rw [card_erase_of_mem ht2, card_erase_of_mem ht]
    have := card_pos.2 ⟨t', ht2⟩
    rw [card_erase_of_mem ht] at this
    omega
  rw [hk]
  exact arith2 _ _ _ _ _ hc (by omega) (card_le_card hsub)

theorem good {l r m : ℕ} (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (xs : Fin m → (Fin l → ZMod 2))
    (ys : Fin m → (Fin r → ZMod 2)) (S : Finset (Fin m))
    (hxs : ∀ s ∈ S, a s (xs s) = 1 ∧ ∀ t ∈ S, t ≠ s → a t (xs s) = 0)
    (hys : ∀ s ∈ S, b s (ys s) = 1 ∧ ∀ t ∈ S, t ≠ s → b t (ys s) = 0) (i : Fin m)
    (hai : a i ≠ 0) (hbi : b i ≠ 0) (hno : ∀ s ∈ S, a i = a s → b i ≠ b s) :
    3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) ≤
      9 * 4 ^ S.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1)).card := by
  rcases side a xs S hxs (a i) with ⟨x0, hx0⟩ | hra <;>
    rcases side b ys S hys (b i) with ⟨y0, hy0⟩ | hrb
  · exact caseAA a b xs ys S hxs hys i x0 hx0 y0 hy0
  · obtain ⟨t, ht, hbt⟩ := pick b ys S (b i) hrb hbi
    exact caseAB a b xs ys S hxs hys i x0 hx0 t ht hbt
  · obtain ⟨t, ht, hat⟩ := pick a xs S (a i) hra hai
    exact caseBA a b xs ys S hxs hys i t ht hat y0 hy0
  · obtain ⟨t, ht, hat⟩ := pick a xs S (a i) hra hai
    obtain ⟨t', ht', hbt⟩ := pick b ys S (b i) hrb hbi
    by_cases htt : t = t'
    · subst htt
      by_cases hex : ∃ s ∈ S, s ≠ t ∧ (a i (xs s) = 1 ∨ b i (ys s) = 1)
      · obtain ⟨s, hs, hst, h | h⟩ := hex
        · exact caseBB a b xs ys S hxs hys i s t hs ht hst h hbt
        · exact caseBB a b xs ys S hxs hys i t s ht hs (Ne.symm hst) hat h
      · push Not at hex
        exfalso
        apply hno t ht
        · refine LinearMap.ext (fun x => ?_)
          rw [hra x, Finset.sum_eq_single t, hat, mul_one]
          · intro s hs hst
            rcases z01 (a i (xs s)) with h0 | h1
            · rw [h0, mul_zero]
            · exact absurd h1 (hex s hs hst).1
          · intro h'
            exact absurd ht h'
        · refine LinearMap.ext (fun y => ?_)
          rw [hrb y, Finset.sum_eq_single t, hbt, mul_one]
          · intro s hs hst
            rcases z01 (b i (ys s)) with h0 | h1
            · rw [h0, mul_zero]
            · exact absurd h1 (hex s hs hst).2
          · intro h'
            exact absurd ht h'
    · exact caseBB a b xs ys S hxs hys i t t' ht ht' htt hat hbt

theorem main (l r m : ℕ) (a : Fin m → (Fin l → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : Fin m → (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (S : Finset (Fin m))
    (hA : LinearIndependent (ZMod 2) (fun i : S => a i.val))
    (hB : LinearIndependent (ZMod 2) (fun i : S => b i.val)) :
    (4 ^ S.card * Nat.card {w : (Fin l → ZMod 2) × (Fin r → ZMod 2) //
        ∀ i, a i w.1 * b i w.2 = 0} =
        3 ^ S.card * (Nat.card (Fin l → ZMod 2) * Nat.card (Fin r → ZMod 2)) ↔
      (∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s)) ∧
    (¬ (∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s) →
      9 * 4 ^ S.card * Nat.card {w : (Fin l → ZMod 2) × (Fin r → ZMod 2) //
        ∀ i, a i w.1 * b i w.2 = 0} ≤
        8 * 3 ^ S.card * (Nat.card (Fin l → ZMod 2) * Nat.card (Fin r → ZMod 2))) := by
  have hH : Nat.card {w : (Fin l → ZMod 2) × (Fin r → ZMod 2) // ∀ i, a i w.1 * b i w.2 = 0} =
      (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ∀ i, a i w.1 * b i w.2 = 0)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hN : Nat.card (Fin l → ZMod 2) * Nat.card (Fin r → ZMod 2) =
      Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) := by
    rw [← Nat.card_prod, Nat.card_eq_fintype_card]
  rw [hH, hN]
  have dx : ∀ s, ∃ x : Fin l → ZMod 2, s ∈ S → (a s x = 1 ∧ ∀ t ∈ S, t ≠ s → a t x = 0) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨x, hx1, hx2⟩ := dual_vec (fun i : S => a i.val) hA ⟨s, hs⟩
      exact ⟨x, fun _ => ⟨hx1, fun t ht hts =>
        hx2 ⟨t, ht⟩ (fun h => hts (congrArg Subtype.val h))⟩⟩
    · exact ⟨0, fun h => absurd h hs⟩
  have dy : ∀ s, ∃ y : Fin r → ZMod 2, s ∈ S → (b s y = 1 ∧ ∀ t ∈ S, t ≠ s → b t y = 0) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨y, hy1, hy2⟩ := dual_vec (fun i : S => b i.val) hB ⟨s, hs⟩
      exact ⟨y, fun _ => ⟨hy1, fun t ht hts =>
        hy2 ⟨t, ht⟩ (fun h => hts (congrArg Subtype.val h))⟩⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose xs hxs using dx
  choose ys hys using dy
  have hE := count a b xs ys S hxs hys S (subset_refl S)
  have hpos : 0 < 3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) :=
    Nat.mul_pos (by positivity) Fintype.card_pos
  have key : ¬ (∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s) →
      9 * 4 ^ S.card * (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ∀ i, a i w.1 * b i w.2 = 0)).card ≤
        8 * 3 ^ S.card * Fintype.card ((Fin l → ZMod 2) × (Fin r → ZMod 2)) := by
    intro hnp
    push Not at hnp
    obtain ⟨i, hai, hbi, hno⟩ := hnp
    have hG := good a b xs ys S hxs hys i hai hbi hno
    have hD : Disjoint (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ∀ i, a i w.1 * b i w.2 = 0))
        (univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1)) := by
      rw [disjoint_filter]
      intro w _ g1 g2
      have := g1 i
      rw [g2.1.2, g2.2, mul_one] at this
      exact absurd this (by decide)
    have hU : univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ∀ i, a i w.1 * b i w.2 = 0) ∪
        univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ((∀ s ∈ S, a s w.1 * b s w.2 = 0) ∧ a i w.1 = 1) ∧ b i w.2 = 1) ⊆
        univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ∀ s ∈ S, a s w.1 * b s w.2 = 0) := by
      intro w hw
      simp only [mem_union, mem_filter, mem_univ, true_and] at hw ⊢
      rcases hw with h | h
      · exact fun s _ => h s
      · exact h.1.1
    have hle := card_le_card hU
    rw [card_union_of_disjoint hD] at hle
    have hm := Nat.mul_le_mul_left (9 * 4 ^ S.card) hle
    nlinarith [hm, hG, hE]
  refine ⟨⟨fun heq => ?_, fun hp => ?_⟩, key⟩
  · by_contra hnp
    have := key hnp
    nlinarith [this, heq, hpos]
  · have : univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
        ∀ i, a i w.1 * b i w.2 = 0) =
        univ.filter (fun w : (Fin l → ZMod 2) × (Fin r → ZMod 2) =>
          ∀ s ∈ S, a s w.1 * b s w.2 = 0) := by
      apply filter_congr
      intro w _
      constructor
      · intro h s _
        exact h s
      · intro h i
        rcases hp i with h0 | h0 | ⟨s, hs, h1, h2⟩
        · rw [h0]
          simp
        · rw [h0]
          simp
        · rw [h1, h2]
          exact h s hs
    rw [this]
    exact hE

end PEqualNP.Outside.L_lib_1063

open PEqualNP.Outside.L_lib_1063 in
theorem PEqualNP.Outside.L_lib_1063 : ∀ l r m : ℕ,
  let F := ZMod 2
  let X := Fin l → F
  let Y := Fin r → F
  ∀ (a : Fin m → X →ₗ[F] F) (b : Fin m → Y →ₗ[F] F) (S : Finset (Fin m)),
    LinearIndependent F (fun i : S => a i.val) → LinearIndependent F (fun i : S => b i.val) →
    let pure := ∀ i, a i = 0 ∨ b i = 0 ∨ ∃ s ∈ S, a i = a s ∧ b i = b s
    let hits := Nat.card {w : X × Y // ∀ i, a i w.1 * b i w.2 = 0}
    let allPairs := Nat.card X * Nat.card Y
    (4^S.card*hits = 3^S.card*allPairs ↔ pure) ∧
      (¬ pure → 9*4^S.card*hits ≤ 8*3^S.card*allPairs) := by
  intro l r m F X Y a b S hA hB pure hits allPairs
  exact main l r m a b S hA hB

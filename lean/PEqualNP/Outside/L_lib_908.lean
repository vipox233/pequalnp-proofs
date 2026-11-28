import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_908

open Finset Module

variable {K : Type} [Field K] {n : ℕ}

/-- The earlier members of layer k before column j. -/
def F (ℓ : ℕ → ℕ) (k j : ℕ) : Finset ℕ := (Finset.range j).filter (fun j' => ℓ j' = k)

def S (v : ℕ → Fin n → K) (ℓ : ℕ → ℕ) (k j : ℕ) : Set (Fin n → K) := v '' ↑(F ℓ k j)

def Rule (v : ℕ → Fin n → K) (ℓ : ℕ → ℕ) (j : ℕ) : Prop :=
  (∀ k < ℓ j, v j ∈ Submodule.span K (S v ℓ k j)) ∧ v j ∉ Submodule.span K (S v ℓ (ℓ j) j)

def col (ℓ : ℕ → ℕ) (j : ℕ) : ℕ := (F ℓ (ℓ j) j).card

theorem F_congr (ℓ ℓ' : ℕ → ℕ) (k j : ℕ) (h : ∀ j' < j, ℓ j' = ℓ' j') : F ℓ k j = F ℓ' k j :=
  Finset.filter_congr (fun x hx => by rw [h x (Finset.mem_range.1 hx)])

theorem exists_layers (v : ℕ → Fin n → K) :
    ∀ N : ℕ, (∀ j < N, v j ≠ 0) → ∃ ℓ : ℕ → ℕ, ∀ j < N, Rule v ℓ j := by
  intro N
  induction N with
  | zero => intro _; exact ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    intro hnz
    obtain ⟨ℓ, hℓ⟩ := ih (fun j hj => hnz j (by omega))
    have hex : ∃ k, v N ∉ Submodule.span K (S v ℓ k N) := by
      refine ⟨(Finset.range N).sup ℓ + 1, ?_⟩
      have hF : F ℓ ((Finset.range N).sup ℓ + 1) N = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro x hx
        have := Finset.le_sup (f := ℓ) hx
        omega
      have hS : S v ℓ ((Finset.range N).sup ℓ + 1) N = ∅ := by
        unfold S; rw [hF]; simp
      rw [hS, Submodule.span_empty, Submodule.mem_bot]
      exact hnz N (by omega)
    classical
    obtain ⟨k0, hk0, hmin⟩ : ∃ k0, v N ∉ Submodule.span K (S v ℓ k0 N) ∧
        ∀ k < k0, v N ∈ Submodule.span K (S v ℓ k N) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
    refine ⟨Function.update ℓ N k0, ?_⟩
    have hlow : ∀ j' < N, Function.update ℓ N k0 j' = ℓ j' := by
      intro j' hj'
      exact Function.update_of_ne (by omega) _ _
    intro j hj
    have hS : ∀ k, S v (Function.update ℓ N k0) k j = S v ℓ k j := by
      intro k
      unfold S
      rw [F_congr _ ℓ k j (fun j' hj' => hlow j' (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have e : Function.update ℓ N k0 j = ℓ j := hlow j hj
      unfold Rule
      simp only [hS, e]
      exact hℓ j hj
    · have e : Function.update ℓ j k0 j = k0 := Function.update_self _ _ _
      unfold Rule
      simp only [hS, e]
      exact ⟨hmin, hk0⟩

theorem li (v : ℕ → Fin n → K) (ℓ : ℕ → ℕ) (k : ℕ) :
    ∀ N, (∀ j < N, Rule v ℓ j) → LinearIndepOn K v (↑(F ℓ k N) : Set ℕ) := by
  intro N
  induction N with
  | zero => intro _; unfold F; simp [linearIndepOn_empty]
  | succ N ih =>
    intro hR
    have ih' := ih (fun j hj => hR j (by omega))
    unfold F
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.coe_insert]
      apply ih'.insert
      have := (hR N (by omega)).2
      rw [h] at this
      exact this
    · exact ih'

theorem card_le_of_li (v : ℕ → Fin n → K) (G : Finset ℕ) (hli : LinearIndepOn K v (↑G : Set ℕ))
    (W : Submodule K (Fin n → K)) (hW : ∀ x ∈ G, v x ∈ W) : G.card ≤ finrank K W := by
  let f : (↑G : Set ℕ) → W := fun x => ⟨v x, hW x x.2⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp W.subtype hli
  have := hf.fintype_card_le_finrank
  simpa using this

theorem span_le_card (v : ℕ → Fin n → K) (G : Finset ℕ) :
    finrank K (Submodule.span K (v '' ↑G)) ≤ G.card := by
  rw [Set.image_eq_range]
  have := finrank_range_le_card (R := K) (fun x : (↑G : Set ℕ) => v x)
  simpa [Set.finrank] using this

theorem F_mono (ℓ : ℕ → ℕ) (k : ℕ) {a b : ℕ} (h : a ≤ b) : F ℓ k a ⊆ F ℓ k b := by
  intro x hx
  unfold F at *
  simp only [Finset.mem_filter, Finset.mem_range] at *
  exact ⟨by omega, hx.2⟩

theorem F_succ_self (ℓ : ℕ → ℕ) (j : ℕ) : (F ℓ (ℓ j) (j + 1)).card = col ℓ j + 1 := by
  unfold col F
  rw [Finset.range_add_one, Finset.filter_insert, if_pos rfl, Finset.card_insert_of_notMem]
  simp

theorem col_lt_of_same (ℓ : ℕ → ℕ) {j q : ℕ} (hjq : j < q) (h : ℓ j = ℓ q) : col ℓ j < col ℓ q := by
  have h1 := F_succ_self ℓ j
  have h2 : F ℓ (ℓ j) (j + 1) ⊆ F ℓ (ℓ q) q := by rw [h]; exact F_mono ℓ _ (by omega)
  have := Finset.card_le_card h2
  unfold col at *
  omega

theorem no_higher (v : ℕ → Fin n → K) (ℓ : ℕ → ℕ) {j q : ℕ} (hjq : j < q)
    (hR : ∀ x ≤ j, Rule v ℓ x) (hlt : ℓ q < ℓ j) : col ℓ j ≠ col ℓ q := by
  intro heq
  have hli := li v ℓ (ℓ j) (j + 1) (fun x hx => hR x (by omega))
  have hW : ∀ x ∈ F ℓ (ℓ j) (j + 1), v x ∈ Submodule.span K (S v ℓ (ℓ q) j) := by
    intro x hx
    unfold F at hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hr := (hR x (by omega)).1 (ℓ q) (by rw [hx.2]; exact hlt)
    refine Submodule.span_mono ?_ hr
    unfold S
    exact Set.image_mono (by exact_mod_cast F_mono ℓ (ℓ q) (by omega : x ≤ j))
  have h1 := card_le_of_li v _ hli _ hW
  have h2 := span_le_card v (F ℓ (ℓ q) j)
  have h3 := Finset.card_le_card (F_mono ℓ (ℓ q) (le_of_lt hjq))
  rw [F_succ_self] at h1
  have h4 : col ℓ j + 1 ≤ (F ℓ (ℓ q) j).card := le_trans h1 h2
  unfold col at heq h4
  omega

theorem witness (v : ℕ → Fin n → K) (ℓ : ℕ → ℕ) (k q : ℕ) (i : Fin n)
    (hq : v q ∈ Submodule.span K (S v ℓ k q)) (hi : v q i ≠ 0) :
    ∃ x ∈ F ℓ k q, v x i ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hle : Submodule.span K (S v ℓ k q) ≤ LinearMap.ker (LinearMap.proj i : (Fin n → K) →ₗ[K] K) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp [hne x hx]
  have := hle hq
  simp at this
  exact hi this

end PEqualNP.Outside.L_lib_908

open PEqualNP.Outside.L_lib_908 in
theorem PEqualNP.Outside.L_lib_908 : ∀ (K : Type) [Field K] (n m p : ℕ) (pivot : Fin n → Fin m) (budget : Fin n → ℕ),
  Function.Surjective pivot →
  ((∃ A : Matrix (Fin n) (Fin m) K, A.rank ≤ p ∧
    ∀ i, A i (pivot i) ≠ 0 ∧
      (@Finset.filter _ (fun j : Fin m => j < pivot i ∧ A i j ≠ 0)
        (Classical.decPred _) Finset.univ).card ≤ budget i) ↔
  ∃ c : Fin m → Fin p, ∀ i,
    (Finset.univ.filter (fun j : Fin m => j < pivot i ∧ c j = c (pivot i))).card ≤ budget i) := by
  intro K _ n m p pivot budget hsurj
  constructor
  · rintro ⟨A, hrank, hA⟩
    let v : ℕ → Fin n → K := fun j => if h : j < m then fun i => A i ⟨j, h⟩ else 0
    have hv : ∀ (j : Fin m), v j.val = fun i => A i j := by
      intro j; simp [v, j.isLt]
    have hnz : ∀ j < m, v j ≠ 0 := by
      intro j hj
      obtain ⟨i, hi⟩ := hsurj ⟨j, hj⟩
      intro h0
      have := congrFun h0 i
      rw [hv ⟨j, hj⟩] at this
      exact (hA i).1 (by rw [hi]; exact this)
    obtain ⟨ℓ, hℓ⟩ := exists_layers v m hnz
    have hcolp : ∀ j : Fin m, col ℓ j.val < p := by
      intro j
      have hli := li v ℓ (ℓ j.val) (j.val + 1) (fun x hx => hℓ x (by omega))
      have hW : ∀ x ∈ F ℓ (ℓ j.val) (j.val + 1), v x ∈ Submodule.span K (Set.range A.col) := by
        intro x hx
        unfold F at hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        have hxm : x < m := by omega
        apply Submodule.subset_span
        refine ⟨⟨x, hxm⟩, ?_⟩
        rw [hv ⟨x, hxm⟩]
        funext i
        simp [Matrix.col]
      have h1 := card_le_of_li v _ hli _ hW
      rw [F_succ_self, ← Matrix.rank_eq_finrank_span_cols] at h1
      omega
    refine ⟨fun j => ⟨col ℓ j.val, hcolp j⟩, fun i => ?_⟩
    set q := pivot i with hqdef
    -- same coloured earlier columns sit in distinct earlier layers
    have hE : (Finset.univ.filter (fun j : Fin m =>
        j < q ∧ (⟨col ℓ j.val, hcolp j⟩ : Fin p) = ⟨col ℓ q.val, hcolp q⟩)).card ≤ ℓ q.val := by
      have := Finset.card_le_card_of_injOn (fun j : Fin m => ℓ j.val)
        (s := Finset.univ.filter (fun j : Fin m =>
          j < q ∧ (⟨col ℓ j.val, hcolp j⟩ : Fin p) = ⟨col ℓ q.val, hcolp q⟩))
        (t := Finset.range (ℓ q.val)) ?_ ?_
      · simpa using this
      · intro j hj
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fin.mk.injEq] at hj
        simp only [Finset.coe_range, Set.mem_Iio]
        have hjq : j.val < q.val := hj.1
        rcases lt_trichotomy (ℓ j.val) (ℓ q.val) with h | h | h
        · exact h
        · exact absurd hj.2 (ne_of_lt (col_lt_of_same ℓ hjq h))
        · exact absurd hj.2 (no_higher v ℓ hjq (fun x hx => hℓ x (by omega)) h)
      · intro j1 hj1 j2 hj2 h12
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fin.mk.injEq] at hj1 hj2
        simp only at h12
        rcases lt_trichotomy j1.val j2.val with h | h | h
        · exact absurd (hj1.2.trans hj2.2.symm) (ne_of_lt (col_lt_of_same ℓ h h12))
        · exact Fin.ext h
        · exact absurd (hj2.2.trans hj1.2.symm) (ne_of_lt (col_lt_of_same ℓ h h12.symm))
    -- each earlier layer holds a nonzero of row i
    have hL : ℓ q.val ≤ (@Finset.filter _ (fun j : Fin m => j < pivot i ∧ A i j ≠ 0)
        (Classical.decPred _) Finset.univ).card := by
      have hsub : Finset.range (ℓ q.val) ⊆
          (@Finset.filter _ (fun j : Fin m => j < pivot i ∧ A i j ≠ 0)
            (Classical.decPred _) Finset.univ).image (fun j : Fin m => ℓ j.val) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hqv : v q.val i ≠ 0 := by rw [hv q]; exact (hA i).1
        obtain ⟨x, hx, hxi⟩ := witness v ℓ k q.val i ((hℓ q.val q.isLt).1 k hk) hqv
        unfold F at hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        have hxm : x < m := by omega
        rw [Finset.mem_image]
        refine ⟨⟨x, hxm⟩, ?_, hx.2⟩
        rw [hv ⟨x, hxm⟩] at hxi
        exact (@Finset.mem_filter _ _ (Classical.decPred _) _ _).2
          ⟨Finset.mem_univ _, (show x < q.val from hx.1), hxi⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      exact this.trans Finset.card_image_le
    exact hE.trans (hL.trans (hA i).2)
  · rintro ⟨c, hc⟩
    let B : Matrix (Fin n) (Fin p) K := Matrix.of fun i k => if k = c (pivot i) then 1 else 0
    let C : Matrix (Fin p) (Fin m) K := Matrix.of fun k j => if c j = k then 1 else 0
    refine ⟨B * C, ?_, fun i => ⟨?_, ?_⟩⟩
    · exact (Matrix.rank_mul_le_left B C).trans (Matrix.rank_le_width B)
    · simp [B, C, Matrix.mul_apply]
    · have e : (@Finset.filter _ (fun j : Fin m => j < pivot i ∧ (B * C) i j ≠ 0)
          (Classical.decPred _) Finset.univ) =
          Finset.univ.filter (fun j : Fin m => j < pivot i ∧ c j = c (pivot i)) := by
        ext j
        simp [B, C, Matrix.mul_apply]
      rw [e]; exact hc i

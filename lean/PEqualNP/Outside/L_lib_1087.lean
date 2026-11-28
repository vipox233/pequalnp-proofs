import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1087

open Module

inductive DT (X : Type) [AddCommGroup X] [Module (ZMod 2) X] where
  | leaf : Bool → DT X
  | node : (X →ₗ[ZMod 2] ZMod 2) → DT X → DT X → DT X

section Trees
variable {X : Type} [AddCommGroup X] [Module (ZMod 2) X]

def DT.depth : DT X → ℕ
  | .leaf _ => 0
  | .node _ t0 t1 => max t0.depth t1.depth + 1

def DT.eval : DT X → X → Bool
  | .leaf b, _ => b
  | .node ℓ t0 t1, x => if ℓ x = 0 then t0.eval x else t1.eval x

def DT.query : DT X → List (ZMod 2) → (X →ₗ[ZMod 2] ZMod 2)
  | .leaf _, _ => 0
  | .node ℓ _ _, [] => ℓ
  | .node _ t0 t1, y :: ys => if y = 0 then t0.query ys else t1.query ys

def DT.result : DT X → List (ZMod 2) → Bool
  | .leaf b, _ => b
  | .node _ _ _, [] => false
  | .node _ t0 t1, y :: ys => if y = 0 then t0.result ys else t1.result ys

lemma z2 (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

lemma DT.result_eq (t : DT X) (x : X) (L : List (ZMod 2)) (hL : t.depth ≤ L.length)
    (h : ∀ i (hi : i < L.length), t.query (L.take i) x = L[i]) : t.result L = t.eval x := by
  induction t generalizing L with
  | leaf b => rfl
  | node ℓ t0 t1 ih0 ih1 =>
    cases L with
    | nil => simp [DT.depth] at hL
    | cons y ys =>
      have h0 := h 0 (by simp)
      simp only [List.take_zero, DT.query, List.getElem_cons_zero] at h0
      simp only [DT.depth, List.length_cons] at hL
      have hs : ∀ i (hi : i < ys.length),
          (if y = 0 then t0.query (ys.take i) else t1.query (ys.take i)) x = ys[i] := by
        intro i hi
        have := h (i+1) (by simp; omega)
        simpa [DT.query] using this
      by_cases hy : y = 0
      · simp only [hy, ite_true] at hs
        simp only [DT.result, DT.eval, hy, ite_true, h0]
        exact ih0 ys (by omega) hs
      · simp only [hy, ite_false] at hs
        have hy' : ℓ x ≠ 0 := by rw [h0]; exact hy
        simp only [DT.result, DT.eval, hy, ite_false, hy', ite_false]
        exact ih1 ys (by omega) hs

lemma DT.compile (t : DT X) (d : ℕ) (hd : t.depth ≤ d) :
    ∃ (ask : (i : Fin d) → (Fin i.val → ZMod 2) → X →ₗ[ZMod 2] ZMod 2)
      (out : (Fin d → ZMod 2) → Bool),
      ∀ (x : X) (z : Fin d → ZMod 2),
        (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) x = z i) → out z = t.eval x := by
  refine ⟨fun i p => t.query (List.ofFn p), fun z => t.result (List.ofFn z), ?_⟩
  intro x z hz
  apply DT.result_eq t x _ (by simpa using hd)
  intro i hi
  simp only [List.length_ofFn] at hi
  have hpre : (List.ofFn z).take i =
      List.ofFn (fun j : Fin (⟨i, hi⟩ : Fin d).val => z ⟨j.val, Nat.lt_trans j.isLt hi⟩) := by
    apply List.ext_getElem
    · simp; omega
    · intro n h1 h2
      simp
  rw [hpre, hz ⟨i, hi⟩]
  simp

def qmap : (n : ℕ) → (X →ₗ[ZMod 2] (Fin n → ZMod 2)) → ((Fin n → ZMod 2) → DT X) → DT X
  | 0, _, k => k 0
  | n+1, L, k => .node ((LinearMap.proj 0).comp L)
      (qmap n ((LinearMap.funLeft (ZMod 2) (ZMod 2) Fin.succ).comp L) (fun y => k (Fin.cons 0 y)))
      (qmap n ((LinearMap.funLeft (ZMod 2) (ZMod 2) Fin.succ).comp L) (fun y => k (Fin.cons 1 y)))

lemma qmap_eval (n : ℕ) (L : X →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : (Fin n → ZMod 2) → DT X) (x : X) :
    (qmap n L k).eval x = (k (L x)).eval x := by
  induction n with
  | zero =>
    simp only [qmap]
    congr 2
    funext i; exact i.elim0
  | succ n ih =>
    simp only [qmap, DT.eval, ih]
    have ht : (LinearMap.funLeft (ZMod 2) (ZMod 2) Fin.succ).comp L x = Fin.tail (L x) := rfl
    have h0 : ((LinearMap.proj 0).comp L) x = L x 0 := rfl
    rw [ht, h0]
    rcases z2 (L x 0) with h | h
    · simp only [h, ite_true]
      rw [← h, Fin.cons_self_tail]
    · simp only [h, one_ne_zero, ite_false]
      rw [← h, Fin.cons_self_tail]

lemma qmap_depth (n : ℕ) (L : X →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : (Fin n → ZMod 2) → DT X) (D : ℕ)
    (hk : ∀ y, (k y).depth ≤ D) : (qmap n L k).depth ≤ n + D := by
  induction n generalizing D with
  | zero => simpa [qmap] using hk 0
  | succ n ih =>
    simp only [qmap, DT.depth]
    have h1 := ih ((LinearMap.funLeft (ZMod 2) (ZMod 2) Fin.succ).comp L) (fun y => k (Fin.cons 0 y)) D
      (fun y => hk _)
    have h2 := ih ((LinearMap.funLeft (ZMod 2) (ZMod 2) Fin.succ).comp L) (fun y => k (Fin.cons 1 y)) D
      (fun y => hk _)
    omega

end Trees

section LinAlg
variable {a : ℕ}

abbrev Vec (a : ℕ) := Fin a → ZMod 2

lemma fr_le (S : Submodule (ZMod 2) (Vec a)) : finrank (ZMod 2) S ≤ a := by
  have := Submodule.finrank_le S; rwa [Module.finrank_fin_fun] at this

lemma sup_le1 (c : Vec a) (S : Submodule (ZMod 2) (Vec a)) :
    finrank (ZMod 2) ((Submodule.span (ZMod 2) {c}) ⊔ S : Submodule (ZMod 2) (Vec a)) ≤
      finrank (ZMod 2) S + 1 := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span (ZMod 2) {c}) S
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({c} : Set (Vec a))) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({c} : Set (Vec a))
    simpa using this
  omega

lemma sup_mem (c : Vec a) (S : Submodule (ZMod 2) (Vec a)) (h : c ∈ S) :
    ((Submodule.span (ZMod 2) {c}) ⊔ S : Submodule (ZMod 2) (Vec a)) = S := by
  apply sup_eq_right.mpr
  exact (Submodule.span_singleton_le_iff_mem c S).mpr h

lemma sup_nmem (c : Vec a) (S : Submodule (ZMod 2) (Vec a)) (h : c ∉ S) :
    finrank (ZMod 2) ((Submodule.span (ZMod 2) {c}) ⊔ S : Submodule (ZMod 2) (Vec a)) =
      finrank (ZMod 2) S + 1 := by
  have hc : c ≠ 0 := by rintro rfl; exact h S.zero_mem
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {c}) S
  have h2 : (Submodule.span (ZMod 2) {c}) ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases Submodule.mem_inf.mp hx with ⟨hx1, hx2⟩
    rcases Submodule.mem_span_singleton.mp hx1 with ⟨t, rfl⟩
    rcases z2 t with ht | ht
    · simp [ht]
    · rw [ht, one_smul] at hx2; exact absurd hx2 h
  rw [h2, finrank_bot, finrank_span_singleton hc] at h1
  omega

noncomputable abbrev qn (V : Submodule (ZMod 2) (Vec a)) : ℕ := finrank (ZMod 2) (Vec a ⧸ V)

noncomputable def piV (V : Submodule (ZMod 2) (Vec a)) : Vec a →ₗ[ZMod 2] (Fin (qn V) → ZMod 2) :=
  ((Module.finBasis (ZMod 2) (Vec a ⧸ V)).equivFun.toLinearMap).comp V.mkQ

lemma ker_piV (V : Submodule (ZMod 2) (Vec a)) : LinearMap.ker (piV V) = V := by
  ext x
  simp only [LinearMap.mem_ker, piV, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

lemma piV_surj (V : Submodule (ZMod 2) (Vec a)) : Function.Surjective (piV V) := by
  exact (Module.finBasis (ZMod 2) (Vec a ⧸ V)).equivFun.surjective.comp (Submodule.mkQ_surjective V)

lemma qn_eq (V : Submodule (ZMod 2) (Vec a)) : qn V + finrank (ZMod 2) V = a := by
  have := Submodule.finrank_quotient_add_finrank V
  rw [Module.finrank_fin_fun] at this; exact this

lemma comap_piV (V : Submodule (ZMod 2) (Vec a)) (c : Vec a) :
    (Submodule.span (ZMod 2) {piV V c}).comap (piV V) = (Submodule.span (ZMod 2) {c}) ⊔ V := by
  have : Submodule.span (ZMod 2) {piV V c} = (Submodule.span (ZMod 2) {c}).map (piV V) := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [this, Submodule.comap_map_eq, ker_piV]

lemma comap_piV_fr (V : Submodule (ZMod 2) (Vec a)) (y : Fin (qn V) → ZMod 2) :
    finrank (ZMod 2) V ≤ finrank (ZMod 2) ((Submodule.span (ZMod 2) {y}).comap (piV V)) ∧
    finrank (ZMod 2) ((Submodule.span (ZMod 2) {y}).comap (piV V)) ≤ finrank (ZMod 2) V + 1 := by
  obtain ⟨c, rfl⟩ := piV_surj V y
  rw [comap_piV]
  exact ⟨Submodule.finrank_mono le_sup_right, sup_le1 c V⟩

end LinAlg

section Upper
variable (a b r : ℕ) (f : ℕ → Bool)

noncomputable def colL (j : ℕ) : Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] Vec a :=
  if h : j < b then
    { toFun := fun A i => A i ⟨j, h⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  else 0

lemma colL_apply (j : ℕ) (h : j < b) (A : Matrix (Fin a) (Fin b) (ZMod 2)) :
    colL a b j A = A.col ⟨j, h⟩ := by
  unfold colL; rw [dif_pos h]; rfl

noncomputable def tree : ℕ → Submodule (ZMod 2) (Vec a) → DT (Matrix (Fin a) (Fin b) (ZMod 2))
  | 0, V => .leaf (f (finrank (ZMod 2) V))
  | m+1, V => if finrank (ZMod 2) V + (m+1) ≤ r then .leaf (f 0) else
      qmap (qn V) ((piV V).comp (colL a b m))
        (fun y => tree m ((Submodule.span (ZMod 2) {y}).comap (piV V)))

noncomputable def W (A : Matrix (Fin a) (Fin b) (ZMod 2)) (m : ℕ) : Submodule (ZMod 2) (Vec a) :=
  Submodule.span (ZMod 2) ((fun j => colL a b j A) '' Set.Ico m b)

lemma W_succ (A : Matrix (Fin a) (Fin b) (ZMod 2)) (m : ℕ) (hm : m < b) :
    W a b A m = (Submodule.span (ZMod 2) {colL a b m A}) ⊔ W a b A (m+1) := by
  unfold W
  rw [← Submodule.span_insert]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_Ico, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    by_cases hj : j = m
    · left; rw [hj]
    · right; exact ⟨j, ⟨by omega, h2⟩, rfl⟩
  · rintro (rfl | ⟨j, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨m, ⟨le_refl _, hm⟩, rfl⟩
    · exact ⟨j, ⟨by omega, h2⟩, rfl⟩

lemma W_b (A : Matrix (Fin a) (Fin b) (ZMod 2)) : W a b A b = ⊥ := by
  unfold W; rw [Set.Ico_self, Set.image_empty, Submodule.span_empty]

lemma W_zero (A : Matrix (Fin a) (Fin b) (ZMod 2)) :
    Matrix.rank A = finrank (ZMod 2) (W a b A 0) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  unfold W
  have hs : Set.range A.col = (fun j => colL a b j A) '' Set.Ico 0 b := by
    ext v
    simp only [Set.mem_range, Set.mem_image, Set.mem_Ico]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, ⟨Nat.zero_le _, j.isLt⟩, colL_apply a b j.val j.isLt A⟩
    · rintro ⟨j, ⟨_, h2⟩, rfl⟩
      exact ⟨⟨j, h2⟩, (colL_apply a b j h2 A).symm⟩
  rw [hs]

lemma W_rank (A : Matrix (Fin a) (Fin b) (ZMod 2)) (k : ℕ) (hk : k ≤ b) :
    Matrix.rank A ≤ finrank (ZMod 2) (W a b A k) + k := by
  induction k with
  | zero => rw [W_zero]; omega
  | succ k ih =>
    have := ih (by omega)
    rw [W_succ a b A k (by omega)] at this
    have h2 := sup_le1 (colL a b k A) (W a b A (k+1))
    omega

lemma tree_eval (hf : ∀ k, k ≤ r → f k = f 0) (A : Matrix (Fin a) (Fin b) (ZMod 2)) :
    ∀ m, m ≤ b → ∀ V, V = W a b A m → (tree a b r f m V).eval A = f (Matrix.rank A) := by
  intro m
  induction m with
  | zero =>
    intro _ V hV
    simp only [tree, DT.eval]
    rw [hV, W_zero]
  | succ m ih =>
    intro hm V hV
    simp only [tree]
    split_ifs with hs
    · simp only [DT.eval]
      have := W_rank a b A (m+1) hm
      rw [← hV] at this
      exact (hf _ (by omega)).symm
    · rw [qmap_eval]
      apply ih (by omega)
      rw [LinearMap.comp_apply, comap_piV, hV, ← W_succ a b A m (by omega)]

def T (r ρ : ℕ) : ℕ := ∑ k ∈ Finset.Ico ρ (r+1), k

lemma T_big (ρ : ℕ) (h : r < ρ) : T r ρ = 0 := by
  unfold T; rw [Finset.Ico_eq_empty (by omega)]; rfl

lemma T_step (ρ : ℕ) (h : ρ ≤ r) : T r ρ = ρ + T r (ρ+1) := by
  unfold T; rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

lemma T_le (ρ : ℕ) : T r ρ ≤ ρ + T r (ρ+1) := by
  by_cases h : ρ ≤ r
  · rw [T_step r ρ h]
  · rw [T_big r ρ (by omega)]; omega

lemma T_bound (ρ : ℕ) (h : ρ ≤ r) : T r ρ ≤ ρ + (r - ρ) * r := by
  rw [T_step r ρ h]
  have : T r (ρ+1) ≤ (r - ρ) * r := by
    unfold T
    have := Finset.sum_le_card_nsmul (Finset.Ico (ρ+1) (r+1)) (fun k => k) r
      (fun x hx => by simp at hx; omega)
    simpa [Nat.card_Ico] using this
  omega

lemma T_zero : T r 0 = Nat.choose (r+1) 2 := by
  unfold T
  rw [← Finset.range_eq_Ico, Finset.sum_range_id, Nat.choose_two_right]

lemma tree_depth0 (m : ℕ) (V : Submodule (ZMod 2) (Vec a)) (h : finrank (ZMod 2) V + m ≤ r) :
    (tree a b r f m V).depth = 0 := by
  cases m with
  | zero => rfl
  | succ m => simp only [tree]; rw [if_pos h]; rfl

lemma tree_depth (har : r < a) : ∀ m (V : Submodule (ZMod 2) (Vec a)), r < finrank (ZMod 2) V + m →
    (tree a b r f m V).depth + T r (finrank (ZMod 2) V) ≤ a * m := by
  intro m
  induction m with
  | zero =>
    intro V hV
    simp only [tree, DT.depth]
    rw [T_big r _ (by omega)]
    simp
  | succ m ih =>
    intro V hV
    simp only [tree]
    rw [if_neg (by omega)]
    have hq := qn_eq V
    have hVa := fr_le V
    have key : ∀ y, (tree a b r f m ((Submodule.span (ZMod 2) {y}).comap (piV V))).depth + qn V
        + T r (finrank (ZMod 2) V) ≤ a * (m+1) := by
      intro y
      obtain ⟨h1, h2⟩ := comap_piV_fr V y
      set V2 := (Submodule.span (ZMod 2) {y}).comap (piV V)
      have hTle := T_le r (finrank (ZMod 2) V)
      have hmul : a * (m+1) = a * m + a := by ring
      rcases Nat.lt_or_ge (finrank (ZMod 2) V) (finrank (ZMod 2) V2) with hlt | hge
      · have he : finrank (ZMod 2) V2 = finrank (ZMod 2) V + 1 := by omega
        have := ih V2 (by omega)
        rw [he] at this
        omega
      · have he : finrank (ZMod 2) V2 = finrank (ZMod 2) V := by omega
        by_cases hc : r < finrank (ZMod 2) V + m
        · have := ih V2 (by omega)
          rw [he] at this
          omega
        · rw [tree_depth0 a b r f m V2 (by omega)]
          have hTb := T_bound r (finrank (ZMod 2) V) (by omega)
          have hmr : (r - finrank (ZMod 2) V) * r ≤ m * a := by
            apply Nat.mul_le_mul (by omega) (by omega)
          have : a * m = m * a := by ring
          omega
    have h0 := key 0
    have hd := qmap_depth (qn V) ((piV V).comp (colL a b m))
      (fun y => tree a b r f m ((Submodule.span (ZMod 2) {y}).comap (piV V)))
      (a * (m+1) - qn V - T r (finrank (ZMod 2) V)) (fun y => by have := key y; omega)
    omega

lemma upper (hf : ∀ k, k ≤ r → f k = f 0) (hr : r < min a b) (d : ℕ)
    (hd : a * b - Nat.choose (r+1) 2 ≤ d) :
    ∃ (ask : (i : Fin d) → (Fin i.val → ZMod 2) → Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (out : (Fin d → ZMod 2) → Bool),
      ∀ (A : Matrix (Fin a) (Fin b) (ZMod 2)) (z : Fin d → ZMod 2),
        (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) A = z i) →
          out z = f (Matrix.rank A) := by
  have hab : r < a := lt_of_lt_of_le hr (min_le_left _ _)
  have hbb : r < b := lt_of_lt_of_le hr (min_le_right _ _)
  have hdep := tree_depth a b r f hab b ⊥ (by simp; omega)
  rw [finrank_bot, T_zero] at hdep
  obtain ⟨ask, out, h⟩ := DT.compile (tree a b r f b ⊥) d (by omega)
  refine ⟨ask, out, fun A z hz => ?_⟩
  rw [h A z hz]
  exact tree_eval a b r f hf A b le_rfl ⊥ (W_b a b A).symm

end Upper

section Lower
variable {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X] [FiniteDimensional (ZMod 2) X]
variable {d : ℕ}

noncomputable def zseq (ask : (i : Fin d) → (Fin i.val → ZMod 2) → X →ₗ[ZMod 2] ZMod 2) (x : X) :
    ℕ → ZMod 2
  | n => if h : n < d then ask ⟨n, h⟩ (fun j => zseq ask x j.val) x else 0
termination_by n => n
decreasing_by exact j.isLt

noncomputable def zA (ask : (i : Fin d) → (Fin i.val → ZMod 2) → X →ₗ[ZMod 2] ZMod 2) (x : X) :
    Fin d → ZMod 2 := fun i => zseq ask x i.val

lemma zA_cons (ask : (i : Fin d) → (Fin i.val → ZMod 2) → X →ₗ[ZMod 2] ZMod 2) (x : X) (i : Fin d) :
    ask i (fun j => zA ask x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) x = zA ask x i := by
  unfold zA
  rw [zseq, dif_pos i.isLt]

lemma zA_unique (ask : (i : Fin d) → (Fin i.val → ZMod 2) → X →ₗ[ZMod 2] ZMod 2) (x : X)
    (z : Fin d → ZMod 2) (hz : ∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) x = z i) :
    z = zA ask x := by
  have key : ∀ m, ∀ i : Fin d, i.val < m → z i = zA ask x i := by
    intro m
    induction m with
    | zero => intro i hi; omega
    | succ m ih =>
      intro i hi
      have hpre : (fun j : Fin i.val => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) =
          (fun j => zA ask x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) := by
        funext j; exact ih _ (by show j.val < m; have := j.isLt; omega)
      rw [← hz i, hpre, zA_cons]
  funext i; exact key (i.val+1) i (by omega)

lemma fiber_dvd (φ : X →ₗ[ZMod 2] (Fin d → ZMod 2)) (z : Fin d → ZMod 2) [DecidableEq X] :
    2 ^ (finrank (ZMod 2) X - d) ∣ (Finset.univ.filter (fun x => φ x = z)).card := by
  classical
  by_cases hne : ∃ x0, φ x0 = z
  · obtain ⟨x0, hx0⟩ := hne
    have hcard : (Finset.univ.filter (fun x => φ x = z)).card =
        (Finset.univ.filter (fun x => x ∈ LinearMap.ker φ)).card := by
      apply Finset.card_nbij' (fun x => x - x0) (fun k => k + x0)
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
        rw [LinearMap.mem_ker, map_sub, hx, hx0, sub_self]
      · intro k hk
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          LinearMap.mem_ker] at hk ⊢
        rw [map_add, hk, hx0, zero_add]
      · intro x _; simp
      · intro k _; simp
    rw [hcard, ← Fintype.card_subtype]
    have h1 : Fintype.card {x // x ∈ LinearMap.ker φ} = 2 ^ finrank (ZMod 2) (LinearMap.ker φ) := by
      have := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker φ)
      rw [ZMod.card] at this
      convert this
    rw [h1]
    apply pow_dvd_pow
    have h2 := LinearMap.finrank_range_add_finrank_ker φ
    have h3 : finrank (ZMod 2) (LinearMap.range φ) ≤ d := by
      have := Submodule.finrank_le (LinearMap.range φ); rwa [Module.finrank_fin_fun] at this
    omega
  · push_neg at hne
    have : Finset.univ.filter (fun x => φ x = z) = ∅ := by
      ext x; simp [hne x]
    rw [this]; simp

lemma lower_dvd [DecidableEq X] (ask : (i : Fin d) → (Fin i.val → ZMod 2) → X →ₗ[ZMod 2] ZMod 2)
    (out : (Fin d → ZMod 2) → Bool) (g : X → Bool)
    (h : ∀ (x : X) (z : Fin d → ZMod 2),
      (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) x = z i) → out z = g x)
    (c : Bool) :
    2 ^ (finrank (ZMod 2) X - d) ∣ (Finset.univ.filter (fun x => g x ≠ c)).card := by
  classical
  have hs : Finset.univ.filter (fun x => g x ≠ c) = Finset.univ.filter (fun x => out (zA ask x) ≠ c) := by
    apply Finset.filter_congr
    intro x _
    rw [h x (zA ask x) (zA_cons ask x)]
  rw [hs, Finset.card_eq_sum_card_fiberwise (f := zA ask) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.dvd_sum
  intro z _
  rw [Finset.filter_filter]
  let φ : X →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    LinearMap.pi (fun i => ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩))
  by_cases hoz : out z ≠ c
  · have : Finset.univ.filter (fun x => out (zA ask x) ≠ c ∧ zA ask x = z) =
        Finset.univ.filter (fun x => φ x = z) := by
      apply Finset.filter_congr
      intro x _
      constructor
      · rintro ⟨_, rfl⟩
        funext i
        exact zA_cons ask x i
      · intro hx
        have hz : z = zA ask x := by
          apply zA_unique
          intro i
          exact congrFun hx i
        exact ⟨hz ▸ hoz, hz.symm⟩
    rw [this]
    exact fiber_dvd φ z
  · have : Finset.univ.filter (fun x => out (zA ask x) ≠ c ∧ zA ask x = z) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, rfl⟩
      exact hoz h1
    rw [this]; simp

end Lower

section Count
variable (a : ℕ)

noncomputable def rk {b : ℕ} (v : Fin b → Vec a) : ℕ :=
  finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v))

noncomputable def cnt (b k : ℕ) : ℕ := (Finset.univ.filter (fun v : Fin b → Vec a => rk a v = k)).card

lemma rk_cons_mem {b : ℕ} (c : Vec a) (v : Fin b → Vec a)
    (h : c ∈ Submodule.span (ZMod 2) (Set.range v)) :
    rk a (Fin.cons c v : Fin (b+1) → Vec a) = rk a v := by
  unfold rk
  rw [Fin.range_cons, Submodule.span_insert, sup_mem c _ h]

lemma rk_cons_nmem {b : ℕ} (c : Vec a) (v : Fin b → Vec a)
    (h : c ∉ Submodule.span (ZMod 2) (Set.range v)) :
    rk a (Fin.cons c v : Fin (b+1) → Vec a) = rk a v + 1 := by
  unfold rk
  rw [Fin.range_cons, Submodule.span_insert]
  exact sup_nmem c _ h

lemma card_sub (S : Submodule (ZMod 2) (Vec a)) [DecidablePred (fun c => c ∈ S)] :
    (Finset.univ.filter (fun c => c ∈ S)).card = 2 ^ finrank (ZMod 2) S := by
  classical
  rw [← Fintype.card_subtype]
  have := Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [ZMod.card] at this
  convert this

lemma card_vec : (Finset.univ : Finset (Vec a)).card = 2 ^ a := by
  simp [Finset.card_univ, ZMod.card]

lemma inner_count {b : ℕ} (v : Fin b → Vec a) (k : ℕ) :
    (Finset.univ.filter (fun c : Vec a => rk a (Fin.cons c v : Fin (b+1) → Vec a) = k)).card =
      (if rk a v = k then 2 ^ k else 0) + (if rk a v + 1 = k then 2 ^ a - 2 ^ rk a v else 0) := by
  classical
  set S := Submodule.span (ZMod 2) (Set.range v)
  have hS : finrank (ZMod 2) S = rk a v := rfl
  have hfil : Finset.univ.filter (fun c : Vec a => rk a (Fin.cons c v : Fin (b+1) → Vec a) = k) =
      Finset.univ.filter (fun c : Vec a => rk a v + (if c ∈ S then 0 else 1) = k) := by
    apply Finset.filter_congr; intro c _
    by_cases hc : c ∈ S
    · rw [rk_cons_mem a c v hc, if_pos hc, add_zero]
    · rw [rk_cons_nmem a c v hc, if_neg hc]
  rw [hfil]
  by_cases h1 : rk a v = k
  · rw [if_pos h1, if_neg (by omega), add_zero]
    have : Finset.univ.filter (fun c : Vec a => rk a v + (if c ∈ S then 0 else 1) = k) =
        Finset.univ.filter (fun c => c ∈ S) := by
      apply Finset.filter_congr; intro c _; split_ifs with hc <;> simp [hc] <;> omega
    rw [this, card_sub, hS, h1]
  · rw [if_neg h1, zero_add]
    by_cases h2 : rk a v + 1 = k
    · rw [if_pos h2]
      have : Finset.univ.filter (fun c : Vec a => rk a v + (if c ∈ S then 0 else 1) = k) =
          Finset.univ.filter (fun c => ¬ c ∈ S) := by
        apply Finset.filter_congr; intro c _; split_ifs with hc <;> simp [hc] <;> omega
      rw [this]
      have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun c : Vec a => c ∈ S)
      rw [card_sub, card_vec, hS] at h3
      omega
    · rw [if_neg h2]
      have : Finset.univ.filter (fun c : Vec a => rk a v + (if c ∈ S then 0 else 1) = k) = ∅ := by
        ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        split_ifs <;> omega
      rw [this]; rfl

lemma sum_ite_card {b : ℕ} (P : (Fin b → Vec a) → Prop) [DecidablePred P] (c : ℕ) :
    ∑ v : Fin b → Vec a, (if P v then c else 0) = (Finset.univ.filter P).card * c := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

lemma cnt_succ (b k : ℕ) :
    cnt a (b+1) k = ∑ v : Fin b → Vec a,
      (Finset.univ.filter (fun c : Vec a => rk a (Fin.cons c v : Fin (b+1) → Vec a) = k)).card := by
  classical
  unfold cnt
  rw [Finset.card_filter]
  have e := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b+1) => Vec a))
    (fun p => if rk a (Fin.cons p.1 p.2 : Fin (b+1) → Vec a) = k then 1 else 0)
    (fun w => if rk a w = k then 1 else 0) (fun p => rfl)
  rw [← e, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.card_filter]

lemma cnt_succ_zero (b : ℕ) : cnt a (b+1) 0 = cnt a b 0 := by
  rw [cnt_succ]
  simp only [inner_count]
  have : ∀ v : Fin b → Vec a, ((if rk a v = 0 then 2 ^ 0 else 0) +
      (if rk a v + 1 = 0 then 2 ^ a - 2 ^ rk a v else 0)) = if rk a v = 0 then 1 else 0 := by
    intro v; split_ifs <;> simp_all
  simp only [this]
  rw [sum_ite_card]; unfold cnt; ring

lemma cnt_succ_succ (b k : ℕ) :
    cnt a (b+1) (k+1) = cnt a b (k+1) * 2 ^ (k+1) + cnt a b k * (2 ^ a - 2 ^ k) := by
  rw [cnt_succ]
  simp only [inner_count]
  have : ∀ v : Fin b → Vec a, ((if rk a v = k+1 then 2 ^ (k+1) else 0) +
      (if rk a v + 1 = k+1 then 2 ^ a - 2 ^ rk a v else 0)) =
      (if rk a v = k+1 then 2 ^ (k+1) else 0) + (if rk a v = k then 2 ^ a - 2 ^ k else 0) := by
    intro v
    by_cases h : rk a v = k
    · have h' : rk a v ≠ k + 1 := by omega
      simp [h']; simp [h]
    · have h' : rk a v + 1 ≠ k + 1 := by omega
      simp [h, h']
  simp only [this]
  rw [Finset.sum_add_distrib, sum_ite_card, sum_ite_card]
  rfl

lemma cnt_zero (k : ℕ) : cnt a 0 k = if k = 0 then 1 else 0 := by
  unfold cnt
  have hr : ∀ v : Fin 0 → Vec a, rk a v = 0 := by
    intro v; unfold rk; rw [Set.range_eq_empty, Submodule.span_empty, finrank_bot]
  by_cases hk : k = 0
  · rw [if_pos hk]
    have : Finset.univ.filter (fun v : Fin 0 → Vec a => rk a v = k) = Finset.univ := by
      ext v; simp [hr v, hk]
    rw [this]; simp
  · rw [if_neg hk]
    have : Finset.univ.filter (fun v : Fin 0 → Vec a => rk a v = k) = ∅ := by
      ext v; simp [hr v]; omega
    rw [this]; rfl

lemma pow_sub_eq (k : ℕ) : 2 ^ a - 2 ^ k = 2 ^ k * (2 ^ (a - k) - 1) := by
  by_cases h : k ≤ a
  · rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h]
  · have h1 : a - k = 0 := by omega
    rw [h1, pow_zero, Nat.sub_self, mul_zero]
    apply Nat.sub_eq_zero_of_le
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma cnt_val : ∀ b k, ∃ q, cnt a b k = 2 ^ Nat.choose k 2 * q ∧ (k ≤ min a b → Odd q) := by
  intro b
  induction b with
  | zero =>
    intro k
    rw [cnt_zero]
    by_cases hk : k = 0
    · refine ⟨1, ?_, fun _ => odd_one⟩
      rw [if_pos hk, hk]; simp
    · refine ⟨0, ?_, fun h => by simp at h; omega⟩
      rw [if_neg hk]; simp
  | succ b ih =>
    intro k
    cases k with
    | zero =>
      obtain ⟨q, hq, ho⟩ := ih 0
      refine ⟨q, ?_, fun _ => ho (by simp)⟩
      rw [cnt_succ_zero, hq]
    | succ k =>
      obtain ⟨q1, hq1, _⟩ := ih (k+1)
      obtain ⟨q0, hq0, ho0⟩ := ih k
      have hc : Nat.choose (k+1) 2 = Nat.choose k 2 + k := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
      refine ⟨q1 * 2 ^ (k+1) + q0 * (2 ^ (a - k) - 1), ?_, ?_⟩
      · rw [cnt_succ_succ, hq1, hq0, pow_sub_eq a k, hc, pow_add]
        ring
      · intro hk
        have hka : k < a := by
          have := min_le_left a (b+1); omega
        have hkb : k ≤ min a b := by
          have := min_le_right a (b+1); simp only [le_min_iff]; omega
        have hodd0 := ho0 hkb
        have hev : Even (q1 * 2 ^ (k+1)) := by
          apply Nat.even_mul.mpr; right
          exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        have hod : Odd (2 ^ (a - k) - 1) := by
          obtain ⟨t, ht⟩ : ∃ t, a - k = t + 1 := ⟨a - k - 1, by omega⟩
          rw [ht, pow_succ]
          have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
          exact ⟨2 ^ t - 1, by omega⟩
        exact hev.add_odd (Nat.odd_mul.mpr ⟨hodd0, hod⟩)

end Count

section Final
variable {a b : ℕ}

lemma two_mat {p q : ℕ} (X : Matrix (Fin p) (Fin q) (ZMod 2)) : X + X = 0 := by
  ext i j
  show X i j + X i j = 0
  generalize X i j = t
  revert t; decide

lemma N_eq (k : ℕ) :
    (Finset.univ.filter (fun A : Matrix (Fin a) (Fin b) (ZMod 2) => Matrix.rank A = k)).card =
      cnt a b k := by
  unfold cnt
  apply Finset.card_nbij' (fun A => A.col) (fun v => Matrix.of (fun i j => v j i))
  · intro A hA
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hA ⊢
    rw [← hA, Matrix.rank_eq_finrank_span_cols]; rfl
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
    rw [← hv, Matrix.rank_eq_finrank_span_cols]; rfl
  · intro A _; ext i j; rfl
  · intro v _; rfl

def Per (g : ℕ → Bool) (X : Matrix (Fin a) (Fin b) (ZMod 2)) : Prop :=
  ∀ A : Matrix (Fin a) (Fin b) (ZMod 2), g (Matrix.rank (A + X)) = g (Matrix.rank A)

variable {g : ℕ → Bool}

lemma per_zero : Per g (0 : Matrix (Fin a) (Fin b) (ZMod 2)) := by
  intro A; rw [add_zero]

lemma per_add {X Y : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) (hY : Per g Y) :
    Per g (X + Y) := by
  intro A; rw [← add_assoc, hY, hX]

lemma per_left (U : Matrix (Fin a) (Fin a) (ZMod 2)) (hU : U * U = 1)
    {X : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) : Per g (U * X) := by
  intro A
  have hdet : IsUnit U.det := Matrix.isUnit_det_of_right_inverse hU
  have : A + U * X = U * (U * A + X) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [this, Matrix.rank_mul_eq_right_of_isUnit_det U _ hdet, hX,
    Matrix.rank_mul_eq_right_of_isUnit_det U _ hdet]

lemma per_right (V : Matrix (Fin b) (Fin b) (ZMod 2)) (hV : V * V = 1)
    {X : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) : Per g (X * V) := by
  intro A
  have hdet : IsUnit V.det := Matrix.isUnit_det_of_right_inverse hV
  have : A + X * V = (A * V + X) * V := by
    rw [Matrix.add_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [this, Matrix.rank_mul_eq_left_of_isUnit_det V _ hdet, hX,
    Matrix.rank_mul_eq_left_of_isUnit_det V _ hdet]

lemma sq_shear {n : ℕ} (i l : Fin n) (h : i ≠ l) :
    (1 + Matrix.single i l (1 : ZMod 2)) * (1 + Matrix.single i l (1 : ZMod 2)) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.single_mul_single_of_ne (h := Ne.symm h), add_zero, add_assoc,
    two_mat, add_zero]

lemma per_sl_ne (i l : Fin a) (h : i ≠ l) {X : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) :
    Per g (Matrix.single i l (1 : ZMod 2) * X) := by
  have h1 := per_add (per_left _ (sq_shear i l h) hX) hX
  have : (1 + Matrix.single i l (1 : ZMod 2)) * X + X = Matrix.single i l (1 : ZMod 2) * X := by
    rw [Matrix.add_mul, Matrix.one_mul, add_comm X, add_assoc, two_mat, add_zero]
  rwa [this] at h1

lemma per_sr_ne (i l : Fin b) (h : i ≠ l) {X : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) :
    Per g (X * Matrix.single i l (1 : ZMod 2)) := by
  have h1 := per_add (per_right _ (sq_shear i l h) hX) hX
  have : X * (1 + Matrix.single i l (1 : ZMod 2)) + X = X * Matrix.single i l (1 : ZMod 2) := by
    rw [Matrix.mul_add, Matrix.mul_one, add_comm X, add_assoc, two_mat, add_zero]
  rwa [this] at h1

lemma per_sl (i l : Fin a) {X : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) :
    Per g (Matrix.single i l (1 : ZMod 2) * X) := by
  by_cases h : i = l
  · subst h
    by_cases hk : ∃ k : Fin a, k ≠ i
    · obtain ⟨k, hk⟩ := hk
      have := per_sl_ne i k (Ne.symm hk) (per_sl_ne k i hk hX)
      rwa [← Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at this
    · push_neg at hk
      have : Matrix.single i i (1 : ZMod 2) = 1 := by
        ext p q
        rw [hk p, hk q]; simp
      rw [this, Matrix.one_mul]; exact hX
  · exact per_sl_ne i l h hX

lemma per_sr (i l : Fin b) {X : Matrix (Fin a) (Fin b) (ZMod 2)} (hX : Per g X) :
    Per g (X * Matrix.single i l (1 : ZMod 2)) := by
  by_cases h : i = l
  · subst h
    by_cases hk : ∃ k : Fin b, k ≠ i
    · obtain ⟨k, hk⟩ := hk
      have := per_sr_ne k i hk (per_sr_ne i k (Ne.symm hk) hX)
      rwa [Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at this
    · push_neg at hk
      have : Matrix.single i i (1 : ZMod 2) = 1 := by
        ext p q
        rw [hk p, hk q]; simp
      rw [this, Matrix.mul_one]; exact hX
  · exact per_sr_ne i l h hX

lemma per_all {K : Matrix (Fin a) (Fin b) (ZMod 2)} (hK : K ≠ 0) (hP : Per g K)
    (B : Matrix (Fin a) (Fin b) (ZMod 2)) : Per g B := by
  obtain ⟨l, m, hlm⟩ : ∃ l m, K l m ≠ 0 := by
    by_contra hc; push_neg at hc; exact hK (by ext l m; exact hc l m)
  have hlm1 : K l m = 1 := by rcases z2 (K l m) with h | h; exact absurd h hlm; exact h
  have hE : ∀ i j, Per g (Matrix.single i j (1 : ZMod 2) : Matrix (Fin a) (Fin b) (ZMod 2)) := by
    intro i j
    have := per_sr m j (per_sl i l hP)
    rwa [Matrix.single_mul_mul_single, hlm1, mul_one, mul_one] at this
  rw [Matrix.matrix_eq_sum_single B]
  apply Finset.sum_induction _ (Per g) (fun _ _ => per_add) per_zero
  intro i _
  apply Finset.sum_induction _ (Per g) (fun _ _ => per_add) per_zero
  intro j _
  rcases z2 (B i j) with h | h
  · rw [h, Matrix.single_zero]; exact per_zero
  · rw [h]; exact hE i j

lemma finrank_M : finrank (ZMod 2) (Matrix (Fin a) (Fin b) (ZMod 2)) = a * b := by
  rw [Module.finrank_matrix]; simp

lemma exists_rank (k : ℕ) (hk : k ≤ min a b) :
    ∃ B : Matrix (Fin a) (Fin b) (ZMod 2), Matrix.rank B = k := by
  obtain ⟨q, hq, ho⟩ := cnt_val a b k
  have hpos : 0 < cnt a b k := by
    rw [hq]
    apply Nat.mul_pos (pow_pos (by norm_num) _)
    obtain ⟨t, ht⟩ := ho hk; omega
  rw [← N_eq] at hpos
  obtain ⟨B, hB⟩ := Finset.card_pos.mp hpos
  exact ⟨B, (Finset.mem_filter.mp hB).2⟩

lemma batch_lower (r d : ℕ) (f : ℕ → Bool) (hr : r < min a b) (hne : f (r+1) ≠ f 0)
    (ask : Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2)) (out : (Fin d → ZMod 2) → Bool)
    (h : ∀ A, out (ask A) = f (Matrix.rank A)) : a * b ≤ d := by
  by_contra hlt
  push_neg at hlt
  have hker : LinearMap.ker ask ≠ ⊥ := by
    intro hb
    have h1 := LinearMap.finrank_range_add_finrank_ker ask
    have h2 : finrank (ZMod 2) (LinearMap.range ask) ≤ d := by
      have := Submodule.finrank_le (LinearMap.range ask); rwa [Module.finrank_fin_fun] at this
    rw [hb, finrank_bot, finrank_M] at h1
    omega
  obtain ⟨K, hK, hK0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hP : Per f K := by
    intro A
    rw [← h, ← h, map_add, LinearMap.mem_ker.mp hK, add_zero]
  obtain ⟨B, hB⟩ := exists_rank (a := a) (b := b) (r+1) (by omega)
  have := per_all hK0 hP B 0
  rw [zero_add, hB, Matrix.rank_zero] at this
  exact hne this

lemma batch_upper (d : ℕ) (f : ℕ → Bool) (hab : 0 < a * b) (hd : a * b ≤ d) :
    ∃ (ask : Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2)) (out : (Fin d → ZMod 2) → Bool),
      ∀ A, out (ask A) = f (Matrix.rank A) := by
  classical
  let e := LinearEquiv.ofFinrankEq (R := ZMod 2) (Matrix (Fin a) (Fin b) (ZMod 2)) (Fin (a*b) → ZMod 2)
    (by rw [finrank_M, Module.finrank_fin_fun])
  let gs : Fin d → Fin (a*b) := fun i => ⟨i.val % (a*b), Nat.mod_lt _ hab⟩
  have hgs : Function.Surjective gs := by
    intro j
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    apply Fin.ext; simp [gs, Nat.mod_eq_of_lt j.isLt]
  let ask := (LinearMap.funLeft (ZMod 2) (ZMod 2) gs).comp e.toLinearMap
  have hinj : Function.Injective ask := by
    intro x y hxy
    exact e.injective (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) gs hgs hxy)
  refine ⟨ask, fun w => if hw : ∃ A, ask A = w then f (Matrix.rank hw.choose) else false, ?_⟩
  intro A
  have hw : ∃ B, ask B = ask A := ⟨A, rfl⟩
  show (if hw : ∃ B, ask B = ask A then f (Matrix.rank hw.choose) else false) = f (Matrix.rank A)
  rw [dif_pos hw, hinj hw.choose_spec]

lemma adaptive_lower (r d : ℕ) (f : ℕ → Bool) (hr : r < min a b)
    (hf : ∀ k, k ≤ r → f k = f 0) (hne : f (r+1) ≠ f 0)
    (ask : (i : Fin d) → (Fin i.val → ZMod 2) → Matrix (Fin a) (Fin b) (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (out : (Fin d → ZMod 2) → Bool)
    (h : ∀ (A : Matrix (Fin a) (Fin b) (ZMod 2)) (z : Fin d → ZMod 2),
      (∀ i, ask i (fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) A = z i) → out z = f (Matrix.rank A)) :
    a * b - Nat.choose (r+1) 2 ≤ d := by
  classical
  by_contra hlt
  push_neg at hlt
  have hra : r + 1 ≤ a := by have := min_le_left a b; omega
  have hdv := lower_dvd ask out (fun A => f (Matrix.rank A)) h (f 0)
  rw [finrank_M] at hdv
  set C := Nat.choose (r+1) 2
  have hdv2 : 2 ^ (C+1) ∣ (Finset.univ.filter
      (fun A : Matrix (Fin a) (Fin b) (ZMod 2) => f (Matrix.rank A) ≠ f 0)).card :=
    (pow_dvd_pow 2 (by omega)).trans hdv
  set s := Finset.univ.filter (fun A : Matrix (Fin a) (Fin b) (ZMod 2) => f (Matrix.rank A) ≠ f 0)
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun A : Matrix (Fin a) (Fin b) (ZMod 2) =>
    Matrix.rank A) (s := s) (t := Finset.range (a+1))
    (fun A _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Matrix.rank_le_height A)))
  have hterm : ∀ k, (s.filter (fun A => Matrix.rank A = k)).card =
      if f k ≠ f 0 then cnt a b k else 0 := by
    intro k
    rw [Finset.filter_filter, ← N_eq]
    split_ifs with hk
    · congr 1; apply Finset.filter_congr
      intro A _; constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2; exact ⟨h2 ▸ hk, h2⟩
    · rw [Finset.card_eq_zero]
      ext A; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro h1 h2; exact hk (h2 ▸ h1)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : r + 1 < a + 1))] at hsum
  have hrest : 2 ^ (C+1) ∣ ∑ k ∈ (Finset.range (a+1)).erase (r+1),
      (s.filter (fun A => Matrix.rank A = k)).card := by
    apply Finset.dvd_sum
    intro k hk
    rw [hterm k]
    have hk1 : k ≠ r + 1 := (Finset.mem_erase.mp hk).1
    by_cases hkr : k ≤ r
    · rw [if_neg (by rw [hf k hkr]; exact fun h => h rfl)]; exact dvd_zero _
    · split_ifs
      · obtain ⟨q, hq, _⟩ := cnt_val a b k
        rw [hq]
        apply Dvd.dvd.mul_right
        apply pow_dvd_pow
        have h1 : Nat.choose (r+2) 2 ≤ Nat.choose k 2 := Nat.choose_le_choose 2 (by omega)
        have h2 : Nat.choose (r+2) 2 = Nat.choose (r+1) 2 + (r+1) := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
        omega
      · exact dvd_zero _
  rw [hterm (r+1), if_pos hne] at hsum
  rw [hsum] at hdv2
  have hmain := (Nat.dvd_add_left hrest).mp hdv2
  obtain ⟨q, hq, ho⟩ := cnt_val a b (r+1)
  rw [hq, pow_succ] at hmain
  have h2q : 2 ∣ q := (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num) _)).mp hmain
  obtain ⟨t, ht⟩ := ho (by omega)
  omega

end Final

end PEqualNP.Outside.L_lib_1087

theorem PEqualNP.Outside.L_lib_1087 : ∀ (a b r d : ℕ) (f : ℕ → Bool), r < min a b →
  (∀ k, k ≤ r → f k = f 0) → f (r+1) ≠ f 0 →
  let F := ZMod 2
  let M := Matrix (Fin a) (Fin b) F
  let W := Fin d → F
  let past := fun (z : W) (i : Fin d) (j : Fin i.val) => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  let adaptive := ∃ (ask : (i : Fin d) → (Fin i.val → F) → M →ₗ[F] F) (out : W → Bool),
    ∀ (A : M) (z : W), (∀ i, ask i (past z i) A = z i) → out z = f (Matrix.rank A)
  let batch := ∃ (ask : M →ₗ[F] W) (out : W → Bool), ∀ A, out (ask A) = f (Matrix.rank A)
  (adaptive ↔ a*b - Nat.choose (r+1) 2 ≤ d) ∧ (batch ↔ a*b ≤ d) := by
  intro a b r d f hr hf hne
  dsimp only
  have ha : 0 < a := by have := min_le_left a b; omega
  have hb : 0 < b := by have := min_le_right a b; omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨ask, out, h⟩
    exact PEqualNP.Outside.L_lib_1087.adaptive_lower r d f hr hf hne ask out h
  · intro hd
    exact PEqualNP.Outside.L_lib_1087.upper a b r f hf hr d hd
  · rintro ⟨ask, out, h⟩
    exact PEqualNP.Outside.L_lib_1087.batch_lower r d f hr hne ask out h
  · intro hd
    exact PEqualNP.Outside.L_lib_1087.batch_upper d f (Nat.mul_pos ha hb) hd

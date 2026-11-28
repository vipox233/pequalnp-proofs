import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33672

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Represents
open scoped Matrix

abbrev F2 := ZMod 2

def b2f (b : Bool) : F2 := if b then 1 else 0

lemma f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> decide

lemma b2f_injective : Function.Injective b2f := by
  intro a b h
  cases a <;> cases b <;> simp [b2f] at h ⊢

def sgn (x : F2) : ℤ := if x = 0 then 1 else -1

lemma sgn_zero : sgn 0 = 1 := rfl
lemma sgn_one : sgn 1 = -1 := rfl

lemma sgn_add (x y : F2) : sgn (x + y) = sgn x * sgn y := by
  fin_cases x <;> fin_cases y <;> decide

lemma sgn_mul_self (x : F2) : sgn x * sgn x = 1 := by
  fin_cases x <;> decide

lemma abs_sgn (x : F2) : |sgn x| = 1 := by
  fin_cases x <;> decide

lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → F2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, sgn_add, ih]

lemma sum_sgn_fin {n : ℕ} (c : Fin n → F2) :
    (∑ x : Fin n → F2, sgn (∑ i, c i * x i)) = if c = 0 then (2 ^ n : ℤ) else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [sgn_zero, Fintype.card_pi, ZMod.card]
  · rw [if_neg hc]
    have hex : ∃ i, c i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc (funext h)
    obtain ⟨i0, hi0⟩ := hex
    have hc1 : c i0 = 1 := (f2_eq_zero_or_one (c i0)).resolve_left hi0
    let inv : (Fin n → F2) ≃ (Fin n → F2) :=
      { toFun := fun x => Function.update x i0 (x i0 + 1)
        invFun := fun x => Function.update x i0 (x i0 + 1)
        left_inv := fun x => by
          ext j
          by_cases hj : j = i0
          · subst hj; simp [add_assoc, f2_add_self]
          · simp [Function.update_of_ne hj]
        right_inv := fun x => by
          ext j
          by_cases hj : j = i0
          · subst hj; simp [add_assoc, f2_add_self]
          · simp [Function.update_of_ne hj] }
    have hflip : ∀ x : Fin n → F2,
        sgn (∑ i, c i * inv x i) = -sgn (∑ i, c i * x i) := by
      intro x
      have hsum : (∑ i, c i * inv x i) = (∑ i, c i * x i) + 1 := by
        have h1 : ∀ i, c i * inv x i = c i * x i + (if i = i0 then 1 else 0) := by
          intro i
          by_cases hi : i = i0
          · subst hi; simp [inv, hc1]
          · simp [inv, Function.update_of_ne hi, hi]
        simp_rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hsum, sgn_add, sgn_one, mul_neg_one]
    have hS : (∑ x : Fin n → F2, sgn (∑ i, c i * x i)) =
        ∑ x : Fin n → F2, sgn (∑ i, c i * inv x i) :=
      (Equiv.sum_comp inv _).symm
    have hneg : (∑ x : Fin n → F2, sgn (∑ i, c i * inv x i)) =
        -(∑ x : Fin n → F2, sgn (∑ i, c i * x i)) := by
      simp_rw [hflip, Finset.sum_neg_distrib]
    omega

def nonlinearG (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsList (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinearG g).toNat])
    (List.replicate w 0)

def depthC (w : ℕ) (Q : Circuit) : ℕ :=
  (depthsList w Q.gates).getD Q.output 0

lemma bool_fun2_poly (f : Bool → Bool → Bool) (u v : Bool) :
    b2f (f u v) =
      b2f (f false false) +
      (b2f (f true false) + b2f (f false false)) * b2f u +
      (b2f (f false true) + b2f (f false false)) * b2f v +
      b2f (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2f u * b2f v) := by
  cases u <;> cases v <;> cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

lemma bool_fun1_poly (f : Bool → Bool) (u : Bool) :
    b2f (f u) = b2f (f false) + (b2f (f true) + b2f (f false)) * b2f u := by
  cases u <;> cases h0 : f false <;> cases h1 : f true <;> decide

def deltaF {a b : ℕ} (P : Fin (a + 2) → Fin (b + 2) → F2) :
    Matrix (Fin (a + 1)) (Fin (b + 1)) F2 :=
  fun x y => P x.succ y.succ + P x.succ 0 + P 0 y.succ + P 0 0

def deltaMat {a b : ℕ} (P : Fin (a + 2) → Fin (b + 2) → Bool) :
    Matrix (Fin (a + 1)) (Fin (b + 1)) F2 :=
  deltaF (fun x y => b2f (P x y))

lemma deltaF_add {a b : ℕ} (P Q : Fin (a + 2) → Fin (b + 2) → F2) :
    deltaF (fun x y => P x y + Q x y) = deltaF P + deltaF Q := by
  ext x y; simp [deltaF]; ring

lemma deltaF_smul {a b : ℕ} (c : F2) (P : Fin (a + 2) → Fin (b + 2) → F2) :
    deltaF (fun x y => c * P x y) = c • deltaF P := by
  ext x y; simp [deltaF]; ring

lemma deltaF_const {a b : ℕ} (c : F2) :
    deltaF (fun (_ : Fin (a + 2)) (_ : Fin (b + 2)) => c) = 0 := by
  ext x y
  simp only [deltaF, Matrix.zero_apply]
  linear_combination f2_add_self c + f2_add_self c

lemma deltaF_sep {a b : ℕ} (f : Fin (a + 2) → F2) (g : Fin (b + 2) → F2) :
    deltaF (fun x y => f x + g y) = 0 := by
  ext x y
  simp only [deltaF, Matrix.zero_apply]
  linear_combination f2_add_self (f x.succ) + f2_add_self (f 0) +
    f2_add_self (g y.succ) + f2_add_self (g 0)

def outerMat {m n : ℕ} (u : Fin m → F2) (v : Fin n → F2) : Matrix (Fin m) (Fin n) F2 :=
  fun i j => u i * v j

lemma rank_outerMat_le_one {m n : ℕ} (u : Fin m → F2) (v : Fin n → F2) :
    (outerMat u v).rank ≤ 1 := by
  rw [Matrix.rank]
  have hsub : LinearMap.range (outerMat u v).mulVecLin ≤ Submodule.span F2 {u} := by
    rintro _ ⟨x, rfl⟩
    have hmv : (outerMat u v).mulVec x = (∑ j, v j * x j) • u := by
      ext i
      simp [Matrix.mulVec, dotProduct, outerMat, Finset.mul_sum, mul_left_comm, mul_comm]
    rw [Matrix.mulVecLin_apply, hmv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  exact (Submodule.finrank_mono hsub).trans ((finrank_span_le_card ({u} : Set (Fin m → F2))).trans (by simp))

lemma rank_add_le' {m n : ℕ} (A B : Matrix (Fin m) (Fin n) F2) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hle := Submodule.finrank_mono hsub
  omega

lemma rank_sum_le' {m n : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin m) (Fin n) F2) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rank_add_le' _ _).trans (Nat.add_le_add_left ih _)

lemma rank_smul_le' {m n : ℕ} (c : F2) (A : Matrix (Fin m) (Fin n) F2) :
    (c • A).rank ≤ A.rank := by
  rcases f2_eq_zero_or_one c with rfl | rfl <;> simp

lemma deltaF_mul_sep {a b : ℕ} (f1 f2 : Fin (a + 2) → F2) (g1 g2 : Fin (b + 2) → F2) :
    (deltaF (fun x y => (f1 x + g1 y) * (f2 x + g2 y))).rank ≤ 2 := by
  have heq : (fun x y => (f1 x + g1 y) * (f2 x + g2 y)) =
      fun x y => (f1 x * f2 x + g1 y * g2 y) + (f1 x * g2 y + f2 x * g1 y) := by
    ext x y; ring
  rw [heq, deltaF_add, deltaF_sep, zero_add]
  have h1 : deltaF (fun x y => f1 x * g2 y + f2 x * g1 y) =
      outerMat (fun x => f1 x.succ + f1 0) (fun y => g2 y.succ + g2 0) +
      outerMat (fun x => f2 x.succ + f2 0) (fun y => g1 y.succ + g1 0) := by
    ext x y; simp [deltaF, outerMat]; ring
  rw [h1]
  exact (rank_add_le' _ _).trans
    (Nat.add_le_add (rank_outerMat_le_one _ _) (rank_outerMat_le_one _ _))

lemma foldl_append_step {α β : Type*} (f : List α → β → α) (init : List α) (l : List β) (g : β) :
    (l ++ [g]).foldl (fun w x => w ++ [f w x]) init =
      let w := l.foldl (fun w x => w ++ [f w x]) init
      w ++ [f w g] := by
  simp [List.foldl_append]

lemma foldl_append_length {α β : Type*} (f : List α → β → α) (init : List α) (l : List β) :
    (l.foldl (fun w x => w ++ [f w x]) init).length = init.length + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [foldl_append_step]; simp [ih]; omega

lemma foldl_append_getD_lt {α β : Type*} (d : α) (f : List α → β → α) (init : List α)
    (l1 l2 : List β) (i : ℕ) (hi : i < init.length + l1.length) :
    ((l1 ++ l2).foldl (fun w x => w ++ [f w x]) init).getD i d =
      (l1.foldl (fun w x => w ++ [f w x]) init).getD i d := by
  induction l2 using List.reverseRecOn with
  | nil => simp
  | append_singleton l2 g ih =>
    rw [← List.append_assoc, foldl_append_step]
    have hlen : ((l1 ++ l2).foldl (fun w x => w ++ [f w x]) init).length =
        init.length + l1.length + l2.length := by
      rw [foldl_append_length, List.length_append]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    exact ih

lemma foldl_append_getD_eq {α β : Type*} (d : α) (f : List α → β → α) (init : List α)
    (l : List β) (g : β) :
    ((l ++ [g]).foldl (fun w x => w ++ [f w x]) init).getD (init.length + l.length) d =
      f (l.foldl (fun w x => w ++ [f w x]) init) g := by
  rw [foldl_append_step]
  have hlen : (l.foldl (fun w x => w ++ [f w x]) init).length = init.length + l.length :=
    foldl_append_length f init l
  rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma depthsList_length (w : ℕ) (gs : List Gate) : (depthsList w gs).length = w + gs.length := by
  have := foldl_append_length (fun ds (g : Gate) =>
    (g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinearG g).toNat) (List.replicate w 0) gs
  simpa [depthsList] using this

lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  simpa [Circuit.wires] using foldl_append_length
    (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)) x gs

def wireVal {a b : ℕ} (gs : List Gate) (i : ℕ) : Fin (a + 2) → Fin (b + 2) → F2 :=
  fun x y => b2f ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i false)

lemma wireVal_append_lt {a b : ℕ} (gs1 gs2 : List Gate) (i : ℕ)
    (hi : i < a + 2 + (b + 2) + gs1.length) :
    wireVal (a := a) (b := b) (gs1 ++ gs2) i = wireVal gs1 i := by
  ext x y
  simp only [wireVal, Circuit.wires]
  have hlen : (oneEach x y).length = a + 2 + (b + 2) := by simp [oneEach]; omega
  rw [foldl_append_getD_lt false _ (oneEach x y) gs1 gs2 i (by omega)]

lemma depthsList_append_lt (n : ℕ) (gs1 gs2 : List Gate) (i : ℕ) (hi : i < n + gs1.length) :
    (depthsList n (gs1 ++ gs2)).getD i 0 = (depthsList n gs1).getD i 0 := by
  simp only [depthsList]
  have hlen : (List.replicate n 0).length = n := List.length_replicate
  exact foldl_append_getD_lt 0 _ (List.replicate n 0) gs1 gs2 i (by omega)

lemma wireVal_snoc_eq {a b : ℕ} (gs : List Gate) (g : Gate) (x : Fin (a + 2)) (y : Fin (b + 2)) :
    wireVal (gs ++ [g]) (a + 2 + (b + 2) + gs.length) x y =
      b2f (g.op.eval (g.inputs.map fun h => (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h false)) := by
  simp only [wireVal, Circuit.wires]
  have hlen : (oneEach x y).length = a + 2 + (b + 2) := by simp [oneEach]; omega
  rw [← hlen, foldl_append_getD_eq]

lemma depthsList_snoc_eq (n : ℕ) (gs : List Gate) (g : Gate) :
    (depthsList n (gs ++ [g])).getD (n + gs.length) 0 =
      (g.inputs.map (fun h => (depthsList n gs).getD h 0)).foldr max 0 + (nonlinearG g).toNat := by
  simp only [depthsList]
  have h := foldl_append_getD_eq 0
    (fun ds (g : Gate) => (g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinearG g).toNat)
    (List.replicate n 0) gs g
  simpa only [List.length_replicate] using h

lemma oneEach_getD_left {n m : ℕ} (x : Fin n) (y : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach x y).getD i false = decide (⟨i, hi⟩ = x) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi]),
    List.getElem?_ofFn, dif_pos hi]
  rfl

lemma oneEach_getD_right {n m : ℕ} (x : Fin n) (y : Fin m) (j : ℕ) (hj : j < m) :
    (oneEach x y).getD (n + j) false = decide (⟨j, hj⟩ = y) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
    List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos hj]
  rfl

lemma ok_imp_rank_le {a b t : ℕ} (P : Fin (a + 2) → Fin (b + 2) → Bool)
    (Q : Circuit)
    (hfan : ∀ g ∈ Q.gates, g.inputs.length ≤ 2)
    (hrep : Represents P Q)
    (hdep : depthC (a + 2 + (b + 2)) Q ≤ 1)
    (hcnt : Q.gates.countP nonlinearG ≤ t) :
    (deltaMat P).rank ≤ 2 * t := by
  set n := a + 2 + (b + 2)
  have hmain : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (∀ j : Fin gs.length, nonlinearG gs[j] = true →
        (depthsList n gs).getD (n + j.val) 0 ≤ 1 →
        (deltaF (wireVal (a := a) (b := b) gs (n + j.val))).rank ≤ 2) ∧
      (∀ i : ℕ,
        ((depthsList n gs).getD i 0 = 0 →
          ∃ f : Fin (a + 2) → F2, ∃ g : Fin (b + 2) → F2,
            ∀ x y, wireVal gs i x y = f x + g y) ∧
        ((depthsList n gs).getD i 0 ≤ 1 →
          ∃ c : Fin gs.length → F2,
            (∀ j, c j ≠ 0 → nonlinearG gs[j] = true ∧ (depthsList n gs).getD (n + j.val) 0 ≤ 1) ∧
            deltaF (wireVal (a := a) (b := b) gs i) =
              ∑ j : Fin gs.length, c j • deltaF (wireVal gs (n + j.val)))) := by
    intro gs hgs
    induction gs using List.reverseRecOn with
    | nil =>
      refine ⟨fun j => Fin.elim0 j, fun i => ?_⟩
      have hsep : ∃ f : Fin (a + 2) → F2, ∃ g : Fin (b + 2) → F2,
          ∀ x y, wireVal [] i x y = f x + g y := by
        by_cases h1 : i < a + 2
        · refine ⟨fun x => if x.val = i then 1 else 0, fun _ => 0, fun x y => ?_⟩
          simp only [wireVal, Circuit.wires, List.foldl_nil, add_zero]
          rw [oneEach_getD_left x y i h1]
          by_cases he : x.val = i
          · have : (⟨i, h1⟩ : Fin (a + 2)) = x := Fin.ext he.symm
            simp [he, this, b2f]
          · have : (⟨i, h1⟩ : Fin (a + 2)) ≠ x := fun h => he (congrArg Fin.val h).symm
            simp [he, this, b2f]
        · by_cases h2 : i < n
          · refine ⟨fun _ => 0, fun y => if a + 2 + y.val = i then 1 else 0, fun x y => ?_⟩
            have hsub : i - (a + 2) < b + 2 := by omega
            have hi_eq : i = (a + 2) + (i - (a + 2)) := by omega
            simp only [wireVal, Circuit.wires, List.foldl_nil, zero_add]
            conv_lhs => rw [hi_eq]
            rw [oneEach_getD_right x y (i - (a + 2)) hsub]
            by_cases he : a + 2 + y.val = i
            · have : (⟨i - (a + 2), hsub⟩ : Fin (b + 2)) = y := by apply Fin.ext; dsimp; omega
              simp [he, this, b2f]
            · have : (⟨i - (a + 2), hsub⟩ : Fin (b + 2)) ≠ y := fun h => he (by
                have := congrArg Fin.val h; dsimp at this; omega)
              simp [he, this, b2f]
          · refine ⟨fun _ => 0, fun _ => 0, fun x y => ?_⟩
            simp only [wireVal, Circuit.wires, List.foldl_nil, add_zero]
            rw [List.getD_eq_default _ _ (by simp [oneEach, n]; omega)]
            rfl
      obtain ⟨f, g, hfg⟩ := hsep
      refine ⟨fun _ => ⟨f, g, hfg⟩, fun _ => ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, ?_⟩⟩
      have : wireVal (a := a) (b := b) [] i = fun x y => f x + g y := by
        ext x y; exact hfg x y
      rw [this, deltaF_sep]
      symm
      exact Finset.sum_eq_zero fun x _ => Fin.elim0 x
    | append_singleton gs gate ih =>
      obtain ⟨ih_rk, ih_w⟩ := ih (fun g hg => hgs g (List.mem_append_left _ hg))
      have hgate_len : gate.inputs.length ≤ 2 := hgs gate (by simp)
      have hnew_d := depthsList_snoc_eq n gs gate
      have hlift_c : ∀ (c : Fin gs.length → F2),
          (∀ j, c j ≠ 0 → nonlinearG gs[j] = true ∧ (depthsList n gs).getD (n + j.val) 0 ≤ 1) →
          ∃ c' : Fin (gs ++ [gate]).length → F2,
            (∀ j, c' j ≠ 0 → nonlinearG (gs ++ [gate])[j] = true ∧
              (depthsList n (gs ++ [gate])).getD (n + j.val) 0 ≤ 1) ∧
            ∑ j : Fin (gs ++ [gate]).length, c' j • deltaF (wireVal (a := a) (b := b) (gs ++ [gate]) (n + j.val)) =
              ∑ j : Fin gs.length, c j • deltaF (wireVal gs (n + j.val)) := by
        intro c hc
        refine ⟨fun j => if hj : j.val < gs.length then c ⟨j.val, hj⟩ else 0, ?_, ?_⟩
        · intro j hj
          have hlt : j.val < gs.length := by
            by_contra hge
            simp [hge] at hj
          simp only [dif_pos hlt] at hj
          have h1 := hc ⟨j.val, hlt⟩ hj
          simp only [Fin.getElem_fin] at h1 ⊢
          rw [List.getElem_append_left hlt, depthsList_append_lt n gs [gate] (n + j.val) (by omega)]
          exact h1
        · have hcast_len : (gs ++ [gate]).length = gs.length + 1 := by simp
          clear hc
          have heq_sum : ∀ (f1 : Fin (gs ++ [gate]).length → Matrix (Fin (a + 1)) (Fin (b + 1)) F2),
              (∑ j : Fin (gs ++ [gate]).length, f1 j) =
                (∑ j : Fin gs.length, f1 ⟨j.val, by simp⟩) + f1 ⟨gs.length, by simp⟩ := by
            intro f1
            let e : Fin (gs.length + 1) ≃ Fin (gs ++ [gate]).length := finCongr hcast_len.symm
            rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
            rfl
          rw [heq_sum]
          simp only [lt_irrefl, ↓reduceDIte, zero_smul, add_zero]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [j.isLt, ↓reduceDIte]
          rw [wireVal_append_lt gs [gate] (n + j.val) (by omega)]
      have hnew_rk : nonlinearG gate = true →
          (depthsList n (gs ++ [gate])).getD (n + gs.length) 0 ≤ 1 →
          (deltaF (wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length))).rank ≤ 2 := by
        intro hnl hd
        rw [hnew_d, hnl] at hd
        have h2 : gate.inputs.length = 2 := by
          simp only [nonlinearG, Bool.and_eq_true, beq_iff_eq] at hnl
          exact hnl.1
        rcases hl : gate.inputs with _ | ⟨h0, _ | ⟨h1, _ | ⟨_, _⟩⟩⟩ <;> simp [hl] at h2
        rw [hl] at hd
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hd
        have hd0 : (depthsList n gs).getD h0 0 = 0 := by omega
        have hd1 : (depthsList n gs).getD h1 0 = 0 := by omega
        obtain ⟨f0, g0, hf0⟩ := (ih_w h0).1 hd0
        obtain ⟨f1, g1, hf1⟩ := (ih_w h1).1 hd1
        have hpoly : ∀ x y, wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) x y =
            b2f (gate.op.eval [false, false]) +
            (b2f (gate.op.eval [true, false]) + b2f (gate.op.eval [false, false])) * (f0 x + g0 y) +
            (b2f (gate.op.eval [false, true]) + b2f (gate.op.eval [false, false])) * (f1 x + g1 y) +
            1 * ((f0 x + g0 y) * (f1 x + g1 y)) := by
          intro x y
          rw [wireVal_snoc_eq, hl]
          simp only [List.map_cons, List.map_nil]
          have hp := bool_fun2_poly (fun u v => gate.op.eval [u, v])
            ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h0 false)
            ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h1 false)
          have hx : xor (xor (gate.op.eval [false, false]) (gate.op.eval [false, true]))
              (xor (gate.op.eval [true, false]) (gate.op.eval [true, true])) = true := by
            simp only [nonlinearG, Bool.and_eq_true] at hnl; exact hnl.2
          rw [hx] at hp
          have h0e : b2f ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h0 false) = f0 x + g0 y := hf0 x y
          have h1e : b2f ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h1 false) = f1 x + g1 y := hf1 x y
          rw [h0e, h1e] at hp
          exact hp
        have heq_w : wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) =
            fun x y =>
              ((b2f (gate.op.eval [false, false]) +
                (b2f (gate.op.eval [true, false]) + b2f (gate.op.eval [false, false])) * f0 x +
                (b2f (gate.op.eval [false, true]) + b2f (gate.op.eval [false, false])) * f1 x) +
               ((b2f (gate.op.eval [true, false]) + b2f (gate.op.eval [false, false])) * g0 y +
                (b2f (gate.op.eval [false, true]) + b2f (gate.op.eval [false, false])) * g1 y)) +
              (f0 x + g0 y) * (f1 x + g1 y) := by
          ext x y; rw [hpoly x y]; ring
        rw [heq_w, deltaF_add, deltaF_sep, zero_add]
        exact deltaF_mul_sep f0 f1 g0 g1
      constructor
      · intro j hj hd
        simp only [Fin.getElem_fin] at hj
        rcases Nat.lt_or_eq_of_le (show j.val ≤ gs.length by have := j.isLt; simp at this; omega) with hlt | heq
        · rw [List.getElem_append_left hlt] at hj
          rw [depthsList_append_lt n gs [gate] (n + j.val) (by omega)] at hd
          rw [wireVal_append_lt gs [gate] (n + j.val) (by omega)]
          exact ih_rk ⟨j.val, hlt⟩ hj hd
        · simp only [heq] at hj hd ⊢
          rw [List.getElem_append_right le_rfl] at hj
          simp only [Nat.sub_self, List.getElem_cons_zero] at hj
          exact hnew_rk hj hd
      · intro i
        rcases Nat.lt_trichotomy i (n + gs.length) with hlt | heq | hgt
        · rw [depthsList_append_lt n gs [gate] i hlt, wireVal_append_lt gs [gate] i hlt]
          refine ⟨(ih_w i).1, fun hd => ?_⟩
          obtain ⟨c, hc, hsum⟩ := (ih_w i).2 hd
          obtain ⟨c', hc', hsum'⟩ := hlift_c c hc
          exact ⟨c', hc', hsum.trans hsum'.symm⟩
        · subst heq
          by_cases hnl : nonlinearG gate = true
          · constructor
            · intro hd
              rw [hnew_d, hnl] at hd
              simp at hd
            · intro hd
              refine ⟨fun j => if j.val = gs.length then 1 else 0, ?_, ?_⟩
              · intro j hj
                have he : j.val = gs.length := by by_contra hne; simp [hne] at hj
                simp only [Fin.getElem_fin, he]
                rw [List.getElem_append_right le_rfl]
                simpa using ⟨hnl, hd⟩
              · have hlen1 : (gs ++ [gate]).length = gs.length + 1 := by simp
                let e : Fin (gs.length + 1) ≃ Fin (gs ++ [gate]).length := finCongr hlen1.symm
                rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                have hz : ∀ j : Fin gs.length,
                    (if (e j.castSucc).val = gs.length then (1 : F2) else 0) •
                      deltaF (wireVal (a := a) (b := b) (gs ++ [gate]) (n + (e j.castSucc).val)) = 0 := by
                  intro j
                  have hne : (e j.castSucc).val ≠ gs.length := by simp [e]; omega
                  simp [hne]
                rw [Finset.sum_eq_zero (fun j _ => hz j), zero_add]
                have hlast : (e (Fin.last gs.length)).val = gs.length := by simp [e]
                simp [hlast]
          · have hnlf : nonlinearG gate = false := Bool.eq_false_iff.mpr hnl
            have hcases : gate.inputs.length = 0 ∨ gate.inputs.length = 1 ∨ gate.inputs.length = 2 := by
              omega
            rcases hcases with hlen0 | hlen1 | hlen2
            · rcases hl : gate.inputs with _ | ⟨_, _⟩
              · have hw : wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) =
                    fun _ _ => b2f (gate.op.eval []) := by
                  ext x y; rw [wireVal_snoc_eq, hl]; rfl
                refine ⟨fun _ => ⟨fun _ => b2f (gate.op.eval []), fun _ => 0, fun x y => by simp [hw]⟩,
                  fun _ => ⟨fun _ => 0, fun _ h => (h rfl).elim, by simp [hw, deltaF_const]⟩⟩
              · simp [hl] at hlen0
            · rcases hl : gate.inputs with _ | ⟨h0, _ | ⟨_, _⟩⟩
              · simp [hl] at hlen1
              · have hd_eq : (depthsList n (gs ++ [gate])).getD (n + gs.length) 0 =
                    (depthsList n gs).getD h0 0 := by
                  rw [hnew_d, hl, hnlf]; simp
                have hw : ∀ x y, wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) x y =
                    b2f (gate.op.eval [false]) +
                    (b2f (gate.op.eval [true]) + b2f (gate.op.eval [false])) * wireVal gs h0 x y := by
                  intro x y
                  rw [wireVal_snoc_eq, hl]
                  exact bool_fun1_poly (fun u => gate.op.eval [u]) _
                constructor
                · intro hd
                  rw [hd_eq] at hd
                  obtain ⟨f0, g0, hf0⟩ := (ih_w h0).1 hd
                  set c0 := b2f (gate.op.eval [false])
                  set c1 := b2f (gate.op.eval [true]) + b2f (gate.op.eval [false])
                  refine ⟨fun x => c0 + c1 * f0 x, fun y => c1 * g0 y, fun x y => ?_⟩
                  rw [hw x y, hf0 x y]; ring
                · intro hd
                  rw [hd_eq] at hd
                  obtain ⟨c, hc, hsum⟩ := (ih_w h0).2 hd
                  set c1 := b2f (gate.op.eval [true]) + b2f (gate.op.eval [false])
                  have hdel : deltaF (wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length)) =
                      c1 • deltaF (wireVal gs h0) := by
                    have heq_f : wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) =
                        fun x y => b2f (gate.op.eval [false]) + c1 * wireVal gs h0 x y := by
                      ext x y; exact hw x y
                    rw [heq_f, deltaF_add, deltaF_const, zero_add, deltaF_smul]
                  obtain ⟨c', hc', hsum'⟩ := hlift_c (fun j => c1 * c j) (fun j hj =>
                    hc j (fun h0 => hj (by simp [h0])))
                  refine ⟨c', hc', ?_⟩
                  rw [hdel, hsum, Finset.smul_sum, hsum']
                  refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]
              · simp [hl] at hlen1
            · rcases hl : gate.inputs with _ | ⟨h0, _ | ⟨h1, _ | ⟨_, _⟩⟩⟩ <;> simp [hl] at hlen2
              have hd_eq : (depthsList n (gs ++ [gate])).getD (n + gs.length) 0 =
                  max ((depthsList n gs).getD h0 0) ((depthsList n gs).getD h1 0) := by
                rw [hnew_d, hl, hnlf]; simp
              have hx : xor (xor (gate.op.eval [false, false]) (gate.op.eval [false, true]))
                  (xor (gate.op.eval [true, false]) (gate.op.eval [true, true])) = false := by
                simp only [nonlinearG, hl, List.length_cons, List.length_nil, beq_self_eq_true,
                  Bool.true_and] at hnlf
                exact hnlf
              set c0 := b2f (gate.op.eval [false, false])
              set c1 := b2f (gate.op.eval [true, false]) + b2f (gate.op.eval [false, false])
              set c2 := b2f (gate.op.eval [false, true]) + b2f (gate.op.eval [false, false])
              have hw : ∀ x y, wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) x y =
                  c0 + c1 * wireVal gs h0 x y + c2 * wireVal gs h1 x y := by
                intro x y
                rw [wireVal_snoc_eq, hl]
                have hp := bool_fun2_poly (fun u v => gate.op.eval [u, v])
                  ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h0 false)
                  ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD h1 false)
                rw [hx] at hp
                simpa [wireVal, b2f, c0, c1, c2] using hp
              constructor
              · intro hd
                rw [hd_eq] at hd
                have hd0 : (depthsList n gs).getD h0 0 = 0 := by omega
                have hd1 : (depthsList n gs).getD h1 0 = 0 := by omega
                obtain ⟨f0, g0, hf0⟩ := (ih_w h0).1 hd0
                obtain ⟨f1, g1, hf1⟩ := (ih_w h1).1 hd1
                refine ⟨fun x => c0 + c1 * f0 x + c2 * f1 x, fun y => c1 * g0 y + c2 * g1 y, fun x y => ?_⟩
                rw [hw x y, hf0 x y, hf1 x y]; ring
              · intro hd
                rw [hd_eq] at hd
                have hd0 : (depthsList n gs).getD h0 0 ≤ 1 := by omega
                have hd1 : (depthsList n gs).getD h1 0 ≤ 1 := by omega
                obtain ⟨d0, hd0c, hsum0⟩ := (ih_w h0).2 hd0
                obtain ⟨d1, hd1c, hsum1⟩ := (ih_w h1).2 hd1
                have hdel : deltaF (wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length)) =
                    c1 • deltaF (wireVal gs h0) + c2 • deltaF (wireVal gs h1) := by
                  have heq_f : wireVal (a := a) (b := b) (gs ++ [gate]) (n + gs.length) =
                      fun x y => (c0 + c1 * wireVal gs h0 x y) + c2 * wireVal gs h1 x y := by
                    ext x y; exact hw x y
                  rw [heq_f, deltaF_add, deltaF_add, deltaF_const, zero_add, deltaF_smul, deltaF_smul]
                obtain ⟨c', hc', hsum'⟩ := hlift_c (fun j => c1 * d0 j + c2 * d1 j) (fun j hj => by
                  by_cases h0z : d0 j = 0
                  · apply hd1c j
                    intro h1z; apply hj; simp [h0z, h1z]
                  · exact hd0c j h0z)
                refine ⟨c', hc', ?_⟩
                rw [hdel, hsum0, hsum1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, hsum']
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [smul_smul, smul_smul, ← add_smul]
        · have hw : wireVal (a := a) (b := b) (gs ++ [gate]) i = fun _ _ => 0 := by
            ext x y
            simp only [wireVal]
            have hlen_o : (oneEach x y).length = n := by simp [oneEach, n]; omega
            rw [List.getD_eq_default _ _ (by
              rw [wires_length, List.length_append, List.length_singleton, hlen_o]; omega)]
            rfl
          refine ⟨fun _ => ⟨fun _ => 0, fun _ => 0, fun x y => by simp [hw]⟩,
            fun _ => ⟨fun _ => 0, fun _ h => (h rfl).elim, by simp [hw, deltaF_const]⟩⟩
  obtain ⟨hrk, hw⟩ := hmain Q.gates hfan
  obtain ⟨c, hc, hsum⟩ := (hw Q.output).2 hdep
  have hPeq : deltaMat P = deltaF (wireVal (a := a) (b := b) Q.gates Q.output) := by
    ext x y
    simp only [deltaMat, deltaF, wireVal]
    have hq : ∀ u v, (Circuit.wires ⟨Q.gates, 0⟩ (oneEach u v)).getD Q.output false = P u v := by
      intro u v
      have := hrep u v
      simpa [Circuit.eval, Circuit.wires] using this
    rw [hq, hq, hq, hq]
  rw [hPeq, hsum]
  set S := Finset.univ.filter fun j : Fin Q.gates.length => nonlinearG Q.gates[j] = true
  have hsub : (∑ j : Fin Q.gates.length, c j • deltaF (wireVal (a := a) (b := b) Q.gates (n + j.val))) =
      ∑ j ∈ S, c j • deltaF (wireVal Q.gates (n + j.val)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hc0 : c j = 0 := by by_contra hne; exact hj (hc j hne).1
    simp [hc0]
  rw [hsub]
  have h1 : (∑ j ∈ S, c j • deltaF (wireVal (a := a) (b := b) Q.gates (n + j.val))).rank ≤
      ∑ j ∈ S, (c j • deltaF (wireVal (a := a) (b := b) Q.gates (n + j.val))).rank :=
    rank_sum_le' S _
  have h2 : (∑ j ∈ S, (c j • deltaF (wireVal (a := a) (b := b) Q.gates (n + j.val))).rank) ≤
      ∑ _j ∈ S, 2 := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hcz : c j = 0
    · simp [hcz]
    · exact (rank_smul_le' _ _).trans (hrk j (hc j hcz).1 (hc j hcz).2)
  have hcard : S.card = Q.gates.countP nonlinearG := by
    simp only [S, List.countP_eq_length_filter]
    have hfin : ∀ (l : List Gate), (Finset.univ.filter fun j : Fin l.length => nonlinearG l[j] = true).card =
        (l.filter nonlinearG).length := by
      intro l
      induction l with
      | nil => simp
      | cons g l ih =>
        rw [List.filter_cons]
        have hsum : (Finset.univ.filter fun j : Fin (g :: l).length => nonlinearG (g :: l)[j] = true).card =
            (if nonlinearG g = true then 1 else 0) +
            (Finset.univ.filter fun j : Fin l.length => nonlinearG l[j] = true).card := by
          rw [Finset.card_filter, Finset.card_filter]
          have hlen : (g :: l).length = l.length + 1 := rfl
          let e : Fin (l.length + 1) ≃ Fin (g :: l).length := finCongr hlen.symm
          rw [← Equiv.sum_comp e, Fin.sum_univ_succ]
          rfl
        rw [hsum, ih]
        cases nonlinearG g <;> simp [Nat.add_comm]
    exact hfin Q.gates
  have h3 : (∑ _j ∈ S, 2) = 2 * S.card := by simp [mul_comm]
  omega

lemma rank_decomp {m n r : ℕ} (A : Matrix (Fin m) (Fin n) F2) (hr : A.rank ≤ r) :
    ∃ (u : Fin r → Fin m → F2) (v : Fin r → Fin n → F2),
      A = ∑ l : Fin r, outerMat (u l) (v l) := by
  set k := A.rank
  let bR : Module.Basis (Fin k) F2 (LinearMap.range A.mulVecLin) :=
    Module.finBasis F2 (LinearMap.range A.mulVecLin)
  let u0 : Fin k → Fin m → F2 := fun l => (bR l : Fin m → F2)
  have hcol_mem : ∀ j : Fin n, A.col j ∈ LinearMap.range A.mulVecLin := fun j =>
    ⟨Pi.single j 1, by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.col, Pi.single_apply]⟩
  let v0 : Fin k → Fin n → F2 := fun l j => bR.repr ⟨A.col j, hcol_mem j⟩ l
  have hA0 : A = ∑ l : Fin k, outerMat (u0 l) (v0 l) := by
    ext i j
    have hcol : (⟨A.col j, hcol_mem j⟩ : LinearMap.range A.mulVecLin) =
        ∑ l : Fin k, v0 l j • bR l := by
      simpa [v0] using (bR.sum_repr ⟨A.col j, hcol_mem j⟩).symm
    have hval := congrArg (fun z : LinearMap.range A.mulVecLin => (z : Fin m → F2) i) hcol
    simpa [u0, outerMat, Matrix.sum_apply, mul_comm] using hval
  refine ⟨fun l => if hl : l.val < k then u0 ⟨l.val, hl⟩ else 0,
    fun l => if hl : l.val < k then v0 ⟨l.val, hl⟩ else 0, ?_⟩
  rw [hA0]
  ext i j
  simp only [Matrix.sum_apply, outerMat]
  have hsum : (∑ l : Fin r, (if hl : l.val < k then u0 ⟨l.val, hl⟩ else 0) i *
      (if hl : l.val < k then v0 ⟨l.val, hl⟩ else 0) j) =
      ∑ l : Fin k, u0 l i * v0 l j := by
    have hfilt : (∑ l : Fin r, (if hl : l.val < k then u0 ⟨l.val, hl⟩ else 0) i *
        (if hl : l.val < k then v0 ⟨l.val, hl⟩ else 0) j) =
        ∑ l ∈ Finset.univ.filter (fun l : Fin r => l.val < k),
          (if hl : l.val < k then u0 ⟨l.val, hl⟩ else 0) i *
          (if hl : l.val < k then v0 ⟨l.val, hl⟩ else 0) j := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp [hl]
    rw [hfilt]
    refine Finset.sum_bij (fun l hl => (⟨l.val, (Finset.mem_filter.mp hl).2⟩ : Fin k)) ?_ ?_ ?_ ?_
    · intro l _; exact Finset.mem_univ _
    · intro l1 hl1 l2 hl2 h
      exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) h)
    · intro l _
      exact ⟨⟨l.val, lt_of_lt_of_le l.isLt hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.isLt⟩, Fin.ext rfl⟩
    · intro l hl
      have hlt : l.val < k := (Finset.mem_filter.mp hl).2
      simp [hlt]
  exact hsum.symm

def goodGates (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
  (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < n + j)

lemma goodGates_readsBack (n : ℕ) (gs : List Gate) (o : ℕ) (h : goodGates n gs) :
    ReadsBack n ⟨gs, o⟩ := by
  intro j hj w hw
  have hg : gateAt ⟨gs, o⟩ j = gs[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hg] at hw
  exact h.2 j hj w hw

lemma goodGates_nil (n : ℕ) : goodGates n [] :=
  ⟨by simp, fun j hj => by simp at hj⟩

lemma goodGates_snoc (n : ℕ) (gs : List Gate) (g : Gate)
    (h : goodGates n gs) (hlen : g.inputs.length ≤ 2)
    (hback : ∀ w ∈ g.inputs, w < n + gs.length) :
    goodGates n (gs ++ [g]) := by
  refine ⟨fun g' hg' => ?_, fun j hj w hw => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact h.1 g' hg'
    · exact hlen
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
    · rw [List.getElem_append_left hlt] at hw
      exact h.2 j hlt w hw
    · rw [List.getElem_append_right le_rfl] at hw
      simp only [Nat.sub_self, List.getElem_cons_zero] at hw
      exact hback w hw

lemma nonlinearG_or_nil : nonlinearG ⟨GateOp.or, []⟩ = false := by
  simp [nonlinearG, GateOp.eval]
lemma nonlinearG_mod2 (u v : ℕ) : nonlinearG ⟨GateOp.mod 2, [u, v]⟩ = false := by
  simp [nonlinearG, GateOp.eval]
lemma nonlinearG_not1 (u : ℕ) : nonlinearG ⟨GateOp.not, [u]⟩ = false := by
  simp [nonlinearG, GateOp.eval]
lemma nonlinearG_and2 (u v : ℕ) : nonlinearG ⟨GateOp.and, [u, v]⟩ = true := by
  simp [nonlinearG, GateOp.eval]

lemma append_zero_gate {a b : ℕ} (gs : List Gate) (h : goodGates (a + 2 + (b + 2)) gs) :
    let gs' := gs ++ [⟨GateOp.or, []⟩]
    let w := a + 2 + (b + 2) + gs.length
    goodGates (a + 2 + (b + 2)) gs' ∧
    gs'.countP nonlinearG = gs.countP nonlinearG ∧
    w < a + 2 + (b + 2) + gs'.length ∧
    (depthsList (a + 2 + (b + 2)) gs').getD w 0 = 0 ∧
    (∀ i < a + 2 + (b + 2) + gs.length,
      wireVal (a := a) (b := b) gs' i = wireVal gs i ∧
      (depthsList (a + 2 + (b + 2)) gs').getD i 0 = (depthsList (a + 2 + (b + 2)) gs).getD i 0) ∧
    (∀ x y, wireVal (a := a) (b := b) gs' w x y = 0) := by
  set n := a + 2 + (b + 2)
  refine ⟨goodGates_snoc n gs _ h (by simp) (by simp),
    by simp [List.countP_append, nonlinearG_or_nil],
    by simp,
    by rw [depthsList_snoc_eq]; simp [nonlinearG_or_nil],
    fun i hi => ⟨wireVal_append_lt gs _ i hi, depthsList_append_lt n gs _ i hi⟩,
    fun x y => by rw [wireVal_snoc_eq]; rfl⟩

lemma append_xor_gate {a b : ℕ} (gs : List Gate) (u v : ℕ)
    (h : goodGates (a + 2 + (b + 2)) gs)
    (hu : u < a + 2 + (b + 2) + gs.length)
    (hv : v < a + 2 + (b + 2) + gs.length) :
    let n := a + 2 + (b + 2)
    let gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    let gs2 := gs1 ++ [⟨GateOp.not, [n + gs.length]⟩]
    let w := n + gs.length + 1
    goodGates n gs2 ∧
    gs2.countP nonlinearG = gs.countP nonlinearG ∧
    w < n + gs2.length ∧
    (depthsList n gs2).getD w 0 =
      max ((depthsList n gs).getD u 0) ((depthsList n gs).getD v 0) ∧
    (∀ i < n + gs.length,
      wireVal (a := a) (b := b) gs2 i = wireVal gs i ∧
      (depthsList n gs2).getD i 0 = (depthsList n gs).getD i 0) ∧
    (∀ x y, wireVal (a := a) (b := b) gs2 w x y =
      wireVal gs u x y + wireVal gs v x y) := by
  set n := a + 2 + (b + 2)
  set g1 : Gate := ⟨GateOp.mod 2, [u, v]⟩
  set gs1 := gs ++ [g1]
  set g2 : Gate := ⟨GateOp.not, [n + gs.length]⟩
  set gs2 := gs1 ++ [g2]
  have hg1 : goodGates n gs1 := goodGates_snoc n gs g1 h (by simp [g1]) (by
    intro w hw; simp [g1] at hw; rcases hw with rfl | rfl <;> omega)
  have hlen1 : gs1.length = gs.length + 1 := by simp [gs1]
  have hg2 : goodGates n gs2 := goodGates_snoc n gs1 g2 hg1 (by simp [g2]) (by
    intro w hw; simp [g2] at hw; subst hw; omega)
  have hd1 : (depthsList n gs1).getD (n + gs.length) 0 =
      max ((depthsList n gs).getD u 0) ((depthsList n gs).getD v 0) := by
    rw [depthsList_snoc_eq]; simp [g1, nonlinearG_mod2]
  have hd2 : (depthsList n gs2).getD (n + gs.length + 1) 0 =
      max ((depthsList n gs).getD u 0) ((depthsList n gs).getD v 0) := by
    have heq : n + gs.length + 1 = n + gs1.length := by omega
    rw [heq, depthsList_snoc_eq]
    simp only [g2, nonlinearG_not1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      Bool.toNat_false, add_zero, hd1]
    exact Nat.max_eq_left (Nat.zero_le _)
  have hpres : ∀ i < n + gs.length,
      wireVal (a := a) (b := b) gs2 i = wireVal gs i ∧
      (depthsList n gs2).getD i 0 = (depthsList n gs).getD i 0 := by
    intro i hi
    have hi1 : i < n + gs1.length := by omega
    refine ⟨?_, ?_⟩
    · rw [wireVal_append_lt gs1 [g2] i hi1, wireVal_append_lt gs [g1] i hi]
    · rw [depthsList_append_lt n gs1 [g2] i hi1, depthsList_append_lt n gs [g1] i hi]
  have hval : ∀ x y, wireVal (a := a) (b := b) gs2 (n + gs.length + 1) x y =
      wireVal gs u x y + wireVal gs v x y := by
    intro x y
    have heq : n + gs.length + 1 = n + gs1.length := by omega
    rw [heq, wireVal_snoc_eq]
    simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    have hv1 : (Circuit.wires ⟨gs1, 0⟩ (oneEach x y)).getD (n + gs.length) false =
        (GateOp.mod 2).eval [(Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD u false,
          (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD v false] := by
      have := wireVal_snoc_eq (a := a) (b := b) gs g1 x y
      simp only [wireVal, g1, List.map_cons, List.map_nil] at this
      exact b2f_injective this
    rw [hv1]
    simp only [wireVal]
    cases (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD u false <;>
      cases (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD v false <;> decide
  refine ⟨hg2, by simp [gs2, gs1, g1, g2, List.countP_append, nonlinearG_mod2, nonlinearG_not1],
    by simp [gs2, gs1]; omega, hd2, hpres, hval⟩

lemma append_and_gate {a b : ℕ} (gs : List Gate) (u v : ℕ)
    (h : goodGates (a + 2 + (b + 2)) gs)
    (hu : u < a + 2 + (b + 2) + gs.length)
    (hv : v < a + 2 + (b + 2) + gs.length) :
    let n := a + 2 + (b + 2)
    let gs' := gs ++ [⟨GateOp.and, [u, v]⟩]
    let w := n + gs.length
    goodGates n gs' ∧
    gs'.countP nonlinearG = gs.countP nonlinearG + 1 ∧
    w < n + gs'.length ∧
    (depthsList n gs').getD w 0 =
      max ((depthsList n gs).getD u 0) ((depthsList n gs).getD v 0) + 1 ∧
    (∀ i < n + gs.length,
      wireVal (a := a) (b := b) gs' i = wireVal gs i ∧
      (depthsList n gs').getD i 0 = (depthsList n gs).getD i 0) ∧
    (∀ x y, wireVal (a := a) (b := b) gs' w x y =
      wireVal gs u x y * wireVal gs v x y) := by
  set n := a + 2 + (b + 2)
  set g1 : Gate := ⟨GateOp.and, [u, v]⟩
  set gs' := gs ++ [g1]
  refine ⟨goodGates_snoc n gs g1 h (by simp [g1]) (by
      intro w hw; simp [g1] at hw; rcases hw with rfl | rfl <;> omega),
    by simp [gs', g1, List.countP_append, nonlinearG_and2],
    by simp [gs'],
    by rw [depthsList_snoc_eq]; simp [g1, nonlinearG_and2],
    fun i hi => ⟨wireVal_append_lt gs [g1] i hi, depthsList_append_lt n gs [g1] i hi⟩,
    fun x y => ?_⟩
  rw [wireVal_snoc_eq]
  simp only [g1, List.map_cons, List.map_nil, GateOp.eval, wireVal]
  cases (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD u false <;>
    cases (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD v false <;> decide

lemma append_xor_list {a b : ℕ} (d : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate),
      goodGates (a + 2 + (b + 2)) gs →
      (∀ w ∈ ws, w < a + 2 + (b + 2) + gs.length ∧ (depthsList (a + 2 + (b + 2)) gs).getD w 0 ≤ d) →
      ∃ (gs' : List Gate) (out : ℕ),
        goodGates (a + 2 + (b + 2)) gs' ∧
        gs'.countP nonlinearG = gs.countP nonlinearG ∧
        gs.length ≤ gs'.length ∧
        out < a + 2 + (b + 2) + gs'.length ∧
        (depthsList (a + 2 + (b + 2)) gs').getD out 0 ≤ d ∧
        (∀ i < a + 2 + (b + 2) + gs.length,
          wireVal (a := a) (b := b) gs' i = wireVal gs i ∧
          (depthsList (a + 2 + (b + 2)) gs').getD i 0 = (depthsList (a + 2 + (b + 2)) gs).getD i 0) ∧
        (∀ x y, wireVal (a := a) (b := b) gs' out x y = (ws.map fun w => wireVal gs w x y).sum) := by
  set n := a + 2 + (b + 2)
  intro ws
  induction ws with
  | nil =>
    intro gs hgs _
    have hz := append_zero_gate (a := a) (b := b) gs hgs
    exact ⟨gs ++ [⟨GateOp.or, []⟩], n + gs.length, hz.1, hz.2.1, by simp, hz.2.2.1,
      by rw [hz.2.2.2.1]; exact Nat.zero_le d, hz.2.2.2.2.1, fun x y => by rw [hz.2.2.2.2.2 x y]; rfl⟩
  | cons w ws ih =>
    intro gs hgs hws
    obtain ⟨gs1, out1, hg1, hcnt1, hle1, hout1, hd1, hpres1, hval1⟩ :=
      ih gs hgs (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    have hw_in := hws w (List.mem_cons_self ..)
    have hw1_lt : w < n + gs1.length := by omega
    have hw1_pres := hpres1 w hw_in.1
    have hx := append_xor_gate (a := a) (b := b) gs1 w out1 hg1 hw1_lt hout1
    refine ⟨_, _, hx.1, hx.2.1.trans hcnt1, by simp; omega, hx.2.2.1, ?_, ?_, ?_⟩
    · rw [hx.2.2.2.1, hw1_pres.2]
      exact max_le hw_in.2 hd1
    · intro i hi
      have h1 := hpres1 i hi
      have h2 := hx.2.2.2.2.1 i (by omega)
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    · intro x y
      rw [hx.2.2.2.2.2 x y, hw1_pres.1, hval1 x y]
      simp

lemma append_sep_wire {a b : ℕ} (gs : List Gate) (hgs : goodGates (a + 2 + (b + 2)) gs)
    (f : Fin (a + 2) → F2) (g : Fin (b + 2) → F2) :
    ∃ (gs' : List Gate) (out : ℕ),
      goodGates (a + 2 + (b + 2)) gs' ∧
      gs'.countP nonlinearG = gs.countP nonlinearG ∧
      gs.length ≤ gs'.length ∧
      out < a + 2 + (b + 2) + gs'.length ∧
      (depthsList (a + 2 + (b + 2)) gs').getD out 0 = 0 ∧
      (∀ i < a + 2 + (b + 2) + gs.length,
        wireVal (a := a) (b := b) gs' i = wireVal gs i ∧
        (depthsList (a + 2 + (b + 2)) gs').getD i 0 = (depthsList (a + 2 + (b + 2)) gs).getD i 0) ∧
      (∀ x y, wireVal (a := a) (b := b) gs' out x y = f x + g y) := by
  set n := a + 2 + (b + 2)
  let wsL : List ℕ := (List.finRange (a + 2)).filterMap fun i => if f i = 1 then some i.val else none
  let wsR : List ℕ := (List.finRange (b + 2)).filterMap fun j => if g j = 1 then some (a + 2 + j.val) else none
  have hmem : ∀ w ∈ wsL ++ wsR, w < n + gs.length ∧ (depthsList n gs).getD w 0 ≤ 0 := by
    intro w hw
    have hw_lt : w < n := by
      simp only [List.mem_append, wsL, wsR, List.mem_filterMap] at hw
      rcases hw with ⟨i, _, hi⟩ | ⟨j, _, hj⟩
      · split_ifs at hi <;> simp at hi; subst hi; omega
      · split_ifs at hj <;> simp at hj; subst hj; omega
    refine ⟨by omega, ?_⟩
    have hd0 : (depthsList n gs).getD w 0 = (depthsList n []).getD w 0 := by
      simpa using depthsList_append_lt n [] gs w (by simpa using hw_lt)
    rw [hd0]
    simp [depthsList, List.getD_eq_getElem?_getD, hw_lt]
  obtain ⟨gs', out, hg', hcnt', hle', hout', hd', hpres', hval'⟩ :=
    append_xor_list (a := a) (b := b) 0 (wsL ++ wsR) gs hgs hmem
  refine ⟨gs', out, hg', hcnt', hle', hout', Nat.eq_zero_of_le_zero hd', hpres', fun x y => ?_⟩
  rw [hval' x y, List.map_append, List.sum_append]
  have hwire_in : ∀ w < n, wireVal (a := a) (b := b) gs w x y = wireVal [] w x y := by
    intro w hw
    have h1 := wireVal_append_lt (a := a) (b := b) [] gs w (by simpa using hw)
    exact congrFun (congrFun h1 x) y
  have hsumL : (wsL.map fun w => wireVal (a := a) (b := b) gs w x y).sum = f x := by
    have hmap : ∀ (l : List (Fin (a + 2))),
        ((l.filterMap fun i => if f i = 1 then some i.val else none).map
          fun w => wireVal (a := a) (b := b) gs w x y).sum =
        (l.map fun i => if i = x then f i else 0).sum := by
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
        by_cases hfi : f i = 1
        · simp only [List.filterMap_cons, hfi, ↓reduceIte, List.map_cons, List.sum_cons, ih]
          rw [hwire_in i.val (by omega)]
          have hwv : wireVal (a := a) (b := b) [] i.val x y = if i = x then 1 else 0 := by
            simp only [wireVal, Circuit.wires, List.foldl_nil]
            rw [oneEach_getD_left x y i.val i.isLt]
            by_cases hix : i = x <;> simp [hix, b2f]
          rw [hwv]
        · have hf0 : f i = 0 := (f2_eq_zero_or_one (f i)).resolve_right hfi
          simp [List.filterMap_cons, hfi, hf0, ih]
    rw [hmap]
    have hfin : ((List.finRange (a + 2)).map fun i => if i = x then f i else 0).sum =
        ∑ i : Fin (a + 2), if i = x then f i else 0 := by
      rw [Fin.sum_univ_def]
    rw [hfin]
    simp
  have hsumR : (wsR.map fun w => wireVal (a := a) (b := b) gs w x y).sum = g y := by
    have hmap : ∀ (l : List (Fin (b + 2))),
        ((l.filterMap fun j => if g j = 1 then some (a + 2 + j.val) else none).map
          fun w => wireVal (a := a) (b := b) gs w x y).sum =
        (l.map fun j => if j = y then g j else 0).sum := by
      intro l
      induction l with
      | nil => simp
      | cons j l ih =>
        by_cases hgj : g j = 1
        · simp only [List.filterMap_cons, hgj, ↓reduceIte, List.map_cons, List.sum_cons, ih]
          rw [hwire_in (a + 2 + j.val) (by omega)]
          have hwv : wireVal (a := a) (b := b) [] (a + 2 + j.val) x y = if j = y then 1 else 0 := by
            simp only [wireVal, Circuit.wires, List.foldl_nil]
            rw [oneEach_getD_right x y j.val j.isLt]
            by_cases hjy : j = y <;> simp [hjy, b2f]
          rw [hwv]
        · have hg0 : g j = 0 := (f2_eq_zero_or_one (g j)).resolve_right hgj
          simp [List.filterMap_cons, hgj, hg0, ih]
    rw [hmap]
    have hfin : ((List.finRange (b + 2)).map fun j => if j = y then g j else 0).sum =
        ∑ j : Fin (b + 2), if j = y then g j else 0 := by
      rw [Fin.sum_univ_def]
    rw [hfin]
    simp
  rw [hsumL, hsumR]

lemma sum_fin_two_mul {α : Type*} [AddCommMonoid α] :
    ∀ (t : ℕ) (f : Fin (2 * t) → α),
      (∑ l : Fin (2 * t), f l) =
        ∑ j : Fin t, (f ⟨2 * j.val, by omega⟩ + f ⟨2 * j.val + 1, by omega⟩) := by
  intro t
  induction t with
  | zero => intro f; simp
  | succ t' iht =>
    intro f
    have hmul : 2 * (t' + 1) = 2 * t' + 1 + 1 := by omega
    let e : Fin (2 * t' + 1 + 1) ≃ Fin (2 * (t' + 1)) := finCongr hmul.symm
    conv_lhs => rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    have h1 : (fun i : Fin (2 * t') => f (e i.castSucc.castSucc)) = fun l => f ⟨l.val, by omega⟩ := by
      ext l; rfl
    rw [h1, iht (fun l => f ⟨l.val, by omega⟩), add_assoc]
    congr 1

lemma rank_le_imp_ok {a b t : ℕ} (P : Fin (a + 2) → Fin (b + 2) → Bool)
    (hr : (deltaMat P).rank ≤ 2 * t) :
    ∃ Q : Circuit,
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (a + 2 + (b + 2)) Q ∧
      Represents P Q ∧
      depthC (a + 2 + (b + 2)) Q ≤ 1 ∧
      Q.gates.countP nonlinearG ≤ t := by
  set n := a + 2 + (b + 2)
  obtain ⟨u', v', hdecomp⟩ := rank_decomp (deltaMat P) hr
  let u : Fin (2 * t) → Fin (a + 2) → F2 := fun l x =>
    Fin.cases 0 (fun x' => u' l x') x
  let v : Fin (2 * t) → Fin (b + 2) → F2 := fun l y =>
    Fin.cases 0 (fun y' => v' l y') y
  let f0 : Fin (a + 2) → F2 := fun x =>
    b2f (P x 0) + b2f (P 0 0) +
      ∑ j : Fin t, u ⟨2 * j.val, by omega⟩ x * u ⟨2 * j.val + 1, by omega⟩ x
  let g0 : Fin (b + 2) → F2 := fun y =>
    b2f (P 0 y) +
      ∑ j : Fin t, v ⟨2 * j.val, by omega⟩ y * v ⟨2 * j.val + 1, by omega⟩ y
  have hP_eq : ∀ x y, b2f (P x y) = f0 x + g0 y +
      ∑ j : Fin t,
        (u ⟨2 * j.val, by omega⟩ x + v ⟨2 * j.val + 1, by omega⟩ y) *
        (u ⟨2 * j.val + 1, by omega⟩ x + v ⟨2 * j.val, by omega⟩ y) := by
    intro x y
    have hsum_pair :
        (∑ j : Fin t,
          (u ⟨2 * j.val, by omega⟩ x + v ⟨2 * j.val + 1, by omega⟩ y) *
          (u ⟨2 * j.val + 1, by omega⟩ x + v ⟨2 * j.val, by omega⟩ y)) =
        (∑ j : Fin t, u ⟨2 * j.val, by omega⟩ x * u ⟨2 * j.val + 1, by omega⟩ x) +
        (∑ j : Fin t, v ⟨2 * j.val, by omega⟩ y * v ⟨2 * j.val + 1, by omega⟩ y) +
        (∑ l : Fin (2 * t), u l x * v l y) := by
      have hexp : ∀ j : Fin t,
          (u ⟨2 * j.val, by omega⟩ x + v ⟨2 * j.val + 1, by omega⟩ y) *
          (u ⟨2 * j.val + 1, by omega⟩ x + v ⟨2 * j.val, by omega⟩ y) =
          (u ⟨2 * j.val, by omega⟩ x * u ⟨2 * j.val + 1, by omega⟩ x +
           v ⟨2 * j.val, by omega⟩ y * v ⟨2 * j.val + 1, by omega⟩ y) +
          (u ⟨2 * j.val, by omega⟩ x * v ⟨2 * j.val, by omega⟩ y +
           u ⟨2 * j.val + 1, by omega⟩ x * v ⟨2 * j.val + 1, by omega⟩ y) := by
        intro j; ring
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1
      exact (sum_fin_two_mul t (fun l => u l x * v l y)).symm
    rw [hsum_pair]
    have h2z : (2 : F2) = 0 := rfl
    have hdel : (∑ l : Fin (2 * t), u l x * v l y) =
        b2f (P x y) + b2f (P x 0) + b2f (P 0 y) + b2f (P 0 0) := by
      refine Fin.cases ?_ (fun x' => Fin.cases ?_ (fun y' => ?_) y) x
      · simp [u]; ring_nf; simp [h2z]
      · simp [v]; ring_nf; simp [h2z]
      · have hval := congrArg (fun M => M x' y') hdecomp
        simpa [u, v, deltaMat, deltaF, outerMat, Matrix.sum_apply] using hval.symm
    rw [hdel]
    simp only [f0, g0]
    ring_nf
    simp [h2z]
  have hbuild_prods : ∀ (m : ℕ) (hm : m ≤ t),
      ∃ (gs : List Gate) (ws : List ℕ),
        goodGates n gs ∧
        gs.countP nonlinearG = m ∧
        ws.length = m ∧
        (∀ w ∈ ws, w < n + gs.length ∧ (depthsList n gs).getD w 0 ≤ 1) ∧
        (∀ x y, (ws.map fun w => wireVal (a := a) (b := b) gs w x y).sum =
          ∑ j : Fin m,
            (u ⟨2 * j.val, by omega⟩ x + v ⟨2 * j.val + 1, by omega⟩ y) *
            (u ⟨2 * j.val + 1, by omega⟩ x + v ⟨2 * j.val, by omega⟩ y)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨[], [], goodGates_nil n, rfl, rfl, by simp, by simp⟩
    | succ m ihm =>
      intro hm
      obtain ⟨gs0, ws0, hg0, hcnt0, hlen0, hws0, hval0⟩ := ihm (Nat.le_of_succ_le hm)
      obtain ⟨gs1, wA, hg1, hcnt1, hle1, hwA_lt, hwA_d, hpres1, hvalA⟩ :=
        append_sep_wire gs0 hg0 (u ⟨2 * m, by omega⟩) (v ⟨2 * m + 1, by omega⟩)
      obtain ⟨gs2, wB, hg2, hcnt2, hle2, hwB_lt, hwB_d, hpres2, hvalB⟩ :=
        append_sep_wire gs1 hg1 (u ⟨2 * m + 1, by omega⟩) (v ⟨2 * m, by omega⟩)
      have hwA2_lt : wA < n + gs2.length := by omega
      have hwA2_p := hpres2 wA hwA_lt
      have hand := append_and_gate (a := a) (b := b) gs2 wA wB hg2 hwA2_lt hwB_lt
      refine ⟨_, (n + gs2.length) :: ws0, hand.1, by omega, by simp [hlen0], ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · refine ⟨hand.2.2.1, ?_⟩
          rw [hand.2.2.2.1, hwA2_p.2, hwA_d, hwB_d]; simp
        · have h0 := hws0 w hw
          have h1 := hpres1 w h0.1
          have h2 := hpres2 w (by omega)
          have h3 := hand.2.2.2.2.1 w (by omega)
          exact ⟨by have := hand.2.2.1; omega, by rw [h3.2, h2.2, h1.2]; exact h0.2⟩
      · intro x y
        rw [List.map_cons, List.sum_cons, hand.2.2.2.2.2 x y, hwA2_p.1, hvalA x y, hvalB x y]
        have hws_eq : (ws0.map fun w => wireVal (a := a) (b := b) (gs2 ++ [⟨GateOp.and, [wA, wB]⟩]) w x y) =
            ws0.map fun w => wireVal gs0 w x y := by
          refine List.map_congr_left fun w hw => ?_
          have h0 := hws0 w hw
          have h1 := hpres1 w h0.1
          have h2 := hpres2 w (by omega)
          have h3 := hand.2.2.2.2.1 w (by omega)
          rw [h3.1, h2.1, h1.1]
        rw [hws_eq, hval0 x y, Fin.sum_univ_castSucc, add_comm]
        rfl
  obtain ⟨gs1, ws1, hg1, hcnt1, _, hws1, hval1⟩ := hbuild_prods t le_rfl
  obtain ⟨gs2, wLin, hg2, hcnt2, hle2, hwLin_lt, hwLin_d, hpres2, hvalLin⟩ :=
    append_sep_wire gs1 hg1 f0 g0
  have hws2 : ∀ w ∈ wLin :: ws1, w < n + gs2.length ∧ (depthsList n gs2).getD w 0 ≤ 1 := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨hwLin_lt, by rw [hwLin_d]; exact Nat.zero_le 1⟩
    · have h0 := hws1 w hw
      have h2 := hpres2 w h0.1
      exact ⟨by omega, by rw [h2.2]; exact h0.2⟩
  obtain ⟨gs3, out, hg3, hcnt3, hle3, hout3, hd3, hpres3, hval3⟩ :=
    append_xor_list (a := a) (b := b) 1 (wLin :: ws1) gs2 hg2 hws2
  refine ⟨⟨gs3, out⟩, hg3.1, goodGates_readsBack n gs3 out hg3, ?_, hd3, by rw [hcnt3, hcnt2, hcnt1]⟩
  intro x y
  apply b2f_injective
  have hev : b2f (Circuit.eval ⟨gs3, out⟩ (oneEach x y)) = wireVal gs3 out x y := rfl
  rw [hev, hval3 x y, List.map_cons, List.sum_cons, hvalLin x y]
  have hws_eq : (ws1.map fun w => wireVal (a := a) (b := b) gs2 w x y) =
      ws1.map fun w => wireVal gs1 w x y := by
    refine List.map_congr_left fun w hw => ?_
    have h0 := hws1 w hw
    rw [(hpres2 w h0.1).1]
  rw [hws_eq, hval1 x y, hP_eq x y]

def okP (a b t : ℕ) (P : Fin (a + 2) → Fin (b + 2) → Bool) : Prop :=
  ∃ Q : Circuit,
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
    ReadsBack (a + 2 + (b + 2)) Q ∧
    Represents P Q ∧
    depthC (a + 2 + (b + 2)) Q ≤ 1 ∧
    Q.gates.countP nonlinearG ≤ t

lemma okP_iff {a b t : ℕ} (P : Fin (a + 2) → Fin (b + 2) → Bool) :
    okP a b t P ↔ (deltaMat P).rank ≤ 2 * t := by
  constructor
  · rintro ⟨Q, h1, _, h3, h4, h5⟩
    exact ok_imp_rank_le P Q h1 h3 h4 h5
  · exact rank_le_imp_ok P

def ipMat {m n : ℕ} (A B : Matrix (Fin m) (Fin n) F2) : F2 :=
  ∑ i, ∑ j, A i j * B i j

def matOfBool {m n : ℕ} (P : Fin m → Fin n → Bool) : Matrix (Fin m) (Fin n) F2 :=
  fun i j => b2f (P i j)

def evenMargins {a b : ℕ} (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) : Prop :=
  (∀ x, (∑ y, A x y) = 0) ∧ (∀ y, (∑ x, A x y) = 0)

def subMat {a b : ℕ} (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) :
    Matrix (Fin (a + 1)) (Fin (b + 1)) F2 :=
  fun x y => A x.succ y.succ

def liftEven {a b : ℕ} (B : Matrix (Fin (a + 1)) (Fin (b + 1)) F2) :
    Matrix (Fin (a + 2)) (Fin (b + 2)) F2 :=
  Fin.cases
    (Fin.cases (∑ x, ∑ y, B x y) (fun y => ∑ x, B x y))
    (fun x => Fin.cases (∑ y, B x y) (fun y => B x y))

lemma liftEven_evenMargins {a b : ℕ} (B : Matrix (Fin (a + 1)) (Fin (b + 1)) F2) :
    evenMargins (liftEven B) := by
  constructor
  · intro x
    refine Fin.cases ?_ (fun x' => ?_) x
    · rw [Fin.sum_univ_succ]
      simp only [liftEven, Fin.cases_zero, Fin.cases_succ]
      rw [Finset.sum_comm]
      exact f2_add_self _
    · rw [Fin.sum_univ_succ]
      simp only [liftEven, Fin.cases_zero, Fin.cases_succ]
      exact f2_add_self _
  · intro y
    refine Fin.cases ?_ (fun y' => ?_) y
    · rw [Fin.sum_univ_succ]
      simp only [liftEven, Fin.cases_zero, Fin.cases_succ]
      exact f2_add_self _
    · rw [Fin.sum_univ_succ]
      simp only [liftEven, Fin.cases_zero, Fin.cases_succ]
      exact f2_add_self _

lemma subMat_liftEven {a b : ℕ} (B : Matrix (Fin (a + 1)) (Fin (b + 1)) F2) :
    subMat (liftEven B) = B := by
  ext x y; rfl

lemma liftEven_subMat {a b : ℕ} (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) (h : evenMargins A) :
    liftEven (subMat A) = A := by
  ext x y
  have hrow : ∀ i : Fin (a + 2), A i 0 = ∑ j : Fin (b + 1), A i j.succ := by
    intro i
    have h1 := h.1 i
    rw [Fin.sum_univ_succ] at h1
    have h2 : A i 0 + (A i 0 + ∑ j : Fin (b + 1), A i j.succ) = A i 0 + 0 := congrArg (A i 0 + ·) h1
    rw [← add_assoc, f2_add_self, zero_add, add_zero] at h2
    exact h2.symm
  have hcol : ∀ j : Fin (b + 2), A 0 j = ∑ i : Fin (a + 1), A i.succ j := by
    intro j
    have h1 := h.2 j
    rw [Fin.sum_univ_succ] at h1
    have h2 : A 0 j + (A 0 j + ∑ i : Fin (a + 1), A i.succ j) = A 0 j + 0 := congrArg (A 0 j + ·) h1
    rw [← add_assoc, f2_add_self, zero_add, add_zero] at h2
    exact h2.symm
  refine Fin.cases ?_ (fun x' => Fin.cases ?_ (fun y' => ?_) y) x
  · refine Fin.cases ?_ (fun y' => ?_) y
    · simp only [liftEven, subMat, Fin.cases_zero]
      rw [hcol 0]
      refine Finset.sum_congr rfl fun i _ => (hrow i.succ).symm
    · simp only [liftEven, subMat, Fin.cases_zero, Fin.cases_succ]
      exact (hcol y'.succ).symm
  · simp only [liftEven, subMat, Fin.cases_zero, Fin.cases_succ]
    exact (hrow x'.succ).symm
  · rfl

lemma ipMat_evenMargins {a b : ℕ} (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2)
    (h : evenMargins A) (P : Fin (a + 2) → Fin (b + 2) → Bool) :
    ipMat A (matOfBool P) = ipMat (subMat A) (deltaMat P) := by
  have hA := (liftEven_subMat A h).symm
  conv_lhs => rw [hA]
  simp only [ipMat, liftEven, subMat, deltaMat, deltaF, matOfBool]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have hrow : ∀ x : Fin (a + 1),
      (∑ y : Fin (b + 2), Fin.cases (∑ y' : Fin (b + 1), A x.succ y'.succ) (fun y' : Fin (b + 1) => A x.succ y'.succ) y *
        b2f (P x.succ y)) =
      (∑ y' : Fin (b + 1), A x.succ y'.succ) * b2f (P x.succ 0) +
      ∑ y' : Fin (b + 1), A x.succ y'.succ * b2f (P x.succ y'.succ) := by
    intro x
    rw [Fin.sum_univ_succ]
    simp
  simp_rw [hrow, Finset.sum_add_distrib]
  have h1 : (∑ x : Fin (a + 1), ∑ y : Fin (b + 1),
      A x.succ y.succ * (b2f (P x.succ y.succ) + b2f (P x.succ 0) + b2f (P 0 y.succ) + b2f (P 0 0))) =
      (∑ x : Fin (a + 1), ∑ y : Fin (b + 1), A x.succ y.succ * b2f (P x.succ y.succ)) +
      (∑ x : Fin (a + 1), (∑ y : Fin (b + 1), A x.succ y.succ) * b2f (P x.succ 0)) +
      (∑ y : Fin (b + 1), (∑ x : Fin (a + 1), A x.succ y.succ) * b2f (P 0 y.succ)) +
      (∑ x : Fin (a + 1), ∑ y : Fin (b + 1), A x.succ y.succ) * b2f (P 0 0) := by
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    congr 1
    exact Finset.sum_comm
  rw [h1]
  ring

noncomputable def charSum (a b t : ℕ) (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) : ℤ := by
  classical
  exact ∑ P : Fin (a + 2) → Fin (b + 2) → Bool,
    if okP a b t P then sgn (ipMat A (matOfBool P)) else 0

lemma charSum_eq_zero_of_not_evenMargins {a b t : ℕ}
    (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) (h : ¬ evenMargins A) :
    charSum a b t A = 0 := by
  classical
  unfold evenMargins at h
  push_neg at h
  have hcases : (∃ x0, ∑ y, A x0 y ≠ 0) ∨ (∃ y0, ∑ x, A x y0 ≠ 0) := by
    by_cases h1 : ∀ x, (∑ y, A x y) = 0
    · exact Or.inr (h h1)
    · push_neg at h1; exact Or.inl h1
  rcases hcases with ⟨x0, hx0⟩ | ⟨y0, hy0⟩
  · have hx1 : (∑ y, A x0 y) = 1 := (f2_eq_zero_or_one _).resolve_left hx0
    let inv : (Fin (a + 2) → Fin (b + 2) → Bool) ≃ (Fin (a + 2) → Fin (b + 2) → Bool) :=
      { toFun := fun P x y => if x = x0 then !P x y else P x y
        invFun := fun P x y => if x = x0 then !P x y else P x y
        left_inv := fun P => by ext x y; by_cases hx : x = x0 <;> simp [hx]
        right_inv := fun P => by ext x y; by_cases hx : x = x0 <;> simp [hx] }
    have hdel : ∀ P, deltaMat (inv P) = deltaMat P := by
      intro P
      have heq : (fun x y => b2f (inv P x y)) =
          fun x y => b2f (P x y) + ((if x = x0 then (1 : F2) else 0) + 0) := by
        ext x y
        change b2f (if x = x0 then !P x y else P x y) = _
        by_cases hx : x = x0
        · subst hx; simp only [↓reduceIte, add_zero]; cases P x y <;> rfl
        · simp [hx]
      simp only [deltaMat]
      rw [heq, deltaF_add, deltaF_sep, add_zero]
    have hok : ∀ P, okP a b t (inv P) ↔ okP a b t P := by
      intro P; rw [okP_iff, okP_iff, hdel]
    have hip : ∀ P, ipMat A (matOfBool (inv P)) = ipMat A (matOfBool P) + 1 := by
      intro P
      simp only [ipMat, matOfBool]
      have hterm : ∀ x y, A x y * b2f (inv P x y) =
          A x y * b2f (P x y) + if x = x0 then A x y else 0 := by
        intro x y
        change A x y * b2f (if x = x0 then !P x y else P x y) = _
        by_cases hx : x = x0
        · subst hx
          simp only [↓reduceIte]
          have hb : b2f (!P x y) = b2f (P x y) + 1 := by cases P x y <;> rfl
          rw [hb]; ring
        · simp [hx]
      simp_rw [hterm, Finset.sum_add_distrib]
      congr 1
      have : (∑ x, ∑ y, if x = x0 then A x y else 0) = ∑ x, if x = x0 then ∑ y, A x y else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : x = x0 <;> simp [hx]
      rw [this, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hx1]
    have hS : charSum a b t A = -charSum a b t A := by
      unfold charSum
      conv_lhs => rw [← Equiv.sum_comp inv]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      by_cases hp : okP a b t P
      · rw [if_pos ((hok P).mpr hp), if_pos hp, hip P, sgn_add, sgn_one, mul_neg_one]
      · rw [if_neg (fun h' => hp ((hok P).mp h')), if_neg hp, neg_zero]
    omega
  · have hy1 : (∑ x, A x y0) = 1 := (f2_eq_zero_or_one _).resolve_left hy0
    let inv : (Fin (a + 2) → Fin (b + 2) → Bool) ≃ (Fin (a + 2) → Fin (b + 2) → Bool) :=
      { toFun := fun P x y => if y = y0 then !P x y else P x y
        invFun := fun P x y => if y = y0 then !P x y else P x y
        left_inv := fun P => by ext x y; by_cases hy : y = y0 <;> simp [hy]
        right_inv := fun P => by ext x y; by_cases hy : y = y0 <;> simp [hy] }
    have hdel : ∀ P, deltaMat (inv P) = deltaMat P := by
      intro P
      have heq : (fun x y => b2f (inv P x y)) =
          fun x y => b2f (P x y) + (0 + if y = y0 then (1 : F2) else 0) := by
        ext x y
        change b2f (if y = y0 then !P x y else P x y) = _
        by_cases hy : y = y0
        · subst hy; simp only [↓reduceIte, zero_add]; cases P x y <;> rfl
        · simp [hy]
      simp only [deltaMat]
      rw [heq, deltaF_add, deltaF_sep, add_zero]
    have hok : ∀ P, okP a b t (inv P) ↔ okP a b t P := by
      intro P; rw [okP_iff, okP_iff, hdel]
    have hip : ∀ P, ipMat A (matOfBool (inv P)) = ipMat A (matOfBool P) + 1 := by
      intro P
      simp only [ipMat, matOfBool]
      have hterm : ∀ x y, A x y * b2f (inv P x y) =
          A x y * b2f (P x y) + if y = y0 then A x y else 0 := by
        intro x y
        change A x y * b2f (if y = y0 then !P x y else P x y) = _
        by_cases hy : y = y0
        · subst hy
          simp only [↓reduceIte]
          have hb : b2f (!P x y) = b2f (P x y) + 1 := by cases P x y <;> rfl
          rw [hb]; ring
        · simp [hy]
      simp_rw [hterm, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      have : (∑ y, ∑ x, if y = y0 then A x y else 0) = ∑ y, if y = y0 then ∑ x, A x y else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : y = y0 <;> simp [hy]
      rw [this, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hy1]
    have hS : charSum a b t A = -charSum a b t A := by
      unfold charSum
      conv_lhs => rw [← Equiv.sum_comp inv]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      by_cases hp : okP a b t P
      · rw [if_pos ((hok P).mpr hp), if_pos hp, hip P, sgn_add, sgn_one, mul_neg_one]
      · rw [if_neg (fun h' => hp ((hok P).mp h')), if_neg hp, neg_zero]
    omega

noncomputable def rankSum {m n : ℕ} (r : ℕ) (B : Matrix (Fin m) (Fin n) F2) : ℤ := by
  classical
  exact ∑ X : Matrix (Fin m) (Fin n) F2, if X.rank ≤ r then sgn (ipMat B X) else 0

def f2b (x : F2) : Bool := decide (x = 1)

lemma b2f_f2b (x : F2) : b2f (f2b x) = x := by
  fin_cases x <;> rfl

lemma f2b_b2f (b : Bool) : f2b (b2f b) = b := by
  cases b <;> rfl

lemma charSum_evenMargins {a b t : ℕ} (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2)
    (h : evenMargins A) :
    charSum a b t A = (2 ^ (a + b + 3) : ℤ) * rankSum (2 * t) (subMat A) := by
  classical
  let e : (Fin (a + 2) → Fin (b + 2) → Bool) ≃
      Matrix (Fin (a + 1)) (Fin (b + 1)) F2 × (Fin (a + 2) → F2) × (Fin (b + 1) → F2) :=
    { toFun := fun P => (deltaMat P, fun x => b2f (P x 0), fun y => b2f (P 0 y.succ))
      invFun := fun ⟨X, c0, r0⟩ x y =>
        f2b (Fin.cases (Fin.cases (c0 0) r0 y)
          (fun x' => Fin.cases (c0 x'.succ) (fun y' => X x' y' + c0 x'.succ + r0 y' + c0 0) y) x)
      left_inv := fun P => by
        ext x y
        apply b2f_injective
        rw [b2f_f2b]
        refine Fin.cases ?_ (fun x' => Fin.cases ?_ (fun y' => ?_) y) x
        · refine Fin.cases ?_ (fun y' => ?_) y <;> simp
        · simp
        · simp only [Fin.cases_succ, deltaMat, deltaF]
          have h2z : (2 : F2) = 0 := rfl
          ring_nf; simp [h2z]
      right_inv := fun ⟨X, c0, r0⟩ => by
        ext x y
        · simp only [deltaMat, deltaF, b2f_f2b, Fin.cases_zero, Fin.cases_succ]
          have h2z : (2 : F2) = 0 := rfl
          ring_nf; simp [h2z]
        · refine Fin.cases ?_ (fun x' => ?_) x <;> simp [b2f_f2b]
        · simp [b2f_f2b] }
  unfold charSum rankSum
  rw [← Equiv.sum_comp e.symm]
  have h1 : ∀ z : Matrix (Fin (a + 1)) (Fin (b + 1)) F2 × (Fin (a + 2) → F2) × (Fin (b + 1) → F2),
      (if okP a b t (e.symm z) then sgn (ipMat A (matOfBool (e.symm z))) else 0) =
      if z.1.rank ≤ 2 * t then sgn (ipMat (subMat A) z.1) else 0 := by
    intro z
    have hdel : deltaMat (e.symm z) = z.1 := congrArg Prod.fst (e.apply_symm_apply z)
    rw [okP_iff, ipMat_evenMargins A h, hdel]
    by_cases hr : z.1.rank ≤ 2 * t <;> simp [hr]
  simp_rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hexp : ((2 ^ (a + 2) : ℕ) : ℤ) * ((2 ^ (b + 1) : ℕ) : ℤ) = (2 ^ (a + b + 3) : ℤ) := by
    push_cast; rw [← pow_add]; congr 1; omega
  rw [← mul_assoc, hexp]

lemma rank_mul_left_inv {m n : ℕ} (U U' : Matrix (Fin m) (Fin m) F2) (hU : U' * U = 1)
    (X : Matrix (Fin m) (Fin n) F2) : (U * X).rank = X.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_right U X
  · calc X.rank = (U' * (U * X)).rank := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
      _ ≤ (U * X).rank := Matrix.rank_mul_le_right U' (U * X)

lemma rank_mul_right_inv {m n : ℕ} (V V' : Matrix (Fin n) (Fin n) F2) (hV : V * V' = 1)
    (X : Matrix (Fin m) (Fin n) F2) : (X * V).rank = X.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_left X V
  · calc X.rank = ((X * V) * V').rank := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
      _ ≤ (X * V).rank := Matrix.rank_mul_le_left (X * V) V'

lemma ipMat_mul_left_right {m n : ℕ} (U : Matrix (Fin m) (Fin m) F2)
    (V : Matrix (Fin n) (Fin n) F2) (B X : Matrix (Fin m) (Fin n) F2) :
    ipMat (U * B * V) X = ipMat B (Uᵀ * X * Vᵀ) := by
  simp only [ipMat, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : (∑ i, ∑ j, (∑ q, (∑ p, U i p * B p q) * V q j) * X i j) =
      ∑ p, ∑ q, B p q * ∑ i, ∑ j, U i p * X i j * V q j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext q
      rw [Finset.sum_comm]
      arg 2; ext i
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext q
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : (∑ p, ∑ q, B p q * ∑ j, (∑ i, U i p * X i j) * V q j) =
      ∑ p, ∑ q, B p q * ∑ i, ∑ j, U i p * X i j * V q j := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h1, h2]

lemma rankSum_mul {m n : ℕ} (r : ℕ) (U U' : Matrix (Fin m) (Fin m) F2)
    (V V' : Matrix (Fin n) (Fin n) F2)
    (hU1 : U * U' = 1) (hU2 : U' * U = 1) (hV1 : V * V' = 1) (hV2 : V' * V = 1)
    (B : Matrix (Fin m) (Fin n) F2) :
    rankSum r (U * B * V) = rankSum r B := by
  classical
  have hUT1 : Uᵀ * U'ᵀ = 1 := by rw [← Matrix.transpose_mul, hU2, Matrix.transpose_one]
  have hUT2 : U'ᵀ * Uᵀ = 1 := by rw [← Matrix.transpose_mul, hU1, Matrix.transpose_one]
  have hVT1 : Vᵀ * V'ᵀ = 1 := by rw [← Matrix.transpose_mul, hV2, Matrix.transpose_one]
  have hVT2 : V'ᵀ * Vᵀ = 1 := by rw [← Matrix.transpose_mul, hV1, Matrix.transpose_one]
  let e : Matrix (Fin m) (Fin n) F2 ≃ Matrix (Fin m) (Fin n) F2 :=
    { toFun := fun X => Uᵀ * X * Vᵀ
      invFun := fun X => U'ᵀ * X * V'ᵀ
      left_inv := fun X => by
        dsimp only
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hVT1, Matrix.mul_one, ← Matrix.mul_assoc, hUT2, Matrix.one_mul]
      right_inv := fun X => by
        dsimp only
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hVT2, Matrix.mul_one, ← Matrix.mul_assoc, hUT1, Matrix.one_mul] }
  unfold rankSum
  conv_rhs => rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [ipMat_mul_left_right]
  have hrk : (e X).rank = X.rank := by
    change (Uᵀ * X * Vᵀ).rank = X.rank
    rw [rank_mul_right_inv Vᵀ V'ᵀ hVT1, rank_mul_left_inv Uᵀ U'ᵀ hUT2]
  rw [hrk]
  rfl

def blockMat {a b : ℕ} (c : F2) (w : Fin b → F2) (u : Fin a → F2)
    (Y : Matrix (Fin a) (Fin b) F2) : Matrix (Fin (a + 1)) (Fin (b + 1)) F2 :=
  Fin.cases (Fin.cases c w) (fun i => Fin.cases (u i) (Y i))

lemma blockMat_zero_zero {a b : ℕ} (c : F2) (w : Fin b → F2) (u : Fin a → F2)
    (Y : Matrix (Fin a) (Fin b) F2) : blockMat c w u Y 0 0 = c := rfl

lemma rank_blockMat_diag {a b : ℕ} (c : F2) (Y : Matrix (Fin a) (Fin b) F2) :
    (blockMat c 0 0 Y).rank = Y.rank + (if c = 0 then 0 else 1) := by
  let M := blockMat c 0 0 Y
  let e : (Fin (a + 1) → F2) ≃ₗ[F2] F2 × (Fin a → F2) :=
    { toFun := fun z => (z 0, fun i => z i.succ)
      invFun := fun p => Fin.cases p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun z => by ext i; refine Fin.cases rfl (fun _ => rfl) i
      right_inv := fun ⟨_, _⟩ => rfl }
  have hrange : Submodule.map e.toLinearMap (LinearMap.range M.mulVecLin) =
      (Submodule.span F2 {c}).prod (LinearMap.range Y.mulVecLin) := by
    ext ⟨z0, z1⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_prod,
      LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, h⟩
      have h0 : z0 = c * x 0 := by
        have := congrArg Prod.fst h
        simp only [e, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct] at this
        rw [Fin.sum_univ_succ] at this
        simpa [M, blockMat] using this.symm
      have h1 : z1 = Y.mulVec (fun j => x j.succ) := by
        have := congrArg Prod.snd h
        ext i
        have hi := congrFun this i
        simp only [e, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct] at hi ⊢
        rw [Fin.sum_univ_succ] at hi
        simpa [M, blockMat] using hi.symm
      refine ⟨?_, ⟨fun j => x j.succ, h1.symm⟩⟩
      rw [h0, mul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton c))
    · rintro ⟨hz0, ⟨y, hy⟩⟩
      rw [Submodule.mem_span_singleton] at hz0
      obtain ⟨s, rfl⟩ := hz0
      refine ⟨M.mulVec (Fin.cases s y), ⟨Fin.cases s y, rfl⟩, ?_⟩
      refine Prod.ext ?_ (funext fun i => ?_)
      · simp only [e, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
        rw [Fin.sum_univ_succ]
        simp [M, blockMat, mul_comm]
      · simp only [e, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
        rw [Fin.sum_univ_succ]
        have hyi := congrFun hy i
        simp only [Matrix.mulVec, dotProduct] at hyi
        simpa [M, blockMat] using hyi
  let ep : ((Submodule.span F2 {c}).prod (LinearMap.range Y.mulVecLin)) ≃ₗ[F2]
      (Submodule.span F2 {c}) × (LinearMap.range Y.mulVecLin) :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Matrix.rank, Matrix.rank, ← LinearEquiv.finrank_map_eq e, hrange,
    LinearEquiv.finrank_eq ep, Module.finrank_prod]
  rcases f2_eq_zero_or_one c with rfl | rfl
  · simp [add_comm]
  · have h1 : Module.finrank F2 (Submodule.span F2 ({(1 : F2)} : Set F2)) = 1 := by
      rw [finrank_span_singleton (one_ne_zero)]
    simp [h1, add_comm]

lemma swapMat_mul_self {n : ℕ} (a0 i0 : Fin n) :
    let P : Matrix (Fin n) (Fin n) F2 := fun i j => if j = Equiv.swap a0 i0 i then 1 else 0
    P * P = 1 := by
  intro P
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  dsimp only [P]
  have h1 : ∀ k : Fin n,
      (if k = Equiv.swap a0 i0 i then (1 : F2) else 0) *
      (if j = Equiv.swap a0 i0 k then 1 else 0) =
      if k = Equiv.swap a0 i0 i then (if j = i then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = Equiv.swap a0 i0 i
    · subst hk; simp [Equiv.swap_apply_self]
    · simp [hk]
  simp_rw [h1, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  by_cases hij : i = j <;> simp [hij, eq_comm]

lemma exists_pivot_block {a b : ℕ} (B : Matrix (Fin (a + 1)) (Fin (b + 1)) F2) (hB : B ≠ 0) :
    ∃ (U U' : Matrix (Fin (a + 1)) (Fin (a + 1)) F2)
      (V V' : Matrix (Fin (b + 1)) (Fin (b + 1)) F2)
      (B' : Matrix (Fin a) (Fin b) F2),
      U * U' = 1 ∧ U' * U = 1 ∧ V * V' = 1 ∧ V' * V = 1 ∧
      U * B * V = blockMat 1 0 0 B' ∧ B'.rank + 1 = B.rank := by
  have hex : ∃ i0 j0, B i0 j0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hB (Matrix.ext h)
  obtain ⟨i0, j0, hij⟩ := hex
  have hij1 : B i0 j0 = 1 := (f2_eq_zero_or_one _).resolve_left hij
  let P : Matrix (Fin (a + 1)) (Fin (a + 1)) F2 := fun i k => if k = Equiv.swap 0 i0 i then 1 else 0
  let Q : Matrix (Fin (b + 1)) (Fin (b + 1)) F2 := fun k j => if k = Equiv.swap 0 j0 j then 1 else 0
  have hP2 : P * P = 1 := swapMat_mul_self 0 i0
  have hQ2 : Q * Q = 1 := by
    have := swapMat_mul_self 0 j0
    have hQt : Q = (fun i j => if j = Equiv.swap 0 j0 i then 1 else 0) := by
      ext i j
      have : (i = Equiv.swap 0 j0 j) ↔ (j = Equiv.swap 0 j0 i) := by
        constructor <;> intro h <;> subst h <;> simp
      simp [Q, this]
    rw [hQt]; exact this
  let B1 := P * B * Q
  have hB1_00 : B1 0 0 = 1 := by
    change (P * B * Q) 0 0 = 1
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    dsimp only [P, Q]
    have h1 : ∀ k : Fin (b + 1),
        (∑ l, (if l = Equiv.swap 0 i0 0 then (1 : F2) else 0) * B l k) *
        (if k = Equiv.swap 0 j0 0 then 1 else 0) =
        if k = j0 then B i0 j0 else 0 := by
      intro k
      have hs : (∑ l, (if l = Equiv.swap 0 i0 0 then (1 : F2) else 0) * B l k) = B i0 k := by
        simp [Equiv.swap_apply_left]
      rw [hs, Equiv.swap_apply_left]
      by_cases hk : k = j0 <;> simp [hk]
    simp_rw [h1, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hij1]
  let u : Fin a → F2 := fun i => B1 i.succ 0
  let L : Matrix (Fin (a + 1)) (Fin (a + 1)) F2 := blockMat 1 0 u 1
  have hL2 : L * L = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [L, blockMat]
      · simp [L, blockMat, Ne.symm (Fin.succ_ne_zero _)]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp only [L, blockMat, Fin.cases_zero, Fin.cases_succ, mul_one, Matrix.one_apply,
          Fin.succ_ne_zero, ↓reduceIte]
        have : (∑ k : Fin a, (if i' = k then (1 : F2) else 0) * u k) = u i' := by simp
        rw [this, f2_add_self]
      · simp only [L, blockMat, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, mul_zero, zero_add,
          Matrix.one_apply, Fin.succ_inj]
        have : (∑ k : Fin a, (if i' = k then (1 : F2) else 0) * (if k = j' then 1 else 0)) =
            if i' = j' then 1 else 0 := by
          by_cases h : i' = j' <;> simp [h]
        exact this
  let B2 := L * B1
  have hB2_00 : B2 0 0 = 1 := by
    simp only [B2, Matrix.mul_apply]
    rw [Fin.sum_univ_succ]
    simp [L, blockMat, hB1_00]
  have hB2_i0 : ∀ i : Fin a, B2 i.succ 0 = 0 := by
    intro i
    simp only [B2, Matrix.mul_apply]
    rw [Fin.sum_univ_succ]
    simp only [L, blockMat, Fin.cases_zero, Fin.cases_succ, hB1_00, mul_one, Matrix.one_apply]
    have : (∑ k : Fin a, (if i = k then (1 : F2) else 0) * B1 k.succ 0) = u i := by simp [u]
    rw [this, f2_add_self]
  let w : Fin b → F2 := fun j => B2 0 j.succ
  let R : Matrix (Fin (b + 1)) (Fin (b + 1)) F2 := blockMat 1 w 0 1
  have hR2 : R * R = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [R, blockMat]
      · simp only [R, blockMat, Fin.cases_zero, Fin.cases_succ, one_mul, Matrix.one_apply,
          Ne.symm (Fin.succ_ne_zero _), ↓reduceIte]
        have : (∑ k : Fin b, w k * (if k = j' then (1 : F2) else 0)) = w j' := by simp
        rw [this, f2_add_self]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [R, blockMat]
      · simp only [R, blockMat, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, zero_mul, zero_add,
          Matrix.one_apply, Fin.succ_inj]
        have : (∑ k : Fin b, (if i' = k then (1 : F2) else 0) * (if k = j' then 1 else 0)) =
            if i' = j' then 1 else 0 := by
          by_cases h : i' = j' <;> simp [h]
        exact this
  let B3 := B2 * R
  let B' : Matrix (Fin a) (Fin b) F2 := fun i j => B3 i.succ j.succ
  have hB3 : B3 = blockMat 1 0 0 B' := by
    ext i j
    refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j' => ?_) j) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp only [B3, Matrix.mul_apply, blockMat, Fin.cases_zero]
        rw [Fin.sum_univ_succ]; simp [R, blockMat, hB2_00]
      · simp only [B3, Matrix.mul_apply, blockMat, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply]
        rw [Fin.sum_univ_succ]
        simp only [R, blockMat, Fin.cases_zero, Fin.cases_succ, hB2_00, one_mul, Matrix.one_apply]
        have : (∑ k : Fin b, B2 0 k.succ * (if k = j' then (1 : F2) else 0)) = w j' := by simp [w]
        rw [this, f2_add_self]
    · simp only [B3, Matrix.mul_apply, blockMat, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply]
      rw [Fin.sum_univ_succ]; simp [R, blockMat, hB2_i0]
    · rfl
  refine ⟨L * P, P * L, Q * R, R * Q, B', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hP2, Matrix.one_mul, hL2]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL2, Matrix.one_mul, hP2]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, hR2, Matrix.one_mul, hQ2]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ2, Matrix.one_mul, hR2]
  · calc (L * P) * B * (Q * R) = L * (P * B * Q) * R := by simp [Matrix.mul_assoc]
      _ = B3 := rfl
      _ = blockMat 1 0 0 B' := hB3
  · have hU2 : (P * L) * (L * P) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL2, Matrix.one_mul, hP2]
    have hV1 : (Q * R) * (R * Q) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, hR2, Matrix.one_mul, hQ2]
    have hrk : (blockMat 1 0 0 B').rank = B.rank := by
      rw [← hB3]
      have : B3 = (L * P) * B * (Q * R) := by simp [B3, B2, B1, Matrix.mul_assoc]
      rw [this, rank_mul_right_inv _ _ hV1, rank_mul_left_inv _ _ hU2]
    rw [rank_blockMat_diag] at hrk
    simpa using hrk

lemma rank_blockMat_schur {a b : ℕ} (c : F2) (w : Fin b → F2) (u : Fin a → F2)
    (Y : Matrix (Fin a) (Fin b) F2) (ξ : Fin b → F2) (η : Fin a → F2)
    (hu : Y.mulVec ξ = u) (hw : Yᵀ.mulVec η = w) :
    (blockMat c w u Y).rank = Y.rank + (if c + dotProduct η u = 0 then 0 else 1) := by
  let L : Matrix (Fin (a + 1)) (Fin (a + 1)) F2 := blockMat 1 η 0 1
  let R : Matrix (Fin (b + 1)) (Fin (b + 1)) F2 := blockMat 1 0 ξ 1
  have hL2 : L * L = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [L, blockMat]
      · simp only [L, blockMat, Fin.cases_zero, Fin.cases_succ, one_mul, Matrix.one_apply,
          Ne.symm (Fin.succ_ne_zero _), ↓reduceIte]
        have : (∑ k : Fin a, η k * (if k = j' then (1 : F2) else 0)) = η j' := by simp
        rw [this, f2_add_self]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [L, blockMat]
      · simp only [L, blockMat, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, zero_mul, zero_add,
          Matrix.one_apply, Fin.succ_inj]
        by_cases h : i' = j' <;> simp [h]
  have hR2 : R * R = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [R, blockMat]
      · simp [R, blockMat, Ne.symm (Fin.succ_ne_zero _)]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp only [R, blockMat, Fin.cases_zero, Fin.cases_succ, mul_one, Matrix.one_apply,
          Fin.succ_ne_zero, ↓reduceIte]
        have : (∑ k : Fin b, (if i' = k then (1 : F2) else 0) * ξ k) = ξ i' := by simp
        rw [this, f2_add_self]
      · simp only [R, blockMat, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, mul_zero, zero_add,
          Matrix.one_apply, Fin.succ_inj]
        by_cases h : i' = j' <;> simp [h]
  have hmul : L * blockMat c w u Y * R = blockMat (c + dotProduct η u) 0 0 Y := by
    have hL : ∀ i j, (L * blockMat c w u Y) i j =
        Fin.cases (Fin.cases (c + dotProduct η u) (fun j' => 0) j)
          (fun i' => Fin.cases (u i') (Y i') j) i := by
      intro i j
      simp only [Matrix.mul_apply]
      rw [Fin.sum_univ_succ]
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [L, blockMat, dotProduct]
        · simp only [L, blockMat, Fin.cases_zero, Fin.cases_succ, one_mul]
          have h1 : (∑ k : Fin a, η k * Y k j') = w j' := by
            have := congrFun hw j'
            simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using this
          rw [h1, f2_add_self]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [L, blockMat, Matrix.one_apply]
        · simp [L, blockMat, Matrix.one_apply]
    ext i j
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_succ]
    simp_rw [hL]
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [R, blockMat]
      · simp [R, blockMat, Pi.zero_apply]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp only [R, blockMat, Fin.cases_zero, Fin.cases_succ, mul_one, Pi.zero_apply]
        have h1 : (∑ k : Fin b, Y i' k * ξ k) = u i' := congrFun hu i'
        rw [h1, f2_add_self]
      · simp [R, blockMat, Matrix.one_apply, Pi.zero_apply]
  have hrk : (L * blockMat c w u Y * R).rank = (blockMat c w u Y).rank := by
    rw [rank_mul_right_inv R R hR2, rank_mul_left_inv L L hL2]
  rw [← hrk, hmul, rank_blockMat_diag]

lemma rank_blockMat_indep_col {a b : ℕ} (w : Fin b → F2) (u : Fin a → F2)
    (Y : Matrix (Fin a) (Fin b) F2) (hu : u ∉ LinearMap.range Y.mulVecLin) :
    (blockMat 0 w u Y).rank = (blockMat 1 w u Y).rank := by
  have hcol : ∀ c : F2,
      (blockMat c w u Y).rank =
        Module.finrank F2 (Submodule.span F2 (Set.range fun j : Fin b => (blockMat c w u Y).col j.succ)) + 1 := by
    intro c
    rw [Matrix.rank_eq_finrank_span_cols]
    let S := Submodule.span F2 (Set.range fun j : Fin b => (blockMat c w u Y).col j.succ)
    have hsp : Submodule.span F2 (Set.range (blockMat c w u Y).col) =
        Submodule.span F2 {(blockMat c w u Y).col 0} ⊔ S := by
      rw [← Submodule.span_union]
      congr 1
      ext v
      simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        refine Fin.cases (Or.inl rfl) (fun j' => Or.inr ⟨j', rfl⟩) j
      · rintro (rfl | ⟨j', rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨j'.succ, rfl⟩
    have hnot : (blockMat c w u Y).col 0 ∉ S := by
      intro hmem
      have hproj : ∀ v ∈ S, (fun i : Fin a => v i.succ) ∈ LinearMap.range Y.mulVecLin := by
        intro v hv
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨j, rfl⟩
          exact ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec, dotProduct, Matrix.col, blockMat, Pi.single_apply]⟩
        · exact Submodule.zero_mem _
        · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
        · intro r x _ hx; exact Submodule.smul_mem _ r hx
      have hu' := hproj _ hmem
      have heq : (fun i : Fin a => (blockMat c w u Y).col 0 i.succ) = u := rfl
      rw [heq] at hu'
      exact hu hu'
    have hne : (blockMat c w u Y).col 0 ≠ 0 := by
      intro hz; apply hnot; rw [hz]; exact Submodule.zero_mem _
    have hinf : Submodule.span F2 {(blockMat c w u Y).col 0} ⊓ S = ⊥ := by
      rw [eq_bot_iff]
      intro v ⟨hv1, hv2⟩
      rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hv1
      obtain ⟨r, rfl⟩ := hv1
      rcases f2_eq_zero_or_one r with rfl | rfl
      · simp
      · simp only [one_smul] at hv2; exact (hnot hv2).elim
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span F2 {(blockMat c w u Y).col 0}) S
    rw [← hsp, hinf, finrank_bot, add_zero, finrank_span_singleton hne] at hsup
    dsimp only [S] at hsup
    omega
  rw [hcol 0, hcol 1]
  have hS : (Set.range fun j : Fin b => (blockMat 0 w u Y).col j.succ) =
      Set.range fun j : Fin b => (blockMat 1 w u Y).col j.succ := by
    congr 1; ext j i
    refine Fin.cases rfl (fun _ => rfl) i
  rw [hS]

lemma rank_blockMat_indep_row {a b : ℕ} (w : Fin b → F2) (u : Fin a → F2)
    (Y : Matrix (Fin a) (Fin b) F2) (hw : w ∉ LinearMap.range Yᵀ.mulVecLin) :
    (blockMat 0 w u Y).rank = (blockMat 1 w u Y).rank := by
  have ht : ∀ c : F2, (blockMat c w u Y)ᵀ = blockMat c u w Yᵀ := by
    intro c; ext i j
    refine Fin.cases (Fin.cases rfl (fun _ => rfl) j) (fun _ => Fin.cases rfl (fun _ => rfl) j) i
  rw [← Matrix.rank_transpose (blockMat 0 w u Y), ← Matrix.rank_transpose (blockMat 1 w u Y),
    ht 0, ht 1]
  exact rank_blockMat_indep_col u w Yᵀ hw

noncomputable def preimg {a b : ℕ} (Y : Matrix (Fin a) (Fin b) F2) (w : Fin b → F2) : Fin a → F2 := by
  classical
  exact if hw : ∃ η : Fin a → F2, Yᵀ.mulVec η = w then Classical.choose hw else 0

lemma mulVec_preimg {a b : ℕ} (Y : Matrix (Fin a) (Fin b) F2) (w : Fin b → F2)
    (hw : w ∈ LinearMap.range Yᵀ.mulVecLin) :
    Yᵀ.mulVec (preimg Y w) = w := by
  classical
  have hex : ∃ η : Fin a → F2, Yᵀ.mulVec η = w := by
    obtain ⟨η, hη⟩ := hw
    rw [Matrix.mulVecLin_apply] at hη
    exact ⟨η, hη⟩
  simp only [preimg, dif_pos hex]
  exact Classical.choose_spec hex

lemma bilinear_sgn_sum {a b : ℕ} (Y : Matrix (Fin a) (Fin b) F2) :
    (∑ u : LinearMap.range Y.mulVecLin, ∑ w : LinearMap.range Yᵀ.mulVecLin,
      sgn (dotProduct (preimg Y w.1) u.1)) = (2 ^ Y.rank : ℤ) := by
  classical
  have hwd : ∀ (ξ : Fin b → F2) (η : Fin a → F2),
      dotProduct (preimg Y (Yᵀ.mulVec η)) (Y.mulVec ξ) = dotProduct η (Y.mulVec ξ) := by
    intro ξ η
    have hspec : Yᵀ.mulVec (preimg Y (Yᵀ.mulVec η)) = Yᵀ.mulVec η :=
      mulVec_preimg Y (Yᵀ.mulVec η) ⟨η, rfl⟩
    have h1 : ∀ v : Fin a → F2, dotProduct v (Y.mulVec ξ) = dotProduct (Yᵀ.mulVec v) ξ := by
      intro v
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h1, hspec]
  have hfib_u : ∀ u : LinearMap.range Y.mulVecLin,
      (Finset.univ.filter fun ξ : Fin b → F2 => Y.mulVec ξ = u.1).card =
      Fintype.card (LinearMap.ker Y.mulVecLin) := by
    intro u
    obtain ⟨ξ0, hξ0⟩ := u.2
    rw [Matrix.mulVecLin_apply] at hξ0
    let e : (LinearMap.ker Y.mulVecLin) ≃ {ξ : Fin b → F2 // Y.mulVec ξ = u.1} :=
      { toFun := fun k => ⟨ξ0 + k.1, by
          have hk : Y.mulVec k.1 = 0 := k.2
          rw [Matrix.mulVec_add, hξ0, hk, add_zero]⟩
        invFun := fun ξ => ⟨ξ.1 + ξ0, by
          show Y.mulVec (ξ.1 + ξ0) = 0
          rw [Matrix.mulVec_add, ξ.2, hξ0]
          ext i; exact f2_add_self _⟩
        left_inv := fun k => by
          ext i; simp only [Pi.add_apply]; rw [add_right_comm, f2_add_self, zero_add]
        right_inv := fun ξ => by
          ext i; simp only [Pi.add_apply]; rw [add_left_comm, f2_add_self, add_zero] }
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr e).symm
  have hfib_w : ∀ w : LinearMap.range Yᵀ.mulVecLin,
      (Finset.univ.filter fun η : Fin a → F2 => Yᵀ.mulVec η = w.1).card =
      Fintype.card (LinearMap.ker Yᵀ.mulVecLin) := by
    intro w
    obtain ⟨η0, hη0⟩ := w.2
    rw [Matrix.mulVecLin_apply] at hη0
    let e : (LinearMap.ker Yᵀ.mulVecLin) ≃ {η : Fin a → F2 // Yᵀ.mulVec η = w.1} :=
      { toFun := fun k => ⟨η0 + k.1, by
          have hk : Yᵀ.mulVec k.1 = 0 := k.2
          rw [Matrix.mulVec_add, hη0, hk, add_zero]⟩
        invFun := fun η => ⟨η.1 + η0, by
          show Yᵀ.mulVec (η.1 + η0) = 0
          rw [Matrix.mulVec_add, η.2, hη0]
          ext i; exact f2_add_self _⟩
        left_inv := fun k => by
          ext i; simp only [Pi.add_apply]; rw [add_right_comm, f2_add_self, zero_add]
        right_inv := fun η => by
          ext i; simp only [Pi.add_apply]; rw [add_left_comm, f2_add_self, add_zero] }
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr e).symm
  have hbig :
      (Fintype.card (LinearMap.ker Y.mulVecLin) : ℤ) *
      (Fintype.card (LinearMap.ker Yᵀ.mulVecLin) : ℤ) *
      (∑ u : LinearMap.range Y.mulVecLin, ∑ w : LinearMap.range Yᵀ.mulVecLin,
        sgn (dotProduct (preimg Y w.1) u.1)) =
      ∑ ξ : Fin b → F2, ∑ η : Fin a → F2, sgn (dotProduct η (Y.mulVec ξ)) := by
    have hL : (∑ ξ : Fin b → F2, ∑ η : Fin a → F2, sgn (dotProduct η (Y.mulVec ξ))) =
        ∑ u : LinearMap.range Y.mulVecLin, ∑ ξ ∈ Finset.univ.filter (fun ξ => Y.mulVec ξ = u.1),
        ∑ w : LinearMap.range Yᵀ.mulVecLin, ∑ η ∈ Finset.univ.filter (fun η => Yᵀ.mulVec η = w.1),
          sgn (dotProduct (preimg Y w.1) u.1) := by
      have hpart1 : ∀ g : (Fin b → F2) → ℤ,
          (∑ ξ : Fin b → F2, g ξ) =
          ∑ u : LinearMap.range Y.mulVecLin,
            ∑ ξ ∈ Finset.univ.filter (fun ξ => Y.mulVec ξ = u.1), g ξ := by
        intro g
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun ξ : Fin b → F2 =>
            (⟨Y.mulVec ξ, ⟨ξ, rfl⟩⟩ : LinearMap.range Y.mulVecLin)) (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr ?_ fun _ _ => rfl
        ext ξ; simp [Subtype.ext_iff]
      have hpart2 : ∀ (ξ : Fin b → F2) (g : (Fin a → F2) → ℤ),
          (∑ η : Fin a → F2, g η) =
          ∑ w : LinearMap.range Yᵀ.mulVecLin,
            ∑ η ∈ Finset.univ.filter (fun η => Yᵀ.mulVec η = w.1), g η := by
        intro _ g
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun η : Fin a → F2 =>
            (⟨Yᵀ.mulVec η, ⟨η, rfl⟩⟩ : LinearMap.range Yᵀ.mulVecLin)) (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr ?_ fun _ _ => rfl
        ext η; simp [Subtype.ext_iff]
      rw [hpart1]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun ξ hξ => ?_
      rw [hpart2 ξ]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun η hη => ?_
      have hu : Y.mulVec ξ = u.1 := (Finset.mem_filter.mp hξ).2
      have hw : Yᵀ.mulVec η = w.1 := (Finset.mem_filter.mp hη).2
      rw [← hu, ← hw]
      exact congrArg sgn (hwd ξ η).symm
    rw [hL]
    simp_rw [Finset.sum_const, nsmul_eq_mul, hfib_w, hfib_u, ← Finset.mul_sum]
    ring
  have hrhs : (∑ ξ : Fin b → F2, ∑ η : Fin a → F2, sgn (dotProduct η (Y.mulVec ξ))) =
      (Fintype.card (LinearMap.ker Y.mulVecLin) : ℤ) * (2 ^ a : ℤ) := by
    have hinner : ∀ ξ : Fin b → F2,
        (∑ η : Fin a → F2, sgn (dotProduct η (Y.mulVec ξ))) =
        if Y.mulVec ξ = 0 then (2 ^ a : ℤ) else 0 := by
      intro ξ
      have : (∑ η : Fin a → F2, sgn (dotProduct η (Y.mulVec ξ))) =
          ∑ η : Fin a → F2, sgn (∑ i, (Y.mulVec ξ) i * η i) := by
        refine Finset.sum_congr rfl fun η _ => ?_
        congr 1; simp only [dotProduct]; refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [this, sum_sgn_fin]
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Finset.univ.filter fun ξ : Fin b → F2 => Y.mulVec ξ = 0).card =
        Fintype.card (LinearMap.ker Y.mulVecLin) := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    exact congrArg Nat.cast hcard
  have hkerT : (Fintype.card (LinearMap.ker Yᵀ.mulVecLin) : ℤ) * (2 ^ Y.rank : ℤ) = (2 ^ a : ℤ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Yᵀ.mulVecLin
    rw [Module.finrank_pi] at h1
    have h2 : Module.finrank F2 (LinearMap.range Yᵀ.mulVecLin) = Y.rank := by
      rw [← Matrix.rank, Matrix.rank_transpose]
    have h3 : Fintype.card (LinearMap.ker Yᵀ.mulVecLin) =
        2 ^ Module.finrank F2 (LinearMap.ker Yᵀ.mulVecLin) := by
      have := Module.card_eq_pow_finrank (K := F2) (V := LinearMap.ker Yᵀ.mulVecLin)
      simpa [ZMod.card] using this
    rw [h3]
    push_cast
    rw [← pow_add, add_comm, ← h2, h1, Fintype.card_fin]
  have hne1 : (Fintype.card (LinearMap.ker Y.mulVecLin) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hne2 : (Fintype.card (LinearMap.ker Yᵀ.mulVecLin) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hprod : (Fintype.card (LinearMap.ker Y.mulVecLin) : ℤ) *
      (Fintype.card (LinearMap.ker Yᵀ.mulVecLin) : ℤ) ≠ 0 := mul_ne_zero hne1 hne2
  apply mul_left_cancel₀ hprod
  rw [hbig, hrhs, ← hkerT]
  ring

lemma rankSum_block {a b : ℕ} (r : ℕ) (B' : Matrix (Fin a) (Fin b) F2) :
    rankSum r (blockMat 1 0 0 B') =
      (2 ^ r : ℤ) * ∑ Y : Matrix (Fin a) (Fin b) F2,
        if Y.rank = r then sgn (ipMat B' Y) else 0 := by
  classical
  let e : Matrix (Fin (a + 1)) (Fin (b + 1)) F2 ≃
      Matrix (Fin a) (Fin b) F2 × (Fin a → F2) × (Fin b → F2) × F2 :=
    { toFun := fun X => (fun i j => X i.succ j.succ, fun i => X i.succ 0, fun j => X 0 j.succ, X 0 0)
      invFun := fun ⟨Y, u, w, c⟩ => blockMat c w u Y
      left_inv := fun X => by
        ext i j
        refine Fin.cases (Fin.cases rfl (fun _ => rfl) j) (fun _ => Fin.cases rfl (fun _ => rfl) j) i
      right_inv := fun ⟨Y, u, w, c⟩ => by
        ext <;> rfl }
  unfold rankSum
  rw [← Equiv.sum_comp e.symm]
  have hip : ∀ Y u w c, ipMat (blockMat 1 0 0 B') (blockMat c w u Y) = c + ipMat B' Y := by
    intro Y u w c
    simp only [ipMat]
    rw [Fin.sum_univ_succ]
    have h0 : (∑ j : Fin (b + 1), blockMat 1 0 0 B' 0 j * blockMat c w u Y 0 j) = c := by
      rw [Fin.sum_univ_succ]; simp [blockMat]
    have hs : ∀ i : Fin a,
        (∑ j : Fin (b + 1), blockMat 1 0 0 B' i.succ j * blockMat c w u Y i.succ j) =
        ∑ j : Fin b, B' i j * Y i j := by
      intro i; rw [Fin.sum_univ_succ]; simp [blockMat]
    rw [h0]
    simp_rw [hs]
  simp_rw [Fintype.sum_prod_type]
  have hY : ∀ Y : Matrix (Fin a) (Fin b) F2,
      (∑ u : Fin a → F2, ∑ w : Fin b → F2, ∑ c : F2,
        if (blockMat c w u Y).rank ≤ r then sgn (ipMat (blockMat 1 0 0 B') (blockMat c w u Y)) else 0) =
      if Y.rank = r then (2 ^ r : ℤ) * sgn (ipMat B' Y) else 0 := by
    intro Y
    have hinner : ∀ u w,
        (∑ c : F2, if (blockMat c w u Y).rank ≤ r then
          sgn (ipMat (blockMat 1 0 0 B') (blockMat c w u Y)) else 0) =
        if u ∈ LinearMap.range Y.mulVecLin ∧ w ∈ LinearMap.range Yᵀ.mulVecLin ∧ Y.rank = r then
          sgn (dotProduct (preimg Y w) u) * sgn (ipMat B' Y)
        else 0 := by
      intro u w
      have hsum2 : ∀ f : F2 → ℤ, (∑ c : F2, f c) = f 0 + f 1 := by
        intro f
        rw [show (Finset.univ : Finset F2) = {0, 1} by decide, Finset.sum_pair zero_ne_one]
      rw [hsum2, hip Y u w 0, hip Y u w 1, zero_add, sgn_add, sgn_one]
      by_cases hu : u ∈ LinearMap.range Y.mulVecLin
      · by_cases hw : w ∈ LinearMap.range Yᵀ.mulVecLin
        · obtain ⟨ξ, hξ⟩ := hu
          rw [Matrix.mulVecLin_apply] at hξ
          have hη := mulVec_preimg Y w hw
          have hr0 := rank_blockMat_schur 0 w u Y ξ (preimg Y w) hξ hη
          have hr1 := rank_blockMat_schur 1 w u Y ξ (preimg Y w) hξ hη
          by_cases heq : Y.rank = r
          · conv_rhs => rw [if_pos ⟨⟨ξ, hξ⟩, hw, heq⟩]
            rcases f2_eq_zero_or_one (dotProduct (preimg Y w) u) with hd | hd
            · simp [hr0, hr1, hd, heq, sgn_zero]
            · simp [hr0, hr1, hd, heq, sgn_one, f2_add_self]
          · conv_rhs => rw [if_neg (fun h => heq h.2.2)]
            rcases lt_or_gt_of_ne heq with hlt | hgt
            · have hle0 : (blockMat 0 w u Y).rank ≤ r := by rw [hr0]; split_ifs <;> omega
              have hle1 : (blockMat 1 w u Y).rank ≤ r := by rw [hr1]; split_ifs <;> omega
              simp [hle0, hle1]
            · have hgt0 : ¬ (blockMat 0 w u Y).rank ≤ r := by rw [hr0]; split_ifs <;> omega
              have hgt1 : ¬ (blockMat 1 w u Y).rank ≤ r := by rw [hr1]; split_ifs <;> omega
              simp [hgt0, hgt1]
        · conv_rhs => rw [if_neg (fun h => hw h.2.1)]
          have hsame := rank_blockMat_indep_row w u Y hw
          rw [hsame]
          by_cases hle : (blockMat 1 w u Y).rank ≤ r <;> simp [hle]
      · conv_rhs => rw [if_neg (fun h => hu h.1)]
        have hsame := rank_blockMat_indep_col w u Y hu
        rw [hsame]
        by_cases hle : (blockMat 1 w u Y).rank ≤ r <;> simp [hle]
    by_cases heq : Y.rank = r
    · rw [if_pos heq]
      simp_rw [hinner]
      have hs1 : (∑ u : Fin a → F2, ∑ w : Fin b → F2,
          if u ∈ LinearMap.range Y.mulVecLin ∧ w ∈ LinearMap.range Yᵀ.mulVecLin ∧ Y.rank = r then
            sgn (dotProduct (preimg Y w) u) * sgn (ipMat B' Y)
          else 0) =
          (∑ u : LinearMap.range Y.mulVecLin, ∑ w : LinearMap.range Yᵀ.mulVecLin,
            sgn (dotProduct (preimg Y w.1) u.1)) * sgn (ipMat B' Y) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.sum_mul]
        have hsub_w : ∀ u : Fin a → F2,
            (∑ w : LinearMap.range Yᵀ.mulVecLin, sgn (dotProduct (preimg Y w.1) u) * sgn (ipMat B' Y)) =
            ∑ w : Fin b → F2,
              if w ∈ LinearMap.range Yᵀ.mulVecLin then sgn (dotProduct (preimg Y w) u) * sgn (ipMat B' Y) else 0 := by
          intro u
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun w _ => (w : Fin b → F2)) ?_ ?_ ?_ ?_
          · intro w _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2⟩
          · intro w1 _ w2 _ h; exact Subtype.ext h
          · intro w hw; exact ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        symm
        simp_rw [hsub_w]
        have hsub_u :
            (∑ u : LinearMap.range Y.mulVecLin,
              ∑ w : Fin b → F2,
                if w ∈ LinearMap.range Yᵀ.mulVecLin then sgn (dotProduct (preimg Y w) u.1) * sgn (ipMat B' Y) else 0) =
            ∑ u ∈ Finset.univ.filter (fun u : Fin a → F2 => u ∈ LinearMap.range Y.mulVecLin),
              ∑ w : Fin b → F2,
                if w ∈ LinearMap.range Yᵀ.mulVecLin then sgn (dotProduct (preimg Y w) u) * sgn (ipMat B' Y) else 0 := by
          refine Finset.sum_bij (fun u _ => (u : Fin a → F2)) ?_ ?_ ?_ ?_
          · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩
          · intro u1 _ u2 _ h; exact Subtype.ext h
          · intro u hu; exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        rw [hsub_u, Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u ∈ LinearMap.range Y.mulVecLin
        · simp only [hu, ↓reduceIte, true_and, heq, and_true]
        · simp only [hu, ↓reduceIte, false_and, Finset.sum_const_zero]
      rw [hs1, bilinear_sgn_sum Y, heq]
    · rw [if_neg heq]
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun w _ => ?_
      rw [hinner u w, if_neg (fun h => heq h.2.2)]
  change (∑ Y : Matrix (Fin a) (Fin b) F2, ∑ u : Fin a → F2, ∑ w : Fin b → F2, ∑ c : F2,
    if (blockMat c w u Y).rank ≤ r then sgn (ipMat (blockMat 1 0 0 B') (blockMat c w u Y)) else 0) = _
  simp_rw [hY, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => by
    by_cases hr : Y.rank = r <;> simp [hr]

lemma exists_two_rank_r_diff {a b r : ℕ} (hr2 : 2 ≤ r) (hra : r ≤ a) (hrb : r ≤ b)
    (B' : Matrix (Fin a) (Fin b) F2) (hB' : B' ≠ 0) :
    ∃ Y1 Y2 : Matrix (Fin a) (Fin b) F2,
      Y1.rank = r ∧ Y2.rank = r ∧ ipMat B' Y1 ≠ ipMat B' Y2 := by
  have hex : ∃ i0 j0, B' i0 j0 ≠ 0 := by
    by_contra h; push_neg at h; exact hB' (Matrix.ext h)
  obtain ⟨i0, j0, hij⟩ := hex
  have hij1 : B' i0 j0 = 1 := (f2_eq_zero_or_one _).resolve_left hij
  let σ : Equiv.Perm (Fin a) := Equiv.swap ⟨0, by omega⟩ i0
  let τ : Equiv.Perm (Fin b) := Equiv.swap ⟨0, by omega⟩ j0
  let Y0 : Matrix (Fin a) (Fin b) F2 := fun i j =>
    if hi : i.val < r then
      if j.val = (i.val + 1) % r then 1 else 0
    else 0
  let Y0' : Matrix (Fin a) (Fin b) F2 := fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else Y0 i j
  have hrk0 : Y0.rank = r := by
    rw [Matrix.rank]
    let S := Submodule.span F2 {v : Fin a → F2 | ∃ k : Fin r, v = Pi.single ⟨k.val, by omega⟩ 1}
    have hrange : LinearMap.range Y0.mulVecLin = S := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        have hvec : Y0.mulVec x = ∑ k : Fin r, x ⟨(k.val + 1) % r, by
            have := Nat.mod_lt (k.val + 1) (by omega : 0 < r); omega⟩ •
            Pi.single ⟨k.val, by omega⟩ (1 : F2) := by
          ext i
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Pi.single_apply]
          by_cases hi : i.val < r
          · have h1 : (∑ j : Fin b, Y0 i j * x j) =
                x ⟨(i.val + 1) % r, by have := Nat.mod_lt (i.val + 1) (by omega : 0 < r); omega⟩ := by
              have hterm : ∀ j : Fin b, Y0 i j * x j =
                  if j = ⟨(i.val + 1) % r, by have := Nat.mod_lt (i.val + 1) (by omega : 0 < r); omega⟩ then
                    x j else 0 := by
                intro j
                simp only [Y0, dif_pos hi]
                by_cases hj : j.val = (i.val + 1) % r
                · have : j = ⟨(i.val + 1) % r, by have := Nat.mod_lt (i.val + 1) (by omega : 0 < r); omega⟩ :=
                    Fin.ext hj
                  simp [hj, this]
                · have : j ≠ ⟨(i.val + 1) % r, by have := Nat.mod_lt (i.val + 1) (by omega : 0 < r); omega⟩ :=
                    fun h => hj (congrArg Fin.val h)
                  simp [hj, this]
              simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
            have h2 : (∑ k : Fin r, x ⟨(k.val + 1) % r, by
                have := Nat.mod_lt (k.val + 1) (by omega : 0 < r); omega⟩ *
                if i = ⟨k.val, by omega⟩ then (1 : F2) else 0) =
                x ⟨(i.val + 1) % r, by have := Nat.mod_lt (i.val + 1) (by omega : 0 < r); omega⟩ := by
              have hterm : ∀ k : Fin r,
                  x ⟨(k.val + 1) % r, by have := Nat.mod_lt (k.val + 1) (by omega : 0 < r); omega⟩ *
                  (if i = ⟨k.val, by omega⟩ then (1 : F2) else 0) =
                  if k = ⟨i.val, hi⟩ then
                    x ⟨(k.val + 1) % r, by have := Nat.mod_lt (k.val + 1) (by omega : 0 < r); omega⟩
                  else 0 := by
                intro k
                by_cases hk : k = ⟨i.val, hi⟩
                · subst hk; simp
                · have hne : i ≠ ⟨k.val, by omega⟩ := fun h => hk (Fin.ext (congrArg Fin.val h).symm)
                  simp [hk, hne]
              simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
            rw [h1, h2]
          · simp only [Y0, dif_neg hi, zero_mul, Finset.sum_const_zero]
            symm
            refine Finset.sum_eq_zero fun k _ => ?_
            have hne : i ≠ ⟨k.val, by omega⟩ := fun h => hi (by rw [h]; exact k.isLt)
            simp [hne]
        rw [Matrix.mulVecLin_apply, hvec]
        exact Submodule.sum_mem _ fun k _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        refine ⟨Pi.single ⟨(k.val + 1) % r, by
            have := Nat.mod_lt (k.val + 1) (by omega : 0 < r); omega⟩ 1, ?_⟩
        ext i
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        by_cases hi : i.val < r
        · simp only [Y0, dif_pos hi]
          have hiff : ((i.val + 1) % r = (k.val + 1) % r) ↔ i = ⟨k.val, by omega⟩ := by
            constructor
            · intro hmod
              have h1 : i.val = k.val := by
                by_cases h1a : i.val + 1 < r <;> by_cases h1b : k.val + 1 < r
                · rw [Nat.mod_eq_of_lt h1a, Nat.mod_eq_of_lt h1b] at hmod; omega
                · rw [Nat.mod_eq_of_lt h1a, show k.val + 1 = r by omega, Nat.mod_self] at hmod; omega
                · rw [show i.val + 1 = r by omega, Nat.mod_self, Nat.mod_eq_of_lt h1b] at hmod; omega
                · omega
              exact Fin.ext h1
            · intro h; rw [h]
          by_cases hik : i = ⟨k.val, by omega⟩
          · rw [if_pos hik, if_pos (hiff.mpr hik).symm]
          · rw [if_neg hik, if_neg (fun h => hik (hiff.mp h.symm))]
        · simp only [Y0, dif_neg hi]
          have hne : i ≠ ⟨k.val, by omega⟩ := fun h => hi (by rw [h]; exact k.isLt)
          simp [hne]
    rw [hrange]
    have hli : LinearIndependent F2 (fun k : Fin r => (Pi.single ⟨k.val, by omega⟩ (1 : F2) : Fin a → F2)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have hk := congrFun hc ⟨k.val, by omega⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.zero_apply] at hk
      have : (∑ j : Fin r, c j * if (⟨k.val, by omega⟩ : Fin a) = ⟨j.val, by omega⟩ then (1 : F2) else 0) = c k := by
        have hterm : ∀ j : Fin r,
            c j * (if (⟨k.val, by omega⟩ : Fin a) = ⟨j.val, by omega⟩ then (1 : F2) else 0) =
            if j = k then c j else 0 := by
          intro j
          by_cases h : j = k
          · subst h; simp
          · have hne : (⟨k.val, by omega⟩ : Fin a) ≠ ⟨j.val, by omega⟩ :=
              fun h' => h (Fin.ext (congrArg Fin.val h').symm)
            simp [h, hne]
        simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      rw [this] at hk; exact hk
    have hset : {v : Fin a → F2 | ∃ k : Fin r, v = Pi.single ⟨k.val, by omega⟩ 1} =
        Set.range (fun k : Fin r => (Pi.single ⟨k.val, by omega⟩ (1 : F2) : Fin a → F2)) := by
      ext v; simp [eq_comm]
    rw [show S = Submodule.span F2 _ from rfl, hset, finrank_span_eq_card hli, Fintype.card_fin]
  have hrk0' : Y0'.rank = r := by
    let E : Matrix (Fin a) (Fin a) F2 := fun i k =>
      if i = k then 1 else if i.val = 0 ∧ k.val = r - 1 then 1 else 0
    have hE2 : E * E = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      dsimp only [E]
      by_cases hi0 : i.val = 0
      · have hne : i.val ≠ r - 1 := by omega
        have hterm : ∀ k : Fin a,
            (if i = k then (1 : F2) else if i.val = 0 ∧ k.val = r - 1 then 1 else 0) *
            (if k = j then 1 else if k.val = 0 ∧ j.val = r - 1 then 1 else 0) =
            (if k = i then (if i = j then 1 else if j.val = r - 1 then 1 else 0) else 0) +
            (if k = ⟨r - 1, by omega⟩ then (if (⟨r - 1, by omega⟩ : Fin a) = j then 1 else 0) else 0) := by
          intro k
          by_cases hki : k = i
          · subst hki
            have hne2 : k ≠ ⟨r - 1, by omega⟩ := fun h => hne (congrArg Fin.val h)
            simp [hi0, hne2]
          · by_cases hkr : k = ⟨r - 1, by omega⟩
            · subst hkr
              have h0ne : ¬ (r - 1 = 0) := by omega
              simp [hi0, Ne.symm hki, hki, h0ne]
            · have hkrv : k.val ≠ r - 1 := fun h => hkr (Fin.ext h)
              simp [Ne.symm hki, hki, hkr, hkrv]
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        by_cases hij : i = j
        · subst hij
          have hne2 : (⟨r - 1, by omega⟩ : Fin a) ≠ i := fun h => hne (congrArg Fin.val h).symm
          simp [hne2]
        · by_cases hjr : j.val = r - 1
          · have : (⟨r - 1, by omega⟩ : Fin a) = j := Fin.ext hjr.symm
            simp [hij, hjr, this, f2_add_self]
          · have : (⟨r - 1, by omega⟩ : Fin a) ≠ j := fun h => hjr (congrArg Fin.val h).symm
            simp [hij, hjr, this]
      · have hterm : ∀ k : Fin a,
            (if i = k then (1 : F2) else if i.val = 0 ∧ k.val = r - 1 then 1 else 0) *
            (if k = j then 1 else if k.val = 0 ∧ j.val = r - 1 then 1 else 0) =
            if k = i then (if i = j then 1 else 0) else 0 := by
          intro k
          by_cases hki : k = i
          · subst hki; simp [hi0]
          · simp [Ne.symm hki, hki, hi0]
        simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    have hmul : E * Y0 = Y0' := by
      ext i j
      rw [Matrix.mul_apply]
      dsimp only [E, Y0']
      by_cases hi0 : i.val = 0
      · have hne : i.val ≠ r - 1 := by omega
        have hterm : ∀ k : Fin a,
            (if i = k then (1 : F2) else if i.val = 0 ∧ k.val = r - 1 then 1 else 0) * Y0 k j =
            (if k = i then Y0 i j else 0) +
            (if k = ⟨r - 1, by omega⟩ then Y0 ⟨r - 1, by omega⟩ j else 0) := by
          intro k
          by_cases hki : k = i
          · subst hki
            have hne2 : k ≠ ⟨r - 1, by omega⟩ := fun h => hne (congrArg Fin.val h)
            simp [hne2]
          · by_cases hkr : k = ⟨r - 1, by omega⟩
            · subst hkr; simp [Ne.symm hki, hki, hi0]
            · have hkrv : k.val ≠ r - 1 := fun h => hkr (Fin.ext h)
              simp [Ne.symm hki, hki, hkr, hkrv]
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        have hlast : Y0 ⟨r - 1, by omega⟩ j = if j.val = 0 then 1 else 0 := by
          have hlt : r - 1 < r := by omega
          have hmod : (r - 1 + 1) % r = 0 := by rw [show r - 1 + 1 = r by omega, Nat.mod_self]
          simp [Y0, hlt, hmod]
        rw [hlast]
        by_cases hj0 : j.val = 0
        · have hy0 : Y0 i j = 0 := by
            have hlt : i.val < r := by omega
            have hmod : (i.val + 1) % r = 1 := by rw [hi0, Nat.mod_eq_of_lt (by omega)]
            simp [Y0, hlt, hmod, hj0]
          simp [hi0, hj0, hy0]
        · simp [hi0, hj0]
      · have hterm : ∀ k : Fin a,
            (if i = k then (1 : F2) else if i.val = 0 ∧ k.val = r - 1 then 1 else 0) * Y0 k j =
            if k = i then Y0 i j else 0 := by
          intro k
          by_cases hki : k = i
          · subst hki; simp [hi0]
          · simp [Ne.symm hki, hki, hi0]
        simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        simp [hi0]
    rw [← hmul, rank_mul_left_inv E E hE2, hrk0]
  let P : Matrix (Fin a) (Fin a) F2 := fun i k => if k = σ i then 1 else 0
  let Q : Matrix (Fin b) (Fin b) F2 := fun k j => if k = τ j then 1 else 0
  have hP2 : P * P = 1 := swapMat_mul_self ⟨0, by omega⟩ i0
  have hQ2 : Q * Q = 1 := by
    have hQt : Q = (fun i j => if j = τ i then 1 else 0) := by
      ext i j
      have : (i = τ j) ↔ (j = τ i) := by
        constructor <;> intro h <;> subst h <;> simp [τ]
      simp [Q, this]
    rw [hQt]
    exact swapMat_mul_self ⟨0, by omega⟩ j0
  refine ⟨P * Y0 * Q, P * Y0' * Q, ?_, ?_, ?_⟩
  · rw [rank_mul_right_inv Q Q hQ2, rank_mul_left_inv P P hP2, hrk0]
  · rw [rank_mul_right_inv Q Q hQ2, rank_mul_left_inv P P hP2, hrk0']
  · have hdiff : ipMat B' (P * Y0' * Q) = ipMat B' (P * Y0 * Q) + 1 := by
      have h1 : P * Y0' * Q = P * Y0 * Q + P * (Y0' + Y0) * Q := by
        rw [Matrix.mul_add, Matrix.add_mul, ← add_assoc]
        ext i j
        simp only [Matrix.add_apply]
        rw [add_right_comm, f2_add_self, zero_add]
      have hsub : ∀ i j, (P * (Y0' + Y0) * Q) i j = if i = i0 ∧ j = j0 then 1 else 0 := by
        intro i j
        have hY : ∀ p q, (Y0' + Y0) p q = if p = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩ then 1 else 0 := by
          intro p q
          rw [Matrix.add_apply]
          dsimp only [Y0']
          by_cases h0 : p.val = 0 ∧ q.val = 0
          · have hp : p = ⟨0, by omega⟩ := Fin.ext h0.1
            have hq : q = ⟨0, by omega⟩ := Fin.ext h0.2
            have hy : Y0 p q = 0 := by
              have hlt : p.val < r := by omega
              have hmod : (p.val + 1) % r = 1 := by rw [h0.1, Nat.mod_eq_of_lt (by omega)]
              simp [Y0, hlt, hmod, h0.2]
            rw [if_pos h0, if_pos ⟨hp, hq⟩, hy, add_zero]
          · have hne : ¬ (p = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩) := by
              rintro ⟨rfl, rfl⟩; exact h0 ⟨rfl, rfl⟩
            simp [h0, hne, f2_add_self]
        rw [Matrix.mul_apply]
        simp_rw [Matrix.mul_apply]
        dsimp only [P, Q]
        simp_rw [hY]
        have hs1 : ∀ q : Fin b,
            (∑ p : Fin a, (if p = σ i then (1 : F2) else 0) *
              (if p = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩ then 1 else 0)) =
            if σ i = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩ then 1 else 0 := by
          intro q
          have hterm : ∀ p : Fin a,
              (if p = σ i then (1 : F2) else 0) *
                (if p = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩ then 1 else 0) =
              if p = σ i then (if σ i = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩ then 1 else 0) else 0 := by
            intro p; by_cases hp : p = σ i <;> simp [hp]
          simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        simp_rw [hs1]
        have hs2 : ∀ q : Fin b,
            (if σ i = ⟨0, by omega⟩ ∧ q = ⟨0, by omega⟩ then (1 : F2) else 0) *
              (if q = τ j then 1 else 0) =
            if q = τ j then (if σ i = ⟨0, by omega⟩ ∧ τ j = ⟨0, by omega⟩ then 1 else 0) else 0 := by
          intro q; by_cases hq : q = τ j <;> simp [hq]
        simp_rw [hs2, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        have hi_iff : σ i = ⟨0, by omega⟩ ↔ i = i0 := by
          simp only [σ, Equiv.swap_apply_eq_iff]; simp
        have hj_iff : τ j = ⟨0, by omega⟩ ↔ j = j0 := by
          simp only [τ, Equiv.swap_apply_eq_iff]; simp
        simp [hi_iff, hj_iff]
      simp only [ipMat, h1, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
      congr 1
      simp_rw [hsub]
      have hterm : ∀ i, (∑ j, B' i j * (if i = i0 ∧ j = j0 then (1 : F2) else 0)) =
          if i = i0 then B' i0 j0 else 0 := by
        intro i
        by_cases hi : i = i0
        · subst hi; simp
        · simp [hi]
      simp_rw [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hij1]
    intro heq
    rw [heq] at hdiff
    have : (0 : F2) = 1 := by
      have h := congrArg (ipMat B' (P * Y0' * Q) + ·) hdiff
      rw [f2_add_self, ← add_assoc, f2_add_self, zero_add] at h
      exact h
    exact zero_ne_one this

lemma exists_rank_r_pos {a b r : ℕ} (hr2 : 2 ≤ r) (hra : r ≤ a) (hrb : r ≤ b) :
    0 < Nat.card {A : Matrix (Fin a) (Fin b) F2 // A.rank = r} := by
  let B0 : Matrix (Fin a) (Fin b) F2 := fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0
  have hB0 : B0 ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [B0] at this
  obtain ⟨Y1, _, h1, _, _⟩ := exists_two_rank_r_diff hr2 hra hrb B0 hB0
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
  exact ⟨⟨Y1, h1⟩⟩

lemma abs_sum_sgn_lt {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (f : α → F2)
    (x1 x2 : α) (hx1 : P x1) (hx2 : P x2) (hne : f x1 ≠ f x2) :
    |∑ x : α, if P x then sgn (f x) else 0| < ((Finset.univ.filter P).card : ℤ) := by
  classical
  have hne_x : x1 ≠ x2 := fun h => hne (congrArg f h)
  have h12 : sgn (f x1) + sgn (f x2) = 0 := by
    rcases f2_eq_zero_or_one (f x1) with h1 | h1 <;> rcases f2_eq_zero_or_one (f x2) with h2 | h2
    · exact (hne (h1.trans h2.symm)).elim
    · simp [h1, h2, sgn_zero, sgn_one]
    · simp [h1, h2, sgn_zero, sgn_one]
    · exact (hne (h1.trans h2.symm)).elim
  set S := Finset.univ.filter P
  have hS_eq : (∑ x : α, if P x then sgn (f x) else 0) = ∑ x ∈ S, sgn (f x) := by
    rw [Finset.sum_filter]
  rw [hS_eq]
  have hmem1 : x1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1⟩
  have hmem2 : x2 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx2⟩
  set T := (S.erase x1).erase x2
  have hsplit : (∑ x ∈ S, sgn (f x)) = (sgn (f x1) + sgn (f x2)) + ∑ x ∈ T, sgn (f x) := by
    have h1 := Finset.add_sum_erase S (fun x => sgn (f x)) hmem1
    have hmem2' : x2 ∈ S.erase x1 := Finset.mem_erase.mpr ⟨hne_x.symm, hmem2⟩
    have h2 := Finset.add_sum_erase (S.erase x1) (fun x => sgn (f x)) hmem2'
    rw [← h1, ← h2, add_assoc]
  rw [hsplit, h12, zero_add]
  have hcard : S.card = T.card + 2 := by
    have h1 := Finset.card_erase_add_one hmem1
    have hmem2' : x2 ∈ S.erase x1 := Finset.mem_erase.mpr ⟨hne_x.symm, hmem2⟩
    have h2 := Finset.card_erase_add_one hmem2'
    change T.card + 1 = (S.erase x1).card at h2
    omega
  have hle : |∑ x ∈ T, sgn (f x)| ≤ (T.card : ℤ) := by
    calc |∑ x ∈ T, sgn (f x)| ≤ ∑ x ∈ T, |sgn (f x)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _x ∈ T, (1 : ℤ) := Finset.sum_congr rfl fun x _ => abs_sgn (f x)
      _ = (T.card : ℤ) := by simp
  omega

lemma charSum_bound {a b t : ℕ} (ht : 0 < t) (hab : 2 * t ≤ min a b)
    (A : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) (hA : A ≠ 0) :
    let cap : ℕ := 2 ^ (a + b + 3 + 2 * t) * Nat.card {Y : Matrix (Fin a) (Fin b) F2 // Y.rank = 2 * t}
    |charSum a b t A| ≤ (cap : ℤ) ∧
    (evenMargins A ∧ (subMat A).rank = 1 → charSum a b t A = (cap : ℤ)) ∧
    (¬ (evenMargins A ∧ (subMat A).rank = 1) → |charSum a b t A| < (cap : ℤ)) := by
  classical
  set r := 2 * t
  set cap : ℕ := 2 ^ (a + b + 3 + r) * Nat.card {Y : Matrix (Fin a) (Fin b) F2 // Y.rank = r}
  have hr2 : 2 ≤ r := by omega
  have hra : r ≤ a := le_trans hab (min_le_left a b)
  have hrb : r ≤ b := le_trans hab (min_le_right a b)
  have hcap_pos : 0 < cap := by
    apply Nat.mul_pos (pow_pos (by decide) _) (exists_rank_r_pos hr2 hra hrb)
  have hcap_eq : (cap : ℤ) =
      (2 ^ (a + b + 3) : ℤ) * ((2 ^ r : ℤ) * (Nat.card {Y : Matrix (Fin a) (Fin b) F2 // Y.rank = r} : ℤ)) := by
    simp only [cap]; push_cast; rw [pow_add]; ring
  have hcard_eq : (Nat.card {Y : Matrix (Fin a) (Fin b) F2 // Y.rank = r} : ℤ) =
      ((Finset.univ.filter fun Y : Matrix (Fin a) (Fin b) F2 => Y.rank = r).card : ℤ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_cases hem : evenMargins A
  · have hsub_ne : subMat A ≠ 0 := by
      intro hz
      apply hA
      rw [← liftEven_subMat A hem, hz]
      ext x y
      refine Fin.cases (Fin.cases ?_ (fun _ => ?_) y) (fun _ => Fin.cases ?_ (fun _ => ?_) y) x <;>
        simp [liftEven]
    obtain ⟨U, U', V, V', B', hU1, hU2, hV1, hV2, hblk, hrk⟩ := exists_pivot_block (subMat A) hsub_ne
    have hcs : charSum a b t A =
        (2 ^ (a + b + 3) : ℤ) * ((2 ^ r : ℤ) *
          ∑ Y : Matrix (Fin a) (Fin b) F2, if Y.rank = r then sgn (ipMat (B') Y) else 0) := by
      rw [charSum_evenMargins A hem, ← rankSum_mul r U U' V V' hU1 hU2 hV1 hV2, hblk, rankSum_block]
    by_cases hr1 : (subMat A).rank = 1
    · have hB'0 : B' = 0 := by
        have hbr : B'.rank = 0 := by omega
        by_contra hne
        have hpos : 0 < B'.rank := by
          obtain ⟨i, j, hij⟩ : ∃ i j, B' i j ≠ 0 := by by_contra h; push_neg at h; exact hne (Matrix.ext h)
          have hmem : B'.col j ∈ LinearMap.range B'.mulVecLin :=
            ⟨Pi.single j 1, by ext k; simp [Matrix.mulVec, dotProduct, Matrix.col, Pi.single_apply]⟩
          have hne_col : (⟨B'.col j, hmem⟩ : LinearMap.range B'.mulVecLin) ≠ 0 := by
            intro hz; exact hij (congrFun (congrArg Subtype.val hz) i)
          exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne_col⟩
        omega
      have heq_cap : charSum a b t A = (cap : ℤ) := by
        rw [hcs, hB'0, hcap_eq, hcard_eq]
        congr 2
        have h0 : ∀ Y : Matrix (Fin a) (Fin b) F2, ipMat 0 Y = 0 := fun _ => by simp [ipMat]
        simp_rw [h0, sgn_zero, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      refine ⟨by rw [heq_cap, abs_of_nonneg (Nat.cast_nonneg _)], fun _ => heq_cap,
        fun h => (h ⟨hem, hr1⟩).elim⟩
    · have hB'ne : B' ≠ 0 := by
        intro h0; rw [h0, Matrix.rank_zero, zero_add] at hrk; exact hr1 hrk.symm
      obtain ⟨Y1, Y2, hY1, hY2, hdiff⟩ := exists_two_rank_r_diff hr2 hra hrb B' hB'ne
      have hlt_sum := abs_sum_sgn_lt (fun Y : Matrix (Fin a) (Fin b) F2 => Y.rank = r)
        (fun Y => ipMat B' Y) Y1 Y2 hY1 hY2 hdiff
      have hlt : |charSum a b t A| < (cap : ℤ) := by
        rw [hcs, hcap_eq, hcard_eq, abs_mul, abs_mul,
          abs_of_pos (pow_pos (by decide : (0 : ℤ) < 2) _),
          abs_of_pos (pow_pos (by decide : (0 : ℤ) < 2) _)]
        have hp1 : (0 : ℤ) < 2 ^ (a + b + 3) := pow_pos (by decide) _
        have hp2 : (0 : ℤ) < 2 ^ r := pow_pos (by decide) _
        exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hlt_sum hp2) hp1
      exact ⟨le_of_lt hlt, fun h => (hr1 h.2).elim, fun _ => hlt⟩
  · have h0 := charSum_eq_zero_of_not_evenMargins (t := t) A hem
    have hlt : |charSum a b t A| < (cap : ℤ) := by rw [h0, abs_zero]; exact_mod_cast hcap_pos
    exact ⟨le_of_lt hlt, fun h => (hem h.1).elim, fun _ => hlt⟩

def linComb {a b d : ℕ} (B : Fin d → Matrix (Fin (a + 2)) (Fin (b + 2)) F2)
    (c : Fin d → F2) : Matrix (Fin (a + 2)) (Fin (b + 2)) F2 :=
  ∑ i : Fin d, c i • B i

lemma linComb_eq_zero_iff {a b d : ℕ} (B : Fin d → Matrix (Fin (a + 2)) (Fin (b + 2)) F2)
    (hind : ∀ S : Finset (Fin d), S.Nonempty → S.sum B ≠ 0) (c : Fin d → F2) :
    linComb B c = 0 ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    let S := Finset.univ.filter fun i : Fin d => c i = 1
    have hSne : S.Nonempty := by
      have : ∃ i, c i ≠ 0 := by by_contra h'; push_neg at h'; exact hc (funext h')
      obtain ⟨i, hi⟩ := this
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (f2_eq_zero_or_one _).resolve_left hi⟩⟩
    have hsum : S.sum B = linComb B c := by
      unfold linComb
      rw [← Finset.sum_subset (Finset.filter_subset (fun i : Fin d => c i = 1) Finset.univ)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        have h1 : c i = 1 := (Finset.mem_filter.mp hi).2
        simp [h1]
      · intro i _ hi
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have h0 : c i = 0 := (f2_eq_zero_or_one _).resolve_right hi
        simp [h0]
    exact hind S hSne (hsum.trans h)
  · intro hc; subst hc; simp [linComb]

lemma charSum_zero {a b t : ℕ} :
    charSum a b t 0 = (Nat.card {P : Fin (a + 2) → Fin (b + 2) → Bool // okP a b t P} : ℤ) := by
  classical
  unfold charSum
  have h0 : ∀ P, ipMat (0 : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) (matOfBool P) = 0 :=
    fun _ => by simp [ipMat]
  simp_rw [h0, sgn_zero, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma cap_le_N {a b t : ℕ} (ht : 0 < t) (hab : 2 * t ≤ min a b) :
    2 ^ (a + b + 3 + 2 * t) * Nat.card {Y : Matrix (Fin a) (Fin b) F2 // Y.rank = 2 * t} ≤
      Nat.card {P : Fin (a + 2) → Fin (b + 2) → Bool // okP a b t P} := by
  classical
  let B0 : Matrix (Fin (a + 1)) (Fin (b + 1)) F2 := fun i j => if i = 0 ∧ j = 0 then 1 else 0
  let A0 := liftEven B0
  have hem : evenMargins A0 := liftEven_evenMargins B0
  have hrk : (subMat A0).rank = 1 := by
    rw [subMat_liftEven]
    have hB0 : B0 = blockMat 1 0 0 (0 : Matrix (Fin a) (Fin b) F2) := by
      ext i j
      refine Fin.cases (Fin.cases rfl (fun _ => rfl) j) (fun _ => Fin.cases rfl (fun _ => rfl) j) i
    rw [hB0, rank_blockMat_diag]; simp
  have hA0ne : A0 ≠ 0 := by
    intro h
    have := congrFun (congrFun h (0 : Fin (a + 1)).succ) (0 : Fin (b + 1)).succ
    simp only [A0, liftEven, Fin.cases_succ, B0, Matrix.zero_apply, and_self, ↓reduceIte] at this
    exact one_ne_zero this
  have hcap := (charSum_bound ht hab A0 hA0ne).2.1 ⟨hem, hrk⟩
  have hle : charSum a b t A0 ≤ charSum a b t 0 := by
    unfold charSum
    refine Finset.sum_le_sum fun P _ => ?_
    by_cases hp : okP a b t P
    · rw [if_pos hp, if_pos hp]
      have h0 : ipMat (0 : Matrix (Fin (a + 2)) (Fin (b + 2)) F2) (matOfBool P) = 0 := by simp [ipMat]
      rw [h0, sgn_zero]
      rcases f2_eq_zero_or_one (ipMat A0 (matOfBool P)) with h | h <;> simp [h, sgn_zero, sgn_one]
    · simp [hp]
  rw [hcap, charSum_zero] at hle
  exact_mod_cast hle

lemma sum_pow_fourier {d k : ℕ} (v : (Fin d → F2) → ℤ) :
    (∑ z : Fin d → F2, (∑ c : Fin d → F2, sgn (∑ i, c i * z i) * v c) ^ k) =
      (2 ^ d : ℤ) * ∑ tup : Fin k → (Fin d → F2),
        if (∑ j, tup j) = 0 then ∏ j, v (tup j) else 0 := by
  have hexp : ∀ z : Fin d → F2,
      (∑ c : Fin d → F2, sgn (∑ i, c i * z i) * v c) ^ k =
      ∑ tup : Fin k → (Fin d → F2),
        sgn (∑ i, (∑ j, tup j) i * z i) * ∏ j, v (tup j) := by
    intro z
    rw [Finset.sum_pow']
    refine Finset.sum_congr rfl fun tup _ => ?_
    rw [Finset.prod_mul_distrib, ← sgn_sum]
    congr 2
    simp only [Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : ∀ tup : Fin k → (Fin d → F2),
      (∑ z : Fin d → F2, sgn (∑ i, (∑ j, tup j) i * z i) * ∏ j, v (tup j)) =
      (2 ^ d : ℤ) * (if (∑ j, tup j) = 0 then ∏ j, v (tup j) else 0) := by
    intro tup
    rw [← Finset.sum_mul, sum_sgn_fin]
    split_ifs <;> ring
  simp_rw [hswap, ← Finset.mul_sum]

lemma moment_eq_fourier {a b t d k : ℕ}
    (B : Fin d → Matrix (Fin (a + 2)) (Fin (b + 2)) F2) :
    let hits := fun (z : Fin d → F2) =>
      Nat.card {P : Fin (a + 2) → Fin (b + 2) → Bool // okP a b t P ∧
        ∀ i, (∑ x, ∑ y, B i x y * b2f (P x y)) = z i}
    (((2 ^ d) ^ k * ∑ z : Fin d → F2, (hits z) ^ k : ℕ) : ℤ) =
      (2 ^ d : ℤ) * ∑ tup : Fin k → (Fin d → F2),
        if (∑ j, tup j) = 0 then ∏ j, charSum a b t (linComb B (tup j)) else 0 := by
  classical
  intro hits
  have hhit : ∀ z : Fin d → F2,
      ((2 ^ d : ℕ) : ℤ) * (hits z : ℤ) =
        ∑ c : Fin d → F2, sgn (∑ i, c i * z i) * charSum a b t (linComb B c) := by
    intro z
    have h1 : ∀ P : Fin (a + 2) → Fin (b + 2) → Bool,
        (∑ c : Fin d → F2, sgn (∑ i, c i * ((∑ x, ∑ y, B i x y * b2f (P x y)) + z i))) =
        if ∀ i, (∑ x, ∑ y, B i x y * b2f (P x y)) = z i then (2 ^ d : ℤ) else 0 := by
      intro P
      have heq : (∑ c : Fin d → F2, sgn (∑ i, c i * ((∑ x, ∑ y, B i x y * b2f (P x y)) + z i))) =
          ∑ c : Fin d → F2, sgn (∑ i, ((∑ x, ∑ y, B i x y * b2f (P x y)) + z i) * c i) := by
        refine Finset.sum_congr rfl fun c _ => by congr 1; refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [heq, sum_sgn_fin]
      have hiff : (fun i => (∑ x, ∑ y, B i x y * b2f (P x y)) + z i) = 0 ↔
          ∀ i, (∑ x, ∑ y, B i x y * b2f (P x y)) = z i := by
        constructor
        · intro h i
          have hi := congrFun h i
          simp only [Pi.zero_apply] at hi
          have h2 := congrArg (· + z i) hi
          rw [add_assoc, f2_add_self, add_zero, zero_add] at h2
          exact h2
        · intro h; ext i; simp only [Pi.zero_apply]; rw [h i, f2_add_self]
      by_cases hcond : ∀ i, (∑ x, ∑ y, B i x y * b2f (P x y)) = z i
      · rw [if_pos (hiff.mpr hcond), if_pos hcond]
      · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
    have hL : ((2 ^ d : ℕ) : ℤ) * (hits z : ℤ) =
        ∑ P : Fin (a + 2) → Fin (b + 2) → Bool,
          if okP a b t P then
            ∑ c : Fin d → F2, sgn (∑ i, c i * ((∑ x, ∑ y, B i x y * b2f (P x y)) + z i))
          else 0 := by
      simp_rw [h1]
      have h2 : (∑ P : Fin (a + 2) → Fin (b + 2) → Bool,
          if okP a b t P then
            if ∀ i, (∑ x, ∑ y, B i x y * b2f (P x y)) = z i then (2 ^ d : ℤ) else 0
          else 0) =
          ∑ P ∈ Finset.univ.filter (fun P : Fin (a + 2) → Fin (b + 2) → Bool =>
            okP a b t P ∧ ∀ i, (∑ x, ∑ y, B i x y * b2f (P x y)) = z i), (2 ^ d : ℤ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun P _ => by split_ifs <;> tauto
      rw [h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
      congr 1
      simp only [hits, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hL]
    have hR : (∑ P : Fin (a + 2) → Fin (b + 2) → Bool,
        if okP a b t P then
          ∑ c : Fin d → F2, sgn (∑ i, c i * ((∑ x, ∑ y, B i x y * b2f (P x y)) + z i))
        else 0) =
        ∑ c : Fin d → F2, sgn (∑ i, c i * z i) * charSum a b t (linComb B c) := by
      have hite : ∀ P,
          (if okP a b t P then
            ∑ c : Fin d → F2, sgn (∑ i, c i * ((∑ x, ∑ y, B i x y * b2f (P x y)) + z i))
          else 0) =
          ∑ c : Fin d → F2,
            if okP a b t P then
              sgn (∑ i, c i * z i) * sgn (ipMat (linComb B c) (matOfBool P))
            else 0 := by
        intro P
        by_cases hp : okP a b t P
        · rw [if_pos hp]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [if_pos hp, ← sgn_add]
          congr 1
          have hip : ipMat (linComb B c) (matOfBool P) =
              ∑ i, c i * ∑ x, ∑ y, B i x y * b2f (P x y) := by
            simp only [ipMat, linComb, matOfBool, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext y
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            conv_rhs => arg 2; ext x; rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
          rw [hip, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        · simp [hp]
      simp_rw [hite]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold charSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
    exact hR
  have hpow : (((2 ^ d) ^ k * ∑ z : Fin d → F2, (hits z) ^ k : ℕ) : ℤ) =
      ∑ z : Fin d → F2, (((2 ^ d : ℕ) : ℤ) * (hits z : ℤ)) ^ k := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by rw [mul_pow]
  rw [hpow]
  simp_rw [hhit]
  exact sum_pow_fourier (fun c => charSum a b t (linComb B c))

lemma bound_eq_fourier {d k N cap : ℕ} (hle : cap ≤ N) :
    let q := 2 ^ d
    (((N + (q - 1) * cap) ^ k + (q - 1) * (N - cap) ^ k : ℕ) : ℤ) =
      (2 ^ d : ℤ) * ∑ tup : Fin k → (Fin d → F2),
        if (∑ j, tup j) = 0 then ∏ j, (if tup j = 0 then (N : ℤ) else (cap : ℤ)) else 0 := by
  intro q
  let w : (Fin d → F2) → ℤ := fun c => if c = 0 then (N : ℤ) else (cap : ℤ)
  have h1 := sum_pow_fourier (d := d) (k := k) w
  rw [← h1]
  have hval : ∀ z : Fin d → F2,
      (∑ c : Fin d → F2, sgn (∑ i, c i * z i) * w c) =
      if z = 0 then (N : ℤ) + ((q - 1 : ℕ) : ℤ) * (cap : ℤ) else (N : ℤ) - (cap : ℤ) := by
    intro z
    have hsplit : (∑ c : Fin d → F2, sgn (∑ i, c i * z i) * w c) =
        ((N : ℤ) - (cap : ℤ)) + (cap : ℤ) * ∑ c : Fin d → F2, sgn (∑ i, c i * z i) := by
      have hterm : ∀ c : Fin d → F2,
          sgn (∑ i, c i * z i) * w c =
          (if c = 0 then (N : ℤ) - (cap : ℤ) else 0) + (cap : ℤ) * sgn (∑ i, c i * z i) := by
        intro c
        by_cases hc : c = 0
        · subst hc; simp [w, sgn_zero]
        · simp [w, hc, mul_comm]
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
        ← Finset.mul_sum]
    rw [hsplit]
    have hsumz : (∑ c : Fin d → F2, sgn (∑ i, c i * z i)) = if z = 0 then (2 ^ d : ℤ) else 0 := by
      have : (∑ c : Fin d → F2, sgn (∑ i, c i * z i)) =
          ∑ c : Fin d → F2, sgn (∑ i, z i * c i) :=
        Finset.sum_congr rfl fun c _ => by congr 1; refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [this, sum_sgn_fin]
    rw [hsumz]
    have hqpos : 1 ≤ q := Nat.one_le_pow d 2 (by decide)
    by_cases hz : z = 0
    · rw [if_pos hz, if_pos hz]
      have hq1 : ((q - 1 : ℕ) : ℤ) = (2 ^ d : ℤ) - 1 := by
        rw [Nat.cast_sub hqpos]; simp [q]
      rw [hq1]; ring
    · rw [if_neg hz, if_neg hz]; ring
  simp_rw [hval]
  have hsum_z : (∑ z : Fin d → F2,
      (if z = 0 then (N : ℤ) + ((q - 1 : ℕ) : ℤ) * (cap : ℤ) else (N : ℤ) - (cap : ℤ)) ^ k) =
      ((N : ℤ) + ((q - 1 : ℕ) : ℤ) * (cap : ℤ)) ^ k +
      ((q - 1 : ℕ) : ℤ) * ((N : ℤ) - (cap : ℤ)) ^ k := by
    have h0 := Finset.add_sum_erase Finset.univ
      (fun z : Fin d → F2 =>
        (if z = 0 then (N : ℤ) + ((q - 1 : ℕ) : ℤ) * (cap : ℤ) else (N : ℤ) - (cap : ℤ)) ^ k)
      (Finset.mem_univ (0 : Fin d → F2))
    rw [← h0, if_pos rfl]
    congr 1
    have her : (∑ z ∈ Finset.univ.erase (0 : Fin d → F2),
        (if z = 0 then (N : ℤ) + ((q - 1 : ℕ) : ℤ) * (cap : ℤ) else (N : ℤ) - (cap : ℤ)) ^ k) =
        ∑ _z ∈ Finset.univ.erase (0 : Fin d → F2), ((N : ℤ) - (cap : ℤ)) ^ k := by
      refine Finset.sum_congr rfl fun z hz => by rw [if_neg (Finset.ne_of_mem_erase hz)]
    rw [her, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Finset.univ.erase (0 : Fin d → F2)).card = q - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_pi]
      simp [q, ZMod.card]
    rw [hcard]
  rw [hsum_z]
  have hsub : ((N - cap : ℕ) : ℤ) = (N : ℤ) - (cap : ℤ) := Nat.cast_sub hle
  push_cast
  rw [hsub]

lemma rank_eq_one_iff_outer {m n : ℕ} (M : Matrix (Fin m) (Fin n) F2) :
    M.rank = 1 ↔ ∃ u v, u ≠ 0 ∧ v ≠ 0 ∧ M = outerMat u v := by
  constructor
  · intro hr
    obtain ⟨u1, v1, hdec⟩ := rank_decomp M (le_of_eq hr)
    rw [Fin.sum_univ_one] at hdec
    have hu : u1 0 ≠ 0 := by
      intro hz; rw [hdec, hz] at hr
      have : outerMat (0 : Fin m → F2) (v1 0) = 0 := by ext i j; simp [outerMat]
      rw [this, Matrix.rank_zero] at hr; omega
    have hv : v1 0 ≠ 0 := by
      intro hz; rw [hdec, hz] at hr
      have : outerMat (u1 0) (0 : Fin n → F2) = 0 := by ext i j; simp [outerMat]
      rw [this, Matrix.rank_zero] at hr; omega
    exact ⟨u1 0, v1 0, hu, hv, hdec⟩
  · rintro ⟨u, v, hu, hv, rfl⟩
    apply le_antisymm (rank_outerMat_le_one u v)
    have hne : outerMat u v ≠ 0 := by
      intro hz
      have ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by by_contra h; push_neg at h; exact hu (funext h)
      have ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by by_contra h; push_neg at h; exact hv (funext h)
      have h0 := congrFun (congrFun hz i) j
      simp [outerMat] at h0
      rcases h0 with h0 | h0
      · exact hi h0
      · exact hj h0
    obtain ⟨i, j, hij⟩ : ∃ i j, outerMat u v i j ≠ 0 := by
      by_contra h; push_neg at h; exact hne (Matrix.ext h)
    have hmem : (outerMat u v).col j ∈ LinearMap.range (outerMat u v).mulVecLin :=
      ⟨Pi.single j 1, by ext k; simp [Matrix.mulVec, dotProduct, Matrix.col, Pi.single_apply]⟩
    have hne_col : (⟨(outerMat u v).col j, hmem⟩ : LinearMap.range (outerMat u v).mulVecLin) ≠ 0 := by
      intro hz; exact hij (congrFun (congrArg Subtype.val hz) i)
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne_col⟩

lemma rank_outer_add_outer_ge_two {m n : ℕ} (u1 u2 : Fin m → F2) (v1 v2 : Fin n → F2)
    (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0) (hu12 : u1 ≠ u2)
    (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hv12 : v1 ≠ v2) :
    2 ≤ (outerMat u1 v1 + outerMat u2 v2).rank := by
  set M := outerMat u1 v1 + outerMat u2 v2
  have hcol : ∀ j : Fin n, M.col j = v1 j • u1 + v2 j • u2 := by
    intro j; ext i; simp [M, Matrix.col, outerMat, mul_comm]
  have hmem_col : ∀ j : Fin n, v1 j • u1 + v2 j • u2 ∈ LinearMap.range M.mulVecLin := by
    intro j
    rw [← hcol j]
    exact ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec, dotProduct, Matrix.col, Pi.single_apply]⟩
  have hboth : u1 ∈ LinearMap.range M.mulVecLin ∧ u2 ∈ LinearMap.range M.mulVecLin := by
    by_cases h1 : ∃ j, v1 j = 1 ∧ v2 j = 0
    · obtain ⟨j1, hj11, hj12⟩ := h1
      have hm1 : u1 ∈ LinearMap.range M.mulVecLin := by
        simpa [hj11, hj12] using hmem_col j1
      obtain ⟨j2, hj2⟩ : ∃ j, v2 j = 1 := by
        have : ∃ j, v2 j ≠ 0 := by by_contra h; push_neg at h; exact hv2 (funext h)
        obtain ⟨j, hj⟩ := this; exact ⟨j, (f2_eq_zero_or_one _).resolve_left hj⟩
      rcases f2_eq_zero_or_one (v1 j2) with h12 | h12
      · exact ⟨hm1, by simpa [h12, hj2] using hmem_col j2⟩
      · have hm12 : u1 + u2 ∈ LinearMap.range M.mulVecLin := by
          simpa [h12, hj2] using hmem_col j2
        have hm2 : u2 ∈ LinearMap.range M.mulVecLin := by
          have := Submodule.add_mem _ hm1 hm12
          have heq : u1 + (u1 + u2) = u2 := by ext i; simp [← add_assoc, f2_add_self]
          rwa [heq] at this
        exact ⟨hm1, hm2⟩
    · push_neg at h1
      have hsub : ∀ j, v1 j = 1 → v2 j = 1 := by
        intro j hj1
        exact (f2_eq_zero_or_one _).resolve_left (h1 j hj1)
      obtain ⟨j1, hj11⟩ : ∃ j, v1 j = 1 := by
        have : ∃ j, v1 j ≠ 0 := by by_contra h; push_neg at h; exact hv1 (funext h)
        obtain ⟨j, hj⟩ := this; exact ⟨j, (f2_eq_zero_or_one _).resolve_left hj⟩
      have hm12 : u1 + u2 ∈ LinearMap.range M.mulVecLin := by
        simpa [hj11, hsub j1 hj11] using hmem_col j1
      obtain ⟨j2, hj2⟩ : ∃ j, v1 j ≠ v2 j := by
        by_contra h; push_neg at h; exact hv12 (funext h)
      have hj21 : v1 j2 = 0 := by
        rcases f2_eq_zero_or_one (v1 j2) with h0 | h1'
        · exact h0
        · exact (hj2 (h1'.trans (hsub j2 h1').symm)).elim
      have hj22 : v2 j2 = 1 := by
        rw [hj21] at hj2; exact (f2_eq_zero_or_one _).resolve_left (Ne.symm hj2)
      have hm2 : u2 ∈ LinearMap.range M.mulVecLin := by
        simpa [hj21, hj22] using hmem_col j2
      have hm1 : u1 ∈ LinearMap.range M.mulVecLin := by
        have := Submodule.add_mem _ hm12 hm2
        have heq : (u1 + u2) + u2 = u1 := by ext i; simp [add_assoc, f2_add_self]
        rwa [heq] at this
      exact ⟨hm1, hm2⟩
  let f : Fin 2 → (Fin m → F2) := fun i => if i = 0 then u1 else u2
  have hli : LinearIndependent F2 f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • u1 + c 1 • u2 = 0 := by
      simpa only [Fin.sum_univ_two, f, ↓reduceIte, Fin.one_eq_zero_iff, Nat.succ_ne_self] using hc
    rcases f2_eq_zero_or_one (c 0) with h0 | h0 <;> rcases f2_eq_zero_or_one (c 1) with h1 | h1
    · intro i; fin_cases i
      · exact h0
      · exact h1
    · simp only [h0, h1, zero_smul, one_smul, zero_add] at hsum; exact (hu2 hsum).elim
    · simp only [h0, h1, zero_smul, one_smul, add_zero] at hsum; exact (hu1 hsum).elim
    · simp only [h0, h1, one_smul] at hsum
      have heq : u1 = u2 := by
        ext i
        have hi := congrFun hsum i
        simp only [Pi.add_apply, Pi.zero_apply] at hi
        have := congrArg (· + u2 i) hi
        rw [add_assoc, f2_add_self, add_zero, zero_add] at this
        exact this
      exact (hu12 heq).elim
  have hsub : Submodule.span F2 (Set.range f) ≤ LinearMap.range M.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hboth.1
    · exact hboth.2
  rw [Matrix.rank]
  have h2 : Module.finrank F2 (Submodule.span F2 (Set.range f)) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmono := Submodule.finrank_mono hsub
  rw [h2] at hmono
  exact hmono

lemma outerMat_eq_iff {m n : ℕ} (u1 u2 : Fin m → F2) (v1 v2 : Fin n → F2)
    (hu1 : u1 ≠ 0) (hv1 : v1 ≠ 0) :
    outerMat u1 v1 = outerMat u2 v2 → u1 = u2 ∧ v1 = v2 := by
  intro heq
  obtain ⟨i0, hi0⟩ : ∃ i, u1 i = 1 := by
    have : ∃ i, u1 i ≠ 0 := by by_contra h; push_neg at h; exact hu1 (funext h)
    obtain ⟨i, hi⟩ := this; exact ⟨i, (f2_eq_zero_or_one _).resolve_left hi⟩
  obtain ⟨j0, hj0⟩ : ∃ j, v1 j = 1 := by
    have : ∃ j, v1 j ≠ 0 := by by_contra h; push_neg at h; exact hv1 (funext h)
    obtain ⟨j, hj⟩ := this; exact ⟨j, (f2_eq_zero_or_one _).resolve_left hj⟩
  have h00 := congrFun (congrFun heq i0) j0
  simp only [outerMat, hi0, hj0, mul_one] at h00
  have hu2_i0 : u2 i0 = 1 := by
    rcases f2_eq_zero_or_one (u2 i0) with h | h
    · simp [h] at h00
    · exact h
  have hv2_j0 : v2 j0 = 1 := by
    rcases f2_eq_zero_or_one (v2 j0) with h | h
    · simp [h] at h00
    · exact h
  constructor
  · ext i
    have hi := congrFun (congrFun heq i) j0
    simpa [outerMat, hj0, hv2_j0] using hi
  · ext j
    have hj := congrFun (congrFun heq i0) j
    simpa [outerMat, hi0, hu2_i0] using hj

lemma rank_one_space_common {a b d : ℕ}
    (B : Fin d → Matrix (Fin (a + 2)) (Fin (b + 2)) F2)
    (hind : ∀ S : Finset (Fin d), S.Nonempty → S.sum B ≠ 0)
    (hall : ∀ c : Fin d → F2, c ≠ 0 → evenMargins (linComb B c) ∧ (subMat (linComb B c)).rank = 1) :
    (∀ i, evenMargins (B i)) ∧
    ((∃ u : Fin (a + 1) → F2, ∀ i, ∃ v : Fin (b + 1) → F2, ∀ x y, B i x.succ y.succ = u x * v y) ∨
     (∃ v : Fin (b + 1) → F2, ∀ i, ∃ u : Fin (a + 1) → F2, ∀ x y, B i x.succ y.succ = u x * v y)) := by
  have hev : ∀ i : Fin d, evenMargins (B i) := by
    intro i
    have h := (hall (Pi.single i 1) (by
      intro hz; have := congrFun hz i; simp at this)).1
    have hlin : linComb B (Pi.single i 1) = B i := by
      simp [linComb, Pi.single_apply]
    rwa [hlin] at h
  refine ⟨hev, ?_⟩
  by_cases hd0 : d = 0
  · subst hd0
    exact Or.inl ⟨0, fun i => Fin.elim0 i⟩
  have hfact : ∀ i : Fin d, ∃ u v, u ≠ 0 ∧ v ≠ 0 ∧ subMat (B i) = outerMat u v := by
    intro i
    have h := (hall (Pi.single i 1) (by
      intro hz; have := congrFun hz i; simp at this)).2
    have hlin : linComb B (Pi.single i 1) = B i := by simp [linComb, Pi.single_apply]
    rw [hlin] at h
    exact (rank_eq_one_iff_outer _).mp h
  choose u v hu hv hB using hfact
  by_cases hd1 : d = 1
  · refine Or.inl ⟨u ⟨0, by omega⟩, fun i => ⟨v i, fun x y => ?_⟩⟩
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi
    exact congrFun (congrFun (hB _) x) y
  have hd2 : 2 ≤ d := by omega
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have hpair : ∀ i j : Fin d, i ≠ j → u i = u j ∨ v i = v j := by
    intro i j hij
    by_contra h
    push_neg at h
    let c : Fin d → F2 := fun k => if k = i ∨ k = j then 1 else 0
    have hcne : c ≠ 0 := by
      intro hz; have := congrFun hz i; simp [c] at this
    have hlin : linComb B c = B i + B j := by
      simp only [linComb, c]
      have hterm : ∀ k : Fin d, (if k = i ∨ k = j then (1 : F2) else 0) • B k =
          (if k = i then B k else 0) + (if k = j then B k else 0) := by
        intro k
        by_cases hki : k = i
        · subst hki; simp [hij]
        · by_cases hkj : k = j
          · subst hkj; simp [hki]
          · simp [hki, hkj]
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    have hrk1 : (subMat (B i + B j)).rank = 1 := by
      rw [← hlin]; exact (hall c hcne).2
    have hsub_add : subMat (B i + B j) = outerMat (u i) (v i) + outerMat (u j) (v j) := by
      rw [← hB i, ← hB j]; rfl
    rw [hsub_add] at hrk1
    have hge2 := rank_outer_add_outer_ge_two (u i) (u j) (v i) (v j) (hu i) (hu j) h.1 (hv i) (hv j) h.2
    omega
  have hBne : ∀ i j : Fin d, i ≠ j → subMat (B i) ≠ subMat (B j) := by
    intro i j hij heq
    have hBij : B i = B j := by
      rw [← liftEven_subMat (B i) (hev i), ← liftEven_subMat (B j) (hev j), heq]
    have h0 : ({i, j} : Finset (Fin d)).sum B = 0 := by
      rw [Finset.sum_pair hij, hBij]
      ext x y; exact f2_add_self _
    exact hind {i, j} (by simp) h0
  rcases hpair i0 i1 hi01 with hu01 | hv01
  · have hv01_ne : v i0 ≠ v i1 := by
      intro hveq
      apply hBne i0 i1 hi01
      rw [hB i0, hB i1, hu01, hveq]
    refine Or.inl ⟨u i0, fun i => ⟨v i, fun x y => ?_⟩⟩
    have hui : u i = u i0 := by
      by_cases hi0' : i = i0
      · rw [hi0']
      · by_cases hi1' : i = i1
        · rw [hi1', hu01]
        · rcases hpair i i0 hi0' with h1 | h1
          · exact h1
          · rcases hpair i i1 hi1' with h2 | h2
            · exact h2.trans hu01.symm
            · exact (hv01_ne (h1.symm.trans h2)).elim
    have := congrFun (congrFun (hB i) x) y
    simpa [subMat, outerMat, hui] using this
  · have hu01_ne : u i0 ≠ u i1 := by
      intro hueq
      apply hBne i0 i1 hi01
      rw [hB i0, hB i1, hueq, hv01]
    refine Or.inr ⟨v i0, fun i => ⟨u i, fun x y => ?_⟩⟩
    have hvi : v i = v i0 := by
      by_cases hi0' : i = i0
      · rw [hi0']
      · by_cases hi1' : i = i1
        · rw [hi1', hv01]
        · rcases hpair i i0 hi0' with h1 | h1
          · rcases hpair i i1 hi1' with h2 | h2
            · exact (hu01_ne (h1.symm.trans h2)).elim
            · exact h2.trans hv01.symm
          · exact h1
    have := congrFun (congrFun (hB i) x) y
    simpa [subMat, outerMat, hvi] using this

lemma main_theorem (a b t d k : ℕ) (ht : 0 < t) (hab : 2 * t ≤ min a b) (hk : 2 ≤ k) :
    let F := ZMod 2
    let R := Fin (a + 2)
    let C := Fin (b + 2)
    let M := Matrix R C F
    let T := R → C → Bool
    let Qs := Fin d → M
    let r := 2 * t
    let cap := 2 ^ (a + b + 3 + r) * Nat.card {A : Matrix (Fin a) (Fin b) F // Matrix.rank A = r}
    let N := Nat.card {P : T // okP a b t P}
    let q := 2 ^ d
    let independent := fun B : Qs => ∀ S : Finset (Fin d), S.Nonempty → S.sum B ≠ 0
    let moment := fun (B : Qs) =>
      let hits := fun (z : Fin d → F) => Nat.card {P : T // okP a b t P ∧ ∀ i,
        (∑ x, ∑ y, B i x y * (if P x y then (1 : F) else 0)) = z i}
      q ^ k * ∑ z : Fin d → F, (hits z) ^ k
    let bound := (N + (q - 1) * cap) ^ k + (q - 1) * (N - cap) ^ k
    let common := fun B : Qs =>
      (∀ i, (∀ x, (∑ y, B i x y) = 0) ∧ (∀ y, (∑ x, B i x y) = 0)) ∧
      ((∃ u : Fin (a + 1) → F, ∀ i, ∃ v : Fin (b + 1) → F,
          ∀ x y, B i x.succ y.succ = u x * v y) ∨
       (∃ v : Fin (b + 1) → F, ∀ i, ∃ u : Fin (a + 1) → F,
          ∀ x y, B i x.succ y.succ = u x * v y))
    (∀ B : Qs, independent B → moment B ≤ bound ∧ (moment B = bound ↔ common B)) ∧
      ((∃ B : Qs, independent B ∧ moment B = bound) ↔ d ≤ max (a + 1) (b + 1)) := by
  intro F R C M T Qs r cap N q independent moment bound common
  have hr2 : 2 ≤ r := by omega
  have hra : r ≤ a := le_trans hab (min_le_left a b)
  have hrb : r ≤ b := le_trans hab (min_le_right a b)
  have hcap_pos : 0 < cap :=
    Nat.mul_pos (pow_pos (by decide) _) (exists_rank_r_pos hr2 hra hrb)
  have hcap_le_N : cap ≤ N := cap_le_N ht hab
  have hN_pos : 0 < N := lt_of_lt_of_le hcap_pos hcap_le_N
  have hpart1 : ∀ B : Qs, independent B → moment B ≤ bound ∧ (moment B = bound ↔ common B) := by
    intro B hind
    let v : (Fin d → F2) → ℤ := fun c => charSum a b t (linComb B c)
    let w : (Fin d → F2) → ℤ := fun c => if c = 0 then (N : ℤ) else (cap : ℤ)
    have hv0 : v 0 = (N : ℤ) := by
      simp only [v, linComb, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      exact charSum_zero
    have hv_le : ∀ c : Fin d → F2, |v c| ≤ w c := by
      intro c
      by_cases hc : c = 0
      · subst hc; rw [hv0]; simp [w]
      · simp only [w, if_neg hc]
        have hne : linComb B c ≠ 0 := by
          intro hz; exact hc ((linComb_eq_zero_iff B hind c).mp hz)
        exact (charSum_bound ht hab (linComb B c) hne).1
    have hw_nonneg : ∀ c : Fin d → F2, 0 ≤ w c := by
      intro c; simp only [w]; split_ifs <;> positivity
    have hterm_le : ∀ tup : Fin k → (Fin d → F2),
        (if (∑ j, tup j) = 0 then ∏ j, v (tup j) else 0) ≤
        if (∑ j, tup j) = 0 then ∏ j, w (tup j) else 0 := by
      intro tup
      by_cases hs : (∑ j, tup j) = 0
      · rw [if_pos hs, if_pos hs]
        have hple : ∀ s : Finset (Fin k), (∏ j ∈ s, |v (tup j)|) ≤ ∏ j ∈ s, w (tup j) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha]
            exact mul_le_mul (hv_le (tup a)) ih (Finset.prod_nonneg fun j _ => abs_nonneg _)
              (hw_nonneg (tup a))
        calc ∏ j, v (tup j) ≤ |∏ j, v (tup j)| := le_abs_self _
          _ = ∏ j, |v (tup j)| := Finset.abs_prod _ _
          _ ≤ ∏ j, w (tup j) := hple Finset.univ
      · simp [hs]
    have hmom_int : (moment B : ℤ) =
        (2 ^ d : ℤ) * ∑ tup : Fin k → (Fin d → F2),
          if (∑ j, tup j) = 0 then ∏ j, v (tup j) else 0 :=
      moment_eq_fourier B
    have hbnd_int : (bound : ℤ) =
        (2 ^ d : ℤ) * ∑ tup : Fin k → (Fin d → F2),
          if (∑ j, tup j) = 0 then ∏ j, w (tup j) else 0 :=
      bound_eq_fourier hcap_le_N
    have hle_int : (moment B : ℤ) ≤ (bound : ℤ) := by
      rw [hmom_int, hbnd_int]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun tup _ => hterm_le tup)
        (by positivity)
    refine ⟨by exact_mod_cast hle_int, ?_⟩
    constructor
    · intro heq
      have heq_int : (moment B : ℤ) = (bound : ℤ) := congrArg Nat.cast heq
      rw [hmom_int, hbnd_int] at heq_int
      have hqne : (2 ^ d : ℤ) ≠ 0 := by positivity
      have hsum_eq := mul_left_cancel₀ hqne heq_int
      have hpoint : ∀ tup : Fin k → (Fin d → F2),
          (if (∑ j, tup j) = 0 then ∏ j, v (tup j) else 0) =
          if (∑ j, tup j) = 0 then ∏ j, w (tup j) else 0 := by
        intro tup
        by_contra hne
        have hlt : (if (∑ j, tup j) = 0 then ∏ j, v (tup j) else 0) <
            if (∑ j, tup j) = 0 then ∏ j, w (tup j) else 0 :=
          lt_of_le_of_ne (hterm_le tup) hne
        have hsum_lt : (∑ t' : Fin k → (Fin d → F2),
            if (∑ j, t' j) = 0 then ∏ j, v (t' j) else 0) <
            ∑ t' : Fin k → (Fin d → F2),
            if (∑ j, t' j) = 0 then ∏ j, w (t' j) else 0 :=
          Finset.sum_lt_sum (fun t' _ => hterm_le t') ⟨tup, Finset.mem_univ _, hlt⟩
        exact (ne_of_lt hsum_lt) hsum_eq
      have hall : ∀ c : Fin d → F2, c ≠ 0 →
          evenMargins (linComb B c) ∧ (subMat (linComb B c)).rank = 1 := by
        intro c hc
        let tup : Fin k → (Fin d → F2) := fun j => if j.val < 2 then c else 0
        have hsum0 : (∑ j : Fin k, tup j) = 0 := by
          ext i
          simp only [Finset.sum_apply, Pi.zero_apply, tup]
          let s : Finset (Fin k) := {⟨0, by omega⟩, ⟨1, by omega⟩}
          have hsub : (∑ j : Fin k, (if j.val < 2 then c else 0) i) =
              ∑ j ∈ s, (if j.val < 2 then c else 0) i := by
            symm; refine Finset.sum_subset (Finset.subset_univ s) fun j _ hj => ?_
            have hge : ¬ j.val < 2 := by
              intro hlt
              apply hj
              simp only [s, Finset.mem_insert, Finset.mem_singleton]
              have : j.val = 0 ∨ j.val = 1 := by omega
              rcases this with h0 | h1
              · exact Or.inl (Fin.ext h0)
              · exact Or.inr (Fin.ext h1)
            simp [hge]
          rw [hsub]
          have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
            intro h; have := congrArg Fin.val h; simp at this
          rw [Finset.sum_pair h01]
          simp [f2_add_self]
        have hp := hpoint tup
        rw [if_pos hsum0, if_pos hsum0] at hp
        have hprod_v : (∏ j : Fin k, v (tup j)) = v c ^ 2 * (N : ℤ) ^ (k - 2) := by
          let s : Finset (Fin k) := {⟨0, by omega⟩, ⟨1, by omega⟩}
          have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
            intro h; have := congrArg Fin.val h; simp at this
          rw [← Finset.prod_mul_prod_compl s]
          have h1 : (∏ j ∈ s, v (tup j)) = v c ^ 2 := by
            rw [Finset.prod_pair h01]; simp [tup, sq]
          have h2 : (∏ j ∈ sᶜ, v (tup j)) = (N : ℤ) ^ (k - 2) := by
            have heq_f : ∀ j ∈ sᶜ, v (tup j) = (N : ℤ) := by
              intro j hj
              have hge : ¬ j.val < 2 := by
                intro hlt
                have hmem : j ∈ s := by
                  simp only [s, Finset.mem_insert, Finset.mem_singleton]
                  have : j.val = 0 ∨ j.val = 1 := by omega
                  rcases this with h0 | h1
                  · exact Or.inl (Fin.ext h0)
                  · exact Or.inr (Fin.ext h1)
                exact (Finset.mem_compl.mp hj) hmem
              simp only [tup, hge, ↓reduceIte, hv0]
            rw [Finset.prod_congr rfl heq_f, Finset.prod_const]
            congr 1
            rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair h01]
          rw [h1, h2]
        have hprod_w : (∏ j : Fin k, w (tup j)) = (cap : ℤ) ^ 2 * (N : ℤ) ^ (k - 2) := by
          let s : Finset (Fin k) := {⟨0, by omega⟩, ⟨1, by omega⟩}
          have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
            intro h; have := congrArg Fin.val h; simp at this
          rw [← Finset.prod_mul_prod_compl s]
          have h1 : (∏ j ∈ s, w (tup j)) = (cap : ℤ) ^ 2 := by
            rw [Finset.prod_pair h01]; simp [tup, w, hc, sq]
          have h2 : (∏ j ∈ sᶜ, w (tup j)) = (N : ℤ) ^ (k - 2) := by
            have heq_f : ∀ j ∈ sᶜ, w (tup j) = (N : ℤ) := by
              intro j hj
              have hge : ¬ j.val < 2 := by
                intro hlt
                have hmem : j ∈ s := by
                  simp only [s, Finset.mem_insert, Finset.mem_singleton]
                  have : j.val = 0 ∨ j.val = 1 := by omega
                  rcases this with h0 | h1
                  · exact Or.inl (Fin.ext h0)
                  · exact Or.inr (Fin.ext h1)
                exact (Finset.mem_compl.mp hj) hmem
              simp only [tup, hge, ↓reduceIte, w]
            rw [Finset.prod_congr rfl heq_f, Finset.prod_const]
            congr 1
            rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair h01]
          rw [h1, h2]
        rw [hprod_v, hprod_w] at hp
        have hNne : ((N : ℤ) ^ (k - 2)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hN_pos)
        have hsq : v c ^ 2 = (cap : ℤ) ^ 2 := mul_right_cancel₀ hNne hp
        have habs : |v c| = (cap : ℤ) := by
          have h1 : |v c| ^ 2 = (cap : ℤ) ^ 2 := by rw [sq_abs, hsq]
          nlinarith [abs_nonneg (v c), Nat.cast_nonneg (α := ℤ) cap]
        by_contra hnot
        have hne : linComb B c ≠ 0 := by
          intro hz; exact hc ((linComb_eq_zero_iff B hind c).mp hz)
        have hlt := (charSum_bound ht hab (linComb B c) hne).2.2 hnot
        exact (ne_of_lt hlt) habs
      exact rank_one_space_common B hind hall
    · intro hcom
      have hvw : ∀ c : Fin d → F2, v c = w c := by
        intro c
        by_cases hc : c = 0
        · subst hc; rw [hv0]; simp [w]
        · simp only [w, if_neg hc]
          have hne : linComb B c ≠ 0 := by
            intro hz; exact hc ((linComb_eq_zero_iff B hind c).mp hz)
          have hem_c : evenMargins (linComb B c) := by
            constructor
            · intro x
              simp only [linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_eq_zero fun i _ => ?_
              rw [← Finset.mul_sum, (hcom.1 i).1 x, mul_zero]
            · intro y
              simp only [linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_eq_zero fun i _ => ?_
              rw [← Finset.mul_sum, (hcom.1 i).2 y, mul_zero]
          have hsub_ne : subMat (linComb B c) ≠ 0 := by
            intro hz
            apply hne
            rw [← liftEven_subMat _ hem_c, hz]
            ext x y
            refine Fin.cases (Fin.cases ?_ (fun _ => ?_) y) (fun _ => Fin.cases ?_ (fun _ => ?_) y) x <;>
              simp [liftEven]
          have hrk_le : (subMat (linComb B c)).rank ≤ 1 := by
            rcases hcom.2 with ⟨u, hu⟩ | ⟨v0, hv0'⟩
            · choose vs hvs using hu
              have hsub_eq : subMat (linComb B c) = outerMat u (fun y => ∑ i, c i * vs i y) := by
                ext x y
                simp only [subMat, linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
                  outerMat, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => by rw [hvs i x y]; ring
              rw [hsub_eq]; exact rank_outerMat_le_one _ _
            · choose us hus using hv0'
              have hsub_eq : subMat (linComb B c) = outerMat (fun x => ∑ i, c i * us i x) v0 := by
                ext x y
                simp only [subMat, linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
                  outerMat, Finset.sum_mul]
                refine Finset.sum_congr rfl fun i _ => by rw [hus i x y]; ring
              rw [hsub_eq]; exact rank_outerMat_le_one _ _
          have hrk_pos : 0 < (subMat (linComb B c)).rank := by
            obtain ⟨x, y, hxy⟩ : ∃ x y, subMat (linComb B c) x y ≠ 0 := by
              by_contra h; push_neg at h; exact hsub_ne (Matrix.ext h)
            have hmem : (subMat (linComb B c)).col y ∈ LinearMap.range (subMat (linComb B c)).mulVecLin :=
              ⟨Pi.single y 1, by ext k; simp [Matrix.mulVec, dotProduct, Matrix.col, Pi.single_apply]⟩
            have hne_col : (⟨(subMat (linComb B c)).col y, hmem⟩ :
                LinearMap.range (subMat (linComb B c)).mulVecLin) ≠ 0 := by
              intro hz; exact hxy (congrFun (congrArg Subtype.val hz) x)
            exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne_col⟩
          have hrk1 : (subMat (linComb B c)).rank = 1 := by omega
          exact (charSum_bound ht hab (linComb B c) hne).2.1 ⟨hem_c, hrk1⟩
      have heq_int : (moment B : ℤ) = (bound : ℤ) := by
        rw [hmom_int, hbnd_int]
        simp_rw [hvw]
      exact_mod_cast heq_int
  refine ⟨hpart1, ?_⟩
  constructor
  · rintro ⟨B, hind, heq⟩
    have hcom := ((hpart1 B hind).2).mp heq
    rcases hcom.2 with ⟨u, hu⟩ | ⟨v0, hv0'⟩
    · choose vs hvs using hu
      have hli : LinearIndependent F2 vs := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hsub0 : subMat (linComb B c) = 0 := by
          ext x y
          simp only [subMat, linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
            Matrix.zero_apply]
          have : (∑ i, c i * B i x.succ y.succ) = u x * (∑ i, c i * vs i y) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by rw [hvs i x y]; ring
          rw [this]
          have hy := congrFun hc y
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hy
          rw [hy, mul_zero]
        have hem_c : evenMargins (linComb B c) := by
          constructor
          · intro x
            simp only [linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, (hcom.1 i).1 x, mul_zero]
          · intro y
            simp only [linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, (hcom.1 i).2 y, mul_zero]
        have hlin0 : linComb B c = 0 := by
          rw [← liftEven_subMat _ hem_c, hsub0]
          ext x y
          refine Fin.cases (Fin.cases ?_ (fun _ => ?_) y) (fun _ => Fin.cases ?_ (fun _ => ?_) y) x <;>
            simp [liftEven]
        have hc0 := (linComb_eq_zero_iff B hind c).mp hlin0
        intro i; rw [hc0]; rfl
      have hle : d ≤ b + 1 := by
        have := hli.fintype_card_le_finrank
        dsimp only [F] at this
        rw [Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at this
        exact this
      exact le_trans hle (le_max_right _ _)
    · choose us hus using hv0'
      have hli : LinearIndependent F2 us := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hsub0 : subMat (linComb B c) = 0 := by
          ext x y
          simp only [subMat, linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
            Matrix.zero_apply]
          have : (∑ i, c i * B i x.succ y.succ) = (∑ i, c i * us i x) * v0 y := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by rw [hus i x y]; ring
          rw [this]
          have hx := congrFun hc x
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
          rw [hx, zero_mul]
        have hem_c : evenMargins (linComb B c) := by
          constructor
          · intro x
            simp only [linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, (hcom.1 i).1 x, mul_zero]
          · intro y
            simp only [linComb, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, (hcom.1 i).2 y, mul_zero]
        have hlin0 : linComb B c = 0 := by
          rw [← liftEven_subMat _ hem_c, hsub0]
          ext x y
          refine Fin.cases (Fin.cases ?_ (fun _ => ?_) y) (fun _ => Fin.cases ?_ (fun _ => ?_) y) x <;>
            simp [liftEven]
        have hc0 := (linComb_eq_zero_iff B hind c).mp hlin0
        intro i; rw [hc0]; rfl
      have hle : d ≤ a + 1 := by
        have := hli.fintype_card_le_finrank
        dsimp only [F] at this
        rw [Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at this
        exact this
      exact le_trans hle (le_max_left _ _)
  · intro hd
    rcases le_max_iff.mp hd with hda | hdb
    · let B : Qs := fun i => liftEven (outerMat (Pi.single ⟨i.val, by omega⟩ 1) (Pi.single 0 1))
      have hind : independent B := by
        intro S hSne h0
        obtain ⟨i0, hi0⟩ := hSne
        have hval := congrFun (congrFun h0 (⟨i0.val, by omega⟩ : Fin (a + 1)).succ) (0 : Fin (b + 1)).succ
        dsimp only [M, R, C, F, B] at hval
        rw [Matrix.sum_apply, Matrix.zero_apply] at hval
        simp only [liftEven, Fin.cases_succ, outerMat, Pi.single_apply, mul_one, ↓reduceIte] at hval
        have h1 : (∑ i ∈ S, if (⟨i0.val, by omega⟩ : Fin (a + 1)) = ⟨i.val, by omega⟩ then (1 : F2) else 0) = 1 := by
          have hterm : ∀ i ∈ S,
              (if (⟨i0.val, by omega⟩ : Fin (a + 1)) = ⟨i.val, by omega⟩ then (1 : F2) else 0) =
              if i = i0 then 1 else 0 := by
            intro i _
            by_cases h : i = i0
            · subst h; simp
            · have hne : (⟨i0.val, by omega⟩ : Fin (a + 1)) ≠ ⟨i.val, by omega⟩ :=
                fun h' => h (Fin.ext (congrArg Fin.val h').symm)
              simp [h, hne]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hi0]
        rw [h1] at hval
        exact one_ne_zero hval
      have hcom : common B := by
        refine ⟨fun i => liftEven_evenMargins _, Or.inr ⟨Pi.single 0 1, fun i =>
          ⟨Pi.single ⟨i.val, by omega⟩ 1, fun x y => rfl⟩⟩⟩
      exact ⟨B, hind, ((hpart1 B hind).2).mpr hcom⟩
    · let B : Qs := fun i => liftEven (outerMat (Pi.single 0 1) (Pi.single ⟨i.val, by omega⟩ 1))
      have hind : independent B := by
        intro S hSne h0
        obtain ⟨i0, hi0⟩ := hSne
        have hval := congrFun (congrFun h0 (0 : Fin (a + 1)).succ) (⟨i0.val, by omega⟩ : Fin (b + 1)).succ
        dsimp only [M, R, C, F, B] at hval
        rw [Matrix.sum_apply, Matrix.zero_apply] at hval
        simp only [liftEven, Fin.cases_succ, outerMat, Pi.single_apply, one_mul, ↓reduceIte] at hval
        have h1 : (∑ i ∈ S, if (⟨i0.val, by omega⟩ : Fin (b + 1)) = ⟨i.val, by omega⟩ then (1 : F2) else 0) = 1 := by
          have hterm : ∀ i ∈ S,
              (if (⟨i0.val, by omega⟩ : Fin (b + 1)) = ⟨i.val, by omega⟩ then (1 : F2) else 0) =
              if i = i0 then 1 else 0 := by
            intro i _
            by_cases h : i = i0
            · subst h; simp
            · have hne : (⟨i0.val, by omega⟩ : Fin (b + 1)) ≠ ⟨i.val, by omega⟩ :=
                fun h' => h (Fin.ext (congrArg Fin.val h').symm)
              simp [h, hne]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hi0]
        rw [h1] at hval
        exact one_ne_zero hval
      have hcom : common B := by
        refine ⟨fun i => liftEven_evenMargins _, Or.inl ⟨Pi.single 0 1, fun i =>
          ⟨Pi.single ⟨i.val, by omega⟩ 1, fun x y => rfl⟩⟩⟩
      exact ⟨B, hind, ((hpart1 B hind).2).mpr hcom⟩

end PEqualNP.Outside.L_meta_33672

theorem PEqualNP.Outside.L_meta_33672 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
  let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
    (Q.gates.foldl (fun (ds : List ℕ) g =>
      ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
      (List.replicate w 0)).getD Q.output 0
  ∀ (a b t d k : ℕ), 0 < t → 2*t ≤ min a b → 2 ≤ k →
    let F := ZMod 2
    let R := Fin (a+2)
    let C := Fin (b+2)
    let M := Matrix R C F
    let T := R → C → Bool
    let Qs := Fin d → M
    let r := 2*t
    let cap := 2^(a+b+3+r) * Nat.card {A : Matrix (Fin a) (Fin b) F // Matrix.rank A = r}
    let ok := fun (P : T) => ∃ Q : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (a+2+(b+2)) Q ∧ PEqualNP.Represents.Represents P Q ∧
      depth (a+2+(b+2)) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t
    let N := Nat.card {P : T // ok P}
    let q := 2^d
    let independent := fun B : Qs => ∀ S : Finset (Fin d), S.Nonempty → S.sum B ≠ 0
    let moment := fun (B : Qs) =>
      let hits := fun (z : Fin d → F) => Nat.card {P : T // ok P ∧ ∀ i,
        (∑ x, ∑ y, B i x y * (if P x y then (1 : F) else 0)) = z i}
      q^k * ∑ z : Fin d → F, (hits z)^k
    let bound := (N+(q-1)*cap)^k + (q-1)*(N-cap)^k
    let common := fun B : Qs =>
      (∀ i, (∀ x, (∑ y, B i x y) = 0) ∧ (∀ y, (∑ x, B i x y) = 0)) ∧
      ((∃ u : Fin (a+1) → F, ∀ i, ∃ v : Fin (b+1) → F,
          ∀ x y, B i x.succ y.succ = u x * v y) ∨
       (∃ v : Fin (b+1) → F, ∀ i, ∃ u : Fin (a+1) → F,
          ∀ x y, B i x.succ y.succ = u x * v y))
    (∀ B : Qs, independent B → moment B ≤ bound ∧ (moment B = bound ↔ common B)) ∧
      ((∃ B : Qs, independent B ∧ moment B = bound) ↔ d ≤ max (a+1) (b+1)) :=
  fun a b t d k ht hab hk => PEqualNP.Outside.L_meta_33672.main_theorem a b t d k ht hab hk

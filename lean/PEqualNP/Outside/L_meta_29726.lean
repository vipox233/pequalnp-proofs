import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29726

open PEqualNP.CircuitLowerBounds Module

def chi (a : ZMod 2) : ℤ := if a = 1 then -1 else 1

def sg (b : Bool) : ℤ := if b then -1 else 1

lemma chi_add : ∀ a b : ZMod 2, chi (a + b) = chi a * chi b := by decide

lemma chi_sub : ∀ a b : ZMod 2, chi (a - b) = chi a * chi b := by decide

lemma sg_xor : ∀ (b : Bool) (a : ZMod 2), sg (xor b (decide (a = 1))) = sg b * chi a := by decide

lemma sg_sq : ∀ b : Bool, sg b * sg b = 1 := by decide

lemma chi_abs : ∀ a b : ZMod 2, |chi a - chi b| ≤ 2 := by decide

lemma chi_cases : ∀ a : ZMod 2, chi a = 1 ∨ chi a = -1 := by decide

lemma dxor : ∀ p q : ZMod 2, decide (p + q = 1) = xor (decide (p = 1)) (decide (q = 1)) := by
  decide

lemma eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

lemma m1 : ∀ A p : Bool, GateOp.eval (GateOp.mod 2) [xor A p] =
    xor (GateOp.eval (GateOp.mod 2) [A]) p := by decide

lemma m2 : ∀ A B p q : Bool, GateOp.eval (GateOp.mod 2) [xor A p, xor B q] =
    xor (GateOp.eval (GateOp.mod 2) [A, B]) (xor p q) := by decide

lemma n1 : ∀ A p : Bool, GateOp.eval GateOp.not [xor A p] =
    xor (GateOp.eval GateOp.not [A]) p := by decide

def dotL (k : ℕ) (c : Fin k → ZMod 2) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun u := c ⬝ᵥ u
  map_add' := dotProduct_add c
  map_smul' r u := by simp [dotProduct_smul]

lemma finrank_inf_ker (k : ℕ) (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (c : Fin k → ZMod 2) :
    finrank (ZMod 2) U ≤ finrank (ZMod 2) ↥(U ⊓ LinearMap.ker (dotL k c)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker (dotL k c))
  have h2 := LinearMap.finrank_range_add_finrank_ker (dotL k c)
  have h3 : finrank (ZMod 2) ↥(LinearMap.range (dotL k c)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (dotL k c))
    simpa using this
  have h4 := Submodule.finrank_le (U ⊔ LinearMap.ker (dotL k c))
  omega

def Inv (k : ℕ) (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (W : (Fin k → ZMod 2) → List Bool) : Prop :=
  ∀ i : ℕ, ∃ c : Fin k → ZMod 2, ∀ x, ∀ u ∈ U,
    (W (x + u)).getD i false = xor ((W x).getD i false) (decide (c ⬝ᵥ u = 1))

def GOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

lemma val_step (k : ℕ) (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (W : (Fin k → ZMod 2) → List Bool) (hI : Inv k U W) (g : Gate) (hg : GOK g) :
    ∃ U' : Submodule (ZMod 2) (Fin k → ZMod 2), U' ≤ U ∧ (g.op ≠ GateOp.and → U' = U) ∧
      finrank (ZMod 2) U ≤ finrank (ZMod 2) U' + 2 ∧
      ∃ c : Fin k → ZMod 2, ∀ x, ∀ u ∈ U',
        g.op.eval (g.inputs.map fun i => (W (x + u)).getD i false) =
          xor (g.op.eval (g.inputs.map fun i => (W x).getD i false)) (decide (c ⬝ᵥ u = 1)) := by
  have z01 : decide ((0 : ZMod 2) = 1) = false := by decide
  obtain ⟨op, ins⟩ := g
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · dsimp only at h1 h2
    subst h1
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h2
    obtain ⟨ca, ha⟩ := hI a
    obtain ⟨cb, hb⟩ := hI b
    refine ⟨U ⊓ LinearMap.ker (dotL k ca) ⊓ LinearMap.ker (dotL k cb),
      inf_le_left.trans inf_le_left, fun h => absurd rfl h, ?_, 0, ?_⟩
    · have e1 := finrank_inf_ker k U ca
      have e2 := finrank_inf_ker k (U ⊓ LinearMap.ker (dotL k ca)) cb
      omega
    · intro x u hu
      rw [Submodule.mem_inf, Submodule.mem_inf] at hu
      obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hu
      have e2 : ca ⬝ᵥ u = 0 := LinearMap.mem_ker.mp hu2
      have e3 : cb ⬝ᵥ u = 0 := LinearMap.mem_ker.mp hu3
      simp only [List.map]
      rw [ha x u hu1, hb x u hu1, e2, e3, zero_dotProduct, z01]
      simp
  · dsimp only at h1 h2
    subst h1
    refine ⟨U, le_rfl, fun _ => rfl, by omega, ?_⟩
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact ⟨0, fun x u _ => by simp⟩
    · obtain ⟨ca, ha⟩ := hI a
      refine ⟨ca, fun x u hu => ?_⟩
      simp only [List.map]
      rw [ha x u hu]
      exact m1 _ _
    · obtain ⟨ca, ha⟩ := hI a
      obtain ⟨cb, hb⟩ := hI b
      refine ⟨ca + cb, fun x u hu => ?_⟩
      simp only [List.map]
      rw [ha x u hu, hb x u hu, add_dotProduct, dxor]
      exact m2 _ _ _ _
    · simp at h2
  · dsimp only at h1 h2
    subst h1
    refine ⟨U, le_rfl, fun _ => rfl, by omega, ?_⟩
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h2
    obtain ⟨ca, ha⟩ := hI a
    refine ⟨ca, fun x u hu => ?_⟩
    simp only [List.map]
    rw [ha x u hu]
    exact n1 _ _

lemma step_inv (k : ℕ) (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (W : (Fin k → ZMod 2) → List Bool) (n : ℕ) (hlen : ∀ x, (W x).length = n)
    (hI : Inv k U W) (g : Gate) (hg : GOK g) :
    ∃ U' : Submodule (ZMod 2) (Fin k → ZMod 2), U' ≤ U ∧ (g.op ≠ GateOp.and → U' = U) ∧
      finrank (ZMod 2) U ≤ finrank (ZMod 2) U' + 2 ∧
      Inv k U' (fun x => W x ++ [g.op.eval (g.inputs.map fun i => (W x).getD i false)]) := by
  have z01 : decide ((0 : ZMod 2) = 1) = false := by decide
  obtain ⟨U', hle, hne, hfr, c, hc⟩ := val_step k U W hI g hg
  refine ⟨U', hle, hne, hfr, fun i => ?_⟩
  rcases lt_trichotomy i n with hi | hi | hi
  · obtain ⟨ci, hci⟩ := hI i
    refine ⟨ci, fun x u hu => ?_⟩
    simp only
    rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hi),
      List.getD_append _ _ _ _ (by rw [hlen]; exact hi)]
    exact hci x u (hle hu)
  · refine ⟨c, fun x u hu => ?_⟩
    simp only
    rw [List.getD_append_right _ _ _ _ (by rw [hlen, hi]),
      List.getD_append_right _ _ _ _ (by rw [hlen, hi]), hlen, hlen, hi, Nat.sub_self]
    exact hc x u hu
  · refine ⟨0, fun x u hu => ?_⟩
    simp only
    rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega),
      List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, hlen]
    obtain ⟨t, ht⟩ : ∃ t, i - n = t + 1 := ⟨i - n - 1, by omega⟩
    rw [ht, zero_dotProduct, z01]
    simp

lemma fold_inv (k : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, GOK g) →
    ∀ (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (W : (Fin k → ZMod 2) → List Bool) (n : ℕ),
    (∀ x, (W x).length = n) → Inv k U W →
    ∃ U' : Submodule (ZMod 2) (Fin k → ZMod 2),
      Inv k U' (fun x => gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W x)) ∧
      finrank (ZMod 2) U ≤ finrank (ZMod 2) U' +
        2 * gs.countP (fun g => @decide (g.op = GateOp.and) (Classical.propDecidable _)) := by
  intro gs
  induction gs with
  | nil =>
    intro _ U W n _ hI
    exact ⟨U, hI, by simp⟩
  | cons g gs ih =>
    intro hg U W n hlen hI
    obtain ⟨U1, hle, hne, hfr, hI1⟩ := step_inv k U W n hlen hI g (hg g (by simp))
    obtain ⟨U2, hI2, hfr2⟩ := ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) U1 _ (n + 1)
      (by intro x; simp [hlen]) hI1
    refine ⟨U2, hI2, ?_⟩
    rw [List.countP_cons]
    by_cases hand : g.op = GateOp.and
    · simp only [hand, decide_true, ite_true]
      omega
    · rw [hne hand] at hfr2
      simp only [hand, decide_false, Bool.false_eq_true, ite_false]
      omega

lemma init_inv (k : ℕ) :
    Inv k ⊤ (fun x => List.ofFn (fun i : Fin k => decide (x i = 1))) := by
  have z01 : decide ((0 : ZMod 2) = 1) = false := by decide
  intro i
  by_cases hi : i < k
  · refine ⟨Pi.single ⟨i, hi⟩ 1, fun x u _ => ?_⟩
    simp only
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      single_one_dotProduct]
    simp only [List.getElem_ofFn, Pi.add_apply]
    exact dxor _ _
  · refine ⟨0, fun x u _ => ?_⟩
    simp only
    rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi),
      zero_dotProduct, z01]
    rfl

lemma struct (k : ℕ) (C : Circuit) (hg : ∀ g ∈ C.gates, GOK g) :
    ∃ (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (c : Fin k → ZMod 2),
      k ≤ finrank (ZMod 2) U +
        2 * C.gates.countP (fun g => @decide (g.op = GateOp.and) (Classical.propDecidable _)) ∧
      ∀ x, ∀ u ∈ U, C.eval (List.ofFn (fun i : Fin k => decide ((x + u) i = 1))) =
        xor (C.eval (List.ofFn (fun i : Fin k => decide (x i = 1)))) (decide (c ⬝ᵥ u = 1)) := by
  obtain ⟨U, hI, hfr⟩ := fold_inv k C.gates hg ⊤ _ k (by intro x; simp) (init_inv k)
  obtain ⟨c, hc⟩ := hI C.output
  refine ⟨U, c, ?_, hc⟩
  rw [finrank_top, Module.finrank_fin_fun] at hfr
  exact hfr

def B (k : ℕ) (b : (Fin k → ZMod 2) → Bool) (w : Fin k → ZMod 2) : ℤ :=
  ∑ x : Fin k → ZMod 2, sg (b x) * chi (w ⬝ᵥ x)

lemma card_V (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp [ZMod.card]

lemma sum_chi (k : ℕ) (z : Fin k → ZMod 2) (hz : z ≠ 0) :
    ∑ x : Fin k → ZMod 2, chi (z ⬝ᵥ x) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have hi1 : z i = 1 := eq_one_of_ne_zero _ hi
  have h1 : ∑ x : Fin k → ZMod 2, chi (z ⬝ᵥ x) =
      ∑ x : Fin k → ZMod 2, chi (z ⬝ᵥ (x + Pi.single i 1)) :=
    (Equiv.sum_comp (Equiv.addRight (Pi.single i 1)) (fun x => chi (z ⬝ᵥ x))).symm
  have h2 : ∀ x : Fin k → ZMod 2, chi (z ⬝ᵥ (x + Pi.single i 1)) = - chi (z ⬝ᵥ x) := by
    intro x
    rw [dotProduct_add, dotProduct_single_one, hi1, chi_add]
    have : chi 1 = -1 := by decide
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_neg_distrib] at h1
  omega

lemma orth (k : ℕ) (x y : Fin k → ZMod 2) :
    ∑ w : Fin k → ZMod 2, chi (w ⬝ᵥ x) * chi (w ⬝ᵥ y) = if x = y then 2 ^ k else 0 := by
  have h : ∀ w : Fin k → ZMod 2, chi (w ⬝ᵥ x) * chi (w ⬝ᵥ y) = chi ((x - y) ⬝ᵥ w) := by
    intro w
    rw [← chi_sub, ← dotProduct_sub, dotProduct_comm]
  rw [Finset.sum_congr rfl (fun w _ => h w)]
  split_ifs with hxy
  · subst hxy
    have c0 : chi 0 = 1 := by decide
    simp [c0]
  · exact sum_chi k _ (sub_ne_zero.mpr hxy)

lemma parseval (k : ℕ) (b : (Fin k → ZMod 2) → Bool) :
    ∑ w : Fin k → ZMod 2, B k b w ^ 2 = 2 ^ k * 2 ^ k := by
  have h : ∀ w : Fin k → ZMod 2, B k b w ^ 2 = ∑ x : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2,
      (sg (b x) * sg (b y)) * (chi (w ⬝ᵥ x) * chi (w ⬝ᵥ y)) := by
    intro w
    rw [sq, B, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_comm]
  have h2 : ∀ x : Fin k → ZMod 2, ∑ w : Fin k → ZMod 2, ∑ y : Fin k → ZMod 2,
      sg (b x) * sg (b y) * (chi (w ⬝ᵥ x) * chi (w ⬝ᵥ y)) = 2 ^ k := by
    intro x
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, orth]
    simp [sg_sq]
  rw [Finset.sum_congr rfl (fun x _ => h2 x)]
  simp

lemma B_zero (k : ℕ) (b : (Fin k → ZMod 2) → Bool) (c w u : Fin k → ZMod 2)
    (hb : ∀ x, b (x + u) = xor (b x) (decide (c ⬝ᵥ u = 1))) (h : (c + w) ⬝ᵥ u = 1) :
    B k b w = 0 := by
  have h1 : B k b w = ∑ x : Fin k → ZMod 2, sg (b (x + u)) * chi (w ⬝ᵥ (x + u)) :=
    (Equiv.sum_comp (Equiv.addRight u) (fun x => sg (b x) * chi (w ⬝ᵥ x))).symm
  have h2 : ∀ x : Fin k → ZMod 2, sg (b (x + u)) * chi (w ⬝ᵥ (x + u)) =
      - (sg (b x) * chi (w ⬝ᵥ x)) := by
    intro x
    rw [hb, sg_xor, dotProduct_add, chi_add]
    have : chi (c ⬝ᵥ u) * chi (w ⬝ᵥ u) = -1 := by
      rw [← chi_add, ← add_dotProduct, h]
      decide
    linear_combination (sg (b x) * chi (w ⬝ᵥ x)) * this
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_neg_distrib] at h1
  change B k b w = - B k b w at h1
  omega

lemma key_id : ∀ (d : Bool → ZMod 2) (β : Bool) (a : ZMod 2),
    2 * (if d β = a then (1 : ℤ) else -1) =
      (chi (d false) + chi (d true)) * chi a +
        (chi (d false) - chi (d true)) * (sg β * chi a) := by
  intro d β a
  cases β
  · generalize d false = p
    generalize d true = q
    revert p q a
    decide
  · generalize d false = p
    generalize d true = q
    revert p q a
    decide

lemma gain_le (k : ℕ) (b : (Fin k → ZMod 2) → Bool) (d : Bool → ZMod 2) (w : Fin k → ZMod 2)
    (hw : w ≠ 0) :
    2 * (((Finset.univ : Finset (Fin k → ZMod 2)).filter
      (fun x => d (b x) = w ⬝ᵥ x)).card : ℤ) - 2 ^ k ≤ |B k b w| := by
  have h1 : 2 * (((Finset.univ : Finset (Fin k → ZMod 2)).filter
      (fun x => d (b x) = w ⬝ᵥ x)).card : ℤ) - 2 ^ k =
      ∑ x : Fin k → ZMod 2, (if d (b x) = w ⬝ᵥ x then (1 : ℤ) else -1) := by
    have e : ∀ x : Fin k → ZMod 2, (if d (b x) = w ⬝ᵥ x then (1 : ℤ) else -1) =
        2 * (if d (b x) = w ⬝ᵥ x then (1 : ℤ) else 0) - 1 := by
      intro x
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.card_filter]
    simp
  have h2 : 2 * ∑ x : Fin k → ZMod 2, (if d (b x) = w ⬝ᵥ x then (1 : ℤ) else -1) =
      (chi (d false) - chi (d true)) * B k b w := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun x _ => key_id d (b x) (w ⬝ᵥ x)),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_chi k w hw]
    simp [B]
  have h3 := chi_abs (d false) (d true)
  have h4 : (chi (d false) - chi (d true)) * B k b w ≤ 2 * |B k b w| := by
    calc (chi (d false) - chi (d true)) * B k b w
        ≤ |(chi (d false) - chi (d true)) * B k b w| := le_abs_self _
      _ = |chi (d false) - chi (d true)| * |B k b w| := abs_mul _ _
      _ ≤ 2 * |B k b w| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
  linarith

lemma gain_sq (k m : ℕ) (v : Fin m ↪ (Fin k → ZMod 2)) (hv : ∀ j, v j ≠ 0)
    (b : (Fin k → ZMod 2) → Bool) (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (c : Fin k → ZMod 2)
    (hb : ∀ x, ∀ u ∈ U, b (x + u) = xor (b x) (decide (c ⬝ᵥ u = 1)))
    (K : Finset (Fin m)) (dec : Bool → Fin m → ZMod 2) (A : Finset (Fin m))
    (hA : ∀ j, (∀ u ∈ U, (c + v j) ⬝ᵥ u = 0) → j ∈ A) :
    (2 * (∑ x : Fin k → ZMod 2, (K.filter (fun j => dec (b x) j = v j ⬝ᵥ x)).card) -
      2 ^ k * K.card) ^ 2 ≤ A.card * (2 ^ k) ^ 2 := by
  by_cases hle : 2 * (∑ x : Fin k → ZMod 2, (K.filter (fun j => dec (b x) j = v j ⬝ᵥ x)).card) ≤
      2 ^ k * K.card
  · rw [Nat.sub_eq_zero_of_le hle]
    simp
  push Not at hle
  have hS : ∑ x : Fin k → ZMod 2, (K.filter (fun j => dec (b x) j = v j ⬝ᵥ x)).card =
      ∑ j ∈ K, ((Finset.univ : Finset (Fin k → ZMod 2)).filter
        (fun x => dec (b x) j = v j ⬝ᵥ x)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hT : ((2 * (∑ x : Fin k → ZMod 2, (K.filter (fun j => dec (b x) j = v j ⬝ᵥ x)).card) -
      2 ^ k * K.card : ℕ) : ℤ) = ∑ j ∈ K, (2 * (((Finset.univ : Finset (Fin k → ZMod 2)).filter
        (fun x => dec (b x) j = v j ⬝ᵥ x)).card : ℤ) - 2 ^ k) := by
    rw [Nat.cast_sub hle.le, hS, Finset.sum_sub_distrib, ← Finset.mul_sum]
    push_cast
    simp [mul_comm]
  have hB0 : ∀ j, j ∉ A → B k b (v j) = 0 := by
    intro j hj
    have hn : ¬ ∀ u ∈ U, (c + v j) ⬝ᵥ u = 0 := fun h => hj (hA j h)
    push Not at hn
    obtain ⟨u, hu, hne⟩ := hn
    exact B_zero k b c (v j) u (fun x => hb x u hu) (eq_one_of_ne_zero _ hne)
  have h5 : ∑ j ∈ K, |B k b (v j)| ≤ ∑ j ∈ A, |B k b (v j)| := by
    have e : ∑ j ∈ K, |B k b (v j)| = ∑ j ∈ K ∩ A, |B k b (v j)| :=
      (Finset.sum_subset Finset.inter_subset_left (fun j hjK hjn => by
        have : j ∉ A := fun hjA => hjn (Finset.mem_inter.mpr ⟨hjK, hjA⟩)
        rw [hB0 j this, abs_zero])).symm
    rw [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => abs_nonneg _)
  have h6 : (∑ j ∈ A, |B k b (v j)|) ^ 2 ≤ (A.card : ℤ) * (2 ^ k) ^ 2 := by
    have e1 : (∑ j ∈ A, |B k b (v j)|) ^ 2 ≤ (A.card : ℤ) * ∑ j ∈ A, |B k b (v j)| ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have e2 : ∑ j ∈ A, |B k b (v j)| ^ 2 ≤ ∑ w : Fin k → ZMod 2, B k b w ^ 2 := by
      simp_rw [sq_abs]
      have e3 : ∑ j ∈ A, B k b (v j) ^ 2 = ∑ w ∈ A.map v, B k b w ^ 2 :=
        (Finset.sum_map A v (fun w => B k b w ^ 2)).symm
      rw [e3]
      exact Finset.sum_le_univ_sum_of_nonneg (fun w => sq_nonneg _)
    rw [parseval] at e2
    calc (∑ j ∈ A, |B k b (v j)|) ^ 2 ≤ (A.card : ℤ) * ∑ j ∈ A, |B k b (v j)| ^ 2 := e1
      _ ≤ (A.card : ℤ) * (2 ^ k * 2 ^ k) := mul_le_mul_of_nonneg_left e2 (Int.natCast_nonneg _)
      _ = (A.card : ℤ) * (2 ^ k) ^ 2 := by ring
  have h7 : ∑ j ∈ K, (2 * (((Finset.univ : Finset (Fin k → ZMod 2)).filter
        (fun x => dec (b x) j = v j ⬝ᵥ x)).card : ℤ) - 2 ^ k) ≤ ∑ j ∈ K, |B k b (v j)| :=
    Finset.sum_le_sum (fun j _ => gain_le k b (fun β => dec β j) (v j) (hv j))
  have h8 : ((2 * (∑ x : Fin k → ZMod 2, (K.filter (fun j => dec (b x) j = v j ⬝ᵥ x)).card) -
      2 ^ k * K.card : ℕ) : ℤ) ^ 2 ≤ (A.card : ℤ) * (2 ^ k) ^ 2 := by
    refine le_trans (pow_le_pow_left₀ (Int.natCast_nonneg _) ?_ 2) h6
    rw [hT]
    exact h7.trans h5
  exact_mod_cast h8

lemma exists_sub (k : ℕ) : ∀ (n : ℕ) (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (h : ℕ),
    finrank (ZMod 2) U = h + n →
    ∃ U' : Submodule (ZMod 2) (Fin k → ZMod 2), U' ≤ U ∧ finrank (ZMod 2) U' = h := by
  intro n
  induction n with
  | zero =>
    intro U h hU
    exact ⟨U, le_rfl, hU⟩
  | succ n ih =>
    intro U h hU
    have hne : U ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hU
      omega
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu0 (funext hcon)
    have hlt : U ⊓ LinearMap.ker (dotL k (Pi.single i 1)) < U := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro heq
      have hu' : u ∈ U ⊓ LinearMap.ker (dotL k (Pi.single i 1)) := by
        rw [heq]
        exact huU
      have e : (Pi.single i 1 : Fin k → ZMod 2) ⬝ᵥ u = 0 := LinearMap.mem_ker.mp hu'.2
      rw [single_one_dotProduct] at e
      exact hi e
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := finrank_inf_ker k U (Pi.single i 1)
    obtain ⟨U', hle, hfr⟩ := ih (U ⊓ LinearMap.ker (dotL k (Pi.single i 1))) h (by omega)
    exact ⟨U', hle.trans inf_le_left, hfr⟩

lemma count_flat (k m h D E : ℕ) (v : Fin m ↪ (Fin k → ZMod 2))
    (hbias : ∀ x : Fin k → ZMod 2, x ≠ 0 →
      D * ((m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter
        (fun j => v j ⬝ᵥ x = 1)).card : ℤ)).natAbs ≤ E * m)
    (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (hU : h ≤ finrank (ZMod 2) U)
    (c : Fin k → ZMod 2) (A : Finset (Fin m))
    (hA : ∀ j ∈ A, ∀ u ∈ U, (c + v j) ⬝ᵥ u = 0) :
    2 ^ h * D * A.card ≤ (D + (2 ^ h - 1) * E) * m := by
  classical
  obtain ⟨U', hle, hfr⟩ := exists_sub k (finrank (ZMod 2) U - h) U h (by omega)
  have hcard : Fintype.card U' = 2 ^ h := by
    rw [card_eq_pow_finrank (K := ZMod 2) (V := U'), hfr, ZMod.card]
  have c0 : chi 0 = 1 := by decide
  have c1 : chi 1 = -1 := by decide
  have hf0 : ∀ j, 0 ≤ ∑ u : U', chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) := by
    intro j
    by_cases hex : ∃ u0 : U', (c + v j) ⬝ᵥ (u0 : Fin k → ZMod 2) = 1
    · obtain ⟨u0, hu0⟩ := hex
      have h1 : ∑ u : U', chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) =
          ∑ u : U', chi ((c + v j) ⬝ᵥ ((u + u0 : U') : Fin k → ZMod 2)) :=
        (Equiv.sum_comp (Equiv.addRight u0)
          (fun u : U' => chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)))).symm
      have h2 : ∀ u : U', chi ((c + v j) ⬝ᵥ ((u + u0 : U') : Fin k → ZMod 2)) =
          - chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) := by
        intro u
        rw [Submodule.coe_add, dotProduct_add, hu0, chi_add, c1]
        ring
      rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_neg_distrib] at h1
      omega
    · push Not at hex
      refine Finset.sum_nonneg (fun u _ => ?_)
      rcases chi_cases ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) with h | h
      · rw [h]
        norm_num
      · exfalso
        unfold chi at h
        split_ifs at h with h'
        exact hex u h'
  have hfA : ∀ j ∈ A, ∑ u : U', chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) = 2 ^ h := by
    intro j hj
    rw [Finset.sum_congr rfl (fun u _ => by rw [hA j hj u (hle u.2), c0])]
    simp [hcard]
  have h1 : (2 ^ h : ℤ) * A.card ≤
      ∑ j : Fin m, ∑ u : U', chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) := by
    have e : (2 ^ h : ℤ) * A.card =
        ∑ j ∈ A, ∑ u : U', chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) := by
      rw [Finset.sum_congr rfl hfA]
      simp [mul_comm]
    rw [e]
    exact Finset.sum_le_univ_sum_of_nonneg hf0
  have h2 : ∑ j : Fin m, ∑ u : U', chi ((c + v j) ⬝ᵥ (u : Fin k → ZMod 2)) =
      ∑ u : U', chi (c ⬝ᵥ (u : Fin k → ZMod 2)) *
        ∑ j : Fin m, chi (v j ⬝ᵥ (u : Fin k → ZMod 2)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_dotProduct, chi_add])
  have h3 : ∀ u : Fin k → ZMod 2, ∑ j : Fin m, chi (v j ⬝ᵥ u) =
      (m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter
        (fun j => v j ⬝ᵥ u = 1)).card : ℤ) := by
    intro u
    have e : ∀ j : Fin m, chi (v j ⬝ᵥ u) = 1 - 2 * (if v j ⬝ᵥ u = 1 then (1 : ℤ) else 0) := by
      intro j
      unfold chi
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.card_filter]
    simp
  have h4 : ∀ u : U', (D : ℤ) * (chi (c ⬝ᵥ (u : Fin k → ZMod 2)) *
      ∑ j : Fin m, chi (v j ⬝ᵥ (u : Fin k → ZMod 2))) ≤
      (E : ℤ) * m + (if u = 0 then (D : ℤ) * m - E * m else 0) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [c0]
    · have hu' : (u : Fin k → ZMod 2) ≠ 0 := fun h => hu (Subtype.ext h)
      have hb := hbias _ hu'
      rw [h3]
      have hb' : (D : ℤ) * |(m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter
          (fun j => v j ⬝ᵥ (u : Fin k → ZMod 2) = 1)).card : ℤ)| ≤ (E : ℤ) * m := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hb
      have hD : (0 : ℤ) ≤ D := Int.natCast_nonneg _
      simp only [hu, ↓reduceIte, add_zero]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hD) hb'
      rcases chi_cases (c ⬝ᵥ (u : Fin k → ZMod 2)) with h | h
      · rw [h, one_mul]
        exact le_abs_self _
      · rw [h, neg_one_mul]
        exact neg_le_abs _
  have h5 : (D : ℤ) * ((2 ^ h : ℤ) * A.card) ≤ 2 ^ h * (E * m) + (D * m - E * m) := by
    calc (D : ℤ) * ((2 ^ h : ℤ) * A.card)
        ≤ (D : ℤ) * ∑ u : U', chi (c ⬝ᵥ (u : Fin k → ZMod 2)) *
          ∑ j : Fin m, chi (v j ⬝ᵥ (u : Fin k → ZMod 2)) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg _)
      _ = ∑ u : U', (D : ℤ) * (chi (c ⬝ᵥ (u : Fin k → ZMod 2)) *
          ∑ j : Fin m, chi (v j ⬝ᵥ (u : Fin k → ZMod 2))) := Finset.mul_sum _ _ _
      _ ≤ ∑ u : U', ((E : ℤ) * m + (if u = 0 then (D : ℤ) * m - E * m else 0)) :=
          Finset.sum_le_sum (fun u _ => h4 u)
      _ = 2 ^ h * (E * m) + (D * m - E * m) := by
          rw [Finset.sum_add_distrib]
          simp [hcard]
  have key : ((2 ^ h * D * A.card : ℕ) : ℤ) ≤ (((D + (2 ^ h - 1) * E) * m : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (Nat.one_le_two_pow (n := h))]
    linarith
  exact_mod_cast key

end PEqualNP.Outside.L_meta_29726

theorem PEqualNP.Outside.L_meta_29726 : (∀ (k m h D E : ℕ), 0 < D →
  let F := ZMod 2
  let V := Fin k → F
  ∀ v : Fin m ↪ V, (∀ j, v j ≠ 0) →
    (∀ x : V, x ≠ 0 →
      let n := ((Finset.univ : Finset (Fin m)).filter (fun j => dotProduct (v j) x = 1)).card
      D*((m : ℤ)-2*(n : ℤ)).natAbs ≤ E*m) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack k C →
      (∀ g ∈ C.gates, (g.op = .and ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)) →
      let s := C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))
      2*s+h ≤ k → ∀ (K : Finset (Fin m)) (dec : Bool → Fin m → F),
        let bit := fun x : V => C.eval (List.ofFn (fun i : Fin k => decide (x i = 1)))
        let G := 2*(∑ x : V, (K.filter (fun j => dec (bit x) j = dotProduct (v j) x)).card) -
          2^k*K.card
        2^h*D*G^2 ≤ (D+(2^h-1)*E)*m*(2^k)^2) := by
  intro k m h D E _ F V v hv hbias C _ hg s hs K dec bit G
  obtain ⟨U, c, hfr, hb⟩ := PEqualNP.Outside.L_meta_29726.struct k C hg
  have hs' : 2 * C.gates.countP
      (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.and)
        (Classical.propDecidable _)) + h ≤ k := hs
  classical
  have h1 := PEqualNP.Outside.L_meta_29726.gain_sq k m v hv bit U c hb K dec
    (Finset.univ.filter (fun j : Fin m => ∀ u ∈ U, (c + v j) ⬝ᵥ u = 0))
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  have h2 := PEqualNP.Outside.L_meta_29726.count_flat k m h D E v hbias U (by omega) c
    (Finset.univ.filter (fun j : Fin m => ∀ u ∈ U, (c + v j) ⬝ᵥ u = 0))
    (fun j hj => (Finset.mem_filter.mp hj).2)
  calc 2 ^ h * D * G ^ 2
      ≤ 2 ^ h * D * ((Finset.univ.filter
        (fun j : Fin m => ∀ u ∈ U, (c + v j) ⬝ᵥ u = 0)).card * (2 ^ k) ^ 2) :=
        Nat.mul_le_mul_left _ h1
    _ = (2 ^ h * D * (Finset.univ.filter
        (fun j : Fin m => ∀ u ∈ U, (c + v j) ⬝ᵥ u = 0)).card) * (2 ^ k) ^ 2 := by ring
    _ ≤ (D + (2 ^ h - 1) * E) * m * (2 ^ k) ^ 2 := Nat.mul_le_mul_right _ h2

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25599_aux

abbrev Bv (m : ℕ) := Fin m → ZMod 2
abbrev Vv (m : ℕ) := (Bv m × Bv m) × (Bv m × Bv m)

def chi (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_zero : chi 0 = 1 := rfl
lemma chi_one : chi 1 = -1 := rfl

lemma zmod2_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

def Qf (m : ℕ) (a b c d : ZMod 2) (z : Vv m) : ZMod 2 :=
  ∑ i, (z.1.1 i * (a * z.2.1 i + b * z.2.2 i) + z.1.2 i * (c * z.2.1 i + d * z.2.2 i))

def Bf (m : ℕ) (a b c d : ZMod 2) (z h : Vv m) : ZMod 2 :=
  ∑ i, (z.1.1 i * (a * h.2.1 i + b * h.2.2 i) + z.1.2 i * (c * h.2.1 i + d * h.2.2 i)
       + h.1.1 i * (a * z.2.1 i + b * z.2.2 i) + h.1.2 i * (c * z.2.1 i + d * z.2.2 i))

lemma Qf_add (m : ℕ) (a b c d : ZMod 2) (z h : Vv m) :
    Qf m a b c d (z + h) = Qf m a b c d z + Qf m a b c d h + Bf m a b c d z h := by
  simp only [Qf, Bf, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

lemma Bf_add_left (m : ℕ) (a b c d : ZMod 2) (z z' h : Vv m) :
    Bf m a b c d (z + z') h = Bf m a b c d z h + Bf m a b c d z' h := by
  simp only [Bf, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

lemma Bf_zero_right (m : ℕ) (a b c d : ZMod 2) (z : Vv m) : Bf m a b c d z 0 = 0 := by
  simp [Bf]

lemma Bf_nondeg (m : ℕ) (a b c d : ZMod 2) (hdet : a * d - b * c = 1) (h : Vv m)
    (H : ∀ z, Bf m a b c d z h = 0) : h = 0 := by
  have e1 : ∀ i, a * h.2.1 i + b * h.2.2 i = 0 := by
    intro i
    have := H ((Pi.single i 1, 0), (0, 0))
    simpa [Bf, Pi.single_apply] using this
  have e2 : ∀ i, c * h.2.1 i + d * h.2.2 i = 0 := by
    intro i
    have := H ((0, Pi.single i 1), (0, 0))
    simpa [Bf, Pi.single_apply] using this
  have e3 : ∀ i, h.1.1 i * a + h.1.2 i * c = 0 := by
    intro i
    have := H ((0, 0), (Pi.single i 1, 0))
    simpa [Bf, Pi.single_apply, Finset.sum_add_distrib] using this
  have e4 : ∀ i, h.1.1 i * b + h.1.2 i * d = 0 := by
    intro i
    have := H ((0, 0), (0, Pi.single i 1))
    simpa [Bf, Pi.single_apply, Finset.sum_add_distrib] using this
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> funext i
  · show h.1.1 i = 0
    linear_combination d * e3 i - c * e4 i - h.1.1 i * hdet
  · show h.1.2 i = 0
    linear_combination -b * e3 i + a * e4 i - h.1.2 i * hdet
  · show h.2.1 i = 0
    linear_combination d * e1 i - b * e2 i - h.2.1 i * hdet
  · show h.2.2 i = 0
    linear_combination -c * e1 i + a * e2 i - h.2.2 i * hdet

lemma sum_chi_additive {m : ℕ} (g : Vv m → ZMod 2) (hg : ∀ z w, g (z + w) = g z + g w)
    (z0 : Vv m) (hz0 : g z0 = 1) : ∑ z, chi (g z) = 0 := by
  have h1 : ∑ z, chi (g (z + z0)) = ∑ z, chi (g z) :=
    Fintype.sum_equiv (Equiv.addRight z0) _ _ (fun z => rfl)
  simp only [hg, hz0, chi_add, chi_one] at h1
  rw [← Finset.sum_mul] at h1
  linarith

lemma card_Vv (m : ℕ) : (Fintype.card (Vv m) : ℤ) = (2 ^ (2 * m)) ^ 2 := by
  simp [Fintype.card_prod, ZMod.card]
  ring

lemma gauss_sq (m : ℕ) (a b c d : ZMod 2) (hdet : a * d - b * c = 1)
    (L : Vv m →ₗ[ZMod 2] ZMod 2) (k : ZMod 2) :
    (∑ z, chi (Qf m a b c d z + L z + k)) ^ 2 = (2 ^ (2 * m)) ^ 2 := by
  set f : Vv m → ZMod 2 := fun z => Qf m a b c d z + L z + k with hfdef
  have hpair : ∀ z h, f z + f (z + h) = (Qf m a b c d h + L h) + Bf m a b c d z h := by
    intro z h
    have eQ := Qf_add m a b c d z h
    have eL : L (z + h) = L z + L h := map_add L z h
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp only [hfdef]
    linear_combination eQ + eL + (Qf m a b c d z + L z + k) * h2
  have hinner : ∀ h : Vv m, ∑ z, chi (Bf m a b c d z h) =
      if h = 0 then (Fintype.card (Vv m) : ℤ) else 0 := by
    intro h
    split_ifs with hh
    · subst hh
      simp [Bf_zero_right, chi_zero]
    · have : ∃ z0, Bf m a b c d z0 h ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hh (Bf_nondeg m a b c d hdet h hc)
      obtain ⟨z0, hz0⟩ := this
      exact sum_chi_additive (fun z => Bf m a b c d z h)
        (fun z w => Bf_add_left m a b c d z w h) z0 (zmod2_ne_zero _ hz0)
  have step1 : ∀ z, ∑ w, chi (f z) * chi (f w) = ∑ h, chi (f z) * chi (f (z + h)) := by
    intro z
    exact (Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun h => rfl)).symm
  have hQ0 : Qf m a b c d 0 = 0 := by simp [Qf]
  have : (∑ z, chi (f z)) ^ 2 = (Fintype.card (Vv m) : ℤ) := by
    calc (∑ z, chi (f z)) ^ 2 = ∑ z, ∑ w, chi (f z) * chi (f w) := by
          rw [sq, Fintype.sum_mul_sum]
      _ = ∑ z, ∑ h, chi (Qf m a b c d h + L h) * chi (Bf m a b c d z h) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [step1 z]
          apply Finset.sum_congr rfl
          intro h _
          rw [← chi_add, hpair, chi_add]
      _ = ∑ h, chi (Qf m a b c d h + L h) * ∑ z, chi (Bf m a b c d z h) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ∑ h, chi (Qf m a b c d h + L h) *
            (if h = 0 then (Fintype.card (Vv m) : ℤ) else 0) := by
          simp only [hinner]
      _ = (Fintype.card (Vv m) : ℤ) := by
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hQ0,
            map_zero, add_zero, chi_zero, one_mul]
  rw [this, card_Vv]

lemma gauss_abs (m : ℕ) (a b c d : ZMod 2) (hdet : a * d - b * c = 1)
    (L : Vv m →ₗ[ZMod 2] ZMod 2) (k : ZMod 2) :
    |∑ z, chi (Qf m a b c d z + L z + k)| ≤ 2 ^ (2 * m) :=
  abs_le_of_sq_le_sq (le_of_eq (gauss_sq m a b c d hdet L k)) (by positivity)

lemma fiber_bound (m : ℕ) (a b c d : ZMod 2) (hdet : a * d - b * c = 1) {ι : Type*} [DecidableEq ι]
    (Lf : ι → Vv m →ₗ[ZMod 2] ZMod 2) (cf : ι → ZMod 2) (J : Finset ι) :
    ∀ (L : Vv m →ₗ[ZMod 2] ZMod 2) (k : ZMod 2),
    |∑ z ∈ Finset.univ.filter (fun z => ∀ j ∈ J, Lf j z = cf j), chi (Qf m a b c d z + L z + k)|
      ≤ 2 ^ (2 * m) := by
  induction J using Finset.induction_on with
  | empty =>
    intro L k
    simpa using gauss_abs m a b c d hdet L k
  | insert j J hj ih =>
    intro L k
    have key : 2 * ∑ z ∈ Finset.univ.filter (fun z => ∀ j' ∈ insert j J, Lf j' z = cf j'),
          chi (Qf m a b c d z + L z + k)
        = ∑ z ∈ Finset.univ.filter (fun z => ∀ j' ∈ J, Lf j' z = cf j'),
            chi (Qf m a b c d z + L z + k)
          + ∑ z ∈ Finset.univ.filter (fun z => ∀ j' ∈ J, Lf j' z = cf j'),
              chi (Qf m a b c d z + (L + Lf j) z + (k + cf j)) := by
      simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      have e : Qf m a b c d z + (L + Lf j) z + (k + cf j)
          = (Qf m a b c d z + L z + k) + (Lf j z + cf j) := by
        simp only [LinearMap.add_apply]; ring
      rw [e, chi_add (Qf m a b c d z + L z + k)]
      have hc : chi (Lf j z + cf j) = if Lf j z = cf j then 1 else -1 := by
        generalize Lf j z = x
        generalize cf j = y
        fin_cases x <;> fin_cases y <;> rfl
      rw [hc]
      simp only [Finset.forall_mem_insert]
      split_ifs <;> first | ring1 | (exfalso; tauto)
    have h1 := ih L k
    have h2 := ih (L + Lf j) (k + cf j)
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith

lemma run_fiber {m q : ℕ} (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (Vv m →ₗ[ZMod 2] ZMod 2))
    (run : Vv m → Fin q → ZMod 2)
    (hf : ∀ (z : Vv m) (j : Fin q),
      run z j = ask j (fun i => run z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z)
    (t : Fin q → ZMod 2) (z : Vv m) :
    run z = t ↔ ∀ j : Fin q,
      ask j (fun i => t ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z = t j := by
  constructor
  · rintro rfl j
    exact (hf z j).symm
  · intro H
    have main : ∀ n, ∀ j : Fin q, j.val < n → run z j = t j := by
      intro n
      induction n with
      | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
      | succ n ih =>
        intro j hj
        rw [hf z j]
        have : (fun i : Fin j.val => run z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)
            = (fun i => t ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) := by
          funext i
          exact ih _ (show i.val < n by have := i.isLt; omega)
        rw [this]
        exact H j
    funext j
    exact main q j j.isLt

lemma fiber_chi_bound {m q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (Vv m →ₗ[ZMod 2] ZMod 2))
    (run : Vv m → Fin q → ZMod 2)
    (hf : ∀ (z : Vv m) (j : Fin q),
      run z j = ask j (fun i => run z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z)
    (t : Fin q → ZMod 2) (a b c d : ZMod 2) (hdet : a * d - b * c = 1) :
    |∑ z ∈ Finset.univ.filter (fun z => run z = t), chi (Qf m a b c d z)| ≤ 2 ^ (2 * m) := by
  have := fiber_bound m a b c d hdet
    (fun j => ask j (fun i => t ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)) t Finset.univ 0 0
  simp only [LinearMap.zero_apply, add_zero] at this
  refine (le_of_eq ?_).trans this
  congr 2
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, true_implies]
  exact run_fiber ask run hf t z

def bitA (m : ℕ) (x : Vv m) : ZMod 2 := ∑ i : Fin m, (x.1.1 i * x.2.1 i + x.1.2 i * x.2.2 i)
def bitB (m : ℕ) (y : Vv m) : ZMod 2 :=
  ∑ i : Fin m, (y.1.1 i * y.2.2 i + y.1.2 i * y.2.1 i + y.1.2 i * y.2.2 i)
def edgeOf (x y : ZMod 2) : Fin 3 × Fin 3 :=
  (if x = 0 then (if y = 0 then (0, 1) else (1, 2)) else (2, 0) : Fin 3 × Fin 3)
def edge (m : ℕ) (z : Vv m) : Fin 3 × Fin 3 := edgeOf (bitA m z) (bitB m z)

lemma bitA_eq (m : ℕ) (z : Vv m) : bitA m z = Qf m 1 0 0 1 z := by
  simp only [bitA, Qf]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bitB_eq (m : ℕ) (z : Vv m) : bitB m z = Qf m 0 1 1 1 z := by
  simp only [bitB, Qf]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bitAB_eq (m : ℕ) (z : Vv m) : bitA m z + bitB m z = Qf m 1 1 1 0 z := by
  simp only [bitA, bitB, Qf, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (z.1.2 i * z.2.2 i) * h2

lemma edge_count (x y : ZMod 2) :
    (4 * (if edgeOf x y = (0, 1) then 1 else 0 : ℤ) = 1 + chi x + chi y + chi (x + y)) ∧
    (4 * (if edgeOf x y = (1, 2) then 1 else 0 : ℤ) = 1 + chi x - chi y - chi (x + y)) ∧
    (4 * (if edgeOf x y = (2, 0) then 1 else 0 : ℤ) = 2 - 2 * chi x) := by
  fin_cases x <;> fin_cases y <;> decide

lemma count_lower (m : ℕ) (F : Finset (Vv m)) (N : ℕ)
    (hA : |∑ z ∈ F, chi (bitA m z)| ≤ N) (hB : |∑ z ∈ F, chi (bitB m z)| ≤ N)
    (hAB : |∑ z ∈ F, chi (bitA m z + bitB m z)| ≤ N) :
    F.card ≤ 4 * (F.filter (fun z => edge m z = (0, 1))).card + 3 * N ∧
    F.card ≤ 4 * (F.filter (fun z => edge m z = (1, 2))).card + 3 * N ∧
    F.card ≤ 4 * (F.filter (fun z => edge m z = (2, 0))).card + 3 * N := by
  have hc : ∀ e : Fin 3 × Fin 3, ((F.filter (fun z => edge m z = e)).card : ℤ)
      = ∑ z ∈ F, (if edge m z = e then 1 else 0 : ℤ) := by
    intro e
    rw [Finset.sum_boole]
  have s0 : 4 * ∑ z ∈ F, (if edge m z = (0, 1) then 1 else 0 : ℤ)
      = (F.card : ℤ) + ∑ z ∈ F, chi (bitA m z) + ∑ z ∈ F, chi (bitB m z)
        + ∑ z ∈ F, chi (bitA m z + bitB m z) := by
    have : ∀ z ∈ F, 4 * (if edge m z = (0, 1) then 1 else 0 : ℤ)
        = 1 + chi (bitA m z) + chi (bitB m z) + chi (bitA m z + bitB m z) :=
      fun z _ => (edge_count _ _).1
    rw [Finset.mul_sum, Finset.sum_congr rfl this]
    simp [Finset.sum_add_distrib]
  have s1 : 4 * ∑ z ∈ F, (if edge m z = (1, 2) then 1 else 0 : ℤ)
      = (F.card : ℤ) + ∑ z ∈ F, chi (bitA m z) - ∑ z ∈ F, chi (bitB m z)
        - ∑ z ∈ F, chi (bitA m z + bitB m z) := by
    have : ∀ z ∈ F, 4 * (if edge m z = (1, 2) then 1 else 0 : ℤ)
        = 1 + chi (bitA m z) - chi (bitB m z) - chi (bitA m z + bitB m z) :=
      fun z _ => (edge_count _ _).2.1
    rw [Finset.mul_sum, Finset.sum_congr rfl this]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s2 : 4 * ∑ z ∈ F, (if edge m z = (2, 0) then 1 else 0 : ℤ)
      = 2 * (F.card : ℤ) - 2 * ∑ z ∈ F, chi (bitA m z) := by
    have : ∀ z ∈ F, 4 * (if edge m z = (2, 0) then 1 else 0 : ℤ)
        = 2 - 2 * chi (bitA m z) :=
      fun z _ => (edge_count _ _).2.2
    rw [Finset.mul_sum, Finset.sum_congr rfl this]
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [abs_le] at hA hB hAB
  refine ⟨?_, ?_, ?_⟩
  · have : (F.card : ℤ) ≤ 4 * ((F.filter (fun z => edge m z = (0, 1))).card : ℤ) + 3 * N := by
      rw [hc]; linarith
    exact_mod_cast this
  · have : (F.card : ℤ) ≤ 4 * ((F.filter (fun z => edge m z = (1, 2))).card : ℤ) + 3 * N := by
      rw [hc]; linarith
    exact_mod_cast this
  · have : (F.card : ℤ) ≤ 4 * ((F.filter (fun z => edge m z = (2, 0))).card : ℤ) + 3 * N := by
      rw [hc]
      have : (0 : ℤ) ≤ F.card := by positivity
      linarith
    exact_mod_cast this

lemma card_Vv_nat (m : ℕ) : Fintype.card (Vv m) = 2 ^ (4 * m) := by
  simp [Fintype.card_prod, ZMod.card]
  ring

lemma exists_inj {α : Type*} (s : Finset α) (n : ℕ) (h : n ≤ s.card) :
    ∃ f : Fin n → α, Function.Injective f ∧ ∀ i, f i ∈ s := by
  refine ⟨fun i => (s.equivFin.symm (Fin.castLE h i)).val, ?_,
    fun i => (s.equivFin.symm (Fin.castLE h i)).property⟩
  intro i j hij
  have := Subtype.val_injective hij
  exact Fin.castLE_injective h (s.equivFin.symm.injective this)

lemma fails_bound {V T : Type*} [Fintype V] [DecidableEq V] (run : V → T)
    (edge : V → Fin 3 × Fin 3)
    (label : T → Fin 3 → Bool) (S : Finset (V × V × V))
    (hS : ∀ e ∈ S, run e.1 = run e.2.1 ∧ run e.1 = run e.2.2 ∧
        edge e.1 = (0, 1) ∧ edge e.2.1 = (1, 2) ∧ edge e.2.2 = (2, 0))
    (h1 : ∀ e ∈ S, ∀ e' ∈ S, e.1 = e'.1 → e = e')
    (h2 : ∀ e ∈ S, ∀ e' ∈ S, e.2.1 = e'.2.1 → e = e')
    (h3 : ∀ e ∈ S, ∀ e' ∈ S, e.2.2 = e'.2.2 → e = e') :
    S.card ≤ (Finset.univ.filter
      (fun key : V => label (run key) (edge key).1 = label (run key) (edge key).2)).card := by
  let φ : V × V × V → V := fun e =>
    if label (run e.1) 0 = label (run e.1) 1 then e.1
    else if label (run e.1) 1 = label (run e.1) 2 then e.2.1 else e.2.2
  have hφ : ∀ e ∈ S, (φ e = e.1 ∧ edge (φ e) = (0, 1) ∨ φ e = e.2.1 ∧ edge (φ e) = (1, 2) ∨
      φ e = e.2.2 ∧ edge (φ e) = (2, 0)) ∧
      label (run (φ e)) (edge (φ e)).1 = label (run (φ e)) (edge (φ e)).2 := by
    intro e he
    obtain ⟨r1, r2, E1, E2, E3⟩ := hS e he
    simp only [φ]
    split_ifs with H1 H2
    · exact ⟨Or.inl ⟨rfl, E1⟩, by rw [E1]; exact H1⟩
    · refine ⟨Or.inr (Or.inl ⟨rfl, E2⟩), ?_⟩
      rw [E2, ← r1]
      exact H2
    · refine ⟨Or.inr (Or.inr ⟨rfl, E3⟩), ?_⟩
      rw [E3, ← r2]
      revert H1 H2
      show ¬label (run e.1) 0 = label (run e.1) 1 → ¬label (run e.1) 1 = label (run e.1) 2 →
        label (run e.1) 2 = label (run e.1) 0
      generalize label (run e.1) 0 = x
      generalize label (run e.1) 1 = y
      generalize label (run e.1) 2 = w
      cases x <;> cases y <;> cases w <;> simp
  apply Finset.card_le_card_of_injOn φ
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hφ e he).2⟩
  · intro e he e' he' heq
    have he0 := (hφ e he).1
    have he0' := (hφ e' he').1
    rcases he0 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases he0' with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩
    all_goals first
      | exact h1 e he e' he' (by rw [← a1, ← a2]; exact heq)
      | exact h2 e he e' he' (by rw [← a1, ← a2]; exact heq)
      | exact h3 e he e' he' (by rw [← a1, ← a2]; exact heq)
      | (exfalso; rw [heq, b2] at b1; exact absurd b1 (by decide))

theorem part2 (m q : ℕ) (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (Vv m →ₗ[ZMod 2] ZMod 2))
    (run : Vv m → Fin q → ZMod 2)
    (hf : ∀ (z : Vv m) (j : Fin q),
      run z j = ask j (fun i => run z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z) :
    ∃ S : Finset (Vv m × Vv m × Vv m),
      (∀ e ∈ S, run e.1 = run e.2.1 ∧ run e.1 = run e.2.2 ∧
        edge m e.1 = (0, 1) ∧ edge m e.2.1 = (1, 2) ∧ edge m e.2.2 = (2, 0)) ∧
      Function.Injective (fun a : S => a.val.1) ∧
      Function.Injective (fun b : S => b.val.2.1) ∧
      Function.Injective (fun c : S => c.val.2.2) ∧
      2 ^ (4 * m) ≤ 4 * S.card + 3 * 2 ^ (2 * m) * (Finset.univ.image run).card ∧
      ∀ label : (Fin q → ZMod 2) → Fin 3 → Bool, S.card ≤
        (Finset.univ.filter (fun key : Vv m =>
          label (run key) (edge m key).1 = label (run key) (edge m key).2)).card := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : (Fin q → ZMod 2) → Finset (Vv m),
      ∀ t, F t = Finset.univ.filter (fun z => run z = t) := ⟨_, fun t => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Fin 3 × Fin 3 → (Fin q → ZMod 2) → Finset (Vv m),
      ∀ e t, P e t = (F t).filter (fun z => edge m z = e) := ⟨_, fun e t => rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : (Fin q → ZMod 2) → ℕ,
      ∀ t, n t = min (P (0, 1) t).card (min (P (1, 2) t).card (P (2, 0) t).card) :=
    ⟨_, fun t => rfl⟩
  have hFbound : ∀ t, (F t).card ≤ 4 * n t + 3 * 2 ^ (2 * m) := by
    intro t
    have hA := fiber_chi_bound ask run hf t 1 0 0 1 (by decide)
    have hB := fiber_chi_bound ask run hf t 0 1 1 1 (by decide)
    have hAB := fiber_chi_bound ask run hf t 1 1 1 0 (by decide)
    simp only [← bitA_eq, ← bitB_eq, ← bitAB_eq, ← hF] at hA hB hAB
    obtain ⟨c0, c1, c2⟩ := count_lower m (F t) (2 ^ (2 * m))
      (by exact_mod_cast hA) (by exact_mod_cast hB) (by exact_mod_cast hAB)
    rw [← hP] at c0 c1 c2
    rw [hn t]
    omega
  have mem_P : ∀ e t z, z ∈ P e t ↔ run z = t ∧ edge m z = e := by
    intro e t z
    rw [hP, Finset.mem_filter, hF, Finset.mem_filter]
    simp
  choose f0 hf0i hf0m using fun t => exists_inj (P (0, 1) t) (n t) (by rw [hn t]; omega)
  choose f1 hf1i hf1m using fun t => exists_inj (P (1, 2) t) (n t) (by rw [hn t]; omega)
  choose f2 hf2i hf2m using fun t => exists_inj (P (2, 0) t) (n t) (by rw [hn t]; omega)
  have keyI : ∀ (e : Fin 3 × Fin 3) (f : (t : Fin q → ZMod 2) → Fin (n t) → Vv m),
      (∀ t, Function.Injective (f t)) → (∀ t i, f t i ∈ P e t) →
      ∀ p p' : (Σ t, Fin (n t)), f p.1 p.2 = f p'.1 p'.2 → p = p' := by
    intro e f hfi hfm p p' h
    obtain ⟨t, i⟩ := p
    obtain ⟨t', i'⟩ := p'
    have a := ((mem_P _ _ _).1 (hfm t i)).1
    have b := ((mem_P _ _ _).1 (hfm t' i')).1
    have ht : t = t' := by
      simp only at h
      rw [h] at a
      exact a.symm.trans b
    subst ht
    have : i = i' := hfi t h
    subst this
    rfl
  let g : (Σ t, Fin (n t)) → Vv m × Vv m × Vv m := fun p => (f0 p.1 p.2, f1 p.1 p.2, f2 p.1 p.2)
  have ginj : Function.Injective g := fun p p' h =>
    keyI _ f0 hf0i hf0m p p' (congrArg Prod.fst h)
  have hS : ∀ e ∈ Finset.univ.image g, run e.1 = run e.2.1 ∧ run e.1 = run e.2.2 ∧
        edge m e.1 = (0, 1) ∧ edge m e.2.1 = (1, 2) ∧ edge m e.2.2 = (2, 0) := by
    intro e he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 he
    have a := (mem_P _ _ _).1 (hf0m p.1 p.2)
    have b := (mem_P _ _ _).1 (hf1m p.1 p.2)
    have c := (mem_P _ _ _).1 (hf2m p.1 p.2)
    exact ⟨a.1.trans b.1.symm, a.1.trans c.1.symm, a.2, b.2, c.2⟩
  have i1 : ∀ e ∈ Finset.univ.image g, ∀ e' ∈ Finset.univ.image g, e.1 = e'.1 → e = e' := by
    intro e he e' he' h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.1 he'
    rw [keyI _ f0 hf0i hf0m p p' h]
  have i2 : ∀ e ∈ Finset.univ.image g, ∀ e' ∈ Finset.univ.image g, e.2.1 = e'.2.1 → e = e' := by
    intro e he e' he' h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.1 he'
    rw [keyI _ f1 hf1i hf1m p p' h]
  have i3 : ∀ e ∈ Finset.univ.image g, ∀ e' ∈ Finset.univ.image g, e.2.2 = e'.2.2 → e = e' := by
    intro e he e' he' h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.1 he'
    rw [keyI _ f2 hf2i hf2m p p' h]
  refine ⟨Finset.univ.image g, hS, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext (i1 x hx y hy h)
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext (i2 x hx y hy h)
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext (i3 x hx y hy h)
  · have hcard : (Finset.univ.image g).card = ∑ t, n t := by
      rw [Finset.card_image_of_injective _ ginj, Finset.card_univ, Fintype.card_sigma]
      simp
    have hV : 2 ^ (4 * m) = ∑ t ∈ Finset.univ.image run, (F t).card := by
      rw [← card_Vv_nat m, ← Finset.card_univ, Finset.card_eq_sum_card_image run Finset.univ]
      exact Finset.sum_congr rfl (fun t _ => (congrArg Finset.card (hF t)).symm)
    rw [hV, hcard]
    calc ∑ t ∈ Finset.univ.image run, (F t).card
        ≤ ∑ t ∈ Finset.univ.image run, (4 * n t + 3 * 2 ^ (2 * m)) :=
          Finset.sum_le_sum (fun t _ => hFbound t)
      _ = 4 * ∑ t ∈ Finset.univ.image run, n t
            + 3 * 2 ^ (2 * m) * (Finset.univ.image run).card := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ 4 * ∑ t, n t + 3 * 2 ^ (2 * m) * (Finset.univ.image run).card := by
          have := Finset.sum_le_sum_of_subset (f := n) (Finset.subset_univ (Finset.univ.image run))
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 this) _
  · intro label
    exact fails_bound run (edge m) label _ hS i1 i2 i3

def label0 (x : ZMod 2) (k : Fin 3) : Bool := if x = 0 then decide (k ≠ 1) else decide (k = 0)

lemma label0_good (x y : ZMod 2) :
    label0 x (edgeOf x y).1 ≠ label0 x (edgeOf x y).2 := by
  fin_cases x <;> fin_cases y <;> decide

theorem part1 (m : ℕ) : ∃ label : ZMod 2 → Fin 3 → Bool,
    ∀ z : Vv m, label (bitA m z) (edge m z).1 ≠ label (bitA m z) (edge m z).2 :=
  ⟨label0, fun z => label0_good (bitA m z) (bitB m z)⟩

def coordA (m k : ℕ) (z : Vv m) : ZMod 2 :=
  if h : k < m then z.1.1 ⟨k, h⟩ else if h' : k - m < m then z.1.2 ⟨k - m, h'⟩ else 0

def coordL (m k : ℕ) : Vv m →ₗ[ZMod 2] ZMod 2 where
  toFun z := coordA m k z
  map_add' z w := by
    unfold coordA
    split_ifs <;> simp
  map_smul' r z := by
    unfold coordA
    split_ifs <;> simp

def lastL (m : ℕ) (p : ℕ → ZMod 2) : Vv m →ₗ[ZMod 2] ZMod 2 where
  toFun z := ∑ i : Fin m, (p i * z.2.1 i + p (m + i) * z.2.2 i)
  map_add' z w := by
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' r z := by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def askF (m : ℕ) : (j : Fin (2 * m + 1)) → (Fin j.val → ZMod 2) → (Vv m →ₗ[ZMod 2] ZMod 2) :=
  fun j p => if j.val < 2 * m then coordL m j.val
    else lastL m (fun k => if hk : k < j.val then p ⟨k, hk⟩ else 0)

def runF (m : ℕ) (z : Vv m) (j : Fin (2 * m + 1)) : ZMod 2 :=
  if j.val < 2 * m then coordA m j.val z else bitA m z

def colorF (m : ℕ) (t : Fin (2 * m + 1) → ZMod 2) (k : Fin 3) : Bool :=
  label0 (t ⟨2 * m, by omega⟩) k

lemma coordA_fst (m : ℕ) (z : Vv m) (i : Fin m) : coordA m i z = z.1.1 i := by
  simp [coordA]

lemma coordA_snd (m : ℕ) (z : Vv m) (i : Fin m) : coordA m (m + i) z = z.1.2 i := by
  have h1 : ¬ (m + (i : ℕ) < m) := by omega
  have h2 : m + (i : ℕ) - m < m := by omega
  rw [coordA, dif_neg h1, dif_pos h2]
  have : (⟨m + (i : ℕ) - m, h2⟩ : Fin m) = i := Fin.ext (by simp)
  rw [this]

lemma follows_runF (m : ℕ) : ∀ (z : Vv m) (j : Fin (2 * m + 1)),
    runF m z j = askF m j (fun i => runF m z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z := by
  intro z j
  by_cases hj : j.val < 2 * m
  · simp only [runF, askF, if_pos hj]
    rfl
  · have hj2 : j.val = 2 * m := by omega
    simp only [askF, if_neg hj]
    simp only [runF, if_neg hj]
    show bitA m z = ∑ i : Fin m, (_ * z.2.1 i + _ * z.2.2 i)
    simp only [bitA]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : (i : ℕ) < j.val := by omega
    have h2 : m + (i : ℕ) < j.val := by omega
    have h3 : (i : ℕ) < 2 * m := by omega
    have h4 : m + (i : ℕ) < 2 * m := by omega
    rw [dif_pos h1, dif_pos h2]
    simp only [if_pos h3, if_pos h4, coordA_fst, coordA_snd]

lemma fails_runF (m : ℕ) :
    Finset.univ.filter (fun key : Vv m =>
      colorF m (runF m key) (edge m key).1 = colorF m (runF m key) (edge m key).2) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro key _
  have h : runF m key ⟨2 * m, by omega⟩ = bitA m key := by
    simp [runF]
  simp only [colorF, h]
  exact label0_good (bitA m key) (bitB m key)

theorem part3 (m : ℕ) :
    ∃ (ask : (j : Fin (2 * m + 1)) → (Fin j.val → ZMod 2) → (Vv m →ₗ[ZMod 2] ZMod 2))
      (run : Vv m → Fin (2 * m + 1) → ZMod 2)
      (color : (Fin (2 * m + 1) → ZMod 2) → Fin 3 → Bool),
      (∀ (z : Vv m) (j : Fin (2 * m + 1)),
        run z j = ask j (fun i => run z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z) ∧
      Finset.univ.filter (fun key : Vv m =>
        color (run key) (edge m key).1 = color (run key) (edge m key).2) = ∅ :=
  ⟨askF m, runF m, colorF m, follows_runF m, fails_runF m⟩

end PEqualNP.Outside.L_meta_25599_aux

theorem PEqualNP.Outside.L_meta_25599 : ∀ m : ℕ,
  let B := Fin m → ZMod 2
  let V := (B × B) × (B × B)
  let bitA := fun x : V => ∑ i : Fin m, (x.1.1 i * x.2.1 i + x.1.2 i * x.2.2 i)
  let bitB := fun y : V => ∑ i : Fin m,
    (y.1.1 i * y.2.2 i + y.1.2 i * y.2.1 i + y.1.2 i * y.2.2 i)
  let edge := fun z : V =>
    (if bitA z = 0 then (if bitB z = 0 then (0, 1) else (1, 2)) else (2, 0) : Fin 3 × Fin 3)
  let Ask := fun q : ℕ => (j : Fin q) → (Fin j.val → ZMod 2) → (V →ₗ[ZMod 2] ZMod 2)
  let follows := fun (q : ℕ) (ask : Ask q) (run : V → Fin q → ZMod 2) =>
    ∀ (z : V) (j : Fin q),
      run z j = ask j (fun i => run z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z
  let fails := fun (q : ℕ) (run : V → Fin q → ZMod 2) (label : (Fin q → ZMod 2) → Fin 3 → Bool) =>
    Finset.univ.filter (fun key : V => label (run key) (edge key).1 = label (run key) (edge key).2)
  (∃ label : ZMod 2 → Fin 3 → Bool,
    ∀ z : V, label (bitA z) (edge z).1 ≠ label (bitA z) (edge z).2) ∧
  (∀ (q : ℕ) (ask : Ask q) (run : V → Fin q → ZMod 2), follows q ask run →
    ∃ S : Finset (V × V × V),
      (∀ e ∈ S, run e.1 = run e.2.1 ∧ run e.1 = run e.2.2 ∧
        edge e.1 = (0, 1) ∧ edge e.2.1 = (1, 2) ∧ edge e.2.2 = (2, 0)) ∧
      Function.Injective (fun a : S => a.val.1) ∧
      Function.Injective (fun b : S => b.val.2.1) ∧
      Function.Injective (fun c : S => c.val.2.2) ∧
      2 ^ (4 * m) ≤ 4 * S.card + 3 * 2 ^ (2 * m) * (Finset.univ.image run).card ∧
      ∀ label : (Fin q → ZMod 2) → Fin 3 → Bool, S.card ≤ (fails q run label).card) ∧
  (let q := 2 * m + 1
   ∃ (ask : Ask q) (run : V → Fin q → ZMod 2) (color : (Fin q → ZMod 2) → Fin 3 → Bool),
     follows q ask run ∧ fails q run color = ∅) := by
  intro m
  exact ⟨PEqualNP.Outside.L_meta_25599_aux.part1 m,
    fun q ask run hf => PEqualNP.Outside.L_meta_25599_aux.part2 m q ask run hf,
    PEqualNP.Outside.L_meta_25599_aux.part3 m⟩

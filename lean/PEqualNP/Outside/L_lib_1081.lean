import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1081
open Module in
abbrev BB (m : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin m → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)
open Module in
theorem BB_apply (m : ℕ) (w y : Fin m → ZMod 2) : BB m w y = ∑ i, w i * y i := rfl
open Module in
theorem ker_BB (m : ℕ) : LinearMap.ker (BB m) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  rw [Submodule.mem_bot]
  funext i
  have h := LinearMap.congr_fun hw (Pi.single i 1)
  rw [BB_apply] at h
  simpa [Pi.single_apply] using h
open Module in
theorem finrank_orth (m : ℕ) (Q : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    finrank (ZMod 2) Q + finrank (ZMod 2) ((BB m).orthogonal Q) = m := by
  have := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := BB m) Q
  rw [ker_BB, inf_bot_eq, finrank_bot, add_zero, finrank_fin_fun] at this
  exact this
open Module in
theorem BB_refl (m : ℕ) : (BB m).IsRefl := by
  intro a b h
  rw [BB_apply] at h ⊢
  simpa [mul_comm] using h
open Module in
theorem orth_orth (m : ℕ) (Q : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (BB m).orthogonal ((BB m).orthogonal Q) = Q := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal (BB_refl m))
  have h1 := finrank_orth m Q
  have h2 := finrank_orth m ((BB m).orthogonal Q)
  omega
open Module in
theorem card_sub (m : ℕ) (Q : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Nat.card Q = 2 ^ finrank (ZMod 2) Q := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
open Module in
def sp {m : ℕ} (S : Finset (Fin m)) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  { carrier := {w | ∀ i, i ∉ S → w i = 0}, add_mem' := by
      intro a b ha hb i hi
      simp only [Set.mem_ofPred_eq] at ha hb
      simp [ha i hi, hb i hi],
    zero_mem' := by intro i _; rfl,
    smul_mem' := by
      intro c a ha i hi
      simp only [Set.mem_ofPred_eq] at ha
      simp [ha i hi] }
open Module in
theorem mem_sp {m : ℕ} (S : Finset (Fin m)) (w : Fin m → ZMod 2) :
    w ∈ sp S ↔ ∀ i, i ∉ S → w i = 0 := Iff.rfl
open Module in
def kl {m : ℕ} (S : Finset (Fin m)) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  { carrier := {y | ∀ i, i ∈ S → y i = 0}, add_mem' := by
      intro a b ha hb i hi
      simp only [Set.mem_ofPred_eq] at ha hb
      simp [ha i hi, hb i hi],
    zero_mem' := by intro i _; rfl,
    smul_mem' := by
      intro c a ha i hi
      simp only [Set.mem_ofPred_eq] at ha
      simp [ha i hi] }
open Module in
theorem mem_kl {m : ℕ} (S : Finset (Fin m)) (w : Fin m → ZMod 2) :
    w ∈ kl S ↔ ∀ i, i ∈ S → w i = 0 := Iff.rfl
open Module in
theorem single_mem_sp {m : ℕ} (S : Finset (Fin m)) (i : Fin m) (hi : i ∈ S) :
    (Pi.single i 1 : Fin m → ZMod 2) ∈ sp S := by
  rw [mem_sp]
  intro j hj
  have : j ≠ i := by rintro rfl; exact hj hi
  simp [this]
open Module in
theorem orth_sp {m : ℕ} (S : Finset (Fin m)) : (BB m).orthogonal (sp S) = kl S := by
  ext y
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_kl]
  constructor
  · intro h i hi
    have := h (Pi.single i 1) (single_mem_sp S i hi)
    rw [BB_apply] at this
    simpa [Pi.single_apply] using this
  · intro h w hw
    rw [BB_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S
    · rw [h i hi, mul_zero]
    · rw [hw i hi, zero_mul]
open Module in
theorem orth_sup {m : ℕ} (A C : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (BB m).orthogonal (A ⊔ C) = (BB m).orthogonal A ⊓ (BB m).orthogonal C := by
  ext y
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha), fun c hc => h c (Submodule.mem_sup_right hc)⟩
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, LinearMap.add_apply, h1 a ha, h2 c hc, add_zero]
open Module in
theorem finrank_kl {m : ℕ} (Q : Submodule (ZMod 2) (Fin m → ZMod 2)) (S : Finset (Fin m)) :
    finrank (ZMod 2) (Q ⊓ kl S : Submodule (ZMod 2) (Fin m → ZMod 2)) +
      finrank (ZMod 2) ((BB m).orthogonal Q ⊔ sp S : Submodule (ZMod 2) (Fin m → ZMod 2)) = m := by
  have h := finrank_orth m ((BB m).orthogonal Q ⊔ sp S)
  rw [orth_sup, orth_orth, orth_sp] at h
  omega
open Module in
theorem sp_eq_span {m : ℕ} (S : Finset (Fin m)) :
    sp S = Submodule.span (ZMod 2) (Set.range (fun i : S => (Pi.single i.val 1 : Fin m → ZMod 2))) := by
  apply le_antisymm
  · intro w hw
    have hw' : w = ∑ i : S, w i.val • (Pi.single i.val 1 : Fin m → ZMod 2) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero]
      by_cases hj : j ∈ S
      · rw [Finset.sum_eq_single ⟨j, hj⟩]
        · simp
        · intro b _ hb
          have : j ≠ b.val := fun h => hb (Subtype.ext h.symm)
          simp [this]
        · simp
      · rw [hw j hj]
        symm
        apply Finset.sum_eq_zero
        intro b _
        have : j ≠ b.val := fun h => hj (h ▸ b.prop)
        simp [this]
    rw [hw']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_sp S i.val i.prop
open Module in
theorem finrank_sp {m : ℕ} (S : Finset (Fin m)) : finrank (ZMod 2) (sp S) = S.card := by
  rw [sp_eq_span]
  have hli : LinearIndependent (ZMod 2) (fun i : S => (Pi.single i.val 1 : Fin m → ZMod 2)) := by
    have := (Pi.basisFun (ZMod 2) (Fin m)).linearIndependent.comp (fun i : S => i.val)
      Subtype.val_injective
    simpa [Function.comp_def] using this
  rw [finrank_span_eq_card hli, Fintype.card_coe]
open Module in
theorem kl_anti {m : ℕ} (S S' : Finset (Fin m)) (h : S ⊆ S') : kl S' ≤ kl S := by
  intro y hy i hi
  exact hy i (h hi)
open Module in
theorem sp_mono {m : ℕ} (S S' : Finset (Fin m)) (h : S ⊆ S') : sp S ≤ sp S' := by
  intro y hy i hi
  exact hy i (fun h' => hi (h h'))
open Module in
def nx {t : ℕ} (i : Fin (3*t)) : Fin (3*t) :=
  ⟨(i.val + 1) % (3*t), Nat.mod_lt _ (by have := i.isLt; omega)⟩
open Module in
def pv {t : ℕ} (i : Fin (3*t)) : Fin (3*t) :=
  ⟨(i.val + (3*t - 1)) % (3*t), Nat.mod_lt _ (by have := i.isLt; omega)⟩
open Module in
theorem nxv {t : ℕ} (i : Fin (3*t)) :
    (i.val + 1 < 3*t ∧ (nx i).val = i.val + 1) ∨ (i.val + 1 = 3*t ∧ (nx i).val = 0) := by
  have hi := i.isLt
  by_cases h : i.val + 1 < 3*t
  · left; exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    have h' : i.val + 1 = 3*t := by omega
    refine ⟨h', ?_⟩
    show (i.val + 1) % (3*t) = 0
    rw [h', Nat.mod_self]
open Module in
theorem pvv {t : ℕ} (i : Fin (3*t)) :
    (0 < i.val ∧ (pv i).val = i.val - 1) ∨ (i.val = 0 ∧ (pv i).val = 3*t - 1) := by
  have hi := i.isLt
  by_cases h : 0 < i.val
  · left
    refine ⟨h, ?_⟩
    show (i.val + (3*t - 1)) % (3*t) = i.val - 1
    have : i.val + (3*t - 1) = (i.val - 1) + 3*t := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · right
    have h' : i.val = 0 := by omega
    refine ⟨h', ?_⟩
    show (i.val + (3*t - 1)) % (3*t) = 3*t - 1
    rw [h', zero_add, Nat.mod_eq_of_lt (by omega)]
open Module in
theorem nx_pv {t : ℕ} (i : Fin (3*t)) : nx (pv i) = i := by
  apply Fin.ext
  have := i.isLt
  rcases nxv (pv i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases pvv i with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
open Module in
theorem pv_nx {t : ℕ} (i : Fin (3*t)) : pv (nx i) = i := by
  apply Fin.ext
  have := i.isLt
  rcases nxv i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases pvv (nx i) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
open Module in
def cv {m : ℕ} (e : ℕ) : Fin m → ZMod 2 := fun i => if i.val % 3 = e ∨ i.val % 3 = 2 then 1 else 0
open Module in
def ZZ (m : ℕ) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range ![cv 0, cv 1])
open Module in
theorem mem_ZZ {m : ℕ} (z : Fin m → ZMod 2) : z ∈ ZZ m ↔ ∃ a b : ZMod 2, a • cv 0 + b • cv 1 = z := by
  rw [ZZ, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c 0, c 1, by rw [← hc, Fin.sum_univ_two]; simp⟩
  · rintro ⟨a, b, h⟩
    exact ⟨![a, b], by rw [Fin.sum_univ_two]; simpa using h⟩
open Module in
def inC {t : ℕ} (x : Fin (3*t) → ZMod 2) : Prop :=
  BB (3*t) (cv 0) x = 0 ∧ BB (3*t) (cv 1) x = 0
open Module in
theorem finrank_ZZ (t : ℕ) (ht : 1 ≤ t) : finrank (ZMod 2) (ZZ (3*t)) = 2 := by
  rw [ZZ, finrank_span_eq_card]
  · simp
  · rw [LinearIndependent.pair_iff]
    intro a b h
    have h0 := congrFun h ⟨0, by omega⟩
    have h1 := congrFun h ⟨1, by omega⟩
    simp [cv] at h0 h1
    exact ⟨h0, h1⟩
open Module in
theorem not_mem_sp_of {m k : ℕ} (g : Fin k → Fin m) (hg : Function.Injective g)
    (z : Fin m → ZMod 2) (hz : ∀ j, z (g j) ≠ 0) (S : Finset (Fin m)) (hS : S.card < k) :
    z ∉ sp S := by
  intro h
  have := Finset.card_le_card_of_injOn g (s := Finset.univ) (t := S) (fun j _ => by
    by_contra hj
    exact hz j (h (g j) (by simpa using hj))) hg.injOn
  simp at this
  omega
open Module in
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide
open Module in
theorem zsupp (t : ℕ) (ht : 3 ≤ t) (z : Fin (3*t) → ZMod 2) (hz : z ∈ ZZ (3*t)) (hz0 : z ≠ 0)
    (S : Finset (Fin (3*t))) (hS : S.card ≤ 5) : z ∉ sp S := by
  obtain ⟨a, b, rfl⟩ := (mem_ZZ z).mp hz
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp at hz0
  · simp only [zero_smul, one_smul, zero_add]
    apply not_mem_sp_of (k := 6) (fun j => ⟨![1,2,4,5,7,8] j, by fin_cases j <;> simp <;> omega⟩)
    · intro j j' h
      simp only [Fin.mk.injEq] at h
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro j; fin_cases j <;> simp [cv]
    · omega
  · simp only [zero_smul, one_smul, add_zero]
    apply not_mem_sp_of (k := 6) (fun j => ⟨![0,2,3,5,6,8] j, by fin_cases j <;> simp <;> omega⟩)
    · intro j j' h
      simp only [Fin.mk.injEq] at h
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro j; fin_cases j <;> simp [cv]
    · omega
  · simp only [one_smul]
    apply not_mem_sp_of (k := 6) (fun j => ⟨![0,1,3,4,6,7] j, by fin_cases j <;> simp <;> omega⟩)
    · intro j j' h
      simp only [Fin.mk.injEq] at h
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro j; fin_cases j <;> simp [cv]
    · omega
open Module in
theorem zsupp8 (t : ℕ) (ht : 4 ≤ t) (z : Fin (3*t) → ZMod 2) (hz : z ∈ ZZ (3*t)) (hz0 : z ≠ 0)
    (S : Finset (Fin (3*t))) (hS : S.card ≤ 7) : z ∉ sp S := by
  obtain ⟨a, b, rfl⟩ := (mem_ZZ z).mp hz
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp at hz0
  · simp only [zero_smul, one_smul, zero_add]
    apply not_mem_sp_of (k := 8)
      (fun j => ⟨![1,2,4,5,7,8,10,11] j, by fin_cases j <;> simp <;> omega⟩)
    · intro j j' h
      simp only [Fin.mk.injEq] at h
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro j; fin_cases j <;> simp [cv]
    · omega
  · simp only [zero_smul, one_smul, add_zero]
    apply not_mem_sp_of (k := 8)
      (fun j => ⟨![0,2,3,5,6,8,9,11] j, by fin_cases j <;> simp <;> omega⟩)
    · intro j j' h
      simp only [Fin.mk.injEq] at h
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro j; fin_cases j <;> simp [cv]
    · omega
  · simp only [one_smul]
    apply not_mem_sp_of (k := 8)
      (fun j => ⟨![0,1,3,4,6,7,9,10] j, by fin_cases j <;> simp <;> omega⟩)
    · intro j j' h
      simp only [Fin.mk.injEq] at h
      fin_cases j <;> fin_cases j' <;> simp_all
    · intro j; fin_cases j <;> simp [cv]
    · omega
open Module in
theorem fzs (t : ℕ) (ht : 3 ≤ t) (S : Finset (Fin (3*t))) (hS : S.card ≤ 5) :
    finrank (ZMod 2) (ZZ (3*t) ⊔ sp S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) = 2 + S.card := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ZZ (3*t)) (sp S)
  have hbot : ZZ (3*t) ⊓ sp S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_bot]
    by_contra h0
    exact zsupp t ht z (Submodule.mem_inf.mp hz).1 h0 S hS (Submodule.mem_inf.mp hz).2
  rw [hbot, finrank_bot, finrank_ZZ t (by omega), finrank_sp] at h
  omega
open Module in
theorem BB_comm (m : ℕ) (a b : Fin m → ZMod 2) : BB m a b = BB m b a := by
  rw [BB_apply, BB_apply]
  simp [mul_comm]
open Module in
theorem BB_single (m : ℕ) (c : Fin m → ZMod 2) (i : Fin m) : BB m c (Pi.single i 1) = c i := by
  rw [BB_apply]
  simp [Pi.single_apply]
open Module in
theorem ZZ_le (t : ℕ) (Q : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) (hQ : ∀ y ∈ Q, inC y) :
    ZZ (3*t) ≤ (BB (3*t)).orthogonal Q := by
  have h0 : cv 0 ∈ (BB (3*t)).orthogonal Q := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro q hq
    rw [BB_comm]
    exact (hQ q hq).1
  have h1 : cv 1 ∈ (BB (3*t)).orthogonal Q := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro q hq
    rw [BB_comm]
    exact (hQ q hq).2
  rw [ZZ, Submodule.span_le, Set.range_subset_iff]
  intro j
  fin_cases j
  · simpa using h0
  · simpa using h1
open Module in
theorem key (t : ℕ) (ht : 3 ≤ t) (Q : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (hQ : ∀ y ∈ Q, inC y) (S : Finset (Fin (3*t))) (hS : S.card ≤ 5) :
    finrank (ZMod 2) (Q ⊓ kl S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) + 2 + S.card ≤ 3*t := by
  have h1 := finrank_kl Q S
  have h2 : finrank (ZMod 2) (ZZ (3*t) ⊔ sp S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) ≤
      finrank (ZMod 2) ((BB (3*t)).orthogonal Q ⊔ sp S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) :=
    Submodule.finrank_mono (sup_le_sup_right (ZZ_le t Q hQ) _)
  rw [fzs t ht S hS] at h2
  omega
open Module in
theorem code_iff (t : ℕ) (x : Fin (3*t) → ZMod 2) :
    (∀ e : Fin 2, (∑ i : Fin (3*t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0) ↔
      inC x := by
  have h : ∀ e : ℕ, (∑ i : Fin (3*t), if i.val % 3 = e ∨ i.val % 3 = 2 then x i else 0) =
      BB (3*t) (cv e) x := by
    intro e
    rw [BB_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [cv]
    split_ifs <;> simp
  rw [Fin.forall_fin_two, inC, h, h]
  rfl
open Module in
def Ns {t : ℕ} (x : Fin (3*t) → ZMod 2) : Finset (Fin (3*t)) :=
  Finset.univ.filter (fun i => x i ≠ 0 ∨ x (nx i) ≠ 0)
open Module in
theorem mem_Ns {t : ℕ} (x : Fin (3*t) → ZMod 2) (i : Fin (3*t)) :
    i ∈ Ns x ↔ (x i ≠ 0 ∨ x (nx i) ≠ 0) := by
  simp [Ns]
open Module in
theorem cond_iff (t : ℕ) (x y : Fin (3*t) → ZMod 2) :
    (∀ i, x i * y i = 0 ∧ x (nx i) * y i = 0) ↔ y ∈ kl (Ns x) := by
  rw [mem_kl]
  simp only [mem_Ns, mul_eq_zero]
  constructor
  · intro h i hi
    rcases hi with hi | hi
    · exact (h i).1.resolve_left hi
    · exact (h i).2.resolve_left hi
  · intro h i
    by_cases hy : y i = 0
    · exact ⟨Or.inr hy, Or.inr hy⟩
    · have : ¬ (x i ≠ 0 ∨ x (nx i) ≠ 0) := fun hh => hy (h i hh)
      push_neg at this
      exact ⟨Or.inl this.1, Or.inl this.2⟩
open Module in
theorem hits_eq (t : ℕ) (Q : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) (x : Fin (3*t) → ZMod 2) :
    Nat.card {y : Q // ∀ i : Fin (3*t), x i * y.val i = 0 ∧ x (nx i) * y.val i = 0} =
      2 ^ finrank (ZMod 2) (Q ⊓ kl (Ns x) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) := by
  rw [← card_sub]
  apply Nat.card_congr
  exact {
    toFun := fun y => ⟨y.val.val, Submodule.mem_inf.mpr ⟨y.val.prop, (cond_iff t x y.val.val).mp y.prop⟩⟩
    invFun := fun y => ⟨⟨y.val, (Submodule.mem_inf.mp y.prop).1⟩,
      (cond_iff t x y.val).mpr (Submodule.mem_inf.mp y.prop).2⟩
    left_inv := fun y => rfl
    right_inv := fun y => rfl }
open Module in
def Far {t : ℕ} (α β : Fin (3*t)) : Prop := β ≠ α ∧ β ≠ nx α ∧ β ≠ pv α
open Module in
def S4 {t : ℕ} (α β : Fin (3*t)) : Finset (Fin (3*t)) := {pv α, α, pv β, β}
open Module in
def Form {t : ℕ} (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) : Prop :=
  (α.val % 3 = β.val % 3 ∧ x = Pi.single α 1 + Pi.single β 1) ∨
  (β = nx (nx α) ∧ x = Pi.single α 1 + Pi.single (nx α) 1 + Pi.single β 1) ∨
  (α = nx (nx β) ∧ x = Pi.single β 1 + Pi.single (nx β) 1 + Pi.single α 1)
open Module in
theorem res_nx {t : ℕ} (i : Fin (3*t)) : (nx i).val % 3 = (i.val % 3 + 1) % 3 := by
  rcases nxv i with ⟨_, h⟩ | ⟨h1, h⟩ <;> omega
open Module in
theorem res_pv {t : ℕ} (i : Fin (3*t)) : (pv i).val % 3 = (i.val % 3 + 2) % 3 := by
  have := i.isLt
  rcases pvv i with ⟨h1, h⟩ | ⟨h1, h⟩ <;> omega
open Module in
theorem cv_val {m : ℕ} (e : ℕ) (i : Fin m) (r : ℕ) (h : i.val % 3 = r) :
    cv e i = if r = e ∨ r = 2 then 1 else 0 := by
  simp [cv, h]
open Module in
theorem zmod2_ne {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with h' | h'
  · exact absurd h' h
  · exact h'
open Module in
theorem BB_x2 (m : ℕ) (c : Fin m → ZMod 2) (a b : ZMod 2) (u v : Fin m) :
    BB m c (a • Pi.single u 1 + b • Pi.single v 1) = a * c u + b * c v := by
  rw [map_add, map_smul, map_smul, BB_single, BB_single]
  simp [smul_eq_mul, mul_comm]
open Module in
theorem BB_x3 (m : ℕ) (c : Fin m → ZMod 2) (a b d : ZMod 2) (u v w : Fin m) :
    BB m c (a • Pi.single u 1 + b • Pi.single v 1 + d • Pi.single w 1) =
      a * c u + b * c v + d * c w := by
  rw [map_add, map_add, map_smul, map_smul, map_smul, BB_single, BB_single, BB_single]
  simp [smul_eq_mul, mul_comm]
open Module in
theorem eq2 {m : ℕ} (x : Fin m → ZMod 2) (a b : Fin m) (hab : a ≠ b)
    (hs : ∀ i, x i ≠ 0 → i = a ∨ i = b) : x = x a • Pi.single a 1 + x b • Pi.single b 1 := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h1 : i = a
  · subst h1; simp [hab]
  · by_cases h2 : i = b
    · subst h2; simp [h1]
    · rw [if_neg h1, if_neg h2, add_zero]
      by_contra h3
      rcases hs i h3 with h4 | h4 <;> contradiction
open Module in
theorem eq3 {m : ℕ} (x : Fin m → ZMod 2) (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : ∀ i, x i ≠ 0 → i = a ∨ i = b ∨ i = c) :
    x = x a • Pi.single a 1 + x b • Pi.single b 1 + x c • Pi.single c 1 := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h1 : i = a
  · subst h1; simp [hab, hac]
  · by_cases h2 : i = b
    · subst h2; simp [h1, hbc]
    · by_cases h3 : i = c
      · subst h3; simp [h1, h2]
      · rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero]
        by_contra h4
        rcases hs i h4 with h5 | h5 | h5 <;> contradiction
open Module in
theorem fin_two_site : ∀ r : ℕ, r < 3 → ∀ a b : ZMod 2,
    a * (if r = 0 ∨ r = 2 then 1 else 0) + b * (if (r+1)%3 = 0 ∨ (r+1)%3 = 2 then 1 else 0) = 0 →
    a * (if r = 1 ∨ r = 2 then 1 else 0) + b * (if (r+1)%3 = 1 ∨ (r+1)%3 = 2 then 1 else 0) = 0 →
    a = 0 ∧ b = 0 := by
  intro r hr
  interval_cases r <;> decide
open Module in
theorem two_site (t : ℕ) (ht : 1 ≤ t) (x : Fin (3*t) → ZMod 2) (hx : inC x) (u : Fin (3*t))
    (hs : ∀ i, x i ≠ 0 → i = u ∨ i = nx u) : x u = 0 ∧ x (nx u) = 0 := by
  have hne : u ≠ nx u := by
    intro h; have := congrArg Fin.val h; rcases nxv u with ⟨_, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hxe := eq2 x u (nx u) hne hs
  obtain ⟨h0, h1⟩ := hx
  rw [hxe, BB_x2] at h0 h1
  have hu : u.val % 3 = u.val % 3 := rfl
  have hnu : (nx u).val % 3 = (u.val % 3 + 1) % 3 := res_nx u
  rw [cv_val 0 u _ hu, cv_val 0 (nx u) _ hnu] at h0
  rw [cv_val 1 u _ hu, cv_val 1 (nx u) _ hnu] at h1
  exact fin_two_site (u.val % 3) (Nat.mod_lt _ (by norm_num)) _ _ h0 h1
open Module in
theorem ne_of_val {m : ℕ} {a b : Fin m} (h : a.val ≠ b.val) : a ≠ b := fun h' => h (congrArg Fin.val h')
open Module in
theorem two_supp (t : ℕ) (ht : 3 ≤ t) (x : Fin (3*t) → ZMod 2) (hx : inC x) (hx0 : x ≠ 0) :
    ∃ α β, x α ≠ 0 ∧ x β ≠ 0 ∧ Far α β := by
  obtain ⟨α, hα⟩ : ∃ α, x α ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  by_cases h : ∃ β, x β ≠ 0 ∧ Far α β
  · obtain ⟨β, hβ, hf⟩ := h
    exact ⟨α, β, hα, hβ, hf⟩
  · have h' : ∀ β, x β ≠ 0 → β = α ∨ β = nx α ∨ β = pv α := by
      intro β hβ
      by_contra hc
      push_neg at hc
      exact h ⟨β, hβ, hc.1, hc.2.1, hc.2.2⟩
    have a1 := α.isLt
    have A1 := nxv α
    have A2 := pvv α
    by_cases h2 : x (nx α) ≠ 0 ∧ x (pv α) ≠ 0
    · refine ⟨pv α, nx α, h2.2, h2.1, ?_, ?_, ?_⟩
      · apply ne_of_val; omega
      · rw [nx_pv]; apply ne_of_val; omega
      · have A3 := pvv (pv α)
        apply ne_of_val; omega
    · exfalso
      rw [not_and_or, not_not, not_not] at h2
      rcases h2 with h2 | h2
      · have := two_site t (by omega) x hx (pv α) (fun i hi => by
          rcases h' i hi with h3 | h3 | h3
          · right; rw [nx_pv]; exact h3
          · subst h3; exact absurd h2 hi
          · left; exact h3)
        rw [nx_pv] at this
        exact hα this.2
      · have := two_site t (by omega) x hx α (fun i hi => by
          rcases h' i hi with h3 | h3 | h3
          · left; exact h3
          · right; exact h3
          · subst h3; exact absurd h2 hi)
        exact hα this.1
open Module in
theorem S4_sub (t : ℕ) (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) (hα : x α ≠ 0) (hβ : x β ≠ 0) :
    S4 α β ⊆ Ns x := by
  intro i hi
  simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hi
  rw [mem_Ns]
  rcases hi with rfl | rfl | rfl | rfl
  · right; rw [nx_pv]; exact hα
  · left; exact hα
  · right; rw [nx_pv]; exact hβ
  · left; exact hβ
open Module in
theorem S4_card (t : ℕ) (ht : 3 ≤ t) (α β : Fin (3*t)) (hf : Far α β) : (S4 α β).card = 4 := by
  obtain ⟨f1, f2, f3⟩ := hf
  have g1 : β.val ≠ α.val := fun h => f1 (Fin.ext h)
  have g2 : β.val ≠ (nx α).val := fun h => f2 (Fin.ext h)
  have g3 : β.val ≠ (pv α).val := fun h => f3 (Fin.ext h)
  have a1 := α.isLt
  have a2 := β.isLt
  have A1 := nxv α
  have A2 := pvv α
  have B2 := pvv β
  rw [S4, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair_eq_two_iff.mpr]
  · apply ne_of_val; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_⟩ <;> apply ne_of_val <;> omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> apply ne_of_val <;> omega
open Module in
theorem five_distinct (t : ℕ) (ht : 3 ≤ t) (i : Fin (3*t)) :
    pv (pv i) ≠ pv i ∧ pv (pv i) ≠ i ∧ pv (pv i) ≠ nx i ∧ pv (pv i) ≠ nx (nx i) ∧
    pv i ≠ i ∧ pv i ≠ nx i ∧ pv i ≠ nx (nx i) ∧ i ≠ nx i ∧ i ≠ nx (nx i) ∧ nx i ≠ nx (nx i) := by
  have a := i.isLt
  have A1 := nxv i
  have A2 := pvv i
  have A3 := nxv (nx i)
  have A4 := pvv (pv i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply ne_of_val <;> omega
open Module in
theorem fin_B : ∀ r : ℕ, r < 3 → ∀ a : ZMod 2,
    1 * (if r = 0 ∨ r = 2 then 1 else 0) + a * (if (r+1)%3 = 0 ∨ (r+1)%3 = 2 then 1 else 0) +
      1 * (if (r+2)%3 = 0 ∨ (r+2)%3 = 2 then 1 else 0) = 0 →
    1 * (if r = 1 ∨ r = 2 then 1 else 0) + a * (if (r+1)%3 = 1 ∨ (r+1)%3 = 2 then 1 else 0) +
      1 * (if (r+2)%3 = 1 ∨ (r+2)%3 = 2 then 1 else 0) = 0 →
    a = 1 := by
  intro r hr
  interval_cases r <;> decide
open Module in
theorem fin_A : ∀ r s : ℕ, r < 3 → s < 3 →
    1 * (if r = 0 ∨ r = 2 then 1 else 0) + 1 * (if s = 0 ∨ s = 2 then (1 : ZMod 2) else 0) = 0 →
    1 * (if r = 1 ∨ r = 2 then 1 else 0) + 1 * (if s = 1 ∨ s = 2 then (1 : ZMod 2) else 0) = 0 →
    r = s := by
  intro r s hr hs
  interval_cases r <;> interval_cases s <;> decide
open Module in
theorem formB1 (t : ℕ) (x : Fin (3*t) → ZMod 2) (hx : inC x) (α β : Fin (3*t))
    (hα1 : x α = 1) (hβ1 : x β = 1) (hB1 : β = nx (nx α)) (hd1 : α ≠ nx α) (hd2 : α ≠ β)
    (hd3 : nx α ≠ β) (hs3 : ∀ i, x i ≠ 0 → i = α ∨ i = nx α ∨ i = β) :
    x = Pi.single α 1 + Pi.single (nx α) 1 + Pi.single β 1 := by
  have hxe := eq3 x α (nx α) β hd1 hd2 hd3 hs3
  obtain ⟨h0, h1⟩ := hx
  rw [hxe, BB_x3] at h0 h1
  have r1 : (nx α).val % 3 = (α.val % 3 + 1) % 3 := res_nx α
  have r2 : β.val % 3 = (α.val % 3 + 2) % 3 := by rw [hB1, res_nx, res_nx]; omega
  rw [cv_val 0 α _ rfl, cv_val 0 (nx α) _ r1, cv_val 0 β _ r2, hα1, hβ1] at h0
  rw [cv_val 1 α _ rfl, cv_val 1 (nx α) _ r1, cv_val 1 β _ r2, hα1, hβ1] at h1
  have hm1 := fin_B (α.val % 3) (Nat.mod_lt _ (by norm_num)) _ h0 h1
  rw [hxe, hα1, hβ1, hm1]
  simp
open Module in
theorem formA (t : ℕ) (x : Fin (3*t) → ZMod 2) (hx : inC x) (α β : Fin (3*t))
    (hα1 : x α = 1) (hβ1 : x β = 1) (hne : α ≠ β) (hs2 : ∀ i, x i ≠ 0 → i = α ∨ i = β) :
    α.val % 3 = β.val % 3 ∧ x = Pi.single α 1 + Pi.single β 1 := by
  have hxe := eq2 x α β hne hs2
  obtain ⟨h0, h1⟩ := hx
  rw [hxe, BB_x2] at h0 h1
  rw [cv_val 0 α _ rfl, cv_val 0 β _ rfl, hα1, hβ1] at h0
  rw [cv_val 1 α _ rfl, cv_val 1 β _ rfl, hα1, hβ1] at h1
  refine ⟨fin_A _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h0 h1, ?_⟩
  rw [hxe, hα1, hβ1]
  simp
open Module in
theorem form_of (t : ℕ) (ht : 3 ≤ t) (x : Fin (3*t) → ZMod 2) (hx : inC x) (α β : Fin (3*t))
    (hα : x α ≠ 0) (hβ : x β ≠ 0) (hf : Far α β) (hN : Ns x ⊆ S4 α β) : Form x α β := by
  have hsup : ∀ i, x i ≠ 0 → i ∈ S4 α β ∧ pv i ∈ S4 α β := by
    intro i hi
    exact ⟨hN ((mem_Ns x i).mpr (Or.inl hi)),
      hN ((mem_Ns x (pv i)).mpr (Or.inr (by rw [nx_pv]; exact hi)))⟩
  have memS : ∀ i, i ∈ S4 α β ↔ (i = pv α ∨ i = α ∨ i = pv β ∨ i = β) := by
    intro i
    simp [S4]
  have hα1 := zmod2_ne hα
  have hβ1 := zmod2_ne hβ
  obtain ⟨f1, f2, f3⟩ := hf
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := five_distinct t ht α
  by_cases hB1 : β = nx (nx α)
  · have hpb : pv β = nx α := by rw [hB1, pv_nx]
    have hpa : x (pv α) = 0 := by
      by_contra h
      rcases (memS _).mp (hsup (pv α) h).2 with h' | h' | h' | h'
      · exact d1 h'
      · exact d2 h'
      · exact d3 (h'.trans hpb)
      · exact d4 (h'.trans hB1)
    right; left
    refine ⟨hB1, formB1 t x hx α β hα1 hβ1 hB1 d8 (hB1 ▸ d9) (hB1 ▸ d10) ?_⟩
    intro i hi
    rcases (memS i).mp (hsup i hi).1 with h' | h' | h' | h'
    · exact absurd (by rw [h']; exact hpa) hi
    · left; exact h'
    · right; left; exact h'.trans hpb
    · right; right; exact h'
  · by_cases hB2 : α = nx (nx β)
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := five_distinct t ht β
      have hpa : pv α = nx β := by rw [hB2, pv_nx]
      have hpb : x (pv β) = 0 := by
        by_contra h
        rcases (memS _).mp (hsup (pv β) h).2 with h' | h' | h' | h'
        · exact e3 (h'.trans hpa)
        · exact e4 (h'.trans hB2)
        · exact e1 h'
        · exact e2 h'
      right; right
      refine ⟨hB2, formB1 t x hx β α hβ1 hα1 hB2 e8 (hB2 ▸ e9) (hB2 ▸ e10) ?_⟩
      intro i hi
      rcases (memS i).mp (hsup i hi).1 with h' | h' | h' | h'
      · right; left; exact h'.trans hpa
      · right; right; exact h'
      · exact absurd (by rw [h']; exact hpb) hi
      · left; exact h'
    · have hpa : x (pv α) = 0 := by
        by_contra h
        rcases (memS _).mp (hsup (pv α) h).2 with h' | h' | h' | h'
        · exact d1 h'
        · exact d2 h'
        · apply f3
          have := congrArg nx h'
          rw [nx_pv, nx_pv] at this
          exact this.symm
        · apply hB2
          rw [← h', nx_pv, nx_pv]
      have hpb : x (pv β) = 0 := by
        by_contra h
        rcases (memS _).mp (hsup (pv β) h).2 with h' | h' | h' | h'
        · apply f2
          have := congrArg nx h'
          rw [nx_pv, nx_pv] at this
          rw [← this, nx_pv]
        · apply hB1
          rw [← h', nx_pv, nx_pv]
        · exact (five_distinct t ht β).1 h'
        · exact (five_distinct t ht β).2.1 h'
      left
      exact formA t x hx α β hα1 hβ1 (Ne.symm f1) (fun i hi => by
        rcases (memS i).mp (hsup i hi).1 with h' | h' | h' | h'
        · exact absurd (by rw [h']; exact hpa) hi
        · left; exact h'
        · exact absurd (by rw [h']; exact hpb) hi
        · right; exact h')
open Module in
theorem part1 (t : ℕ) (ht : 3 ≤ t) (Q : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (hQ : ∀ y ∈ Q, inC y) (hdim : 3*t - 4 ≤ finrank (ZMod 2) Q) (x : Fin (3*t) → ZMod 2)
    (hx : inC x) (hx0 : x ≠ 0) :
    finrank (ZMod 2) (Q ⊓ kl (Ns x) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) + 2 ≤
      finrank (ZMod 2) Q := by
  obtain ⟨α, β, hα, hβ, hf⟩ := two_supp t ht x hx hx0
  have hc := S4_card t ht α β hf
  have h1 := key t ht Q hQ (S4 α β) (by omega)
  have h2 : finrank (ZMod 2) (Q ⊓ kl (Ns x) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) ≤
      finrank (ZMod 2) (Q ⊓ kl (S4 α β) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) :=
    Submodule.finrank_mono (inf_le_inf_left _ (kl_anti _ _ (S4_sub t x α β hα hβ)))
  omega
open Module in
theorem edata (t : ℕ) (ht : 3 ≤ t) (Q : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (hQ : ∀ y ∈ Q, inC y) (hdim : 3*t - 4 ≤ finrank (ZMod 2) Q) (x : Fin (3*t) → ZMod 2)
    (hx : inC x) (hx0 : x ≠ 0)
    (heq : finrank (ZMod 2) (Q ⊓ kl (Ns x) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) + 2 =
      finrank (ZMod 2) Q) :
    ∃ α β, Far α β ∧ Ns x = S4 α β ∧ Form x α β ∧
      (BB (3*t)).orthogonal Q ≤ ZZ (3*t) ⊔ sp (S4 α β) ∧
      finrank (ZMod 2) ((BB (3*t)).orthogonal Q) = 4 := by
  obtain ⟨α, β, hα, hβ, hf⟩ := two_supp t ht x hx hx0
  have hc4 := S4_card t ht α β hf
  have hsub := S4_sub t x α β hα hβ
  have hN : Ns x ⊆ S4 α β := by
    intro γ hγ
    by_contra hγ'
    have hc5 : (insert γ (S4 α β)).card = 5 := by rw [Finset.card_insert_of_notMem hγ', hc4]
    have h1 := key t ht Q hQ (insert γ (S4 α β)) (by omega)
    have h2 : finrank (ZMod 2) (Q ⊓ kl (Ns x) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) ≤
        finrank (ZMod 2) (Q ⊓ kl (insert γ (S4 α β)) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) :=
      Submodule.finrank_mono (inf_le_inf_left _ (kl_anti _ _ (Finset.insert_subset hγ hsub)))
    omega
  have hNe : Ns x = S4 α β := Finset.Subset.antisymm hN hsub
  refine ⟨α, β, hf, hNe, form_of t ht x hx α β hα hβ hf hN, ?_⟩
  rw [hNe] at heq
  have h1 := finrank_kl Q (S4 α β)
  have h2 := finrank_orth (3*t) Q
  have h3 := fzs t ht (S4 α β) (by omega)
  rw [hc4] at h3
  have h4 : ZZ (3*t) ⊔ sp (S4 α β) ≤ (BB (3*t)).orthogonal Q ⊔ sp (S4 α β) :=
    sup_le_sup_right (ZZ_le t Q hQ) _
  have h5 := Submodule.finrank_mono h4
  have hR4 : finrank (ZMod 2) ((BB (3*t)).orthogonal Q) = 4 := by omega
  have heq2 : ZZ (3*t) ⊔ sp (S4 α β) = (BB (3*t)).orthogonal Q ⊔ sp (S4 α β) :=
    Submodule.eq_of_le_of_finrank_le h4 (by omega)
  refine ⟨?_, hR4⟩
  rw [heq2]
  exact le_sup_left
open Module in
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide
open Module in
theorem zmod2_eq_of_add (a b : ZMod 2) (h : a + b = 0) : a = b := by
  revert a b; decide
open Module in
theorem cv0_mem (m : ℕ) : cv 0 ∈ ZZ m := Submodule.subset_span ⟨0, rfl⟩
open Module in
theorem cv1_mem (m : ℕ) : cv 1 ∈ ZZ m := Submodule.subset_span ⟨1, rfl⟩
open Module in
theorem pair_lem {m : ℕ} (Z R : Submodule (ZMod 2) (Fin m → ZMod 2)) (S S' : Finset (Fin m))
    (h1 : R ≤ Z ⊔ sp S) (h2 : R ≤ Z ⊔ sp S') (hc : ∀ z ∈ Z, z ∈ sp (S ∪ S') → z = 0) :
    R ≤ Z ⊔ sp (S ∩ S') := by
  intro r hr
  obtain ⟨z, hz, f, hf, rfl⟩ := Submodule.mem_sup.mp (h1 hr)
  obtain ⟨z', hz', f', hf', he⟩ := Submodule.mem_sup.mp (h2 hr)
  have hzz' : z + z' ∈ sp (S ∪ S') := by
    rw [mem_sp]
    intro i hi
    rw [Finset.mem_union, not_or] at hi
    have e1 := congrFun he i
    have a1 := hf i hi.1
    have a2 := hf' i hi.2
    simp only [Pi.add_apply] at e1 ⊢
    rw [a1, a2, add_zero, add_zero] at e1
    rw [e1]
    exact zmod2_add_self _
  have h0 := hc _ (Z.add_mem hz hz') hzz'
  have hzeq : z' = z := by
    funext i
    exact (zmod2_eq_of_add _ _ (congrFun h0 i)).symm
  rw [hzeq] at he
  have hfeq : f' = f := add_left_cancel he
  refine Submodule.mem_sup.mpr ⟨z, hz, f, ?_, rfl⟩
  rw [mem_sp]
  intro i hi
  rw [Finset.mem_inter, not_and_or] at hi
  rcases hi with hi | hi
  · exact hf i hi
  · rw [← hfeq]; exact hf' i hi
open Module in
theorem adj_lem (t : ℕ) (R : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) (K : Finset (Fin (3*t)))
    (p : Fin (3*t)) (h : R ≤ ZZ (3*t) ⊔ sp K) (hK : K ⊆ {p, nx p})
    (hR : finrank (ZMod 2) R = 4) :
    (Pi.single p 1 : Fin (3*t) → ZMod 2) ∈ R ∧ (Pi.single (nx p) 1 : Fin (3*t) → ZMod 2) ∈ R := by
  have h1 : R ≤ ZZ (3*t) ⊔ sp {p, nx p} := h.trans (sup_le_sup_left (sp_mono _ _ hK) _)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (ZZ (3*t)) (sp {p, nx p})
  have h3 : finrank (ZMod 2) (ZZ (3*t)) ≤ 2 := by
    have := finrank_span_le_card (R := ZMod 2) (Set.range ![cv 0, cv 1] : Set (Fin (3*t) → ZMod 2))
    refine this.trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have h4 : finrank (ZMod 2) (sp ({p, nx p} : Finset (Fin (3*t)))) ≤ 2 := by
    rw [finrank_sp]; exact Finset.card_le_two
  have h5 : R = ZZ (3*t) ⊔ sp {p, nx p} := Submodule.eq_of_le_of_finrank_le h1 (by omega)
  rw [h5]
  exact ⟨Submodule.mem_sup_right (single_mem_sp _ _ (by simp)),
    Submodule.mem_sup_right (single_mem_sp _ _ (by simp))⟩
open Module in
theorem disj_lem (t : ℕ) (ht : 3 ≤ t) (R : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (S S' : Finset (Fin (3*t))) (h1 : R ≤ ZZ (3*t) ⊔ sp S) (h2 : R ≤ ZZ (3*t) ⊔ sp S')
    (hS : S.card = 4) (hS' : S'.card = 4) (hR : finrank (ZMod 2) R = 4) (hZ : ZZ (3*t) ≤ R)
    (hd : S ∩ S' = ∅) : False := by
  have k1 : 2 ≤ finrank (ZMod 2) (R ⊓ sp S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) := by
    have e := Submodule.finrank_sup_add_finrank_inf_eq R (sp S)
    have e2 : finrank (ZMod 2) (R ⊔ sp S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) ≤
        finrank (ZMod 2) (ZZ (3*t) ⊔ sp S : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) :=
      Submodule.finrank_mono (sup_le h1 le_sup_right)
    have e3 := fzs t ht S (by omega)
    rw [finrank_sp, hS, hR] at e
    omega
  have k2 : 2 ≤ finrank (ZMod 2) (R ⊓ sp S' : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) := by
    have e := Submodule.finrank_sup_add_finrank_inf_eq R (sp S')
    have e2 : finrank (ZMod 2) (R ⊔ sp S' : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) ≤
        finrank (ZMod 2) (ZZ (3*t) ⊔ sp S' : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) :=
      Submodule.finrank_mono (sup_le h2 le_sup_right)
    have e3 := fzs t ht S' (by omega)
    rw [finrank_sp, hS', hR] at e
    omega
  have hbot : (R ⊓ sp S) ⊓ (R ⊓ sp S') = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hw1 := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hw).1).2
    have hw2 := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hw).2).2
    funext i
    by_cases hi : i ∈ S
    · have : i ∉ S' := by
        intro h
        have := Finset.mem_inter.mpr ⟨hi, h⟩
        rw [hd] at this
        simp at this
      exact hw2 i this
    · exact hw1 i hi
  have e := Submodule.finrank_sup_add_finrank_inf_eq (R ⊓ sp S) (R ⊓ sp S')
  rw [hbot, finrank_bot] at e
  have hle : (R ⊓ sp S) ⊔ (R ⊓ sp S') ≤ R := sup_le inf_le_left inf_le_left
  have heq : (R ⊓ sp S) ⊔ (R ⊓ sp S') = R := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hsub : R ≤ sp (S ∪ S') := by
    rw [← heq]
    exact sup_le (inf_le_right.trans (sp_mono _ _ Finset.subset_union_left))
      (inf_le_right.trans (sp_mono _ _ Finset.subset_union_right))
  have hc0 := hsub (hZ (cv0_mem _))
  have hc1 := hsub (hZ (cv1_mem _))
  have hall : ∀ i, i ∈ S ∪ S' := by
    intro i
    by_contra hi
    have a := hc0 i hi
    have b := hc1 i hi
    simp only [cv] at a b
    split_ifs at a b with h5 h6 <;> first | exact absurd a one_ne_zero | exact absurd b one_ne_zero | omega
  have c1 : (Finset.univ : Finset (Fin (3*t))).card ≤ (S ∪ S').card :=
    Finset.card_le_card (fun i _ => hall i)
  have c2 := Finset.card_union_le S S'
  simp only [Finset.card_univ, Fintype.card_fin] at c1
  omega
open Module in
theorem card_le_three (α : Type) [Finite α] (h : ∀ f : Fin 4 → α, ¬ Function.Injective f) :
    Nat.card α ≤ 3 := by
  by_contra hc
  push_neg at hc
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨f⟩ := Function.Embedding.nonempty_iff_card_le.mpr
    (show Fintype.card (Fin 4) ≤ Fintype.card α by simp; omega)
  exact h f f.injective
open Module in
def Val {t : ℕ} (u v : Fin (3*t)) : Prop := u.val % 3 = v.val % 3 ∨ v = nx (nx u) ∨ u = nx (nx v)
open Module in
def ED {t : ℕ} (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) : Prop :=
  Far α β ∧ Ns x = S4 α β ∧ Form x α β
open Module in
theorem val_of_form {t : ℕ} (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) (h : Form x α β) :
    Val α β := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · left; exact h
  · right; left; exact h
  · right; right; exact h
open Module in
theorem val_symm {t : ℕ} (u v : Fin (3*t)) (h : Val u v) : Val v u := by
  rcases h with h | h | h
  · left; exact h.symm
  · right; right; exact h
  · right; left; exact h
open Module in
theorem S4_comm {t : ℕ} (α β : Fin (3*t)) : S4 α β = S4 β α := by
  ext i
  simp only [S4, Finset.mem_insert, Finset.mem_singleton]
  tauto
open Module in
theorem mem_S4 {t : ℕ} (α β i : Fin (3*t)) : i ∈ S4 α β ↔ (i = pv α ∨ i = α ∨ i = pv β ∨ i = β) := by
  simp [S4]
open Module in
theorem supp_char (t : ℕ) (ht : 3 ≤ t) (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t))
    (h : ED x α β) (i : Fin (3*t)) : x i ≠ 0 ↔ (i ∈ Ns x ∧ pv i ∈ Ns x) := by
  obtain ⟨hf, hN, hF⟩ := h
  constructor
  · intro hi
    exact ⟨(mem_Ns x i).mpr (Or.inl hi), (mem_Ns x (pv i)).mpr (Or.inr (by rw [nx_pv]; exact hi))⟩
  · rintro ⟨h1, h2⟩
    rw [hN] at h1 h2
    obtain ⟨f1, f2, f3⟩ := hf
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := five_distinct t ht α
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := five_distinct t ht β
    rcases hF with ⟨hr, hx⟩ | ⟨hB, hx⟩ | ⟨hB, hx⟩
    · have hi : i = α ∨ i = β := by
        rcases (mem_S4 α β i).mp h1 with h | h | h | h
        · exfalso
          subst h
          rcases (mem_S4 α β _).mp h2 with h' | h' | h' | h'
          · exact d1 h'
          · exact d2 h'
          · apply f3
            have := congrArg nx h'
            rw [nx_pv, nx_pv] at this
            exact this.symm
          · have hα : α = nx (nx β) := by rw [← h', nx_pv, nx_pv]
            have r1 := res_nx β
            have r2 := res_nx (nx β)
            rw [← hα] at r2
            omega
        · left; exact h
        · exfalso
          subst h
          rcases (mem_S4 α β _).mp h2 with h' | h' | h' | h'
          · apply f2
            have := congrArg nx h'
            rw [nx_pv, nx_pv] at this
            rw [← this, nx_pv]
          · have hβ : β = nx (nx α) := by rw [← h', nx_pv, nx_pv]
            have r1 := res_nx α
            have r2 := res_nx (nx α)
            rw [← hβ] at r2
            omega
          · exact e1 h'
          · exact e2 h'
        · right; exact h
      rw [hx]
      rcases hi with rfl | rfl
      · simp [Pi.single_apply, Ne.symm f1]
      · simp [Pi.single_apply, f1]
    · have hpb : pv β = nx α := by rw [hB, pv_nx]
      have hi : i = α ∨ i = nx α ∨ i = β := by
        rcases (mem_S4 α β i).mp h1 with h | h | h | h
        · exfalso
          subst h
          rcases (mem_S4 α β _).mp h2 with h' | h' | h' | h'
          · exact d1 h'
          · exact d2 h'
          · exact d3 (h'.trans hpb)
          · exact d4 (h'.trans hB)
        · left; exact h
        · right; left; exact h.trans hpb
        · right; right; exact h
      rw [hx, hB]
      rcases hi with rfl | rfl | rfl
      · simp [Pi.single_apply, d8, d9]
      · simp [Pi.single_apply, Ne.symm d8, d10]
      · rw [hB]
        simp [Pi.single_apply, Ne.symm d9, Ne.symm d10]
    · have hpa : pv α = nx β := by rw [hB, pv_nx]
      have hi : i = β ∨ i = nx β ∨ i = α := by
        rcases (mem_S4 α β i).mp h1 with h | h | h | h
        · right; left; exact h.trans hpa
        · right; right; exact h
        · exfalso
          subst h
          rcases (mem_S4 α β _).mp h2 with h' | h' | h' | h'
          · exact e3 (h'.trans hpa)
          · exact e4 (h'.trans hB)
          · exact e1 h'
          · exact e2 h'
        · left; exact h
      rw [hx, hB]
      rcases hi with rfl | rfl | rfl
      · simp [Pi.single_apply, e8, e9]
      · simp [Pi.single_apply, Ne.symm e8, e10]
      · rw [hB]
        simp [Pi.single_apply, Ne.symm e9, Ne.symm e10]
open Module in
theorem inj_data (t : ℕ) (ht : 3 ≤ t) (x x' : Fin (3*t) → ZMod 2) (α β α' β' : Fin (3*t))
    (h : ED x α β) (h' : ED x' α' β') (hN : Ns x = Ns x') : x = x' := by
  funext i
  have h1 := supp_char t ht x α β h i
  have h2 := supp_char t ht x' α' β' h' i
  rw [hN] at h1
  rcases zmod2_cases (x i) with ha | ha <;> rcases zmod2_cases (x' i) with hb | hb
  · rw [ha, hb]
  · exfalso
    have := h2.mp (by rw [hb]; exact one_ne_zero)
    exact h1.mpr this ha
  · exfalso
    have := h1.mp (by rw [ha]; exact one_ne_zero)
    exact h2.mpr this hb
  · rw [ha, hb]
open Module in
theorem combo (t : ℕ) (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) (h : ED x α β)
    (a b : Fin (3*t)) (hab : Far a b) (ha : a ∈ Ns x) (hb : b ∈ Ns x) :
    ∃ u v, (u = a ∨ u = nx a) ∧ (v = b ∨ v = nx b) ∧ Ns x = S4 u v ∧ Val u v := by
  obtain ⟨_, hN, hF⟩ := h
  rw [hN] at ha hb
  have hV := val_of_form x α β hF
  obtain ⟨g1, g2, g3⟩ := hab
  rcases (mem_S4 α β a).mp ha with h | h | h | h
  · refine ⟨α, β, Or.inr (by rw [h, nx_pv]), ?_, hN, hV⟩
    rcases (mem_S4 α β b).mp hb with h' | h' | h' | h'
    · exact absurd (h'.trans h.symm) g1
    · exfalso; apply g2; rw [h', h, nx_pv]
    · right; rw [h', nx_pv]
    · left; exact h'.symm
  · refine ⟨α, β, Or.inl h.symm, ?_, hN, hV⟩
    rcases (mem_S4 α β b).mp hb with h' | h' | h' | h'
    · exfalso; apply g3; rw [h', h]
    · exact absurd (h'.trans h.symm) g1
    · right; rw [h', nx_pv]
    · left; exact h'.symm
  · refine ⟨β, α, Or.inr (by rw [h, nx_pv]), ?_, by rw [hN, S4_comm], val_symm _ _ hV⟩
    rcases (mem_S4 α β b).mp hb with h' | h' | h' | h'
    · right; rw [h', nx_pv]
    · left; exact h'.symm
    · exact absurd (h'.trans h.symm) g1
    · exfalso; apply g2; rw [h', h, nx_pv]
  · refine ⟨β, α, Or.inl h.symm, ?_, by rw [hN, S4_comm], val_symm _ _ hV⟩
    rcases (mem_S4 α β b).mp hb with h' | h' | h' | h'
    · right; rw [h', nx_pv]
    · left; exact h'.symm
    · exfalso; apply g3; rw [h', h]
    · exact absurd (h'.trans h.symm) g1
open Module in
theorem val_d (t : ℕ) (ht : 3 ≤ t) (u v : Fin (3*t)) (e : ℕ) (he : e < 3*t)
    (hv : v.val = u.val + e ∨ v.val + 3*t = u.val + e) (hV : Val u v) :
    e % 3 = 0 ∨ e = 2 ∨ e = 3*t - 2 := by
  have gu := u.isLt
  have gv := v.isLt
  rcases hV with h | h | h
  · left; omega
  · right; left
    have h1 := congrArg Fin.val h
    have A1 := nxv u
    have A2 := nxv (nx u)
    omega
  · right; right
    have h1 := congrArg Fin.val h
    have B1 := nxv v
    have B2 := nxv (nx v)
    omega
open Module in
theorem four_val (t : ℕ) (ht : 3 ≤ t) (a b : Fin (3*t)) (hab : Far a b) (h1 : Val a b)
    (h2 : Val (nx a) b) (h3 : Val a (nx b)) : False := by
  obtain ⟨g1, g2, g3⟩ := hab
  have ga := a.isLt
  have gb := b.isLt
  have v1 : b.val ≠ a.val := fun h => g1 (Fin.ext h)
  have v2 : b.val ≠ (nx a).val := fun h => g2 (Fin.ext h)
  have v3 : b.val ≠ (pv a).val := fun h => g3 (Fin.ext h)
  have A1 := nxv a
  have A2 := pvv a
  have B1 := nxv b
  obtain ⟨d, hd, hdv⟩ : ∃ d, d < 3*t ∧ (b.val = a.val + d ∨ b.val + 3*t = a.val + d) := by
    by_cases h : a.val ≤ b.val
    · exact ⟨b.val - a.val, by omega, Or.inl (by omega)⟩
    · exact ⟨b.val + 3*t - a.val, by omega, Or.inr (by omega)⟩
  have hd2 : 2 ≤ d ∧ d ≤ 3*t - 2 := by omega
  have k1 := val_d t ht a b d hd hdv h1
  have k2 := val_d t ht (nx a) b (d - 1) (by omega) (by omega) h2
  have k3 := val_d t ht a (nx b) (d + 1) (by omega) (by omega) h3
  omega
open Module in
theorem four_combos {α : Type} (a a' b b' : α) (ha : a ≠ a') (hb : b ≠ b') (u v : Fin 4 → α)
    (hu : ∀ i, u i = a ∨ u i = a') (hv : ∀ i, v i = b ∨ v i = b')
    (hd : ∀ i j, u i = u j → v i = v j → i = j) :
    (∃ i, u i = a ∧ v i = b) ∧ (∃ i, u i = a' ∧ v i = b) ∧ (∃ i, u i = a ∧ v i = b') := by
  classical
  let f : Fin 4 → Bool × Bool := fun i => (decide (u i = a'), decide (v i = b'))
  have hinj : Function.Injective f := by
    intro i j hij
    simp only [f, Prod.mk.injEq] at hij
    obtain ⟨hij1, hij2⟩ := hij
    apply hd
    · rcases hu i with h1 | h1 <;> rcases hu j with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2] at hij1; simp [ha] at hij1
      · rw [h1, h2] at hij1; simp [ha] at hij1
      · rw [h1, h2]
    · rcases hv i with h1 | h1 <;> rcases hv j with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2] at hij2; simp [hb] at hij2
      · rw [h1, h2] at hij2; simp [hb] at hij2
      · rw [h1, h2]
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp⟩).2
  have key : ∀ c1 c2 : Bool, ∃ i, (u i = a' ↔ c1 = true) ∧ (v i = b' ↔ c2 = true) := by
    intro c1 c2
    obtain ⟨i, hi⟩ := hsurj (c1, c2)
    simp only [f, Prod.mk.injEq] at hi
    refine ⟨i, ?_, ?_⟩
    · rw [← hi.1]; simp
    · rw [← hi.2]; simp
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, h1, h2⟩ := key false false
    refine ⟨i, ?_, ?_⟩
    · rcases hu i with h | h
      · exact h
      · exact absurd (h1.mp h) (by simp)
    · rcases hv i with h | h
      · exact h
      · exact absurd (h2.mp h) (by simp)
  · obtain ⟨i, h1, h2⟩ := key true false
    refine ⟨i, h1.mpr rfl, ?_⟩
    rcases hv i with h | h
    · exact h
    · exact absurd (h2.mp h) (by simp)
  · obtain ⟨i, h1, h2⟩ := key false true
    refine ⟨i, ?_, h2.mpr rfl⟩
    rcases hu i with h | h
    · exact h
    · exact absurd (h1.mp h) (by simp)
open Module in
theorem count_lem (t : ℕ) (ht : 3 ≤ t) (a b : Fin (3*t)) (hab : Far a b)
    (x : Fin 4 → (Fin (3*t) → ZMod 2)) (hinj : Function.Injective x)
    (hED : ∀ i, ∃ α β, ED (x i) α β) (hmem : ∀ i, a ∈ Ns (x i) ∧ b ∈ Ns (x i)) : False := by
  have hc : ∀ i, ∃ u v, (u = a ∨ u = nx a) ∧ (v = b ∨ v = nx b) ∧ Ns (x i) = S4 u v ∧ Val u v := by
    intro i
    obtain ⟨α, β, h⟩ := hED i
    exact combo t (x i) α β h a b hab (hmem i).1 (hmem i).2
  choose u v hu hv hN hV using hc
  have hd : ∀ i j, u i = u j → v i = v j → i = j := by
    intro i j h1 h2
    apply hinj
    obtain ⟨α, β, hi⟩ := hED i
    obtain ⟨α', β', hj⟩ := hED j
    exact inj_data t ht (x i) (x j) α β α' β' hi hj (by rw [hN i, hN j, h1, h2])
  have hne1 : a ≠ nx a := (five_distinct t ht a).2.2.2.2.2.2.2.1
  have hne2 : b ≠ nx b := (five_distinct t ht b).2.2.2.2.2.2.2.1
  obtain ⟨⟨i1, h11, h12⟩, ⟨i2, h21, h22⟩, ⟨i3, h31, h32⟩⟩ :=
    four_combos a (nx a) b (nx b) hne1 hne2 u v hu hv hd
  have k1 := hV i1
  rw [h11, h12] at k1
  have k2 := hV i2
  rw [h21, h22] at k2
  have k3 := hV i3
  rw [h31, h32] at k3
  exact four_val t ht a b hab k1 k2 k3
open Module in
theorem Kapp (t : ℕ) (ht : 4 ≤ t) (R : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) (hZ : ZZ (3*t) ≤ R)
    (hR : finrank (ZMod 2) R = 4) (S0 : Finset (Fin (3*t))) (hS0 : S0.card = 4)
    (h0 : R ≤ ZZ (3*t) ⊔ sp S0)
    (hnadj : ∀ p, ¬ ((Pi.single p 1 : Fin (3*t) → ZMod 2) ∈ R ∧
      (Pi.single (nx p) 1 : Fin (3*t) → ZMod 2) ∈ R)) :
    ∃ a b, Far a b ∧ ∀ S : Finset (Fin (3*t)), S.card = 4 → R ≤ ZZ (3*t) ⊔ sp S → a ∈ S ∧ b ∈ S := by
  classical
  obtain ⟨K, hKm⟩ : ∃ K : Finset (Fin (3*t)), ∀ i, i ∈ K ↔ ∃ v ∈ R ⊓ sp S0, v i ≠ 0 :=
    ⟨Finset.univ.filter (fun i => ∃ v ∈ R ⊓ sp S0, v i ≠ 0),
      fun i => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hK1 : R ≤ ZZ (3*t) ⊔ sp K := by
    intro r hr
    obtain ⟨z, hz, f, hf, rfl⟩ := Submodule.mem_sup.mp (h0 hr)
    have hfR : f ∈ R := by
      have := R.sub_mem hr (hZ hz)
      simpa using this
    refine Submodule.mem_sup.mpr ⟨z, hz, f, ?_, rfl⟩
    rw [mem_sp]
    intro i hi
    by_contra hfi
    exact hi ((hKm i).mpr ⟨f, Submodule.mem_inf.mpr ⟨hfR, hf⟩, hfi⟩)
  have hK2 : ∀ S : Finset (Fin (3*t)), S.card = 4 → R ≤ ZZ (3*t) ⊔ sp S → K ⊆ S := by
    intro S hS hRS i hi
    obtain ⟨v, hv, hvi⟩ := (hKm i).mp hi
    have hne : S0 ∩ S ≠ ∅ := fun hd => disj_lem t (by omega) R S0 S h0 hRS hS0 hS hR hZ hd
    have hcard : (S0 ∪ S).card ≤ 7 := by
      have e := Finset.card_union_add_card_inter S0 S
      have : 0 < (S0 ∩ S).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    have hp := pair_lem (ZZ (3*t)) R S0 S h0 hRS (fun z hz hzs => by
      by_contra hz0
      exact zsupp8 t ht z hz hz0 (S0 ∪ S) hcard hzs)
    obtain ⟨z, hz, f, hf, hvf⟩ := Submodule.mem_sup.mp (hp (Submodule.mem_inf.mp hv).1)
    have hz0 : z = 0 := by
      by_contra hz0
      apply zsupp t (by omega) z hz hz0 S0 (by omega)
      rw [mem_sp]
      intro j hj
      have e1 := congrFun hvf j
      have e2 := (Submodule.mem_inf.mp hv).2 j hj
      have e3 := hf j (fun h => hj (Finset.mem_inter.mp h).1)
      simp only [Pi.add_apply] at e1
      rw [e3, add_zero] at e1
      rw [e1]
      exact e2
    rw [hz0, zero_add] at hvf
    rw [← hvf] at hvi
    by_contra hiS
    exact hvi (hf i (fun h => hiS (Finset.mem_inter.mp h).2))
  have hK3 : ∀ p, ¬ K ⊆ {p, nx p} := by
    intro p hp
    exact hnadj p (adj_lem t R K p hK1 hp hR)
  have hKne : K.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hK3 ⟨0, by omega⟩ (by rw [h]; exact Finset.empty_subset _)
  obtain ⟨a, ha⟩ := hKne
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ K, b ≠ a ∧ b ≠ nx a := by
    by_contra h
    push_neg at h
    apply hK3 a
    intro b hb
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : b = a
    · left; exact h1
    · right; exact h b hb h1
  obtain ⟨b', hb', hb'1⟩ : ∃ b ∈ K, b ≠ pv a ∧ b ≠ a := by
    by_contra h
    push_neg at h
    apply hK3 (pv a)
    intro b hb
    rw [Finset.mem_insert, Finset.mem_singleton, nx_pv]
    by_cases h1 : b = pv a
    · left; exact h1
    · right; exact h b hb h1
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := five_distinct t (by omega) a
  have fin : ∀ u v, u ∈ K → v ∈ K → Far u v → ∃ a b, Far a b ∧ ∀ S : Finset (Fin (3*t)),
      S.card = 4 → R ≤ ZZ (3*t) ⊔ sp S → a ∈ S ∧ b ∈ S :=
    fun u v hu hv huv => ⟨u, v, huv, fun S hS hRS => ⟨hK2 S hS hRS hu, hK2 S hS hRS hv⟩⟩
  by_cases hb2 : b = pv a
  · by_cases hb'2 : b' = nx a
    · rw [hb2] at hb
      rw [hb'2] at hb'
      refine fin (pv a) (nx a) hb hb' ⟨Ne.symm d6, ?_, Ne.symm d3⟩
      rw [nx_pv]; exact Ne.symm d8
    · exact fin a b' ha hb' ⟨hb'1.2, hb'2, hb'1.1⟩
  · exact fin a b ha hb ⟨hb1.1, hb1.2, hb2⟩
open Module in
theorem far_symm {t : ℕ} (α β : Fin (3*t)) (h : Far α β) : Far β α := by
  obtain ⟨f1, f2, f3⟩ := h
  refine ⟨Ne.symm f1, ?_, ?_⟩
  · intro h; apply f3; rw [h, pv_nx]
  · intro h; apply f2; rw [h, nx_pv]
open Module in
theorem form_symm {t : ℕ} (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) (h : Form x α β) :
    Form x β α := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1.symm, by rw [h2, add_comm]⟩
  · right; right; exact ⟨h1, h2⟩
  · right; left; exact ⟨h1, h2⟩
open Module in
theorem ED_symm {t : ℕ} (x : Fin (3*t) → ZMod 2) (α β : Fin (3*t)) (h : ED x α β) : ED x β α :=
  ⟨far_symm α β h.1, by rw [h.2.1, S4_comm], form_symm x α β h.2.2⟩
open Module in
theorem single_in (t : ℕ) (ht : 3 ≤ t) (R : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (S : Finset (Fin (3*t))) (hS : S.card ≤ 4) (h : R ≤ ZZ (3*t) ⊔ sp S) (p : Fin (3*t))
    (hp : (Pi.single p 1 : Fin (3*t) → ZMod 2) ∈ R) : p ∈ S := by
  by_contra hpS
  obtain ⟨z, hz, f, hf, hzf⟩ := Submodule.mem_sup.mp (h hp)
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, zero_add] at hzf
    have := hf p hpS
    rw [hzf] at this
    simp at this
  apply zsupp t ht z hz hz0 (insert p S) (by have := Finset.card_insert_le p S; omega)
  rw [mem_sp]
  intro i hi
  rw [Finset.mem_insert, not_or] at hi
  have e1 := congrFun hzf i
  simp only [Pi.add_apply] at e1
  rw [hf i hi.2, add_zero] at e1
  rw [e1]
  simp [Pi.single_apply, hi.1]
open Module in
def T1 {t : ℕ} (c : Fin (3*t)) : Fin (3*t) → ZMod 2 :=
  Pi.single c 1 + Pi.single (nx c) 1 + Pi.single (nx (nx c)) 1
open Module in
def T2 {t : ℕ} (c : Fin (3*t)) : Fin (3*t) → ZMod 2 :=
  Pi.single (pv (pv c)) 1 + Pi.single (pv c) 1 + Pi.single c 1
open Module in
def T3 {t : ℕ} (c : Fin (3*t)) : Fin (3*t) → ZMod 2 :=
  Pi.single (pv c) 1 + Pi.single c 1 + Pi.single (nx c) 1
open Module in
theorem four_ne (t : ℕ) (ht : 3 ≤ t) (i : Fin (3*t)) : nx (nx (nx (nx i))) ≠ i := by
  have a := i.isLt
  have A1 := nxv i
  have A2 := nxv (nx i)
  have A3 := nxv (nx (nx i))
  have A4 := nxv (nx (nx (nx i)))
  apply ne_of_val
  omega
open Module in
theorem adj_half (t : ℕ) (ht : 3 ≤ t) (x : Fin (3*t) → ZMod 2) (α β p : Fin (3*t)) (h : ED x α β)
    (hp : p = pv α ∨ p = α) (hnp : nx p ∈ S4 α β) :
    (∃ γ : Fin (3*t), γ.val % 3 = (nx p).val % 3 ∧ γ ≠ nx p ∧
        x = Pi.single (nx p) 1 + Pi.single γ 1) ∨
      x = T1 (nx p) ∨ x = T2 (nx p) ∨ x = T3 (nx p) := by
  obtain ⟨⟨f1, f2, f3⟩, hN, hF⟩ := h
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := five_distinct t ht α
  rcases hp with hp | hp
  · rw [hp, nx_pv]
    rcases hF with ⟨hr, hx⟩ | ⟨hB, hx⟩ | ⟨hB, hx⟩
    · left; exact ⟨β, hr.symm, f1, hx⟩
    · right; left; rw [T1, hx, hB]
    · right; right; left
      have e1 : pv α = nx β := by rw [hB, pv_nx]
      rw [T2, hx, e1, pv_nx]
  · rw [hp] at hnp ⊢
    rcases (mem_S4 α β _).mp hnp with h | h | h | h
    · exact absurd h.symm d6
    · exact absurd h.symm d8
    · have hB : β = nx (nx α) := by rw [h, nx_pv]
      rcases hF with ⟨hr, hx⟩ | ⟨hB', hx⟩ | ⟨hB', hx⟩
      · exfalso
        have r1 := res_nx α
        have r2 := res_nx (nx α)
        rw [← hB] at r2
        omega
      · right; right; right
        rw [T3, pv_nx, hx, ← hB]
      · exfalso
        rw [hB] at hB'
        exact four_ne t ht α hB'.symm
    · exact absurd h.symm f2
open Module in
theorem adj_class (t : ℕ) (ht : 3 ≤ t) (R : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (x : Fin (3*t) → ZMod 2) (α β p : Fin (3*t)) (h : ED x α β) (hR : R ≤ ZZ (3*t) ⊔ sp (S4 α β))
    (hp : (Pi.single p 1 : Fin (3*t) → ZMod 2) ∈ R)
    (hnp : (Pi.single (nx p) 1 : Fin (3*t) → ZMod 2) ∈ R) :
    (∃ γ : Fin (3*t), γ.val % 3 = (nx p).val % 3 ∧ γ ≠ nx p ∧
        x = Pi.single (nx p) 1 + Pi.single γ 1) ∨
      x = T1 (nx p) ∨ x = T2 (nx p) ∨ x = T3 (nx p) := by
  have hc := S4_card t ht α β h.1
  have h1 := single_in t ht R (S4 α β) (by omega) hR p hp
  have h2 := single_in t ht R (S4 α β) (by omega) hR (nx p) hnp
  rcases (mem_S4 α β p).mp h1 with e | e | e | e
  · exact adj_half t ht x α β p h (Or.inl e) h2
  · exact adj_half t ht x α β p h (Or.inr e) h2
  · exact adj_half t ht x β α p (ED_symm x α β h) (Or.inl e) (by rw [S4_comm]; exact h2)
  · exact adj_half t ht x β α p (ED_symm x α β h) (Or.inr e) (by rw [S4_comm]; exact h2)
open Module in
theorem res_ne {t : ℕ} (γ c : Fin (3*t)) (hγ : γ.val % 3 = c.val % 3) :
    γ ≠ nx c ∧ γ ≠ nx (nx c) ∧ γ ≠ pv c ∧ γ ≠ pv (pv c) := by
  have r1 := res_nx c
  have r2 := res_nx (nx c)
  have r3 := res_pv c
  have r4 := res_pv (pv c)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hγ <;> omega
open Module in
theorem piv_li {ι : Type} [Fintype ι] {m : ℕ} (g : ι → (Fin m → ZMod 2)) (ρ : ι → ℕ)
    (h : ∀ i, ∃ c, g i c ≠ 0 ∧ ∀ j, j ≠ i → ρ i ≤ ρ j → g j c = 0) :
    LinearIndependent (ZMod 2) g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  have hS : (Finset.univ.filter (fun i => a i ≠ 0)).Nonempty := ⟨i0, by simp [hi0]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ ρ hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hmin
  obtain ⟨c, hc, hj⟩ := h i
  have e := congrFun ha c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  rw [Finset.sum_eq_single i] at e
  · exact hc ((mul_eq_zero.mp e).resolve_left hi)
  · intro j _ hji
    by_cases haj : a j = 0
    · rw [haj, zero_mul]
    · rw [hj j hji (hmin j haj), mul_zero]
  · intro hi'
    exact absurd (Finset.mem_univ i) hi'
open Module in
def gB {t : ℕ} (c : Fin (3*t)) :
    {γ : Fin (3*t) // γ.val % 3 = c.val % 3 ∧ γ ≠ c} ⊕ Fin 3 → (Fin (3*t) → ZMod 2) :=
  Sum.elim (fun γ => Pi.single c 1 + Pi.single γ.val 1) ![T1 c, T2 c, T3 c]
open Module in
def rB {t : ℕ} (c : Fin (3*t)) : {γ : Fin (3*t) // γ.val % 3 = c.val % 3 ∧ γ ≠ c} ⊕ Fin 3 → ℕ :=
  Sum.elim (fun _ => 0) ![0, 0, 1]
open Module in
theorem gB_li (t : ℕ) (ht : 3 ≤ t) (c : Fin (3*t)) : LinearIndependent (ZMod 2) (gB c) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := five_distinct t ht c
  apply piv_li (gB c) (rB c)
  intro i
  rcases i with ⟨γ, hγ1, hγ2⟩ | k
  · obtain ⟨n1, n2, n3, n4⟩ := res_ne γ c hγ1
    refine ⟨γ, ?_, ?_⟩
    · simp [gB, Pi.single_apply, hγ2]
    · intro j hj _
      rcases j with ⟨γ', hγ'1, hγ'2⟩ | k
      · have hne : γ ≠ γ' := fun h => hj (by subst h; rfl)
        simp [gB, Pi.single_apply, hγ2, hne]
      · fin_cases k <;> simp [gB, T1, T2, T3, Pi.single_apply, hγ2, n1, n2, n3, n4]
  · fin_cases k
    · refine ⟨nx (nx c), ?_, ?_⟩
      · simp [gB, T1, Pi.single_apply, d9.symm, d10.symm]
      · intro j hj _
        rcases j with ⟨γ', hγ'1, hγ'2⟩ | k
        · obtain ⟨n1, n2, n3, n4⟩ := res_ne γ' c hγ'1
          simp [gB, Pi.single_apply, d9.symm, n2.symm]
        · fin_cases k
          · exact (hj rfl).elim
          · simp [gB, T2, Pi.single_apply, d4.symm, d7.symm, d9.symm]
          · simp [gB, T3, Pi.single_apply, d7.symm, d9.symm, d10.symm]
    · refine ⟨pv (pv c), ?_, ?_⟩
      · simp [gB, T2, Pi.single_apply, d1, d2]
      · intro j hj _
        rcases j with ⟨γ', hγ'1, hγ'2⟩ | k
        · obtain ⟨n1, n2, n3, n4⟩ := res_ne γ' c hγ'1
          simp [gB, Pi.single_apply, d2, n4.symm]
        · fin_cases k
          · simp [gB, T1, Pi.single_apply, d2, d3, d4]
          · exact (hj rfl).elim
          · simp [gB, T3, Pi.single_apply, d1, d2, d3]
    · refine ⟨nx c, ?_, ?_⟩
      · simp [gB, T3, Pi.single_apply, d6.symm, d8.symm]
      · intro j hj hle
        rcases j with ⟨γ', hγ'1, hγ'2⟩ | k
        · simp [rB] at hle
        · fin_cases k
          · simp [rB] at hle
          · simp [rB] at hle
          · exact (hj rfl).elim
open Module in
theorem card_le_fr {t : ℕ} (ht : 3 ≤ t) (P : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (pr : P → Prop) (c : Fin (3*t))
    (hcl : ∀ x : {x : P // pr x}, ∃ k, (x.val : Fin (3*t) → ZMod 2) = gB c k) :
    Nat.card {x : P // pr x} ≤ finrank (ZMod 2) P := by
  classical
  choose φ hφ using hcl
  have hφi : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    rw [hφ a, hφ b, hab]
  have hli : LinearIndependent (ZMod 2) (fun x : {x : P // pr x} => (x.val : P)) := by
    apply LinearIndependent.of_comp P.subtype
    have e : (P.subtype ∘ fun x : {x : P // pr x} => (x.val : P)) = gB c ∘ φ := by
      funext x
      exact hφ x
    rw [e]
    exact (gB_li t ht c).comp φ hφi
  haveI : Fintype {x : P // pr x} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact hli.fintype_card_le_finrank
open Module in
def L9 : Fin 18 → Finset (Fin (3*3)) := ![{0, 2, 3, 8}, {0, 1, 3, 4}, {1, 2, 4, 5}, {2, 3, 5, 6},
  {3, 4, 6, 7}, {4, 5, 7, 8}, {0, 5, 6, 8}, {0, 1, 6, 7}, {1, 2, 7, 8}, {0, 1, 2, 8}, {0, 1, 2, 3},
  {1, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {5, 6, 7, 8}, {0, 6, 7, 8}, {0, 1, 7, 8}]
open Module in
def cpb (S S' : Finset (Fin (3*3))) : Bool :=
  decide ((∀ p : Fin (3*3), ¬ (S ∩ S' ⊆ {p, nx p})) ∨
    ((∃ r : Fin 3, ∀ i : Fin (3*3), i.val % 3 ≠ r.val → i ∈ S ∪ S') ∧ (S ∩ S').Nonempty))
open Module in
def tb : Fin 18 → Fin 18 → Bool := fun i j => cpb (L9 i) (L9 j)
open Module in
theorem clique9 : ∀ i j : Fin 18, i ≠ j → tb i j = true → ∀ k : Fin 18, i ≠ k → j ≠ k →
    tb i k = true → tb j k = true → ∀ l : Fin 18, i ≠ l → j ≠ l → k ≠ l →
    tb i l = true → tb j l = true → tb k l = true → False := by
  decide
open Module in
theorem L9_cover : ∀ α β : Fin (3*3), Far α β → Val α β → ∃ k : Fin 18, S4 α β = L9 k := by
  unfold Far Val S4
  decide
open Module in
theorem cpb_true (R : Submodule (ZMod 2) (Fin (3*3) → ZMod 2)) (hZ : ZZ (3*3) ≤ R)
    (hR : finrank (ZMod 2) R = 4)
    (hnadj : ∀ p, ¬ ((Pi.single p 1 : Fin (3*3) → ZMod 2) ∈ R ∧
      (Pi.single (nx p) 1 : Fin (3*3) → ZMod 2) ∈ R))
    (S S' : Finset (Fin (3*3))) (hS : S.card = 4) (hS' : S'.card = 4)
    (h1 : R ≤ ZZ (3*3) ⊔ sp S) (h2 : R ≤ ZZ (3*3) ⊔ sp S') : cpb S S' = true := by
  unfold cpb
  rw [decide_eq_true_iff]
  by_cases hc : ∀ z ∈ ZZ (3*3), z ∈ sp (S ∪ S') → z = 0
  · left
    intro p hp
    exact hnadj p (adj_lem 3 R (S ∩ S') p (pair_lem (ZZ (3*3)) R S S' h1 h2 hc) hp hR)
  · right
    refine ⟨?_, ?_⟩
    · push_neg at hc
      obtain ⟨z, hz, hzs, hz0⟩ := hc
      obtain ⟨a, b, rfl⟩ := (mem_ZZ z).mp hz
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
      · simp at hz0
      · refine ⟨0, fun i hi => ?_⟩
        by_contra hiS
        have e := hzs i hiS
        have hr : i.val % 3 = 1 ∨ i.val % 3 = 2 := by
          change i.val % 3 ≠ 0 at hi
          omega
        rcases hr with hr | hr <;> simp [cv, hr] at e
      · refine ⟨1, fun i hi => ?_⟩
        by_contra hiS
        have e := hzs i hiS
        have hr : i.val % 3 = 0 ∨ i.val % 3 = 2 := by
          change i.val % 3 ≠ 1 at hi
          omega
        rcases hr with hr | hr <;> simp [cv, hr] at e
      · refine ⟨2, fun i hi => ?_⟩
        by_contra hiS
        have e := hzs i hiS
        have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 := by
          change i.val % 3 ≠ 2 at hi
          omega
        rcases hr with hr | hr <;> simp [cv, hr] at e
    · rw [Finset.nonempty_iff_ne_empty]
      intro hd
      exact disj_lem 3 le_rfl R S S' h1 h2 hS hS' hR hZ hd
open Module in
theorem count3 (R : Submodule (ZMod 2) (Fin (3*3) → ZMod 2)) (hZ : ZZ (3*3) ≤ R)
    (hR : finrank (ZMod 2) R = 4)
    (hnadj : ∀ p, ¬ ((Pi.single p 1 : Fin (3*3) → ZMod 2) ∈ R ∧
      (Pi.single (nx p) 1 : Fin (3*3) → ZMod 2) ∈ R))
    (x : Fin 4 → (Fin (3*3) → ZMod 2)) (hinj : Function.Injective x)
    (hED : ∀ i, ∃ α β, ED (x i) α β ∧ R ≤ ZZ (3*3) ⊔ sp (S4 α β)) : False := by
  have hk : ∀ i, ∃ k : Fin 18, Ns (x i) = L9 k ∧ R ≤ ZZ (3*3) ⊔ sp (L9 k) := by
    intro i
    obtain ⟨α, β, h, hRS⟩ := hED i
    obtain ⟨k, hk⟩ := L9_cover α β h.1 (val_of_form _ _ _ h.2.2)
    exact ⟨k, by rw [h.2.1, hk], by rw [← hk]; exact hRS⟩
  choose k hkN hkR using hk
  have hcard : ∀ i, (L9 (k i)).card = 4 := by
    intro i
    obtain ⟨α, β, h, _⟩ := hED i
    rw [← hkN i, h.2.1]
    exact S4_card 3 le_rfl α β h.1
  have hne : ∀ i j, i ≠ j → k i ≠ k j := by
    intro i j hij e
    apply hij
    apply hinj
    obtain ⟨α, β, h, _⟩ := hED i
    obtain ⟨α', β', h', _⟩ := hED j
    exact inj_data 3 le_rfl (x i) (x j) α β α' β' h h' (by rw [hkN i, hkN j, e])
  have htb : ∀ i j, tb (k i) (k j) = true := fun i j =>
    cpb_true R hZ hR hnadj _ _ (hcard i) (hcard j) (hkR i) (hkR j)
  exact clique9 (k 0) (k 1) (hne 0 1 (by decide)) (htb 0 1) (k 2) (hne 0 2 (by decide))
    (hne 1 2 (by decide)) (htb 0 2) (htb 1 2) (k 3) (hne 0 3 (by decide)) (hne 1 3 (by decide))
    (hne 2 3 (by decide)) (htb 0 3) (htb 1 3) (htb 2 3)
open Module in
theorem main (t : ℕ) (h3 : 3 ≤ t) (P Q : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
    (hP : ∀ x ∈ P, inC x) (hQ : ∀ y ∈ Q, inC y) (hdim : 3*t - 4 ≤ finrank (ZMod 2) Q) :
    (∀ x : P, x ≠ 0 → 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} ≤ Nat.card Q) ∧
    Nat.card {x : P // x ≠ 0 ∧ 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} = Nat.card Q} ≤
      max (finrank (ZMod 2) P) (if t = 3 then 4 else 3) ∧
    (5 ≤ Nat.card {x : P // x ≠ 0 ∧ 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} = Nat.card Q} →
      ∃ i : Fin (3*t), ∀ y : Q, y.val i = 0 ∧ y.val (nx i) = 0) := by
  classical
  have hcardQ : Nat.card Q = 2 ^ finrank (ZMod 2) Q := card_sub _ Q
  have hh : ∀ x : P, Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} =
      2 ^ finrank (ZMod 2) (Q ⊓ kl (Ns x.val) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) :=
    fun x => hits_eq t Q x.val
  have hx0 : ∀ x : P, x ≠ 0 → x.val ≠ 0 := fun x hx h => hx (Subtype.ext h)
  have hE : ∀ x : P, (x ≠ 0 ∧ 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} = Nat.card Q) →
      x.val ≠ 0 ∧ finrank (ZMod 2) (Q ⊓ kl (Ns x.val) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) +
        2 = finrank (ZMod 2) Q := by
    rintro x ⟨hx, he⟩
    refine ⟨hx0 x hx, ?_⟩
    rw [hh, hcardQ] at he
    have h4 : 2 ^ (finrank (ZMod 2) (Q ⊓ kl (Ns x.val) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) +
        2) = 2 ^ finrank (ZMod 2) Q := by
      rw [pow_add, ← he]; ring
    exact Nat.pow_right_injective (le_refl 2) h4
  obtain ⟨R, hRdef⟩ : ∃ R, R = (BB (3*t)).orthogonal Q := ⟨_, rfl⟩
  have hZR : ZZ (3*t) ≤ R := by rw [hRdef]; exact ZZ_le t Q hQ
  have hEd : ∀ x : {x : P // x ≠ 0 ∧ 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} = Nat.card Q},
      ∃ α β, ED x.val.val α β ∧ R ≤ ZZ (3*t) ⊔ sp (S4 α β) ∧ finrank (ZMod 2) R = 4 := by
    intro x
    obtain ⟨h1, h2⟩ := hE x.val x.prop
    obtain ⟨α, β, hf, hN, hF, hR', hR4⟩ :=
      edata t h3 Q hQ hdim x.val.val (hP _ x.val.prop) h1 h2
    rw [← hRdef] at hR' hR4
    exact ⟨α, β, ⟨hf, hN, hF⟩, hR', hR4⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hh, hcardQ]
    have := part1 t h3 Q hQ hdim x.val (hP x.val x.prop) (hx0 x hx)
    calc 4 * 2 ^ finrank (ZMod 2) (Q ⊓ kl (Ns x.val) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2))
        = 2 ^ (finrank (ZMod 2) (Q ⊓ kl (Ns x.val) : Submodule (ZMod 2) (Fin (3*t) → ZMod 2)) +
          2) := by rw [pow_add]; ring
      _ ≤ 2 ^ finrank (ZMod 2) Q := Nat.pow_le_pow_right (by norm_num) this
  by_cases hadj : ∃ p, (Pi.single p 1 : Fin (3*t) → ZMod 2) ∈ R ∧
      (Pi.single (nx p) 1 : Fin (3*t) → ZMod 2) ∈ R
  · obtain ⟨p, hp1, hp2⟩ := hadj
    have hc := card_le_fr h3 P (fun x : P => x ≠ 0 ∧ 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} = Nat.card Q) (nx p) (fun x => by
      obtain ⟨α, β, hED, hRS, _⟩ := hEd x
      rcases adj_class t h3 R x.val.val α β p hED hRS hp1 hp2 with ⟨γ, hγ1, hγ2, hx⟩ | hx | hx | hx
      · exact ⟨Sum.inl ⟨γ, hγ1, hγ2⟩, hx⟩
      · exact ⟨Sum.inr 0, hx⟩
      · exact ⟨Sum.inr 1, hx⟩
      · exact ⟨Sum.inr 2, hx⟩)
    refine ⟨le_max_of_le_left hc, fun _ => ⟨p, fun y => ⟨?_, ?_⟩⟩⟩
    · rw [hRdef] at hp1
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hp1) y.val y.prop
      rw [← BB_single (3*t) y.val p]
      exact this
    · rw [hRdef] at hp2
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hp2) y.val y.prop
      rw [← BB_single (3*t) y.val (nx p)]
      exact this
  · have hnadj : ∀ p, ¬ ((Pi.single p 1 : Fin (3*t) → ZMod 2) ∈ R ∧
        (Pi.single (nx p) 1 : Fin (3*t) → ZMod 2) ∈ R) := fun p h => hadj ⟨p, h⟩
    have hc : Nat.card {x : P // x ≠ 0 ∧ 4 * Nat.card {y : Q // ∀ i : Fin (3*t),
        x.val i * y.val i = 0 ∧ x.val (nx i) * y.val i = 0} = Nat.card Q} ≤ 3 := by
      apply card_le_three
      intro f hf
      have hxi : Function.Injective (fun i => (f i).val.val) := by
        intro i j hij
        apply hf
        apply Subtype.ext
        apply Subtype.ext
        exact hij
      obtain ⟨α0, β0, h0, hR0, hR4⟩ := hEd (f 0)
      rcases Nat.lt_or_ge t 4 with ht4 | ht4
      · have ht3 : t = 3 := by omega
        subst ht3
        exact count3 R hZR hR4 hnadj (fun i => (f i).val.val) hxi (fun i => by
          obtain ⟨α, β, h, hRS, _⟩ := hEd (f i)
          exact ⟨α, β, h, hRS⟩)
      · obtain ⟨a, b, hab, hall⟩ :=
          Kapp t ht4 R hZR hR4 (S4 α0 β0) (S4_card t h3 α0 β0 h0.1) hR0 hnadj
        apply count_lem t h3 a b hab (fun i => (f i).val.val) hxi
        · intro i
          obtain ⟨α, β, h, _⟩ := hEd (f i)
          exact ⟨α, β, h⟩
        · intro i
          obtain ⟨α, β, h, hRS, _⟩ := hEd (f i)
          have := hall (S4 α β) (S4_card t h3 α β h.1) hRS
          show a ∈ Ns (f i).val.val ∧ b ∈ Ns (f i).val.val
          rw [h.2.1]
          exact this
    refine ⟨le_max_of_le_right ?_, fun h5 => (by omega : False).elim⟩
    split_ifs <;> omega
end PEqualNP.Outside.L_lib_1081
theorem PEqualNP.Outside.L_lib_1081 : ∀ (t : ℕ) (ht : 0 < t), 3 ≤ t →
  let F := ZMod 2
  let n := 3*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
  let code := fun (x : W) => ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
  ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
    n-4 ≤ Module.finrank F Q →
    let hits := fun (x : P) => Nat.card {y : Q // ∀ i : Fin n,
      x.val i * y.val i = 0 ∧ x.val (ix (i.val+1)) * y.val i = 0}
    let count := Nat.card {x : P // x ≠ 0 ∧ 4*hits x = Nat.card Q}
    (∀ x : P, x ≠ 0 → 4*hits x ≤ Nat.card Q) ∧
      count ≤ max (Module.finrank F P) (if t = 3 then 4 else 3) ∧
      (5 ≤ count → ∃ i : Fin n, ∀ y : Q, y.val i = 0 ∧ y.val (ix (i.val+1)) = 0)
    := by
  intro t ht h3 F n W ix code P Q hP hQ hdim hits count
  exact PEqualNP.Outside.L_lib_1081.main t h3 P Q
    (fun x hx => (PEqualNP.Outside.L_lib_1081.code_iff t x).mp (hP x hx))
    (fun y hy => (PEqualNP.Outside.L_lib_1081.code_iff t y).mp (hQ y hy)) hdim

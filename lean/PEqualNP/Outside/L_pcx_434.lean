import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_434
open Module
theorem distrib {ι : Type*} [DecidableEq ι] (a c : ι → ℕ) (hac : ∀ i, a i ≤ c i) (s : Finset ι) :
    ∀ h : ℕ, ∑ i ∈ s, a i ≤ h → h ≤ ∑ i ∈ s, c i →
    ∃ x : ι → ℕ, (∀ i, a i ≤ x i ∧ x i ≤ c i) ∧ ∑ i ∈ s, x i = h := by
  induction s using Finset.induction_on with
  | empty =>
    intro h _ h2
    refine ⟨a, fun i => ⟨le_rfl, hac i⟩, ?_⟩
    simp only [Finset.sum_empty] at h2 ⊢
    omega
  | insert j s hj ih =>
    intro h h1 h2
    rw [Finset.sum_insert hj] at h1 h2
    have hAC : ∑ i ∈ s, a i ≤ ∑ i ∈ s, c i := Finset.sum_le_sum (fun i _ => hac i)
    have hj' := hac j
    obtain ⟨x, hx, hs⟩ := ih (h - max (a j) (h - ∑ i ∈ s, c i)) (by omega) (by omega)
    refine ⟨Function.update x j (max (a j) (h - ∑ i ∈ s, c i)), fun i => ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hij]
        exact hx i
    · rw [Finset.sum_insert hj, Function.update_self]
      have : ∑ i ∈ s, Function.update x j (max (a j) (h - ∑ i ∈ s, c i)) i = ∑ i ∈ s, x i :=
        Finset.sum_congr rfl (fun i hi => Function.update_of_ne (by rintro rfl; exact hj hi) _ _)
      rw [this]
      omega
theorem interp {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q P : Submodule K V) (hQP : Q ≤ P) (s : ℕ) : finrank K Q ≤ s → s ≤ finrank K P →
    ∃ U : Submodule K V, Q ≤ U ∧ U ≤ P ∧ finrank K U = s := by
  induction s with
  | zero => intro h1 _; exact ⟨Q, le_rfl, hQP, by omega⟩
  | succ n ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · exact ⟨Q, le_rfl, hQP, h⟩
    · obtain ⟨U, hQU, hUP, hU⟩ := ih (by omega) (by omega)
      have hne : U ≠ P := by rintro rfl; omega
      obtain ⟨x, hxP, hxU⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hUP hne)
      have hx0 : x ≠ 0 := by rintro rfl; exact hxU U.zero_mem
      refine ⟨U ⊔ K ∙ x, le_sup_of_le_left hQU,
        sup_le hUP ((Submodule.span_singleton_le_iff_mem _ _).mpr hxP), ?_⟩
      have h3 := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ x)
      have h4 : U ⊓ (K ∙ x) = ⊥ :=
        disjoint_iff.mp ((Submodule.disjoint_span_singleton' hx0).mpr hxU)
      rw [h4, finrank_bot, finrank_span_singleton hx0, hU] at h3
      omega
theorem finrank_pi_sub {ι : Type*} [Fintype ι] {K : Type*} [Field K] {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]
    (U : (i : ι) → Submodule K (W i)) :
    finrank K (Submodule.pi Set.univ U) = ∑ i, finrank K (U i) := by
  let e : Submodule.pi Set.univ U ≃ₗ[K] ((i : ι) → U i) :=
    { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      invFun := fun y => ⟨fun i => (y i).1, fun i _ => (y i).2⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
theorem pinterp {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]
    (Q P : (i : ι) → Submodule K (W i)) (hQP : ∀ i, Q i ≤ P i) (s : ℕ)
    (h1 : ∑ i, finrank K (Q i) ≤ s) (h2 : s ≤ ∑ i, finrank K (P i)) :
    ∃ U : (i : ι) → Submodule K (W i), (∀ i, Q i ≤ U i ∧ U i ≤ P i) ∧
      ∑ i, finrank K (U i) = s := by
  obtain ⟨x, hx, hs⟩ := distrib (fun i => finrank K (Q i)) (fun i => finrank K (P i))
    (fun i => Submodule.finrank_mono (hQP i)) Finset.univ s h1 h2
  have := fun i => interp (Q i) (P i) (hQP i) (x i) (hx i).1 (hx i).2
  choose U hQU hUP hU using this
  exact ⟨U, fun i => ⟨hQU i, hUP i⟩, by rw [← hs]; exact Finset.sum_congr rfl (fun i _ => hU i)⟩
abbrev Blk (n c : ℕ) := ((Fin n → ZMod 2) × (Fin n → ZMod 2)) × (Fin c → ZMod 2)
def Bb {n c : ℕ} (u v : Blk n c) : ZMod 2 := ∑ j : Fin n, (u.1.1 j * v.1.2 j + u.1.2 j * v.1.1 j)
theorem Bb_add_left {n c : ℕ} (u u' v : Blk n c) : Bb (u + u') v = Bb u v + Bb u' v := by
  unfold Bb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring
theorem Bb_add_right {n c : ℕ} (u v v' : Blk n c) : Bb u (v + v') = Bb u v + Bb u v' := by
  unfold Bb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring
theorem Bb_smul_left {n c : ℕ} (a : ZMod 2) (u v : Blk n c) : Bb (a • u) v = a * Bb u v := by
  unfold Bb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring
theorem Bb_smul_right {n c : ℕ} (a : ZMod 2) (u v : Blk n c) : Bb u (a • v) = a * Bb u v := by
  unfold Bb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring
theorem Bb_zero_left {n c : ℕ} (v : Blk n c) : Bb 0 v = 0 := by simp [Bb]
theorem Bb_zero_right {n c : ℕ} (u : Blk n c) : Bb u 0 = 0 := by simp [Bb]
def phi (n t c : ℕ) (hm : t ≤ n) : Blk n c →ₗ[ZMod 2] (Fin t → ZMod 2) where
  toFun u := fun j => u.1.1 (Fin.castLE hm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def psi (n t c : ℕ) (hm : t ≤ n) :
    Blk n c →ₗ[ZMod 2] (Fin n → ZMod 2) × (Fin (n - t) → ZMod 2) where
  toFun u := (u.1.1, fun j => u.1.2 ⟨t + j.val, by have := j.isLt; omega⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem finrank_Blk (n c : ℕ) : finrank (ZMod 2) (Blk n c) = n + n + c := by
  simp [Blk, Module.finrank_prod]
theorem ker_phi_ge (n t c : ℕ) (hm : t ≤ n) :
    n + n + c ≤ finrank (ZMod 2) (LinearMap.ker (phi n t c hm)) + t := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (phi n t c hm)
  have h2 := Submodule.finrank_le (LinearMap.range (phi n t c hm))
  rw [Module.finrank_fin_fun] at h2
  rw [finrank_Blk] at h1
  omega
theorem ker_psi_ge (n t c : ℕ) (hm : t ≤ n) :
    t + c ≤ finrank (ZMod 2) (LinearMap.ker (psi n t c hm)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (psi n t c hm)
  have h2 := Submodule.finrank_le (LinearMap.range (psi n t c hm))
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h2
  rw [finrank_Blk] at h1
  omega
theorem ker_psi_le (n t c : ℕ) (hm : t ≤ n) :
    LinearMap.ker (psi n t c hm) ≤ LinearMap.ker (phi n t c hm) := by
  intro u hu
  rw [LinearMap.mem_ker] at hu ⊢
  have h1 : u.1.1 = 0 := congrArg Prod.fst hu
  funext j
  show u.1.1 (Fin.castLE hm j) = 0
  rw [h1]
  rfl
theorem orth_blk (n t c : ℕ) (hm : t ≤ n) (u v : Blk n c)
    (hu : u ∈ LinearMap.ker (psi n t c hm)) (hv : v ∈ LinearMap.ker (phi n t c hm)) :
    Bb u v = 0 := by
  rw [LinearMap.mem_ker] at hu hv
  have h1 : u.1.1 = 0 := congrArg Prod.fst hu
  have h2 : ∀ j : Fin n, t ≤ j.val → u.1.2 j = 0 := by
    intro j hj
    have key : u.1.2 ⟨t + (j.val - t), by omega⟩ = 0 :=
      congrFun (congrArg Prod.snd hu) ⟨j.val - t, by omega⟩
    have e : (⟨t + (j.val - t), by omega⟩ : Fin n) = j := Fin.ext (by show t + (j.val - t) = j.val; omega)
    rw [e] at key
    exact key
  have h3 : ∀ j : Fin n, j.val < t → v.1.1 j = 0 := by
    intro j hj
    have key : v.1.1 (Fin.castLE hm ⟨j.val, hj⟩) = 0 := congrFun hv ⟨j.val, hj⟩
    have e : Fin.castLE hm ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [e] at key
    exact key
  unfold Bb
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [h1]
  simp only [Pi.zero_apply, zero_mul, zero_add]
  by_cases hj : j.val < t
  · rw [h3 j hj, mul_zero]
  · rw [h2 j (by omega), zero_mul]
abbrev X {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) := (i : Fin r) → Blk (m i) (b i).toNat
def beta {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) : LinearMap.BilinForm (ZMod 2) (X m b) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i, Bb (x i) (y i))
    (fun x x' y => by simp only [Pi.add_apply, Bb_add_left, Finset.sum_add_distrib])
    (fun a x y => by simp only [Pi.smul_apply, Bb_smul_left, smul_eq_mul, Finset.mul_sum])
    (fun x y y' => by simp only [Pi.add_apply, Bb_add_right, Finset.sum_add_distrib])
    (fun a x y => by simp only [Pi.smul_apply, Bb_smul_right, smul_eq_mul, Finset.mul_sum])
theorem beta_apply {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (x y : X m b) :
    beta m b x y = ∑ i, Bb (x i) (y i) := rfl
theorem Rs_add_mem {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (S : Submodule (ZMod 2) (X m b))
    (T : Finset (Fin r)) (x y : X m b)
    (hx : x ∈ S ∧ (∀ i, i ∉ T → x i = 0) ∧ ∀ v ∈ S, ∀ i, Bb (x i) (v i) = 0)
    (hy : y ∈ S ∧ (∀ i, i ∉ T → y i = 0) ∧ ∀ v ∈ S, ∀ i, Bb (y i) (v i) = 0) :
    x + y ∈ S ∧ (∀ i, i ∉ T → (x + y) i = 0) ∧ ∀ v ∈ S, ∀ i, Bb ((x + y) i) (v i) = 0 := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨S.add_mem hx1 hy1, fun i hi => ?_, fun v hv i => ?_⟩
  · show x i + y i = 0
    rw [hx2 i hi, hy2 i hi, add_zero]
  · show Bb (x i + y i) (v i) = 0
    rw [Bb_add_left, hx3 v hv i, hy3 v hv i, add_zero]
theorem Rs_smul_mem {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (S : Submodule (ZMod 2) (X m b))
    (T : Finset (Fin r)) (a : ZMod 2) (x : X m b)
    (hx : x ∈ S ∧ (∀ i, i ∉ T → x i = 0) ∧ ∀ v ∈ S, ∀ i, Bb (x i) (v i) = 0) :
    a • x ∈ S ∧ (∀ i, i ∉ T → (a • x) i = 0) ∧ ∀ v ∈ S, ∀ i, Bb ((a • x) i) (v i) = 0 := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨S.smul_mem a hx1, fun i hi => ?_, fun v hv i => ?_⟩
  · show a • x i = 0
    rw [hx2 i hi, smul_zero]
  · show Bb (a • x i) (v i) = 0
    rw [Bb_smul_left, hx3 v hv i, mul_zero]
def Rs {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (S : Submodule (ZMod 2) (X m b))
    (T : Finset (Fin r)) : Submodule (ZMod 2) (X m b) :=
  { carrier := {x | x ∈ S ∧ (∀ i, i ∉ T → x i = 0) ∧ ∀ v ∈ S, ∀ i, Bb (x i) (v i) = 0}
    zero_mem' := ⟨S.zero_mem, fun _ _ => rfl, fun _ _ _ => Bb_zero_left _⟩
    smul_mem' := fun a {x} hx => Rs_smul_mem m b S T a x hx, add_mem' := fun hx hy => Rs_add_mem m b S T _ _ hx hy }
theorem mem_Rs {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) {S : Submodule (ZMod 2) (X m b)}
    {T : Finset (Fin r)} {x : X m b} :
    x ∈ Rs m b S T ↔ x ∈ S ∧ (∀ i, i ∉ T → x i = 0) ∧ ∀ v ∈ S, ∀ i, Bb (x i) (v i) = 0 :=
  Iff.rfl
theorem finrank_X {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) :
    finrank (ZMod 2) (X m b) = ∑ i, (2 * m i + (b i).toNat) := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [finrank_Blk]
  ring
def piT {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (T : Finset (Fin r)) :
    X m b →ₗ[ZMod 2] ((i : T) → Blk (m i) (b i).toNat) where
  toFun x := fun i => x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def maskT {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (W : Submodule (ZMod 2) (X m b))
    (T : Finset (Fin r)) : W →ₗ[ZMod 2] ((i : T) → (Fin (b i).toNat → ZMod 2)) where
  toFun x := fun i => (x.1 i.1).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem ker_raw {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (x : X m b)
    (hx : x ∈ LinearMap.ker (beta m b)) (i : Fin r) : (x i).1 = 0 := by
  rw [LinearMap.mem_ker] at hx
  have key : ∀ w : Blk (m i) (b i).toNat, Bb (x i) w = 0 := by
    intro w
    have h1 := LinearMap.congr_fun hx (Pi.single i w)
    rw [beta_apply, LinearMap.zero_apply] at h1
    rwa [Finset.sum_eq_single i (fun i' _ hi' => by rw [Pi.single_eq_of_ne hi']; exact Bb_zero_right _)
      (fun hi => absurd (Finset.mem_univ i) hi), Pi.single_eq_same] at h1
  have hp := fun j => key ((0, Pi.single j 1), 0)
  have hq := fun j => key ((Pi.single j 1, 0), 0)
  simp [Bb, Pi.single_apply] at hp hq
  exact Prod.ext (funext hp) (funext hq)
theorem Rs_le {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (S : Submodule (ZMod 2) (X m b))
    (T : Finset (Fin r)) : Rs m b S T ≤ S := fun _ hx => ((mem_Rs m b).mp hx).1
theorem upper {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (S : Submodule (ZMod 2) (X m b))
    (T : Finset (Fin r)) :
    finrank (ZMod 2) (Rs m b S T) ≤ min (finrank (ZMod 2) S) ((∑ i ∈ T, (b i).toNat) +
      min (∑ i, (2 * m i + (b i).toNat) - finrank (ZMod 2) S) (∑ i ∈ T, m i)) := by
  have hA := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := beta m b) (Rs m b S T)
  rw [finrank_X] at hA
  have hK : finrank (ZMod 2) ↥(Rs m b S T ⊓ LinearMap.ker (beta m b)) ≤ ∑ i ∈ T, (b i).toNat := by
    have hinj : Function.Injective (maskT m b (Rs m b S T ⊓ LinearMap.ker (beta m b)) T) := by
      intro x y hxy
      have hx := Submodule.mem_inf.mp x.2
      have hy := Submodule.mem_inf.mp y.2
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ T
      · have h1 : (x.1 i).2 = (y.1 i).2 := congrFun hxy ⟨i, hi⟩
        exact Prod.ext ((ker_raw m b x.1 hx.2 i).trans (ker_raw m b y.1 hy.2 i).symm) h1
      · rw [((mem_Rs m b).mp hx.1).2.1 i hi, ((mem_Rs m b).mp hy.1).2.1 i hi]
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi_fintype] at this
    simp only [Module.finrank_fin_fun] at this
    rw [Finset.sum_coe_sort (s := T) (f := fun i => (b i).toNat)] at this
    exact this
  have hSo : S ≤ (beta m b).orthogonal (Rs m b S T) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [beta_apply]
    exact Finset.sum_eq_zero (fun i _ => ((mem_Rs m b).mp hn).2.2 v hv i)
  have hKo : LinearMap.ker (piT m b T) ≤ (beta m b).orthogonal (Rs m b S T) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [beta_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hi : i ∈ T
    · have : v i = 0 := congrFun hv ⟨i, hi⟩
      rw [this]
      exact Bb_zero_right _
    · rw [((mem_Rs m b).mp hn).2.1 i hi]
      exact Bb_zero_left _
  have hRo : Rs m b S T ≤ (beta m b).orthogonal (Rs m b S T) := le_trans (Rs_le m b S T) hSo
  have hdisj : Rs m b S T ⊓ LinearMap.ker (piT m b T) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    rw [LinearMap.mem_ker] at hx2
    funext i
    by_cases hi : i ∈ T
    · exact congrFun hx2 ⟨i, hi⟩
    · exact ((mem_Rs m b).mp hx1).2.1 i hi
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Rs m b S T) (LinearMap.ker (piT m b T))
  rw [hdisj, finrank_bot] at hsup
  have hrn := LinearMap.finrank_range_add_finrank_ker (piT m b T)
  have hrange := Submodule.finrank_le (LinearMap.range (piT m b T))
  rw [Module.finrank_pi_fintype] at hrange
  rw [finrank_X] at hrn
  simp only [finrank_Blk] at hrange
  rw [Finset.sum_coe_sort (s := T) (f := fun i => m i + m i + (b i).toNat)] at hrange
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hrange
  have h1 := Submodule.finrank_mono hSo
  have h2 := Submodule.finrank_mono (sup_le hRo hKo)
  have h3 := Submodule.finrank_mono (Rs_le m b S T)
  omega
def Dd {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (T : Finset (Fin r)) (tt : Fin r → ℕ)
    (hm : ∀ i, tt i ≤ m i) (i : Fin r) : Submodule (ZMod 2) (Blk (m i) (b i).toNat) :=
  if i ∈ T then LinearMap.ker (psi (m i) (tt i) (b i).toNat (hm i)) else ⊥
def Od {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (tt : Fin r → ℕ)
    (hm : ∀ i, tt i ≤ m i) (i : Fin r) : Submodule (ZMod 2) (Blk (m i) (b i).toNat) :=
  LinearMap.ker (phi (m i) (tt i) (b i).toNat (hm i))
theorem Dd_pos {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (T : Finset (Fin r)) (tt : Fin r → ℕ)
    (hm : ∀ i, tt i ≤ m i) {i : Fin r} (hi : i ∈ T) :
    Dd m b T tt hm i = LinearMap.ker (psi (m i) (tt i) (b i).toNat (hm i)) := by
  unfold Dd
  simp [hi]
theorem Dd_neg {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (T : Finset (Fin r)) (tt : Fin r → ℕ)
    (hm : ∀ i, tt i ≤ m i) {i : Fin r} (hi : i ∉ T) : Dd m b T tt hm i = ⊥ := by
  unfold Dd
  simp [hi]
theorem lower {r : ℕ} (m : Fin r → ℕ) (b : Fin r → Bool) (T : Finset (Fin r)) (h : ℕ)
    (hh : h ≤ ∑ i, (2 * m i + (b i).toNat)) :
    ∃ U : (i : Fin r) → Submodule (ZMod 2) (Blk (m i) (b i).toNat),
      finrank (ZMod 2) (Submodule.pi Set.univ U) = h ∧
      min h ((∑ i ∈ T, (b i).toNat) + min (∑ i, (2 * m i + (b i).toNat) - h) (∑ i ∈ T, m i)) ≤
        finrank (ZMod 2) (Rs m b (Submodule.pi Set.univ U) T) := by
  obtain ⟨tt, htt, hts⟩ := distrib (fun _ => 0) (fun i => if i ∈ T then m i else 0)
    (fun i => Nat.zero_le _) Finset.univ (min (∑ i, (2 * m i + (b i).toNat) - h) (∑ i ∈ T, m i))
    (by simp) (by rw [Finset.sum_ite_mem, Finset.univ_inter]; omega)
  have hm : ∀ i, tt i ≤ m i := fun i => by
    have := (htt i).2
    split_ifs at this <;> omega
  have hT0 : ∀ i, i ∉ T → tt i = 0 := fun i hi => by
    have := (htt i).2
    simp only [hi, ite_false] at this
    omega
  have hDO : ∀ i, Dd m b T tt hm i ≤ Od m b tt hm i := by
    intro i
    by_cases hi : i ∈ T
    · rw [Dd_pos m b T tt hm hi]
      exact ker_psi_le _ _ _ _
    · rw [Dd_neg m b T tt hm hi]
      exact bot_le
  have hDdim : ∀ i, i ∈ T → tt i + (b i).toNat ≤ finrank (ZMod 2) (Dd m b T tt hm i) := by
    intro i hi
    rw [Dd_pos m b T tt hm hi]
    exact ker_psi_ge _ _ _ _
  have hOdim : ∀ i, 2 * m i + (b i).toNat ≤ finrank (ZMod 2) (Od m b tt hm i) + tt i := by
    intro i
    have := ker_phi_ge (m i) (tt i) (b i).toNat (hm i)
    unfold Od
    omega
  have hsumD : min (∑ i, (2 * m i + (b i).toNat) - h) (∑ i ∈ T, m i) + ∑ i ∈ T, (b i).toNat ≤
      ∑ i, finrank (ZMod 2) (Dd m b T tt hm i) := by
    have h1 : ∑ i ∈ T, (tt i + (b i).toNat) ≤ ∑ i ∈ T, finrank (ZMod 2) (Dd m b T tt hm i) :=
      Finset.sum_le_sum (fun i hi => hDdim i hi)
    have h2 : ∑ i ∈ T, finrank (ZMod 2) (Dd m b T tt hm i) ≤
        ∑ i, finrank (ZMod 2) (Dd m b T tt hm i) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    have h3 : ∑ i ∈ T, tt i = ∑ i, tt i :=
      Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => hT0 i hi)
    rw [Finset.sum_add_distrib, h3, hts] at h1
    omega
  have hsumO : ∑ i, (2 * m i + (b i).toNat) ≤ ∑ i, finrank (ZMod 2) (Od m b tt hm i) +
      min (∑ i, (2 * m i + (b i).toNat) - h) (∑ i ∈ T, m i) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hOdim i)
    have e : ∑ i, (finrank (ZMod 2) (Od m b tt hm i) + tt i) =
        ∑ i, finrank (ZMod 2) (Od m b tt hm i) + ∑ i, tt i := Finset.sum_add_distrib
    rw [e, hts] at this
    exact this
  obtain ⟨Q, hQ, hQs⟩ := pinterp (fun i => (⊥ : Submodule (ZMod 2) (Blk (m i) (b i).toNat)))
    (Dd m b T tt hm) (fun i => bot_le)
    (min h (min (∑ i, (2 * m i + (b i).toNat) - h) (∑ i ∈ T, m i) + ∑ i ∈ T, (b i).toNat))
    (by simp) (by omega)
  obtain ⟨U, hU, hUs⟩ := pinterp Q (Od m b tt hm) (fun i => le_trans (hQ i).2 (hDO i)) h
    (by omega) (by omega)
  refine ⟨U, by rw [finrank_pi_sub, hUs], ?_⟩
  have hQR : Submodule.pi Set.univ Q ≤ Rs m b (Submodule.pi Set.univ U) T := by
    intro x hx
    rw [Submodule.mem_pi] at hx
    refine (mem_Rs m b).mpr ⟨?_, ?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro i _
      exact (hU i).1 (hx i (Set.mem_univ i))
    · intro i hi
      have := (hQ i).2 (hx i (Set.mem_univ i))
      rw [Dd_neg m b T tt hm hi, Submodule.mem_bot] at this
      exact this
    · intro v hv i
      rw [Submodule.mem_pi] at hv
      have hxD := (hQ i).2 (hx i (Set.mem_univ i))
      have hvO := (hU i).2 (hv i (Set.mem_univ i))
      by_cases hi : i ∈ T
      · rw [Dd_pos m b T tt hm hi] at hxD
        exact orth_blk _ _ _ _ _ _ hxD hvO
      · rw [Dd_neg m b T tt hm hi, Submodule.mem_bot] at hxD
        rw [hxD]
        exact Bb_zero_left _
  have h5 : finrank (ZMod 2) (Submodule.pi Set.univ Q) ≤
      finrank (ZMod 2) (Rs m b (Submodule.pi Set.univ U) T) := Submodule.finrank_mono hQR
  rw [finrank_pi_sub, hQs] at h5
  calc _ ≤ min h (min (∑ i, (2 * m i + (b i).toNat) - h) (∑ i ∈ T, m i) +
        ∑ i ∈ T, (b i).toNat) := by omega
    _ ≤ _ := h5
theorem main (r : ℕ) (m : Fin r → ℕ) (b : Fin r → Bool) (T : Finset (Fin r)) (h k : ℕ)
    (hh : h ≤ ∑ i : Fin r, (2*m i+(b i).toNat)) (productOnly : Bool) :
    (∃ S : Submodule (ZMod 2) (X m b), Module.finrank (ZMod 2) S = h ∧
      (productOnly = true → ∃ U : (i : Fin r) → Submodule (ZMod 2) (Blk (m i) (b i).toNat),
        ∀ x : X m b, x ∈ S ↔ ∀ i : Fin r, x i ∈ U i) ∧
      k ≤ Nat.card {u : S // (∀ i : Fin r, i ∉ T → u.val i = 0) ∧
        ∀ v : S, ∀ i : Fin r, Bb (u.val i) (v.val i) = 0}) ↔
    k ≤ 2 ^ (min h ((∑ i ∈ T, (b i).toNat) +
      min ((∑ i : Fin r, (2*m i+(b i).toNat)) - h) (∑ i ∈ T, m i))) := by
  have hcard : ∀ S : Submodule (ZMod 2) (X m b),
      Nat.card {u : S // (∀ i : Fin r, i ∉ T → u.val i = 0) ∧
        ∀ v : S, ∀ i : Fin r, Bb (u.val i) (v.val i) = 0} = 2 ^ finrank (ZMod 2) (Rs m b S T) := by
    intro S
    have e1 : Nat.card (Rs m b S T) = 2 ^ finrank (ZMod 2) (Rs m b S T) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [← e1]
    exact Nat.card_congr
      { toFun := fun u => ⟨u.1.1, (mem_Rs m b).mpr ⟨u.1.2, u.2.1, fun v hv i => u.2.2 ⟨v, hv⟩ i⟩⟩
        invFun := fun x => ⟨⟨x.1, ((mem_Rs m b).mp x.2).1⟩, ((mem_Rs m b).mp x.2).2.1,
          fun v i => ((mem_Rs m b).mp x.2).2.2 v.1 v.2 i⟩
        left_inv := fun u => rfl
        right_inv := fun x => rfl }
  constructor
  · rintro ⟨S, hS, -, hk⟩
    rw [hcard S] at hk
    have := upper m b S T
    rw [hS] at this
    exact le_trans hk (Nat.pow_le_pow_right (by norm_num) this)
  · intro hk
    obtain ⟨U, hU1, hU2⟩ := lower m b T h hh
    refine ⟨Submodule.pi Set.univ U, hU1, fun _ => ⟨U, fun x => by simp [Submodule.mem_pi]⟩, ?_⟩
    rw [hcard]
    exact le_trans hk (Nat.pow_le_pow_right (by norm_num) hU2)
end PEqualNP.Outside.L_pcx_434
theorem PEqualNP.Outside.L_pcx_434 : ∀ (r : ℕ) (m : Fin r → ℕ) (b : Fin r → Bool),
  let F := ZMod 2
  let V := fun i : Fin r =>
    ((Fin (m i) → F) × (Fin (m i) → F)) × (Fin (b i).toNat → F)
  let X := (i : Fin r) → V i
  let N := ∑ i : Fin r, (2*m i+(b i).toNat)
  let B := fun (i : Fin r) (u v : V i) =>
    ∑ j : Fin (m i), (u.1.1 j*v.1.2 j + u.1.2 j*v.1.1 j)
  ∀ (T : Finset (Fin r)) (h k : ℕ) (_ : h ≤ N) (productOnly : Bool),
    let cap := min h ((∑ i ∈ T, (b i).toNat) + min (N-h) (∑ i ∈ T, m i))
    (∃ S : Submodule F X, Module.finrank F S = h ∧
      (productOnly = true → ∃ U : (i : Fin r) → Submodule F (V i),
        ∀ x : X, x ∈ S ↔ ∀ i : Fin r, x i ∈ U i) ∧
      k ≤ Nat.card {u : S // (∀ i : Fin r, i ∉ T → u.val i = 0) ∧
        ∀ v : S, ∀ i : Fin r, B i (u.val i) (v.val i) = 0}) ↔ k ≤ 2^cap := by
  intro r m b F V X N B T h k hh productOnly cap
  exact PEqualNP.Outside.L_pcx_434.main r m b T h k hh productOnly

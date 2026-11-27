import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_248

lemma dbl {m : ℕ} (x : Fin m → ZMod 2) : x + x = 0 := by
  funext j
  exact CharTwo.add_self_eq_zero (x j)

lemma eqz {m : ℕ} (x y : Fin m → ZMod 2) (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [dbl y, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]

lemma p1 (n : ℕ) (k : Fin 3 → ℕ)
    (A : (i : Fin 3) → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (k i) → ZMod 2))
    (b : (i : Fin 3) → (Fin (k i) → ZMod 2)) :
    (∀ word : Fin 3 → (Fin n → ZMod 2),
      (∀ i : Fin 3, A i (word i) + b i = A i (word (i + 1)) + b i) → ∀ p : Fin 3, word p = word 0) ↔
    ∀ u : Fin 3 → (Fin n → ZMod 2), (∀ e, A e (u e) = 0) → (∑ e, u e) = 0 → ∀ e, u e = 0 := by
  constructor
  · intro hs u hu hsum
    rw [Fin.sum_univ_three] at hsum
    have h01 : u 0 + u 1 = u 2 := eqz _ _ hsum
    have hw := hs ![0, u 0, u 0 + u 1] (by
      intro i
      fin_cases i
      · show A 0 0 + b 0 = A 0 (u 0) + b 0
        rw [map_zero, hu 0]
      · show A 1 (u 0) + b 1 = A 1 (u 0 + u 1) + b 1
        rw [map_add, hu 1, add_zero]
      · show A 2 (u 0 + u 1) + b 2 = A 2 0 + b 2
        rw [h01, hu 2, map_zero])
    have h0 : u 0 = 0 := hw 1
    have h1' : u 0 + u 1 = 0 := hw 2
    have h1 : u 1 = 0 := by
      rw [h0, zero_add] at h1'
      exact h1'
    have h2 : u 2 = 0 := by
      rw [← h01, h0, h1, add_zero]
    intro e
    fin_cases e
    · exact h0
    · exact h1
    · exact h2
  · intro hk word hw
    have hA : ∀ i : Fin 3, A i (word i + word (i + 1)) = 0 := by
      intro i
      rw [map_add, add_right_cancel (hw i)]
      exact dbl _
    have hsum : (∑ e : Fin 3, (word e + word (e + 1))) = 0 := by
      rw [Fin.sum_univ_three]
      show (word 0 + word 1) + (word 1 + word 2) + (word 2 + word 0) = 0
      have : (word 0 + word 1) + (word 1 + word 2) + (word 2 + word 0) =
          (word 0 + word 0) + (word 1 + word 1) + (word 2 + word 2) := by abel
      rw [this, dbl (word 0), dbl (word 1), dbl (word 2), add_zero, add_zero]
    have hz := hk (fun e => word e + word (e + 1)) hA hsum
    have e01 : word 0 = word 1 := eqz _ _ (hz 0)
    have e12 : word 1 = word 2 := eqz _ _ (hz 1)
    intro p
    fin_cases p
    · rfl
    · exact e01.symm
    · exact (e01.trans e12).symm

def del (n k s m : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x := fun j => if h : (if j.val < s then j.val else j.val + m) < n then x ⟨_, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases h : (if j.val < s then j.val else j.val + m) < n <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : (if j.val < s then j.val else j.val + m) < n <;> simp [h]

lemma del_zero (n k s m : ℕ) (hk : n - m ≤ k) (hs : s + m ≤ n) (x : Fin n → ZMod 2)
    (hx : del n k s m x = 0) (i : Fin n) (hi : ¬ (s ≤ i.val ∧ i.val < s + m)) : x i = 0 := by
  by_cases h1 : i.val < s
  · have hj : i.val < k := by omega
    have := congrFun hx ⟨i.val, hj⟩
    have hc : (if i.val < s then i.val else i.val + m) < n := by
      rw [if_pos h1]
      exact i.2
    simp only [del, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [dif_pos hc] at this
    have hi' : (⟨if i.val < s then i.val else i.val + m, hc⟩ : Fin n) = i := by
      apply Fin.ext
      show (if i.val < s then i.val else i.val + m) = i.val
      rw [if_pos h1]
    rw [hi'] at this
    exact this
  · have h2 : s + m ≤ i.val := by omega
    have hj : i.val - m < k := by
      have := i.2
      omega
    have := congrFun hx ⟨i.val - m, hj⟩
    have hns : ¬ (i.val - m < s) := by omega
    have hc : (if i.val - m < s then i.val - m else i.val - m + m) < n := by
      rw [if_neg hns]
      have := i.2
      omega
    simp only [del, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [dif_pos hc] at this
    have hi' : (⟨if i.val - m < s then i.val - m else i.val - m + m, hc⟩ : Fin n) = i := by
      apply Fin.ext
      show (if i.val - m < s then i.val - m else i.val - m + m) = i.val
      rw [if_neg hns]
      omega
    rw [hi'] at this
    exact this

lemma p2a (n : ℕ) (k : Fin 3 → ℕ)
    (A : (i : Fin 3) → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (k i) → ZMod 2))
    (hk : ∀ u : Fin 3 → (Fin n → ZMod 2), (∀ e, A e (u e) = 0) → (∑ e, u e) = 0 → ∀ e, u e = 0) :
    2 * n ≤ ∑ j : Fin 3, min n (k j) := by
  let Φ : ((e : Fin 3) → LinearMap.ker (A e)) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    ∑ e : Fin 3, (LinearMap.ker (A e)).subtype.comp (LinearMap.proj e)
  have hΦ : ∀ u, Φ u = ∑ e : Fin 3, (u e : Fin n → ZMod 2) := by
    intro u
    simp [Φ, LinearMap.sum_apply]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hΦ] at hu
    have := hk (fun e => (u e : Fin n → ZMod 2)) (fun e => (u e).2) hu
    funext e
    exact Subtype.ext (this e)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, Module.finrank_fin_fun, Fin.sum_univ_three] at hle
  have hr : ∀ e : Fin 3, Module.finrank (ZMod 2) (LinearMap.range (A e)) +
      Module.finrank (ZMod 2) (LinearMap.ker (A e)) = n := by
    intro e
    have := LinearMap.finrank_range_add_finrank_ker (A e)
    rw [Module.finrank_fin_fun] at this
    exact this
  have hrk : ∀ e : Fin 3, Module.finrank (ZMod 2) (LinearMap.range (A e)) ≤ k e := by
    intro e
    have := Submodule.finrank_le (LinearMap.range (A e))
    rw [Module.finrank_fin_fun] at this
    exact this
  rw [Fin.sum_univ_three]
  have a0 := hr 0
  have a1 := hr 1
  have a2 := hr 2
  have b0 := hrk 0
  have b1 := hrk 1
  have b2 := hrk 2
  omega

lemma p2b (n : ℕ) (k : Fin 3 → ℕ) (h : 2 * n ≤ ∑ j : Fin 3, min n (k j)) :
    ∃ (A : (i : Fin 3) → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (k i) → ZMod 2)),
      ∀ u : Fin 3 → (Fin n → ZMod 2), (∀ e, A e (u e) = 0) → (∑ e, u e) = 0 → ∀ e, u e = 0 := by
  rw [Fin.sum_univ_three] at h
  refine ⟨fun e => del n (k e) (if e = 0 then 0 else if e = 1 then n - min n (k 0)
    else (n - min n (k 0)) + (n - min n (k 1))) (n - min n (k e)), ?_⟩
  intro u hu hsum
  have z0 : ∀ i : Fin n, ¬ (i.val < n - min n (k 0)) → u 0 i = 0 := by
    intro i hi
    refine del_zero n (k 0) 0 (n - min n (k 0)) (by omega) (by omega) (u 0) (hu 0) i (by omega)
  have z1 : ∀ i : Fin n, ¬ (n - min n (k 0) ≤ i.val ∧ i.val < (n - min n (k 0)) + (n - min n (k 1))) →
      u 1 i = 0 := by
    intro i hi
    refine del_zero n (k 1) (n - min n (k 0)) (n - min n (k 1)) (by omega) (by omega) (u 1) (hu 1) i hi
  have z2 : ∀ i : Fin n, ¬ ((n - min n (k 0)) + (n - min n (k 1)) ≤ i.val ∧
      i.val < (n - min n (k 0)) + (n - min n (k 1)) + (n - min n (k 2))) → u 2 i = 0 := by
    intro i hi
    refine del_zero n (k 2) ((n - min n (k 0)) + (n - min n (k 1))) (n - min n (k 2)) (by omega) (by omega)
      (u 2) (hu 2) i hi
  rw [Fin.sum_univ_three] at hsum
  have hpt : ∀ i : Fin n, u 0 i + u 1 i + u 2 i = 0 := fun i => congrFun hsum i
  have hall : ∀ i : Fin n, u 0 i = 0 ∧ u 1 i = 0 ∧ u 2 i = 0 := by
    intro i
    have hp := hpt i
    by_cases h0 : i.val < n - min n (k 0)
    · have e1 := z1 i (by omega)
      have e2 := z2 i (by omega)
      rw [e1, e2, add_zero, add_zero] at hp
      exact ⟨hp, e1, e2⟩
    · have e0 := z0 i h0
      by_cases h1 : i.val < (n - min n (k 0)) + (n - min n (k 1))
      · have e2 := z2 i (by omega)
        rw [e0, e2, zero_add, add_zero] at hp
        exact ⟨e0, hp, e2⟩
      · have e1 := z1 i (by omega)
        rw [e0, e1, zero_add, zero_add] at hp
        exact ⟨e0, e1, hp⟩
  intro e
  funext i
  fin_cases e
  · exact (hall i).1
  · exact (hall i).2.1
  · exact (hall i).2.2

end PEqualNP.Outside.L_pcx_248

theorem PEqualNP.Outside.L_pcx_248 : ∀ (n : ℕ) (k : Fin 3 → ℕ),
  let X := Fin n → ZMod 2
  let Y := fun i : Fin 3 => Fin (k i) → ZMod 2
  let sound := fun code : X → (index : Fin 3) → Y index =>
    ∀ word : Fin 3 → X, (∀ i : Fin 3, code (word i) i = code (word (i+1)) i) →
      ∀ p : Fin 3, word p = word 0
  (∀ (A : (i : Fin 3) → X →ₗ[ZMod 2] Y i) (b : (i : Fin 3) → Y i),
    sound (fun input slot => A slot input + b slot) ↔
      ∀ u : Fin 3 → X, (∀ e, A e (u e) = 0) → (∑ e, u e) = 0 → ∀ e, u e = 0) ∧
  ((∃ (maps : (i : Fin 3) → X →ₗ[ZMod 2] Y i) (offset : (i : Fin 3) → Y i),
      sound (fun z edge => maps edge z + offset edge)) ↔
    2*n ≤ ∑ j : Fin 3, min n (k j)) := by
  intro n k X Y sound
  refine ⟨fun A b => PEqualNP.Outside.L_pcx_248.p1 n k A b, ?_⟩
  constructor
  · rintro ⟨maps, offset, hs⟩
    exact PEqualNP.Outside.L_pcx_248.p2a n k maps ((PEqualNP.Outside.L_pcx_248.p1 n k maps offset).mp hs)
  · intro h
    obtain ⟨A, hA⟩ := PEqualNP.Outside.L_pcx_248.p2b n k h
    exact ⟨A, fun _ => 0, (PEqualNP.Outside.L_pcx_248.p1 n k A (fun _ => 0)).mpr hA⟩

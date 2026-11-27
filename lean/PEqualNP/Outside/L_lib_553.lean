import Mathlib

namespace PEqualNP.Outside.L_lib_553_aux

open Matrix

theorem li_insert {K : Type} [Field K] {d : ℕ} (f : List (Fin q) → (Fin d → K))
    (P : Finset (List (Fin q))) (x : List (Fin q)) (hx : x ∉ P)
    (h : LinearIndependent K (fun w : P => f w.val))
    (hf : f x ∉ Submodule.span K (f '' (↑P : Set (List (Fin q))))) :
    LinearIndependent K (fun w : (insert x P : Finset (List (Fin q))) => f w.val) := by
  have h2 : LinearIndepOn K f (insert x (↑P : Set (List (Fin q)))) :=
    (linearIndepOn_insert (by simpa using hx)).2 ⟨h, hf⟩
  rw [← Finset.coe_insert] at h2
  exact h2

theorem card_le {K : Type} [Field K] {d : ℕ} (f : List (Fin q) → (Fin d → K))
    (P : Finset (List (Fin q))) (h : LinearIndependent K (fun w : P => f w.val)) :
    P.card ≤ d := by
  have := h.fintype_card_le_finrank
  simpa using this

theorem pre_closed (P : Finset (List (Fin q))) (hP : ∀ w a, w ++ [a] ∈ P → w ∈ P) :
    ∀ v u, u ++ v ∈ P → u ∈ P := by
  intro v
  induction v using List.reverseRecOn with
  | nil => intro u hu; simpa using hu
  | append_singleton v b ih =>
    intro u hu
    apply ih
    apply hP _ b
    simpa [List.append_assoc] using hu

theorem len_lt {K : Type} [Field K] {d : ℕ} (f : List (Fin q) → (Fin d → K))
    (P : Finset (List (Fin q))) (hP : ∀ w a, w ++ [a] ∈ P → w ∈ P)
    (h : LinearIndependent K (fun w : P => f w.val)) : ∀ w ∈ P, w.length < d := by
  intro w hw
  have hsub : (Finset.range (w.length + 1)).image (fun k => w.take k) ⊆ P := by
    intro u hu
    simp only [Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨k, _, rfl⟩ := hu
    exact pre_closed P hP (w.drop k) _ (by simpa using hw)
  have hc : ((Finset.range (w.length + 1)).image (fun k => w.take k)).card = w.length + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg List.length hab
    simp only [List.length_take] at this
    omega
  have := Finset.card_le_card hsub
  have := card_le f P h
  omega

theorem extend {K : Type} [Field K] {d : ℕ} (s : Fin d → K) (f : List (Fin q) → (Fin d → K))
    (hf0 : f [] = s) :
    ∀ n, ∀ P : Finset (List (Fin q)), d - P.card = n → (∀ w a, w ++ [a] ∈ P → w ∈ P) →
      LinearIndependent K (fun w : P => f w.val) →
      ∃ P' : Finset (List (Fin q)), (∀ w a, w ++ [a] ∈ P' → w ∈ P') ∧
        LinearIndependent K (fun w : P' => f w.val) ∧
        s ∈ Submodule.span K (f '' (↑P' : Set (List (Fin q)))) ∧
        ∀ w ∈ P', ∀ a, f (w ++ [a]) ∈ Submodule.span K (f '' (↑P' : Set (List (Fin q)))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP hli
  have hcard := card_le f P hli
  by_cases hs : s ∈ Submodule.span K (f '' (↑P : Set (List (Fin q))))
  · by_cases hcl : ∀ w ∈ P, ∀ a, f (w ++ [a]) ∈ Submodule.span K (f '' (↑P : Set (List (Fin q))))
    · exact ⟨P, hP, hli, hs, hcl⟩
    · push Not at hcl
      obtain ⟨w, hw, a, hwa⟩ := hcl
      have hnot : w ++ [a] ∉ P := by
        intro hm
        exact hwa (Submodule.subset_span ⟨_, hm, rfl⟩)
      have hli' := li_insert f P _ hnot hli hwa
      have hc' := card_le f _ hli'
      rw [Finset.card_insert_of_notMem hnot] at hc'
      refine ih (d - (insert (w ++ [a]) P).card) (by rw [Finset.card_insert_of_notMem hnot]; omega)
        _ rfl ?_ hli'
      intro v b hv
      rcases Finset.mem_insert.mp hv with h1 | h1
      · have := List.append_inj' h1 rfl
        rw [this.1]
        exact Finset.mem_insert_of_mem hw
      · exact Finset.mem_insert_of_mem (hP v b h1)
  · have hnot : [] ∉ P := by
      intro hm
      exact hs (hf0 ▸ Submodule.subset_span ⟨_, hm, rfl⟩)
    have hli' := li_insert f P [] hnot hli (by rw [hf0]; exact hs)
    have hc' := card_le f _ hli'
    rw [Finset.card_insert_of_notMem hnot] at hc'
    refine ih (d - (insert [] P).card) (by rw [Finset.card_insert_of_notMem hnot]; omega)
      _ rfl ?_ hli'
    intro v b hv
    rcases Finset.mem_insert.mp hv with h1 | h1
    · simp at h1
    · exact Finset.mem_insert_of_mem (hP v b h1)

theorem span_main {K : Type} [Field K] (q d : ℕ) (s : Fin d → K)
    (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) :
    ∃ P : Finset (List (Fin q)), P.card ≤ d ∧
      (∀ w ∈ P, w.length < d) ∧ (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧
      LinearIndependent K (fun w : P => (fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s) w.val) ∧
      ∀ w, (fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s) w ∈
        Submodule.span K ((fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s) ''
          (↑P : Set (List (Fin q)))) := by
  set f := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s with hfdef
  have hf0 : f [] = s := rfl
  have hfs : ∀ w a, f (w ++ [a]) = A a (f w) := by
    intro w a
    simp [hfdef, List.foldl_append]
  obtain ⟨P, hP, hli, hs, hcl⟩ := extend s f hf0 (d - (∅ : Finset (List (Fin q))).card) ∅ rfl
    (by simp) (linearIndependent_empty_type)
  refine ⟨P, card_le f P hli, len_lt f P hP hli, hP, hli, ?_⟩
  set S := Submodule.span K (f '' (↑P : Set (List (Fin q))))
  have hinv : ∀ a, S ≤ S.comap (A a) := by
    intro a
    rw [Submodule.span_le]
    rintro y ⟨w, hw, rfl⟩
    show A a (f w) ∈ S
    rw [← hfs]
    exact hcl w hw a
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [hf0]; exact hs
  | append_singleton w a ih =>
    rw [hfs]
    exact hinv a ih

def init {d : ℕ} (s : Fin d → ℚ) : Matrix (Fin d) (Fin d) ℚ := Matrix.of (fun i j => s i * s j)

def Gk {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) (k : ℕ) :
    Matrix (Fin d) (Fin d) ℚ :=
  Nat.rec (motive := fun _ => Matrix (Fin d) (Fin d) ℚ) (init s)
    (fun _ old => init s + ∑ a : Fin q, A a * old * (A a).transpose) k

def run {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) (w : List (Fin q)) :
    Fin d → ℚ := w.foldl (fun v a => Matrix.mulVec (A a) v) s

theorem run_snoc {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ)
    (w : List (Fin q)) (a : Fin q) : run s A (w ++ [a]) = A a *ᵥ run s A w := by
  simp [run, List.foldl_append]

theorem adj {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) (v z : Fin d → ℚ) :
    (M *ᵥ v) ⬝ᵥ z = v ⬝ᵥ (M.transpose *ᵥ z) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

theorem initv {d : ℕ} (s z : Fin d → ℚ) : init s *ᵥ z = (s ⬝ᵥ z) • s := by
  ext i
  simp only [init, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem key2 {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) (k : ℕ)
    (z : Fin d → ℚ) : Gk s A (k + 1) *ᵥ z =
      (s ⬝ᵥ z) • s + ∑ a : Fin q, A a *ᵥ (Gk s A k *ᵥ ((A a).transpose *ᵥ z)) := by
  show (init s + ∑ a : Fin q, A a * Gk s A k * (A a).transpose) *ᵥ z = _
  rw [Matrix.add_mulVec, initv, Matrix.sum_mulVec]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem key {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) (k : ℕ)
    (z : Fin d → ℚ) : z ⬝ᵥ (Gk s A (k + 1) *ᵥ z) =
      (s ⬝ᵥ z) ^ 2 + ∑ a : Fin q, ((A a).transpose *ᵥ z) ⬝ᵥ
        (Gk s A k *ᵥ ((A a).transpose *ᵥ z)) := by
  rw [key2, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_comm z s, sq]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [dotProduct_comm, adj, dotProduct_comm]

theorem zero_side {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) :
    ∀ k z, (∀ w : List (Fin q), w.length ≤ k → run s A w ⬝ᵥ z = 0) → Gk s A k *ᵥ z = 0 := by
  intro k
  induction k with
  | zero =>
    intro z h
    show init s *ᵥ z = 0
    rw [initv]
    have : s ⬝ᵥ z = 0 := h [] (by simp)
    simp [this]
  | succ k ih =>
    intro z h
    rw [key2]
    have h0 : s ⬝ᵥ z = 0 := h [] (by simp)
    have hs : ∀ a, Gk s A k *ᵥ ((A a).transpose *ᵥ z) = 0 := by
      intro a
      apply ih
      intro u hu
      rw [← adj, ← run_snoc]
      exact h _ (by simp; omega)
    simp [h0, hs]

theorem pos_side {q d : ℕ} (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) :
    ∀ k z, 0 ≤ z ⬝ᵥ (Gk s A k *ᵥ z) ∧ (z ⬝ᵥ (Gk s A k *ᵥ z) = 0 →
      ∀ w : List (Fin q), w.length ≤ k → run s A w ⬝ᵥ z = 0) := by
  intro k
  induction k with
  | zero =>
    intro z
    have e : z ⬝ᵥ (Gk s A 0 *ᵥ z) = (s ⬝ᵥ z) ^ 2 := by
      show z ⬝ᵥ (init s *ᵥ z) = _
      rw [initv, dotProduct_smul, smul_eq_mul, dotProduct_comm z s, sq]
    rw [e]
    refine ⟨sq_nonneg _, ?_⟩
    intro h0 w hw
    have hw' : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  | succ k ih =>
    intro z
    rw [key]
    have hnn : ∀ a ∈ (Finset.univ : Finset (Fin q)), 0 ≤ ((A a).transpose *ᵥ z) ⬝ᵥ
        (Gk s A k *ᵥ ((A a).transpose *ᵥ z)) := fun a _ => (ih _).1
    refine ⟨add_nonneg (sq_nonneg _) (Finset.sum_nonneg hnn), ?_⟩
    intro h0
    have h1 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (Finset.sum_nonneg hnn)).1 h0
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.2
    intro w hw
    induction w using List.reverseRecOn with
    | nil => exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1.1
    | append_singleton u a _ =>
      rw [run_snoc, adj]
      exact (ih _).2 (h2 a (Finset.mem_univ _)) u (by simp at hw; omega)

theorem main (q d : ℕ) (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ) (z : Fin d → ℚ) :
    Gk s A (d - 1) *ᵥ z = 0 ↔ ∀ w : List (Fin q), z ⬝ᵥ run s A w = 0 := by
  constructor
  · intro h
    have hq : z ⬝ᵥ (Gk s A (d - 1) *ᵥ z) = 0 := by rw [h]; simp
    have hshort := (pos_side s A (d - 1) z).2 hq
    obtain ⟨P, _, hlen, _, _, hspan⟩ := span_main q d s (fun a => Matrix.mulVecLin (A a))
    let ℓ : (Fin d → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun v => z ⬝ᵥ v
        map_add' := fun x y => dotProduct_add z x y
        map_smul' := fun c x => by simp [dotProduct_smul] }
    have hle : Submodule.span ℚ ((fun (w : List (Fin q)) =>
        w.foldl (fun x a => Matrix.mulVecLin (A a) x) s) '' (↑P : Set (List (Fin q)))) ≤
        LinearMap.ker ℓ := by
      rw [Submodule.span_le]
      rintro y ⟨u, hu, rfl⟩
      show z ⬝ᵥ _ = 0
      rw [dotProduct_comm]
      have := hshort u (by have := hlen u hu; omega)
      exact this
    intro w
    exact hle (hspan w)
  · intro h
    apply zero_side
    intro w _
    rw [dotProduct_comm]
    exact h w

end PEqualNP.Outside.L_lib_553_aux

theorem PEqualNP.Outside.L_lib_553 : ∀ (q d : ℕ) (s : Fin d → ℚ) (A : Fin q → Matrix (Fin d) (Fin d) ℚ),
  let init := Matrix.of (fun i j => s i * s j)
  let upd := fun G : Matrix (Fin d) (Fin d) ℚ =>
    init + ∑ a : Fin q, A a * G * (A a).transpose
  let G := Nat.rec init (fun _ old => upd old) (d - 1)
  ∀ z : Fin d → ℚ, Matrix.mulVec G z = 0 ↔
    ∀ w : List (Fin q), dotProduct z (w.foldl (fun v a => Matrix.mulVec (A a) v) s) = 0 := by
  intro q d s A init upd G z
  exact PEqualNP.Outside.L_lib_553_aux.main q d s A z
